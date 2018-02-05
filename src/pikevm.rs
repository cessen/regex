// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This module implements the Pike VM. That is, it guarantees linear time
// search of a regex on any text with memory use proportional to the size of
// the regex.
//
// It is equal in power to the backtracking engine in this crate, except the
// backtracking engine is typically faster on small regexes/texts at the
// expense of a bigger memory footprint.
//
// It can do more than the DFA can (specifically, record capture locations
// and execute Unicode word boundary assertions), but at a slower speed.
// Specifically, the Pike VM exectues a DFA implicitly by repeatedly expanding
// epsilon transitions. That is, the Pike VM engine can be in multiple states
// at once where as the DFA is only ever in one state at a time.
//
// Therefore, the Pike VM is generally treated as the fallback when the other
// matching engines either aren't feasible to run or are insufficient.

use input::{Input, InputAt, is_empty_match};
use prog::{Program, InstPtr};
use re_trait::Slot;
use sparse::SparseSet;

/// An NFA simulation matching engine.
#[derive(Debug)]
pub struct Fsm<'r> {
    /// The sequence of opcodes (among other things) that is actually executed.
    ///
    /// The program may be byte oriented or Unicode codepoint oriented.
    prog: &'r Program,
    /// Whether the engine should quit immediately if it finds any match.
    /// This is used when we only care if there _is_ a match or not, not
    /// what the match(es) is.
    quit_after_match: bool,
}

/// A cached allocation that can be reused on each execution.
#[derive(Clone, Debug)]
pub struct Cache {
    /// A pair of ordered sets for tracking NFA states.
    clist: Threads,
    nlist: Threads,
    /// An explicit stack used for following epsilon transitions.
    stack: Vec<FollowEpsilon>,
    /// Keeps track of whether all matches have been made so far.
    all_matched: bool,
    /// The previous input
    at_prev: InputAt,
    /// The current byte position in the total input
    pos: usize,
}

/// An ordered set of NFA states and their captures.
#[derive(Clone, Debug)]
struct Threads {
    /// An ordered set of opcodes (each opcode is an NFA state).
    set: SparseSet,
    /// Captures for every NFA state.
    ///
    /// It is stored in row-major order, where the columns are the capture
    /// slots and the rows are the states.
    caps: Vec<Slot>,
    /// The number of capture slots stored per thread. (Every capture has
    /// two slots.)
    slots_per_thread: usize,
}

/// A representation of an explicit stack frame when following epsilon
/// transitions. This is used to avoid recursion.
#[derive(Clone, Debug)]
enum FollowEpsilon {
    /// Follow transitions at the given instruction pointer.
    IP(InstPtr),
    /// Restore the capture slot with the given position in the input.
    Capture { slot: usize, pos: Slot },
}

impl Cache {
    /// Create a new allocation used by the NFA machine to record execution
    /// and captures.
    pub fn new(prog: &Program) -> Self {
        let mut clist = Threads::new();
        let mut nlist = Threads::new();
        clist.resize(prog.len(), prog.captures.len());
        nlist.resize(prog.len(), prog.captures.len());
        Cache {
            clist: clist,
            nlist: nlist,
            stack: vec![],
            all_matched: false,
            at_prev: InputAt::null(),
            pos: 0,
        }
    }

    pub fn prep_for_next_match(&mut self) {
        self.clist.set.clear();
        self.nlist.set.clear();
        self.all_matched = false;
    }

    pub fn reset(&mut self) {
        self.prep_for_next_match();
        self.at_prev = InputAt::null();
    }
}

impl<'r> Fsm<'r> {
    /// Creates a new instance of the PikeVM engine.
    pub fn new(
        prog: &'r Program,
        quit_after_match: bool,
    ) -> Self {
        Fsm {
            prog: prog,
            quit_after_match: quit_after_match,
        }
    }

    /// Feed the engine a single token (byte or unicode scalar value).
    ///
    /// Returns whether it's done matching or not:
    ///     - true: done matching.
    ///     - false: needs more input to complete matching.
    ///
    /// When it indicates that it's done matching, the matches (if any)
    /// are in `matches` and `slots`.  `matches` and `slots` should not
    /// be manipulated in between calls if more input is needed, as
    /// they are used progressively across calls during the matching
    /// process.
    pub fn next<I: Input>(
        &mut self,
        cache: &mut Cache,
        matches: &mut [bool],
        slots: &mut [Slot],
        at: InputAt,
        input: &I,
    ) -> bool {
        let mut stop = false;

        let at_prev = input.prev(at);

        if cache.clist.set.is_empty() {
            // Two ways to bail out when our current set of threads is
            // empty.
            //
            // 1. We have a match (or all matches if we're looking for
            //    matches for multiple regexes)--so we're done exploring
            //    any possible alternatives. Time to quit.
            //
            // 2. If the expression starts with a '^' we can terminate as
            //    soon as the last thread dies.
            if cache.all_matched
                || (!at.is_start() && self.prog.is_anchored_start) {
                return true;
            }
        }

        // This simulates a preceding '.*?' for every regex by adding
        // a state starting at the current position in the input for the
        // beginning of the program only if we don't already have a match.
        if cache.clist.set.is_empty()
            || (!self.prog.is_anchored_start && !cache.all_matched) {
            cache.clist.set.insert(0);
        }

        // Process epsilons in clist, and put the resulting non-epsilon
        // instructions into nlist.
        // Also copy over non-epsilon instructions without processing.
        cache.nlist.set.clear();
        for i in 0..cache.clist.set.len() {
            let ip = cache.clist.set[i];
            self.add_with_epsilon_processing(
                &mut cache.stack,
                &mut cache.nlist,
                cache.clist.caps(ip),
                ip,
                at_prev,
                at,
                input.only_utf8()
            );
        }

        // Process instructions in nlist, and put the resulting instructions
        // into clist.
        let mut matched = false;
        cache.clist.set.clear();
        for i in 0..cache.nlist.set.len() {
            let ip = cache.nlist.set[i];

            use prog::Inst::*;
            matched |= match self.prog[ip] {
                Match(match_slot) => {
                    if match_slot < matches.len() {
                        matches[match_slot] = true;
                    } else {
                        matches[0] = true;
                    }
                    for (slot, val) in slots.iter_mut().zip(cache.nlist.caps(ip).iter()) {
                        *slot = *val;
                    }
                    true
                }
                Char(ref inst) => {
                    if inst.c == at.char() {
                        self.add(&mut cache.clist, cache.nlist.caps(ip), inst.goto);
                    }
                    false
                }
                Ranges(ref inst) => {
                    if inst.matches(at.char()) {
                        self.add(&mut cache.clist, cache.nlist.caps(ip), inst.goto);
                    }
                    false
                }
                Bytes(ref inst) => {
                    if let Some(b) = at.byte() {
                        if inst.matches(b) {
                            self.add(&mut cache.clist, cache.nlist.caps(ip), inst.goto);
                        }
                    }
                    false
                }
                EmptyLook(_) | Save(_) | Split(_) => false,
            };

            // If we only care if a match occurs (not its
            // position), then we can quit right now.
            // We also don't need to check the rest of the threads
            // in this set if there's only one match possible because
            // we've matched something ("leftmost-first"). However, we
            // still need to check threads in the next set to support
            // things like greedy matching.
            if matched && (self.quit_after_match || self.prog.matches.len() == 1) {
                stop = self.quit_after_match;
                break;
            }
        }

        if matched {
            cache.all_matched = cache.all_matched || matches.iter().all(|&b| b);
        }

        return stop;
    }

    // Adds an instruction and copies associated captures to nlist.
    // Does no additional processing (e.g. of epsilons).
    fn add(
        &mut self,
        nlist: &mut Threads,
        thread_caps: &mut [Option<usize>],
        ip: usize,
    ) {
        // Only add if it's not already added
        if !nlist.set.contains(ip) {
            nlist.set.insert(ip);
            let t = &mut nlist.caps(ip);
            for (slot, val) in t.iter_mut().zip(thread_caps.iter()) {
                *slot = *val;
            }
        }
    }

    /// Follows epsilon transitions and adds them for processing to nlist,
    /// starting at and including ip.
    fn add_with_epsilon_processing(
        &mut self,
        stack: &mut Vec<FollowEpsilon>,
        nlist: &mut Threads,
        thread_caps: &mut [Option<usize>],
        ip: usize,
        at_prev: InputAt,
        at: InputAt,
        only_utf8: bool,
    ) {
        stack.push(FollowEpsilon::IP(ip));
        while let Some(frame) = stack.pop() {
            match frame {
                FollowEpsilon::IP(mut ip) => {
                    // Instead of pushing and popping to the stack, we mutate
                    // ip as we traverse the set of states. We only push to
                    // the stack when we absolutely need recursion (restoring
                    // captures or following a branch).
                    use prog::Inst::*;
                    loop {
                        // Don't visit states we've already added.
                        if nlist.set.contains(ip) {
                            break;
                        }
                        nlist.set.insert(ip);
                        match self.prog[ip] {
                            EmptyLook(ref inst) => {
                                if is_empty_match(
                                    at_prev,
                                    at,
                                    only_utf8,
                                    inst,
                                ) {
                                    ip = inst.goto;
                                }
                            }
                            Save(ref inst) => {
                                if inst.slot < thread_caps.len() {
                                    stack.push(FollowEpsilon::Capture {
                                        slot: inst.slot,
                                        pos: thread_caps[inst.slot],
                                    });
                                    thread_caps[inst.slot] = Some(at.pos());
                                }
                                ip = inst.goto;
                            }
                            Split(ref inst) => {
                                stack.push(FollowEpsilon::IP(inst.goto2));
                                ip = inst.goto1;
                            }
                            Match(_) | Char(_) | Ranges(_) | Bytes(_) => {
                                let t = &mut nlist.caps(ip);
                                for (slot, val) in t.iter_mut().zip(thread_caps.iter()) {
                                    *slot = *val;
                                }
                                break;
                            }
                        }
                    }
                }
                FollowEpsilon::Capture { slot, pos } => {
                    thread_caps[slot] = pos;
                }
            }
        }
    }
}

impl Threads {
    fn new() -> Self {
        Threads {
            set: SparseSet::new(0),
            caps: vec![],
            slots_per_thread: 0,
        }
    }

    fn resize(&mut self, num_insts: usize, ncaps: usize) {
        if num_insts == self.set.capacity() {
            return;
        }
        self.slots_per_thread = ncaps * 2;
        self.set = SparseSet::new(num_insts);
        self.caps = vec![None; self.slots_per_thread * num_insts];
    }

    fn caps(&mut self, pc: usize) -> &mut [Option<usize>] {
        let i = pc * self.slots_per_thread;
        &mut self.caps[i..i + self.slots_per_thread]
    }
}
