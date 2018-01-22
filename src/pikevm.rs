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

use std::mem;

use input::{Input, InputAt};
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
    /// Input buffer for finding unicode code points.
    char_buffer: [u8; 4],
    char_buffer_len: usize,
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
            char_buffer: [0; 4],
            char_buffer_len: 0,
            pos: 0,
        }
    }

    pub fn prep_for_next_match(&mut self) {
        self.clist.set.clear();
        self.nlist.set.clear();
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

    /// Execute the NFA matching engine.
    ///
    /// If there's a match, `exec` returns `true` and populates the given
    /// captures accordingly.
    pub fn exec<I: Input>(
        &mut self,
        cache: &mut Cache,
        matches: &mut [bool],
        slots: &mut [Slot],
        start: usize,
        input: &I,
    ) {
        cache.prep_for_next_match();
        cache.pos = start;

        let mut at = input.at(cache.pos);
        cache.all_matched = false;
'LOOP:  loop {
            let stop = self.next(
                cache,
                matches,
                slots,
                at,
                input,
            );

            if stop || at.is_end() {
                break;
            }
            at = input.at(at.next_pos());
        }
    }

    pub fn next<I: Input>(
        &mut self,
        cache: &mut Cache,
        matches: &mut [bool],
        slots: &mut [Slot],
        at: InputAt,
        input: &I,
    ) -> bool {
        let mut stop = false;

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
            self.add(&mut cache.stack, &mut cache.clist, slots, 0, at, input);
        }
        // The previous call to "add" actually inspects the position just
        // before the current character. For stepping through the machine,
        // we can to look at the current character, so we advance the
        // input.
        let at_next = input.at(at.next_pos());

        // Loop through the threads and run them against this step of input.
        let mut matched = false;
        for i in 0..cache.clist.set.len() {
            let ip = cache.clist.set[i];

            use prog::Inst::*;
            matched |= match self.prog[ip] {
                Match(match_slot) => {
                    if match_slot < matches.len() {
                        matches[match_slot] = true;
                    } else {
                        matches[0] = true;
                    }
                    for (slot, val) in slots.iter_mut().zip(cache.clist.caps(ip).iter()) {
                        *slot = *val;
                    }
                    true
                }
                Char(ref inst) => {
                    if inst.c == at.char() {
                        self.add(&mut cache.stack, &mut cache.nlist, cache.clist.caps(ip), inst.goto, at_next, input);
                    }
                    false
                }
                Ranges(ref inst) => {
                    if inst.matches(at.char()) {
                        self.add(&mut cache.stack, &mut cache.nlist, cache.clist.caps(ip), inst.goto, at_next, input);
                    }
                    false
                }
                Bytes(ref inst) => {
                    if let Some(b) = at.byte() {
                        if inst.matches(b) {
                            self.add(&mut cache.stack, &mut cache.nlist, cache.clist.caps(ip), inst.goto, at_next, input);
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

        if !stop {
            mem::swap(&mut cache.clist, &mut cache.nlist);
            cache.nlist.set.clear();
        }

        return stop;
    }

    /// Follows epsilon transitions and adds them for processing to nlist,
    /// starting at and including ip.
    fn add<I: Input>(
        &mut self,
        stack: &mut Vec<FollowEpsilon>,
        nlist: &mut Threads,
        thread_caps: &mut [Option<usize>],
        ip: usize,
        at: InputAt,
        input: &I,
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
                                if input.is_empty_match(at, inst) {
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
