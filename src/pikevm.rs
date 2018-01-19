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
pub struct Fsm<'r, I> {
    /// The sequence of opcodes (among other things) that is actually executed.
    ///
    /// The program may be byte oriented or Unicode codepoint oriented.
    prog: &'r Program,
    /// An explicit stack used for following epsilon transitions. (This is
    /// borrowed from the cache.)
    cache: &'r mut Cache,
    /// The input to search.
    input: I,
}

/// A cached allocation that can be reused on each execution.
#[derive(Clone, Debug)]
pub struct Cache {
    /// A pair of ordered sets for tracking NFA states.
    clist: Threads,
    nlist: Threads,
    /// An explicit stack used for following epsilon transitions.
    stack: Vec<FollowEpsilon>,
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
    pub fn new(_prog: &Program) -> Self {
        Cache {
            clist: Threads::new(),
            nlist: Threads::new(),
            stack: vec![],
        }
    }
}

impl<'r, I: Input> Fsm<'r, I> {
    pub fn new(
        prog: &'r Program,
        cache: &'r mut Cache,
        input: I,
    ) -> Self {
        Fsm {
            prog: prog,
            cache: cache,
            input: input,
        }
    }

    /// Execute the NFA matching engine.
    ///
    /// If there's a match, `exec` returns `true` and populates the given
    /// captures accordingly.
    pub fn exec(
        &mut self,
        matches: &mut [bool],
        slots: &mut [Slot],
        quit_after_match: bool,
        start: usize,
    ) -> bool {
        self.cache.clist.resize(self.prog.len(), self.prog.captures.len());
        self.cache.nlist.resize(self.prog.len(), self.prog.captures.len());
        let mut at = self.input.at(start);

        let mut matched = false;
        let mut all_matched = false;
        self.cache.clist.set.clear();
        self.cache.nlist.set.clear();
'LOOP:  loop {
            if self.cache.clist.set.is_empty() {
                // Two ways to bail out when our current set of threads is
                // empty.
                //
                // 1. We have a match---so we're done exploring any possible
                //    alternatives. Time to quit. (We can't do this if we're
                //    looking for matches for multiple regexes, unless we know
                //    they all matched.)
                //
                // 2. If the expression starts with a '^' we can terminate as
                //    soon as the last thread dies.
                if (matched && matches.len() <= 1)
                    || all_matched
                    || (!at.is_start() && self.prog.is_anchored_start) {
                    break;
                }
            }

            // This simulates a preceding '.*?' for every regex by adding
            // a state starting at the current position in the input for the
            // beginning of the program only if we don't already have a match.
            if self.cache.clist.set.is_empty()
                || (!self.prog.is_anchored_start && !all_matched) {
                self.add(Some(slots), 0, 0, at);
            }
            // The previous call to "add" actually inspects the position just
            // before the current character. For stepping through the machine,
            // we can to look at the current character, so we advance the
            // input.
            let at_next = self.input.at(at.next_pos());
            for i in 0..self.cache.clist.set.len() {
                let ip = self.cache.clist.set[i];

                // Do step
                use prog::Inst::*;
                let step_result = match self.prog[ip] {
                    Match(match_slot) => {
                        if match_slot < matches.len() {
                            matches[match_slot] = true;
                        }
                        for (slot, val) in slots.iter_mut().zip(self.cache.clist.caps(ip).iter()) {
                            *slot = *val;
                        }
                        true
                    }
                    Char(ref inst) => {
                        if inst.c == at.char() {
                            self.add(None, ip, inst.goto, at_next);
                        }
                        false
                    }
                    Ranges(ref inst) => {
                        if inst.matches(at.char()) {
                            self.add(None, ip, inst.goto, at_next);
                        }
                        false
                    }
                    Bytes(ref inst) => {
                        if let Some(b) = at.byte() {
                            if inst.matches(b) {
                                self.add(None, ip, inst.goto, at_next);
                            }
                        }
                        false
                    }
                    EmptyLook(_) | Save(_) | Split(_) => false,
                };

                if step_result {
                    matched = true;
                    all_matched = all_matched || matches.iter().all(|&b| b);
                    if quit_after_match {
                        // If we only care if a match occurs (not its
                        // position), then we can quit right now.
                        break 'LOOP;
                    }
                    if self.prog.matches.len() == 1 {
                        // We don't need to check the rest of the threads
                        // in this set because we've matched something
                        // ("leftmost-first"). However, we still need to check
                        // threads in the next set to support things like
                        // greedy matching.
                        //
                        // This is only true on normal regexes. For regex sets,
                        // we need to mush on to observe other matches.
                        break;
                    }
                }
            }
            if at.is_end() {
                break;
            }
            at = at_next;
            mem::swap(&mut self.cache.clist, &mut self.cache.nlist);
            self.cache.nlist.set.clear();
        }
        matched
    }

    /// Follows epsilon transitions and adds them for processing to nlist,
    /// starting at and including ip.
    fn add(
        &mut self,
        thread_caps: Option<&mut [Option<usize>]>,
        ip_prev: usize,
        ip: usize,
        at: InputAt,
    ) {
        let (nlist, thread_caps) = if let Some(tc) = thread_caps {
            (&mut self.cache.clist, tc)
        } else {
            (&mut self.cache.nlist, self.cache.clist.caps(ip_prev))
        };
        self.cache.stack.push(FollowEpsilon::IP(ip));
        while let Some(frame) = self.cache.stack.pop() {
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
                                if self.input.is_empty_match(at, inst) {
                                    ip = inst.goto;
                                }
                            }
                            Save(ref inst) => {
                                if inst.slot < thread_caps.len() {
                                    self.cache.stack.push(FollowEpsilon::Capture {
                                        slot: inst.slot,
                                        pos: thread_caps[inst.slot],
                                    });
                                    thread_caps[inst.slot] = Some(at.pos());
                                }
                                ip = inst.goto;
                            }
                            Split(ref inst) => {
                                self.cache.stack.push(FollowEpsilon::IP(inst.goto2));
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
