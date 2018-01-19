// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use thread_local::CachedThreadLocal;
use syntax::{Expr, ExprBuilder, Literals};

use compile::Compiler;
use error::Error;
use input::{ByteInput, CharInput};
use pikevm;
use prog::Program;
use re_builder::RegexOptions;
use re_set;
use re_trait::{RegularExpression, Slot, Locations, as_slots};
use re_unicode;
use utf8::next_utf8;

/// `Exec` manages the execution of a regular expression.
///
/// In particular, this manages the various compiled forms of a single regular
/// expression and the choice of which matching engine to use to execute a
/// regular expression.
pub struct Exec {
    /// All read only state.
    ro: Arc<ExecReadOnly>,
    /// Caches for the various matching engines.
    cache: CachedThreadLocal<ProgramCache>,
}

/// `ExecNoSync` is like `Exec`, except it embeds a reference to a cache. This
/// means it is no longer Sync, but we can now avoid the overhead of
/// synchronization to fetch the cache.
#[derive(Debug)]
pub struct ExecNoSync<'c> {
    /// All read only state.
    ro: &'c Arc<ExecReadOnly>,
    /// Caches for the various matching engines.
    cache: &'c ProgramCache,
}

/// `ExecNoSyncStr` is like `ExecNoSync`, but matches on &str instead of &[u8].
pub struct ExecNoSyncStr<'c>(ExecNoSync<'c>);

/// `ExecReadOnly` comprises all read only state for a regex. Namely, all such
/// state is determined at compile time and never changes during search.
#[derive(Debug)]
struct ExecReadOnly {
    /// The original regular expressions given by the caller to compile.
    res: Vec<String>,
    /// A compiled program that is used in the NFA simulation and backtracking.
    /// It can be byte-based or Unicode codepoint based.
    ///
    /// N.B. It is not possibly to make this byte-based from the public API.
    /// It is only used for testing byte based programs in the NFA simulations.
    nfa: Program,
    /// match_type encodes as much upfront knowledge about how we're going to
    /// execute a search as possible.
    match_type: MatchType,
}

/// Facilitates the construction of an executor by exposing various knobs
/// to control how a regex is executed and what kinds of resources it's
/// permitted to use.
pub struct ExecBuilder {
    options: RegexOptions,
    match_type: Option<MatchType>,
    bytes: bool,
    only_utf8: bool,
}

/// Parsed represents a set of parsed regular expressions and their detected
/// literals.
struct Parsed {
    exprs: Vec<Expr>,
    bytes: bool,
}

impl ExecBuilder {
    /// Create a regex execution builder.
    ///
    /// This uses default settings for everything except the regex itself,
    /// which must be provided. Further knobs can be set by calling methods,
    /// and then finally, `build` to actually create the executor.
    pub fn new(re: &str) -> Self {
        Self::new_many(&[re])
    }

    /// Like new, but compiles the union of the given regular expressions.
    ///
    /// Note that when compiling 2 or more regular expressions, capture groups
    /// are completely unsupported. (This means both `find` and `captures`
    /// wont work.)
    pub fn new_many<I, S>(res: I) -> Self
            where S: AsRef<str>, I: IntoIterator<Item=S> {
        let mut opts = RegexOptions::default();
        opts.pats = res.into_iter().map(|s| s.as_ref().to_owned()).collect();
        Self::new_options(opts)
    }

    /// Create a regex execution builder.
    pub fn new_options(opts: RegexOptions) -> Self {
        ExecBuilder {
            options: opts,
            match_type: None,
            bytes: false,
            only_utf8: true,
        }
    }

    /// Set the matching engine to be automatically determined.
    ///
    /// This is the default state and will apply whatever optimizations are
    /// possible, such as running a DFA.
    ///
    /// This overrides whatever was previously set via the `nfa` or
    /// `bounded_backtracking` methods.
    pub fn automatic(mut self) -> Self {
        self.match_type = None;
        self
    }

    /// Sets the matching engine to use the NFA algorithm no matter what
    /// optimizations are possible.
    ///
    /// This overrides whatever was previously set via the `automatic` or
    /// `bounded_backtracking` methods.
    pub fn nfa(mut self) -> Self {
        self.match_type = Some(MatchType::Nfa);
        self
    }

    /// Compiles byte based programs for use with the NFA matching engines.
    ///
    /// By default, the NFA engines match on Unicode scalar values. They can
    /// be made to use byte based programs instead. In general, the byte based
    /// programs are slower because of a less efficient encoding of character
    /// classes.
    ///
    /// Note that this does not impact DFA matching engines, which always
    /// execute on bytes.
    pub fn bytes(mut self, yes: bool) -> Self {
        self.bytes = yes;
        self
    }

    /// When disabled, the program compiled may match arbitrary bytes.
    ///
    /// When enabled (the default), all compiled programs exclusively match
    /// valid UTF-8 bytes.
    pub fn only_utf8(mut self, yes: bool) -> Self {
        self.only_utf8 = yes;
        self
    }

    /// Set the Unicode flag.
    pub fn unicode(mut self, yes: bool) -> Self {
        self.options.unicode = yes;
        self
    }

    /// Parse the current set of patterns into their AST and extract literals.
    fn parse(&self) -> Result<Parsed, Error> {
        let mut exprs = Vec::with_capacity(self.options.pats.len());
        let mut prefixes = Some(Literals::empty());
        let mut suffixes = Some(Literals::empty());
        let mut bytes = false;
        let is_set = self.options.pats.len() > 1;
        // If we're compiling a regex set and that set has any anchored
        // expressions, then disable all literal optimizations.
        for pat in &self.options.pats {
            let parser =
                ExprBuilder::new()
                    .case_insensitive(self.options.case_insensitive)
                    .multi_line(self.options.multi_line)
                    .dot_matches_new_line(self.options.dot_matches_new_line)
                    .swap_greed(self.options.swap_greed)
                    .ignore_whitespace(self.options.ignore_whitespace)
                    .unicode(self.options.unicode)
                    .allow_bytes(!self.only_utf8);
            let expr = try!(parser.parse(pat));
            bytes = bytes || expr.has_bytes();

            if !expr.is_anchored_start() && expr.has_anchored_start() {
                // Partial anchors unfortunately make it hard to use prefixes,
                // so disable them.
                prefixes = None;
            } else if is_set && expr.is_anchored_start() {
                // Regex sets with anchors do not go well with literal
                // optimizations.
                prefixes = None;
            }
            prefixes = prefixes.and_then(|mut prefixes| {
                if !prefixes.union_prefixes(&expr) {
                    None
                } else {
                    Some(prefixes)
                }
            });

            if !expr.is_anchored_end() && expr.has_anchored_end() {
                // Partial anchors unfortunately make it hard to use suffixes,
                // so disable them.
                suffixes = None;
            } else if is_set && expr.is_anchored_end() {
                // Regex sets with anchors do not go well with literal
                // optimizations.
                prefixes = None;
            }
            suffixes = suffixes.and_then(|mut suffixes| {
                if !suffixes.union_suffixes(&expr) {
                    None
                } else {
                    Some(suffixes)
                }
            });
            exprs.push(expr);
        }
        Ok(Parsed {
            exprs: exprs,
            bytes: bytes,
        })
    }

    /// Build an executor that can run a regular expression.
    pub fn build(self) -> Result<Exec, Error> {
        // Special case when we have no patterns to compile.
        // This can happen when compiling a regex set.
        if self.options.pats.is_empty() {
            let ro = Arc::new(ExecReadOnly {
                res: vec![],
                nfa: Program::new(),
                match_type: MatchType::Nothing,
            });
            return Ok(Exec { ro: ro, cache: CachedThreadLocal::new() });
        }
        let parsed = try!(self.parse());
        let nfa = try!(
            Compiler::new()
                     .size_limit(self.options.size_limit)
                     .bytes(self.bytes || parsed.bytes)
                     .only_utf8(self.only_utf8)
                     .compile(&parsed.exprs));

        let mut ro = ExecReadOnly {
            res: self.options.pats,
            nfa: nfa,
            match_type: MatchType::Nothing,
        };
        ro.match_type = ro.choose_match_type(self.match_type);

        let ro = Arc::new(ro);
        Ok(Exec { ro: ro, cache: CachedThreadLocal::new() })
    }
}

impl<'c> RegularExpression for ExecNoSyncStr<'c> {
    type Text = str;

    fn slots_len(&self) -> usize { self.0.slots_len() }

    fn next_after_empty(&self, text: &str, i: usize) -> usize {
        next_utf8(text.as_bytes(), i)
    }

    #[inline(always)] // reduces constant overhead
    fn shortest_match_at(&self, text: &str, start: usize) -> Option<usize> {
        self.0.shortest_match_at(text.as_bytes(), start)
    }

    #[inline(always)] // reduces constant overhead
    fn is_match_at(&self, text: &str, start: usize) -> bool {
        self.0.is_match_at(text.as_bytes(), start)
    }

    #[inline(always)] // reduces constant overhead
    fn find_at(&self, text: &str, start: usize) -> Option<(usize, usize)> {
        self.0.find_at(text.as_bytes(), start)
    }

    #[inline(always)] // reduces constant overhead
    fn read_captures_at(
        &self,
        locs: &mut Locations,
        text: &str,
        start: usize,
    ) -> Option<(usize, usize)> {
        self.0.read_captures_at(locs, text.as_bytes(), start)
    }
}

impl<'c> RegularExpression for ExecNoSync<'c> {
    type Text = [u8];

    /// Returns the number of capture slots in the regular expression. (There
    /// are two slots for every capture group, corresponding to possibly empty
    /// start and end locations of the capture.)
    fn slots_len(&self) -> usize {
        self.ro.nfa.captures.len() * 2
    }

    fn next_after_empty(&self, _text: &[u8], i: usize) -> usize {
        i + 1
    }

    /// Returns the end of a match location, possibly occurring before the
    /// end location of the correct leftmost-first match.
    #[inline(always)] // reduces constant overhead
    fn shortest_match_at(&self, text: &[u8], start: usize) -> Option<usize> {
        match self.ro.match_type {
            MatchType::Nfa => self.shortest_nfa(text, start),
            MatchType::Nothing => None,
        }
    }

    /// Returns true if and only if the regex matches text.
    ///
    /// For single regular expressions, this is equivalent to calling
    /// shortest_match(...).is_some().
    #[inline(always)] // reduces constant overhead
    fn is_match_at(&self, text: &[u8], start: usize) -> bool {
        // We need to do this dance because shortest_match relies on the NFA
        // filling in captures[1], but a RegexSet has no captures. In other
        // words, a RegexSet can't (currently) use shortest_match. ---AG
        match self.ro.match_type {
            MatchType::Nfa => self.match_nfa(text, start),
            MatchType::Nothing => false,
        }
    }

    /// Finds the start and end location of the leftmost-first match, starting
    /// at the given location.
    #[inline(always)] // reduces constant overhead
    fn find_at(&self, text: &[u8], start: usize) -> Option<(usize, usize)> {
        match self.ro.match_type {
            MatchType::Nfa => self.find_nfa(text, start),
            MatchType::Nothing => None,
        }
    }

    /// Finds the start and end location of the leftmost-first match and also
    /// fills in all matching capture groups.
    ///
    /// The number of capture slots given should be equal to the total number
    /// of capture slots in the compiled program.
    ///
    /// Note that the first two slots always correspond to the start and end
    /// locations of the overall match.
    fn read_captures_at(
        &self,
        locs: &mut Locations,
        text: &[u8],
        start: usize,
    ) -> Option<(usize, usize)> {
        let slots = as_slots(locs);
        for slot in slots.iter_mut() {
            *slot = None;
        }
        // If the caller unnecessarily uses this, then we try to save them
        // from themselves.
        match slots.len() {
            0 => return self.find_at(text, start),
            2 => {
                return self.find_at(text, start).map(|(s, e)| {
                    slots[0] = Some(s);
                    slots[1] = Some(e);
                    (s, e)
                });
            }
            _ => {} // fallthrough
        }
        match self.ro.match_type {
            MatchType::Nfa => {
                self.captures_nfa(slots, text, start)
            }
            MatchType::Nothing => None,
        }
    }
}

impl<'c> ExecNoSync<'c> {
    /// Executes the NFA engine to return whether there is a match or not.
    ///
    /// Ideally, we could use shortest_nfa(...).is_some() and get the same
    /// performance characteristics, but regex sets don't have captures, which
    /// shortest_nfa depends on.
    fn match_nfa(
        &self,
        text: &[u8],
        start: usize,
    ) -> bool {
        self.exec_pikevm(&mut [false], &mut [], true, text, start)
    }

    /// Finds the shortest match using an NFA.
    fn shortest_nfa(&self, text: &[u8], start: usize) -> Option<usize> {
        let mut slots = [None, None];
        if self.exec_pikevm(&mut [false], &mut slots, true, text, start) {
            slots[1]
        } else {
            None
        }
    }

    /// Like find, but executes an NFA engine.
    fn find_nfa(
        &self,
        text: &[u8],
        start: usize,
    ) -> Option<(usize, usize)> {
        let mut slots = [None, None];
        if self.exec_pikevm(&mut [false], &mut slots, false, text, start) {
            match (slots[0], slots[1]) {
                (Some(s), Some(e)) => Some((s, e)),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Like find_nfa, but fills in captures.
    ///
    /// `slots` should have length equal to `2 * nfa.captures.len()`.
    fn captures_nfa(
        &self,
        slots: &mut [Slot],
        text: &[u8],
        start: usize,
    ) -> Option<(usize, usize)> {
        if self.exec_pikevm(&mut [false], slots, false, text, start) {
            match (slots[0], slots[1]) {
                (Some(s), Some(e)) => Some((s, e)),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Always run the NFA algorithm.
    fn exec_pikevm(
        &self,
        matches: &mut [bool],
        slots: &mut [Slot],
        quit_after_match: bool,
        text: &[u8],
        start: usize,
    ) -> bool {
        let cache = &mut self.cache.borrow_mut().pikevm;
        if self.ro.nfa.uses_bytes() {
            let mut fsm = pikevm::Fsm::new(
                &self.ro.nfa,
                &mut cache.stack,
                ByteInput::new(text, self.ro.nfa.only_utf8),
            );
            fsm.exec(
                &mut cache.clist,
                &mut cache.nlist,
                matches,
                slots,
                quit_after_match,
                start)
        } else {
            let mut fsm = pikevm::Fsm::new(
                &self.ro.nfa,
                &mut cache.stack,
                CharInput::new(text),
                );
            fsm.exec(
                &mut cache.clist,
                &mut cache.nlist,
                matches,
                slots,
                quit_after_match,
                start)
        }
    }

    /// Finds which regular expressions match the given text.
    ///
    /// `matches` should have length equal to the number of regexes being
    /// searched.
    ///
    /// This is only useful when one wants to know which regexes in a set
    /// match some text.
    pub fn many_matches_at(
        &self,
        matches: &mut [bool],
        text: &[u8],
        start: usize,
    ) -> bool {
        use self::MatchType::*;
        match self.ro.match_type {
            Nfa => self.exec_pikevm(matches, &mut [], false, text, start),
            Nothing => false,
        }
    }

    pub fn capture_name_idx(&self) -> &Arc<HashMap<String, usize>> {
        &self.ro.nfa.capture_name_idx
    }
}

impl<'c> ExecNoSyncStr<'c> {
    pub fn capture_name_idx(&self) -> &Arc<HashMap<String, usize>> {
        self.0.capture_name_idx()
    }
}

impl Exec {
    /// Get a searcher that isn't Sync.
    #[inline(always)] // reduces constant overhead
    pub fn searcher(&self) -> ExecNoSync {
        let create = || Box::new(RefCell::new(ProgramCacheInner::new(&self.ro)));
        ExecNoSync {
            ro: &self.ro, // a clone is too expensive here! (and not needed)
            cache: self.cache.get_or(create),
        }
    }

    /// Get a searcher that isn't Sync and can match on &str.
    #[inline(always)] // reduces constant overhead
    pub fn searcher_str(&self) -> ExecNoSyncStr {
        ExecNoSyncStr(self.searcher())
    }

    /// Build a Regex from this executor.
    pub fn into_regex(self) -> re_unicode::Regex {
        re_unicode::Regex::from(self)
    }

    /// Build a RegexSet from this executor.
    pub fn into_regex_set(self) -> re_set::unicode::RegexSet {
        re_set::unicode::RegexSet::from(self)
    }

    /// The original regular expressions given by the caller that were
    /// compiled.
    pub fn regex_strings(&self) -> &[String] {
        &self.ro.res
    }

    /// Return a slice of capture names.
    ///
    /// Any capture that isn't named is None.
    pub fn capture_names(&self) -> &[Option<String>] {
        &self.ro.nfa.captures
    }

    /// Return a reference to named groups mapping (from group name to
    /// group position).
    pub fn capture_name_idx(&self) -> &Arc<HashMap<String, usize>> {
        &self.ro.nfa.capture_name_idx
    }
}

impl Clone for Exec {
    fn clone(&self) -> Exec {
        Exec {
            ro: self.ro.clone(),
            cache: CachedThreadLocal::new(),
        }
    }
}

impl ExecReadOnly {
    fn choose_match_type(&self, hint: Option<MatchType>) -> MatchType {
        use self::MatchType::*;
        if let Some(Nfa) = hint {
            return hint.unwrap();
        }
        // If the NFA is empty, then we'll never match anything.
        if self.nfa.insts.is_empty() {
            return Nothing;
        }
        Nfa
    }
}

#[derive(Clone, Copy, Debug)]
enum MatchType {
    /// An NFA variant.
    Nfa,
    /// No match is ever possible, so don't ever try to search.
    Nothing,
}

/// `ProgramCache` maintains reusable allocations for each matching engine
/// available to a particular program.
pub type ProgramCache = RefCell<ProgramCacheInner>;

#[derive(Clone, Debug)]
pub struct ProgramCacheInner {
    pub pikevm: pikevm::Cache,
}

impl ProgramCacheInner {
    fn new(ro: &ExecReadOnly) -> Self {
        ProgramCacheInner {
            pikevm: pikevm::Cache::new(&ro.nfa),
        }
    }
}
