use quote::quote;
use regex_automata::{
    dfa::{
        dense::{Builder, DFA},
        Automaton,
    },
    nfa::thompson::Config,
    util::{primitives::StateID, start},
    Anchored,
};

struct Transition {
    ranges: Vec<(u8, u8)>,
    next: usize,
}

struct State {
    trans: Vec<Transition>,
    eof_next: usize,
    is_match: bool,
    is_dead: bool,
    is_quit: bool,
}

struct Translator(Vec<usize>);

impl State {
    fn new() -> Self {
        Self {
            trans: Vec::new(),
            eof_next: 0,
            is_match: false,
            is_dead: false,
            is_quit: false,
        }
    }
}

impl Translator {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn translate(&self, id: StateID) -> usize {
        self.0
            .get(id.as_usize())
            .and_then(|state| {
                if *state == usize::MAX {
                    None
                } else {
                    Some(*state)
                }
            })
            .expect("internal error in pars_macros during regex compilation")
    }

    fn try_add(&mut self, id: StateID, state: usize) -> bool {
        let id = id.as_usize();
        if self.0.len() <= id {
            if self.0.capacity() < id + 1 {
                let new_cap = std::cmp::max(id + 1, self.0.capacity() * 2);
                self.0.reserve(new_cap - self.0.capacity());
            }
            self.0.resize(id + 1, usize::MAX);
            self.0[id] = state;
            return true;
        }
        if self.0[id] == usize::MAX {
            self.0[id] = state;
            return true;
        }
        return false;
    }
}

fn compile_dfa(dfa: DFA<Vec<u32>>, ascii: bool) -> Result<Vec<State>, String> {
    let mut states = Vec::new();
    let mut trans = Translator::new();
    let start = match dfa.start_state(&start::Config::new().anchored(Anchored::Yes)) {
        Ok(start) => start,
        Err(e) => {
            return Err(format!("{e}"));
        }
    };
    compile_dfa_impl(&dfa, start, &mut states, &mut trans, ascii);
    Ok(states)
}

fn compile_dfa_impl(
    dfa: &DFA<Vec<u32>>,
    curr: StateID,
    states: &mut Vec<State>,
    trans: &mut Translator,
    ascii: bool,
) {
    use std::collections::{hash_map::Entry, HashMap};

    let state = states.len();
    if !trans.try_add(curr, states.len()) {
        return;
    }
    states.push(State::new());

    if dfa.is_dead_state(curr) {
        let s = &mut states[state];
        s.eof_next = state;
        s.is_match = dfa.is_match_state(curr);
        s.is_dead = true;
        s.is_quit = dfa.is_quit_state(curr);
        return;
    }

    if dfa.is_quit_state(curr) {
        let s = &mut states[state];
        s.eof_next = state;
        s.is_quit = true;
        return;
    }

    let mut transitions: HashMap<usize, Vec<(u8, u8)>> = HashMap::new();
    for b in 0..=(if ascii { 127 } else { 255 }) {
        let next = dfa.next_state(curr, b);
        compile_dfa_impl(dfa, next, states, trans, ascii);
        let next = trans.translate(next);
        if next != state {
            match transitions.entry(next) {
                Entry::Occupied(mut entry) => {
                    if entry
                        .get_mut()
                        .last_mut()
                        .map(|r| {
                            if r.1 + 1 == b {
                                r.1 = b;
                                false
                            } else {
                                true
                            }
                        })
                        .unwrap_or(true)
                    {
                        entry.get_mut().push((b, b));
                    }
                }
                Entry::Vacant(entry) => {
                    entry.insert(vec![(b, b)]);
                }
            }
        }
    }
    let eof_next = dfa.next_eoi_state(curr);
    compile_dfa_impl(dfa, eof_next, states, trans, ascii);
    let s = &mut states[state];
    s.trans = transitions
        .drain()
        .map(|(next, ranges)| Transition { ranges, next })
        .collect();
    s.eof_next = trans.translate(eof_next);
    s.is_match = dfa.is_match_state(curr);
}

fn gen_states(count: usize) -> Vec<syn::Ident> {
    (0..count)
        .into_iter()
        .map(|state| syn::Ident::new(&format!("State{state}")[..], proc_macro2::Span::call_site()))
        .collect()
}

pub fn compile_bytes(regex: &str) -> proc_macro2::TokenStream {
    let config = Config::new().utf8(false).shrink(true);
    let dfa = match Builder::new().thompson(config).build(regex) {
        Ok(dfa) => dfa,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let states = match compile_dfa(dfa, false) {
        Ok(states) => states,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let state_names = gen_states(states.len());
    let state_impls = states.iter().enumerate().map(|(id, state)| {
        let name = &state_names[id];
        let match_impl = if state.is_match {
            Some(quote! {
                match_end = ::core::option::Option::Some(::core::clone::Clone::clone(&prev_input));
            })
        } else {
            None
        };

        let transitions = state.trans.iter().map(|trans| {
            let ranges = trans.ranges.iter().map(|(start, end)| if start == end {
                quote! { #start }
            } else {
                quote! { #start ..= #end }
            });
            let next = &state_names[trans.next];
            quote! {
                #(#ranges)|* => {
                    state = State::#next;
                }
            }
        });
        let eof_next = &state_names[state.eof_next];

        if state.is_quit {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                }
            }
        } else if state.is_dead {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if let ::core::option::Option::Some(match_end) = match_end {
                        return ::core::result::Result::Ok(::pars::Success((), match_end));
                    } else if ::pars::Input::is_empty(&input) {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::need_more_input(prev_input), orig_input));
                    } else {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                    }
                }
            }
        } else {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    prev_input = ::core::clone::Clone::clone(&input);
                    if ::pars::Input::is_empty(&input) {
                        state = State::#eof_next;
                    } else {
                        match ::pars::bytes::ByteInput::parse_byte(input) {
                            ::core::result::Result::Ok(::pars::Success(b, rem)) => {
                                input = rem;
                                match b {
                                    #(#transitions,)*
                                    #[allow(unreachable_patterns)]
                                    _ => {},
                                }
                            },
                            ::core::result::Result::Err(fail) => {
                                return ::core::result::Result::Err(fail);
                            }
                        }
                    }
                }
            }
        }
    });

    quote! {
        |input| {
            fn __pars_regex_impl<I: ::pars::bytes::ByteInput>(mut input: I) -> ::pars::bytes::PResult<(), I> {
                enum State { #(#state_names),* }
                let mut state = State::State0;
                let mut match_end: ::core::option::Option<I> = ::core::option::Option::None;
                let orig_input = ::core::clone::Clone::clone(&input);
                let mut prev_input = ::core::clone::Clone::clone(&input);
                loop {
                    match state {
                        #(#state_impls),*
                    }
                }
            }

            __pars_regex_impl(input)
        }
    }
}

pub fn compile_ascii_strict(regex: &str) -> proc_macro2::TokenStream {
    let config = Config::new().utf8(true).shrink(true);
    let dfa = match Builder::new().thompson(config).build(regex) {
        Ok(dfa) => dfa,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let states = match compile_dfa(dfa, true) {
        Ok(states) => states,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let state_names = gen_states(states.len());
    let state_impls = states.iter().enumerate().map(|(id, state)| {
        let name = &state_names[id];
        let match_impl = if state.is_match {
            Some(quote! {
                match_end = ::core::option::Option::Some(::core::clone::Clone::clone(&prev_input));
            })
        } else {
            None
        };

        let transitions = state.trans.iter().map(|trans| {
            let ranges = trans.ranges.iter().map(|(start, end)| if start == end {
                quote! { #start }
            } else {
                quote! { #start ..= #end }
            });
            let next = &state_names[trans.next];
            quote! {
                #(#ranges)|* => {
                    state = State::#next;
                }
            }
        });
        let eof_next = &state_names[state.eof_next];

        if state.is_quit {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                }
            }
        } else if state.is_dead {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if let ::core::option::Option::Some(match_end) = match_end {
                        return ::core::result::Result::Ok(::pars::Success((), match_end));
                    } else if ::pars::Input::is_empty(&input) {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::need_more_input(prev_input), orig_input));
                    } else {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                    }
                }
            }
        } else {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    prev_input = ::core::clone::Clone::clone(&input);
                    if ::pars::Input::is_empty(&input) {
                        state = State::#eof_next;
                    } else {
                        match ::pars::ascii::AsciiInput::parse_char(input) {
                            ::core::result::Result::Ok(::pars::Success(b, rem)) => {
                                input = rem;
                                match b.as_byte() {
                                    #(#transitions,)*
                                    #[allow(unreachable_patterns)]
                                    128u8..=255u8 => { unsafe { ::core::hint::unrechable_unchecked(); } },
                                    #[allow(unreachable_patterns)]
                                    _ => {},
                                }
                            },
                            ::core::result::Result::Err(fail) => {
                                return ::core::result::Result::Err(fail);
                            }
                        }
                    }
                }
            }
        }
    });

    quote! {
        |input| {
            fn __pars_regex_impl<I: ::pars::ascii::AsciiInput>(mut input: I) -> ::pars::ascii::PResult<(), I> {
                enum State { #(#state_names),* }
                let mut state = State::State0;
                let mut match_end: ::core::option::Option<I> = ::core::option::Option::None;
                let orig_input = ::core::clone::Clone::clone(&input);
                let mut prev_input = ::core::clone::Clone::clone(&input);
                loop {
                    match state {
                        #(#state_impls),*
                    }
                }
            }

            __pars_regex_impl(input)
        }
    }
}

pub fn compile_ascii_lossy(regex: &str) -> proc_macro2::TokenStream {
    let config = Config::new().utf8(true).shrink(true);
    let dfa = match Builder::new().thompson(config).build(regex) {
        Ok(dfa) => dfa,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let states = match compile_dfa(dfa, true) {
        Ok(states) => states,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let state_names = gen_states(states.len());
    let state_impls = states.iter().enumerate().map(|(id, state)| {
        let name = &state_names[id];
        let match_impl = if state.is_match {
            Some(quote! {
                match_end = ::core::option::Option::Some(::core::clone::Clone::clone(&prev_input));
            })
        } else {
            None
        };

        let transitions = state.trans.iter().map(|trans| {
            let ranges = trans.ranges.iter().map(|(start, end)| if start == end {
                quote! { #start }
            } else {
                quote! { #start ..= #end }
            });
            let next = &state_names[trans.next];
            quote! {
                #(#ranges)|* => {
                    state = State::#next;
                }
            }
        });
        let eof_next = &state_names[state.eof_next];

        if state.is_quit {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                }
            }
        } else if state.is_dead {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if let ::core::option::Option::Some(match_end) = match_end {
                        return ::core::result::Result::Ok(::pars::Success((), match_end));
                    } else if ::pars::Input::is_empty(&input) {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::need_more_input(prev_input), orig_input));
                    } else {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                    }
                }
            }
        } else {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    prev_input = ::core::clone::Clone::clone(&input);
                    if ::pars::Input::is_empty(&input) {
                        state = State::#eof_next;
                    } else {
                        match ::pars::ascii::AsciiInput::parse_char_lossy(input) {
                            ::core::result::Result::Ok(::pars::Success(b, rem)) => {
                                input = rem;
                                match b.as_byte() {
                                    #(#transitions,)*
                                    #[allow(unreachable_patterns)]
                                    128u8..=255u8 => { unsafe { ::core::hint::unreachable_unchecked() } },
                                    #[allow(unreachable_patterns)]
                                    _ => {},
                                }
                            },
                            ::core::result::Result::Err(fail) => {
                                return ::core::result::Result::Err(fail);
                            }
                        }
                    }
                }
            }
        }
    });

    quote! {
        |input| {
            fn __pars_regex_impl<I: ::pars::ascii::AsciiInput>(mut input: I) -> ::pars::ascii::PResult<(), I> {
                enum State { #(#state_names),* }
                let mut state = State::State0;
                let mut match_end: ::core::option::Option<I> = ::core::option::Option::None;
                let orig_input = ::core::clone::Clone::clone(&input);
                let mut prev_input = ::core::clone::Clone::clone(&input);
                loop {
                    match state {
                        #(#state_impls),*
                    }
                }
            }

            __pars_regex_impl(input)
        }
    }
}

pub fn compile_unicode_strict(regex: &str) -> proc_macro2::TokenStream {
    let config = Config::new().utf8(true).shrink(true);
    let dfa = match Builder::new().thompson(config).build(regex) {
        Ok(dfa) => dfa,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let states = match compile_dfa(dfa, false) {
        Ok(states) => states,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let state_names = gen_states(states.len());
    let state_impls = states.iter().enumerate().map(|(id, state)| {
        let name = &state_names[id];
        let match_impl = if state.is_match {
            Some(quote! {
                match_end = ::core::option::Option::Some(::core::clone::Clone::clone(&prev_input));
            })
        } else {
            None
        };

        let transitions = state.trans.iter().map(|trans| {
            let ranges = trans.ranges.iter().map(|(start, end)| if start == end {
                quote! { #start }
            } else {
                quote! { #start ..= #end }
            });
            let next = &state_names[trans.next];
            quote! {
                #(#ranges)|* => {
                    state = State::#next;
                }
            }
        });
        let eof_next = &state_names[state.eof_next];

        if state.is_quit {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                }
            }
        } else if state.is_dead {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if let ::core::option::Option::Some(match_end) = match_end {
                        return ::core::result::Result::Ok(::pars::Success((), match_end));
                    } else if ::pars::Input::is_empty(&input) {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::need_more_input(prev_input), orig_input));
                    } else {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                    }
                }
            }
        } else {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if ::pars::Input::is_empty(&input) && pos == 4 {
                        prev_input = ::core::clone::Clone::clone(&input);
                        state = State::#eof_next;
                    } else {
                        if pos == 4 {
                            prev_input = ::core::clone::Clone::clone(&input);
                            let mut tmp = [0u8; 4];
                            match ::pars::unicode::UnicodeInput::parse_utf8(input, &mut tmp[..]) {
                                ::core::result::Result::Ok(::pars::Success(ch, rem)) => {
                                    input = rem;
                                    pos = 4 - ch.len();
                                    buf[pos..].copy_from_slice(ch.as_bytes());
                                },
                                ::core::result::Result::Err(e) => { return ::core::result::Result::Err(e); }
                            }
                        }
                        let b = buf[pos];
                        pos += 1;

                        match b {
                            #(#transitions,)*
                            #[allow(unreachable_patterns)]
                            _ => {},
                        }
                    }
                }
            }
        }
    });

    quote! {
        |input| {
            fn __pars_regex_impl<I: ::pars::unicode::UnicodeInput>(mut input: I) -> ::pars::unicode::PResult<(), I> {
                enum State { #(#state_names),* }
                let mut state = State::State0;
                let mut match_end: ::core::option::Option<I> = ::core::option::Option::None;
                let mut buf = [0u8; 4];
                let mut pos = 4usize;
                let orig_input = ::core::clone::Clone::clone(&input);
                let mut prev_input = ::core::clone::Clone::clone(&input);
                loop {
                    match state {
                        #(#state_impls),*
                    }
                }
            }

            __pars_regex_impl(input)
        }
    }
}

pub fn compile_unicode_lossy(regex: &str) -> proc_macro2::TokenStream {
    let config = Config::new().utf8(true).shrink(true);
    let dfa = match Builder::new().thompson(config).build(regex) {
        Ok(dfa) => dfa,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let states = match compile_dfa(dfa, false) {
        Ok(states) => states,
        Err(e) => {
            let msg = format!("regex compiliation error: {e}");
            return quote! {
                ::core::compile_error!(#msg)
            };
        }
    };
    let state_names = gen_states(states.len());
    let state_impls = states.iter().enumerate().map(|(id, state)| {
        let name = &state_names[id];
        let match_impl = if state.is_match {
            Some(quote! {
                match_end = ::core::option::Option::Some(::core::clone::Clone::clone(&prev_input));
            })
        } else {
            None
        };

        let transitions = state.trans.iter().map(|trans| {
            let ranges = trans.ranges.iter().map(|(start, end)| if start == end {
                quote! { #start }
            } else {
                quote! { #start ..= #end }
            });
            let next = &state_names[trans.next];
            quote! {
                #(#ranges)|* => {
                    state = State::#next;
                }
            }
        });
        let eof_next = &state_names[state.eof_next];

        if state.is_quit {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                }
            }
        } else if state.is_dead {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if let ::core::option::Option::Some(match_end) = match_end {
                        return ::core::result::Result::Ok(::pars::Success((), match_end));
                    } else if ::pars::Input::is_empty(&input) {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::need_more_input(prev_input), orig_input));
                    } else {
                        return ::core::result::Result::Err(::pars::Failure(::pars::Error::invalid_input(prev_input), orig_input));
                    }
                }
            }
        } else {
            quote! {
                #[allow(unreachable_patterns)]
                State::#name => {
                    #match_impl
                    if ::pars::Input::is_empty(&input) && pos == 4 {
                        prev_input = ::core::clone::Clone::clone(&input);
                        state = State::#eof_next;
                    } else {
                        if pos == 4 {
                            prev_input = ::core::clone::Clone::clone(&input);
                            let mut tmp = [0u8; 4];
                            match ::pars::unicode::UnicodeInput::parse_utf8_lossy(input, &mut tmp[..]) {
                                ::core::result::Result::Ok(::pars::Success(ch, rem)) => {
                                    input = rem;
                                    pos = 4 - ch.len();
                                    buf[pos..].copy_from_slice(ch.as_bytes());
                                },
                                ::core::result::Result::Err(e) => { return ::core::result::Result::Err(e); }
                            }
                        }
                        let b = buf[pos];
                        pos += 1;

                        match b {
                            #(#transitions,)*
                            #[allow(unreachable_patterns)]
                            _ => {},
                        }
                    }
                }
            }
        }
    });

    quote! {
        |input| {
            fn __pars_regex_impl<I: ::pars::unicode::UnicodeInput>(mut input: I) -> ::pars::unicode::PResult<(), I> {
                enum State { #(#state_names),* }
                let mut state = State::State0;
                let mut match_end: ::core::option::Option<I> = ::core::option::Option::None;
                let mut buf = [0u8; 4];
                let mut pos = 4usize;
                let orig_input = ::core::clone::Clone::clone(&input);
                let mut prev_input = ::core::clone::Clone::clone(&input);
                loop {
                    match state {
                        #(#state_impls),*
                    }
                }
            }

            __pars_regex_impl(input)
        }
    }
}
