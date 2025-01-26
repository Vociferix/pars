use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parse_macro_input, Expr, Ident, Index, Token};

mod regex;

struct Args(Punctuated<Expr, Token![,]>);

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut punc = Punctuated::new();
        while !input.is_empty() {
            punc.push_value(input.parse()?);
            let comma: Result<Token![,]> = input.parse();
            match comma {
                Ok(comma) => {
                    punc.push_punct(comma);
                }
                Err(e) => {
                    if input.is_empty() {
                        break;
                    } else {
                        return Err(e);
                    }
                }
            }
        }
        Ok(Self(punc))
    }
}

#[proc_macro]
pub fn seq(args: TokenStream) -> TokenStream {
    let Args(args) = parse_macro_input!(args as Args);
    let args: Vec<_> = args.into_iter().collect();
    if args.is_empty() {
        return quote! {
            { ::pars::basic::constant(|| ()) }
        }
        .into();
    }
    let pairs = seq_pairs(&args[..]);
    let tuple = seq_tuple(0, args.len());
    let vars = (0..args.len()).into_iter().map(|idx| {
        let var = Ident::new(&format!("__pars_seq_elem_{idx}"), Span::call_site());
        quote! { #var }
    });
    quote! {
        {
            ::pars::basic::map({ #pairs }, |#tuple| (#(#vars,)*))
        }
    }
    .into()
}

fn seq_pairs(args: &[Expr]) -> proc_macro2::TokenStream {
    if args.len() == 1 {
        let arg = &args[0];
        quote! {
            { #arg }
        }
    } else if args.len() == 2 {
        let arg1 = &args[0];
        let arg2 = &args[1];
        quote! {
            { ::pars::basic::pair(#arg1, #arg2) }
        }
    } else {
        let mid = args.len() / 2;
        let first = seq_pairs(&args[..mid]);
        let second = seq_pairs(&args[mid..]);
        quote! {
            { ::pars::basic::pair(#first, #second) }
        }
    }
}

fn seq_tuple(start: usize, end: usize) -> proc_macro2::TokenStream {
    let len = end - start;
    if len == 1 {
        let var = Ident::new(&format!("__pars_seq_elem_{start}"), Span::call_site());
        quote! { #var }
    } else if len == 2 {
        let var1 = Ident::new(&format!("__pars_seq_elem_{start}"), Span::call_site());
        let var2 = Ident::new(&format!("__pars_seq_elem_{}", start + 1), Span::call_site());
        quote! { (#var1, #var2,) }
    } else {
        let mid = start + (len / 2);
        let first = seq_tuple(start, mid);
        let second = seq_tuple(mid, end);
        quote! { (#first, #second,) }
    }
}

#[proc_macro]
pub fn alt(args: TokenStream) -> TokenStream {
    let Args(args) = parse_macro_input!(args as Args);
    let args: Vec<_> = args.into_iter().collect();
    if args.is_empty() {
        return quote! {
            { ::pars::basic::constant(|| ()) }
        }
        .into();
    }
    alt_impl(&args[..]).into()
}

fn alt_impl(args: &[Expr]) -> proc_macro2::TokenStream {
    if args.len() == 1 {
        let arg = &args[0];
        quote! {
            { #arg }
        }
    } else if args.len() == 2 {
        let arg1 = &args[0];
        let arg2 = &args[1];
        quote! {
            { ::pars::basic::either(#arg1, #arg2) }
        }
    } else {
        let mid = args.len() / 2;
        let first = alt_impl(&args[..mid]);
        let second = alt_impl(&args[mid..]);
        quote! {
            { ::pars::basic::either(#first, #second) }
        }
    }
}

#[proc_macro]
pub fn permutation(args: TokenStream) -> TokenStream {
    let Args(args) = parse_macro_input!(args as Args);
    if args.is_empty() {
        return quote! {
            { ::pars::basic::constant(|| ()) }
        }
        .into();
    }

    let ty_params_vec: Vec<Ident> = (0..args.len())
        .into_iter()
        .map(|idx| Ident::new(&format!("__ParsPermutationP{idx}"), Span::call_site()))
        .collect();
    let ty_params = &ty_params_vec[..];

    let vars_vec: Vec<Ident> = (0..args.len())
        .into_iter()
        .map(|idx| Ident::new(&format!("__pars_permutation_var_{idx}"), Span::call_site()))
        .collect();
    let vars = &vars_vec[..];

    let state_vec: Vec<Ident> = (0..args.len())
        .into_iter()
        .map(|idx| {
            Ident::new(
                &format!("__pars_permutation_state_{idx}"),
                Span::call_site(),
            )
        })
        .collect();
    let state = &state_vec[..];

    let vars_init_vec: Vec<_> = vars
        .iter()
        .zip(ty_params.iter())
        .zip(state.iter())
        .map(|((var, ty), st)| {
            quote! {
                let mut #st: bool = false;
                let mut #var: ::core::mem::MaybeUninit<<#ty as ::pars::Parse<__ParsPermutationInput>>::Parsed> = const { ::core::mem::MaybeUninit::uninit() };
            }
        })
        .collect();
    let vars_init = &vars_init_vec[..];

    let parse_impls_vec: Vec<_> = vars.iter().zip(state.iter()).enumerate().map(|(idx, (var, st))| {
        let idx = Index { index: idx as u32, span: Span::call_site(), };
        quote! {
            if !#st {
                match self.#idx.parse(__pars_permutation_rem) {
                    ::core::result::Result::Ok(::pars::Success(__pars_permutation_val, __pars_permutation_new_rem)) => {
                        __pars_permutation_rem = __pars_permutation_new_rem;
                        #var.write(__pars_permutation_val);
                        #st = true;
                        __pars_permutation_parsed += 1;
                        continue;
                    },
                    ::core::result::Result::Err(::pars::Failure(__pars_permutation_new_err, __pars_permutation_new_rem)) => {
                        __pars_permutation_err = Some(__pars_permutation_new_err);
                        __pars_permutation_rem = __pars_permutation_new_rem;
                    },
                }
            }
        }
    }).collect();
    let parse_impls = &parse_impls_vec[..];

    let drops_vec: Vec<_> = vars
        .iter()
        .zip(state.iter())
        .map(|(var, st)| {
            quote! {
                if #st {
                    unsafe { #var.assume_init_drop(); }
                }
            }
        })
        .collect();
    let drops = &drops_vec[..];

    let count = args.len();

    let arg_exprs = args.iter();

    quote! {
        {
            struct __ParsPermutationParser<#(#ty_params,)* __ParsPermutationInput>(#(#ty_params,)* ::core::marker::PhantomData<__ParsPermutationInput>)
            where
                #(#ty_params: ::pars::Parse<__ParsPermutationInput>,)*
                __ParsPermutationInput: ::pars::Input;

            impl<#(#ty_params,)* __ParsPermutationInput> ::pars::Parse<__ParsPermutationInput> for __ParsPermutationParser<#(#ty_params,)* __ParsPermutationInput>
            where
                #(#ty_params: ::pars::Parse<__ParsPermutationInput>,)*
                __ParsPermutationInput: ::pars::Input,
            {
                type Parsed = (#(<#ty_params as ::pars::Parse<__ParsPermutationInput>>::Parsed,)*);

                fn parse(&self, __pars_permutation_input: __ParsPermutationInput) -> ::pars::PResult<Self::Parsed, __ParsPermutationInput> {
                    let mut __pars_permutation_parsed = 0usize;
                    let mut __pars_permutation_rem = __pars_permutation_input.clone();
                    let mut __pars_permutation_err = None;
                    #(#vars_init)*

                    while __pars_permutation_parsed != #count {
                        #(#parse_impls)*
                        #(#drops)*
                        return ::core::result::Result::Err(::pars::Failure(match __pars_permutation_err {
                            Some(__pars_permutation_err) => __pars_permutation_err,
                            None => ::core::unreachable!(),
                        }, __pars_permutation_input));
                    }

                    ::core::result::Result::Ok(::pars::Success(unsafe {
                        (#(#vars.assume_init(),)*)
                    }, __pars_permutation_rem))
                }
            }

            __ParsPermutationParser(#(#arg_exprs,)* ::core::marker::PhantomData)
        }
    }.into()
}

#[proc_macro]
pub fn ascii(args: TokenStream) -> TokenStream {
    use litrs::Literal;

    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one integer, character, string, byte, or byte string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one integer, character, string, byte, or byte string literal argument") }.into();
    }

    match Literal::try_from(tok) {
        Ok(Literal::Integer(lit)) => {
            if let Some(value) = lit.value::<u8>().and_then(|val| if val < 0x80 { Some(val) } else { None }) {
                quote! {
                    unsafe { const { ::core::mem::transmute::<::core::primitive::u8, ::pars::ascii::AsciiChar>(#value) } }
                }
            } else {
                quote! {
                    ::core::compile_error!("integer value out of range for ASCII")
                }
            }
        },
        Ok(Literal::Char(lit)) => {
            let ch = lit.value() as u32;
            if ch < 0x80 {
                let ch = ch as u8;
                quote! {
                    unsafe { const { ::core::mem::transmute::<::core::primitive::u8, ::pars::ascii::AsciiChar>(#ch) } }
                }
            } else {
                quote! {
                    ::core::compile_error!("character is non-ASCII")
                }
            }
        },
        Ok(Literal::String(lit)) => {
            let s = lit.value();
            let mut is_ascii = true;
            for ch in s.chars() {
                if (ch as u32) >= 0x80 {
                    is_ascii = false;
                    break;
                }
            }
            if is_ascii {
                quote! {
                    unsafe { const {
                        ::core::mem::transmute::<&'static str, &'static ::pars::ascii::AsciiStr>(#s)
                    }}
                }
            } else {
                quote! {
                    ::core::compile_error!("string contains non-ASCII characters")
                }
            }
        },
        Ok(Literal::Byte(lit)) => {
            let ch = lit.value();
            if ch < 0x80 {
                quote! {
                    unsafe { const { ::core::mem::transmute::<::core::primitive::u8, ::pars::ascii::AsciiChar>(#ch) } }
                }
            } else {
                quote! {
                    ::core::compile_error!("byte is non-ASCII")
                }
            }
        },
        Ok(Literal::ByteString(lit)) => {
            let s = lit.value();
            let mut is_ascii = true;
            for ch in s {
                if *ch >= 0x80 {
                    is_ascii = false;
                    break;
                }
            }
            if is_ascii {
                quote! {
                    unsafe { const {
                        ::core::mem::transmute::<&'static [::core::primitive::u8], &'static ::pars::ascii::AsciiStr>(&[#(#s),*])
                    }}
                }
            } else {
                quote! {
                    ::core::compile_error!("byte string contains non-ASCII bytes")
                }
            }
        },
        _ => quote! {
            ::core::compile_error!("expected one integer, character, string, byte, or byte string literal argument")
        },
    }.into()
}

#[proc_macro]
pub fn regex_bytes(args: TokenStream) -> TokenStream {
    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    }
    let regex = match litrs::StringLit::try_from(tok) {
        Ok(regex) => regex.value().to_string(),
        Err(_) => {
            return quote! { ::core::compile_error!("expected one string literal argument") }
                .into();
        }
    };

    let gen = regex::compile_bytes(&regex[..]);
    quote! {
        const { #gen }
    }
    .into()
}

#[proc_macro]
pub fn regex_ascii_strict(args: TokenStream) -> TokenStream {
    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    }
    let regex = match litrs::StringLit::try_from(tok) {
        Ok(regex) => regex.value().to_string(),
        Err(_) => {
            return quote! { ::core::compile_error!("expected one string literal argument") }
                .into();
        }
    };

    let gen = regex::compile_ascii_strict(&regex[..]);
    quote! {
        const { #gen }
    }
    .into()
}

#[proc_macro]
pub fn regex_ascii_lossy(args: TokenStream) -> TokenStream {
    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    }
    let regex = match litrs::StringLit::try_from(tok) {
        Ok(regex) => regex.value().to_string(),
        Err(_) => {
            return quote! { ::core::compile_error!("expected one string literal argument") }
                .into();
        }
    };

    let gen = regex::compile_ascii_lossy(&regex[..]);
    quote! {
        const { #gen }
    }
    .into()
}

#[proc_macro]
pub fn regex_unicode_strict(args: TokenStream) -> TokenStream {
    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    }
    let regex = match litrs::StringLit::try_from(tok) {
        Ok(regex) => regex.value().to_string(),
        Err(_) => {
            return quote! { ::core::compile_error!("expected one string literal argument") }
                .into();
        }
    };

    let gen = regex::compile_unicode_strict(&regex[..]);
    quote! {
        const { #gen }
    }
    .into()
}

#[proc_macro]
pub fn regex_unicode_lossy(args: TokenStream) -> TokenStream {
    let mut toks = args.into_iter();
    let Some(tok) = toks.next() else {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    };
    if let Some(_) = toks.next() {
        return quote! { ::core::compile_error!("expected one string literal argument") }.into();
    }
    let regex = match litrs::StringLit::try_from(tok) {
        Ok(regex) => regex.value().to_string(),
        Err(_) => {
            return quote! { ::core::compile_error!("expected one string literal argument") }
                .into();
        }
    };

    let gen = regex::compile_unicode_lossy(&regex[..]);
    quote! {
        const { #gen }
    }
    .into()
}
