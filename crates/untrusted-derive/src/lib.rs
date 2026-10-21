//! `#[derive(Decode)]` for structs whose fields all implement `untrusted::Decode`.
//!
//! This macro is deliberately *not* trusted. The code it generates is extracted
//! to Lean with Aeneas, and `derive_decode_spec` proves it correct there, so a
//! bug here shows up as a failed proof rather than a false guarantee. To keep
//! those proofs simple, the generated code always has the same shape: one
//! `reader.decode::<FieldType>()?` per field, in declaration order, then the
//! struct literal.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{parse_macro_input, Data, DeriveInput, Error, Fields};

/// Derives `untrusted::Decode` by decoding every field in declaration order.
///
/// Supported: structs with named fields, tuple structs and unit structs, without
/// generic parameters. Enums, unions and generic structs are rejected.
#[proc_macro_derive(Decode)]
pub fn derive_decode(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    expand(&input)
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

fn expand(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    if !input.generics.params.is_empty() || input.generics.where_clause.is_some() {
        return Err(Error::new_spanned(
            &input.generics,
            "#[derive(Decode)] does not support generic parameters",
        ));
    }
    let data = match &input.data {
        Data::Struct(data) => data,
        Data::Enum(e) => {
            return Err(Error::new_spanned(
                e.enum_token,
                "#[derive(Decode)] supports structs only",
            ))
        }
        Data::Union(u) => {
            return Err(Error::new_spanned(
                u.union_token,
                "#[derive(Decode)] supports structs only",
            ))
        }
    };

    // Locals are `field_<i>`, and the reader is `r`: neither may be named
    // `reader`, which would shadow the `reader` namespace in the generated Lean.
    let locals: Vec<_> = (0..data.fields.len())
        .map(|i| format_ident!("field_{}", i))
        .collect();
    let types = data.fields.iter().map(|f| &f.ty);
    let reads = quote! {
        #( let #locals = r.decode::<#types>()?; )*
    };
    let value = match &data.fields {
        Fields::Named(fields) => {
            let names = fields.named.iter().map(|f| f.ident.as_ref().unwrap());
            quote! { #name { #( #names: #locals ),* } }
        }
        Fields::Unnamed(_) => quote! { #name( #( #locals ),* ) },
        Fields::Unit => quote! { #name },
    };
    let reader = if data.fields.is_empty() {
        quote!(_r)
    } else {
        quote!(r)
    };

    Ok(quote! {
        impl ::untrusted::Decode for #name {
            fn decode(
                #reader: &mut ::untrusted::Reader<'_>,
            ) -> ::core::result::Result<Self, ::untrusted::ValidationError> {
                #reads
                ::core::result::Result::Ok(#value)
            }
        }
    })
}

/// Derives `untrusted::Encode` by encoding every field in declaration order.
///
/// Supported: structs with named fields, tuple structs and unit structs, with
/// lifetime parameters but no type or const parameters (so a field may borrow
/// a payload, `&'a [u8]`). Enums and unions are rejected. As with `Decode`,
/// the generated code always has the same shape, one `w.encode(&self.field)?`
/// per field and then `Ok(())`, which `derive_encode_spec` proves in Lean.
#[proc_macro_derive(Encode)]
pub fn derive_encode(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    expand_encode(&input)
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

fn expand_encode(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let name = &input.ident;
    let only_lifetimes = input
        .generics
        .params
        .iter()
        .all(|p| matches!(p, syn::GenericParam::Lifetime(_)));
    if !only_lifetimes || input.generics.where_clause.is_some() {
        return Err(Error::new_spanned(
            &input.generics,
            "#[derive(Encode)] supports lifetime parameters only",
        ));
    }
    let data = match &input.data {
        Data::Struct(data) => data,
        Data::Enum(e) => {
            return Err(Error::new_spanned(
                e.enum_token,
                "#[derive(Encode)] supports structs only",
            ))
        }
        Data::Union(u) => {
            return Err(Error::new_spanned(
                u.union_token,
                "#[derive(Encode)] supports structs only",
            ))
        }
    };

    let types = data.fields.iter().map(|f| &f.ty);
    let accesses: Vec<TokenStream2> = match &data.fields {
        Fields::Named(fields) => fields
            .named
            .iter()
            .map(|f| {
                let n = f.ident.as_ref().unwrap();
                quote!(#n)
            })
            .collect(),
        Fields::Unnamed(fields) => (0..fields.unnamed.len())
            .map(|i| {
                let i = syn::Index::from(i);
                quote!(#i)
            })
            .collect(),
        Fields::Unit => Vec::new(),
    };
    // The writer is `w`: it may not be named `writer`, which would shadow the
    // `writer` namespace in the generated Lean.
    let writer = if data.fields.is_empty() {
        quote!(_w)
    } else {
        quote!(w)
    };
    let (impl_generics, ty_generics, _) = input.generics.split_for_impl();

    Ok(quote! {
        impl #impl_generics ::untrusted::Encode for #name #ty_generics {
            fn encode(
                &self,
                #writer: &mut ::untrusted::Writer<'_>,
            ) -> ::core::result::Result<(), ::untrusted::EncodeError> {
                #( <#types as ::untrusted::Encode>::encode(&self.#accesses, w)?; )*
                ::core::result::Result::Ok(())
            }
        }
    })
}
