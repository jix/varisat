use std::fmt::Write;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, punctuated::Punctuated, Attribute, Fields, Ident, Lit, LitStr, Meta,
    MetaNameValue, Token,
};
use synstructure::decl_derive;

/// Get the doc comment as LitStr from the attributes
fn doc_from_attrs(attrs: &[Attribute]) -> Vec<LitStr> {
    let mut lines = vec![];

    for attr in attrs.iter() {
        if let Ok(Meta::NameValue(MetaNameValue {
            ident,
            lit: Lit::Str(doc_str),
            ..
        })) = attr.parse_meta()
        {
            if ident == "doc" {
                lines.push(doc_str);;
            }
        }
    }

    lines
}

/// Find a field inside the doc comment
fn get_doc_field(name: &str, attrs: &[Attribute]) -> Option<LitStr> {
    let re = regex::Regex::new(&format!(r"\b{}: ([^;]+)", regex::escape(name))).unwrap();

    for doc_str in doc_from_attrs(attrs) {
        if let Some(expr_str) = re.captures(&doc_str.value()) {
            let expr_str = expr_str.get(1).unwrap().as_str();
            let expr_str = LitStr::new(expr_str, doc_str.span());
            return Some(expr_str);
        }
    }

    None
}

/// Derives a default instance from the documentation.
fn derive_doc_default(s: synstructure::Structure) -> TokenStream {
    let variant = match s.variants() {
        [variant] => variant,
        _ => panic!("DocDefault requires a struct"),
    };

    let body = variant.construct(|field, _| {
        get_doc_field("Default", &field.attrs)
            .map(|expr_str| {
                expr_str
                    .parse::<TokenStream>()
                    .expect("error parsing default expression")
            })
            .unwrap_or(parse_quote!(Default::default()))
    });

    s.gen_impl(quote! {
        gen impl Default for @Self {
            fn default() -> Self {
                #body
            }
        }
    })
}

decl_derive!([DocDefault] => derive_doc_default);

/// Derives an update struct and method for a config struct.
fn derive_config_update(s: synstructure::Structure) -> TokenStream {
    let variant = match s.variants() {
        [variant] => variant,
        _ => panic!("ConfigUpdate requires a struct"),
    };

    let fields = match variant.ast().fields {
        Fields::Named(fields_named) => &fields_named.named,
        _ => panic!("ConfigUpdate requires named fields"),
    };

    assert!(
        s.referenced_ty_params().is_empty(),
        "ConfigUpdate doesn't support type parameters"
    );

    let ident = &s.ast().ident;
    let update_struct_ident = Ident::new(&format!("{}Update", ident), ident.span());

    let vis = &s.ast().vis;

    let update_struct_body = fields
        .iter()
        .map(|field| {
            let ty = &field.ty;
            let mut field = field.clone();
            field.ty = parse_quote!(Option<#ty>);
            field
        })
        .collect::<Punctuated<_, Token![,]>>();

    let check_ranges = fields
        .iter()
        .map(|field| {
            if let Some(range) = get_doc_field("Range", &field.attrs) {
                // TODO use toml instead of fmt::Debug for errors?
                let ident = &field.ident;
                let error_msg = format!(
                    "{} must be in range {} but was set to {{:?}}",
                    quote!(#ident),
                    range.value()
                );
                let range = range
                    .parse::<TokenStream>()
                    .expect("error parsing range expression");
                quote! {
                    if let Some(value) = &self.#ident {
                        failure::ensure!((#range).contains(value), #error_msg, value);
                    }
                }
            } else {
                quote!()
            }
        })
        .collect::<TokenStream>();

    let apply_updates = fields
        .iter()
        .map(|field| {
            let ident = &field.ident;
            quote! {
                if let Some(value) = &self.#ident {
                    config.#ident = value.clone();
                }
            }
        })
        .collect::<TokenStream>();

    let merge_updates = fields
        .iter()
        .map(|field| {
            let ident = &field.ident;
            quote! {
                if let Some(value) = config_update.#ident {
                    self.#ident = Some(value);
                }
            }
        })
        .collect::<TokenStream>();

    let mut help_str = String::new();

    for field in fields.iter() {
        let ident = &field.ident;
        writeln!(&mut help_str, "{}:", quote!(#ident)).unwrap();
        for line in doc_from_attrs(&field.attrs).iter() {
            if line.value().is_empty() {
                writeln!(&mut help_str, "").unwrap();
            } else {
                writeln!(&mut help_str, "   {}", line.value()).unwrap();
            }
        }
        writeln!(&mut help_str, "").unwrap();
    }

    let doc = format!("Updates configuration values of [`{}`].", ident);

    quote! {
        #[doc = #doc]
        #[derive(Default, serde::Serialize, serde::Deserialize)]
        #[serde(deny_unknown_fields)]
        #vis struct #update_struct_ident {
            #update_struct_body
        }

        impl #ident {
            /// Return a string describing all supported configuration options.
            pub fn help() -> &'static str {
                #help_str
            }
        }

        impl #update_struct_ident {
            /// Create an empty config update.
            pub fn new() -> #update_struct_ident {
                #update_struct_ident::default()
            }

            /// Apply the configuration update.
            ///
            /// If an error occurs, the configuration is not changed.
            pub fn apply(&self, config: &mut #ident) -> Result<(), failure::Error> {
                #check_ranges
                #apply_updates
                Ok(())
            }

            /// Merge two configuration updates.
            ///
            /// Add the given update, overwriting values of the receiving update.
            pub fn merge(&mut self, config_update: #update_struct_ident) {
                #merge_updates
            }
        }
    }
}

decl_derive!([ConfigUpdate] => derive_config_update);
