use quote::quote;
use syn::{parse_quote, Expr, Lit, LitStr, Meta, MetaNameValue};
use synstructure::decl_derive;

/// Derives a default instance from the documentation.
fn derive_doc_default(s: synstructure::Structure) -> proc_macro2::TokenStream {
    let variant = match s.variants() {
        [variant] => variant,
        _ => panic!("DocDefault requires a struct"),
    };

    let default_re = regex::Regex::new(r"\(Default: (.*)\)").unwrap();

    let body = variant.construct(|field, _| {
        let mut default_value: Expr = parse_quote!(Default::default());
        for attr in field.attrs.iter() {
            if let Ok(Meta::NameValue(MetaNameValue {
                ident,
                lit: Lit::Str(doc_str),
                ..
            })) = attr.parse_meta()
            {
                if ident != "doc" {
                    continue;
                }
                if let Some(default_str) = default_re.captures(&doc_str.value()) {
                    let default_str = default_str.get(1).unwrap().as_str();
                    let default_str = LitStr::new(default_str, doc_str.span());
                    default_value = default_str
                        .parse()
                        .expect("error parsing default expression");
                }
            }
        }
        default_value
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
