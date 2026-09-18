//! Proc macro for declarative diagnostic definitions.
//!
//! `#[derive(Diagnostic)]` generates a `build(self) -> Diagnostic` method
//! on the struct, using the builder API from `lang::diagnostic`.
//!
//! ## Attributes
//!
//! ### Struct-level: `#[diag(...)]`
//! ```ignore
//! #[diag("summary `{$name}`", code = "E0001", error, Semantic)]
//! ```
//! - First positional: summary string (supports `{$field}` interpolation)
//! - `code = "..."`: error code
//! - `error` or `warning`: severity (default: `error`)
//! - `Parse`, `Semantic`, or `Type`: phase (default: `Semantic`)
//!
//! ### Field-level: `#[span(label = "...")]`
//! Marks the primary span field. The `label` is the primary label message
//! (supports `{$field}` interpolation).
//!
//! ### Field-level: `#[suggestion(...)]`
//! ```ignore
//! #[suggestion("message `{$name}`", replacement = "{$replacement}", applicability = "machine-applicable")]
//! ```
//! The field's value is used as the suggestion span. `replacement` supports
//! interpolation. `applicability` is `machine-applicable` or `maybe-incorrect`.
//!
//! ### Field-level: `#[note("...")]`
//! Adds a note. The string supports `{$field}` interpolation. Can be on any
//! field type (the field value is not used, only interpolated into the note).
//!
//! ### Field-level: `#[secondary_label("...")]`
//! The field must be `Range<usize>`. Adds a secondary label at that span.
//! The string supports `{$field}` interpolation.
//!
//! ## Interpolation
//!
//! `{$field_name}` in any string is replaced with the field's value at
//! build time. Fields that are not annotated with any attribute are pure
//! data — available for interpolation but not rendered directly.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{parse_macro_input, DeriveInput, Field};

mod parse;

use parse::{DiagAttr, FieldAttr, InterpolatedString};

/// Derives a `build(self) -> Diagnostic` method from the `#[diag]`, `#[span]`, `#[suggestion]`,
/// `#[note]`, and `#[secondary_label]` attributes on a diagnostic struct.
///
/// Attribute parsing errors are reported as `compile_error!` in the expansion rather than as a
/// panic, so a malformed annotation surfaces at the definition site. See the module header for
/// the attribute grammar and the `{$field}` interpolation syntax.
#[proc_macro_derive(Diagnostic, attributes(diag, span, suggestion, note, secondary_label))]
pub fn derive_diagnostic(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match expand(&input) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let struct_name = &input.ident;

    // Parse struct-level #[diag(...)] attribute
    let diag_attr = DiagAttr::parse_from_attrs(&input.attrs)?;

    // Parse fields
    let fields: Vec<&Field> = match &input.data {
        syn::Data::Struct(s) => s.fields.iter().collect(),
        _ => {
            return Err(syn::Error::new_spanned(
                input,
                "Diagnostic can only be derived on structs",
            ));
        }
    };

    // Find the primary span field (#[span(...)])
    let span_field = fields
        .iter()
        .find(|f| f.attrs.iter().any(|a| a.path().is_ident("span")))
        .ok_or_else(|| {
            syn::Error::new_spanned(
                struct_name,
                "Diagnostic struct must have a #[span(label = \"...\")] field",
            )
        })?;

    let span_field_name = span_field.ident.as_ref().unwrap();

    // Parse span label from #[span(label = "...")]
    let span_label = span_field
        .attrs
        .iter()
        .find(|a| a.path().is_ident("span"))
        .map(|a| {
            let items = parse::parse_attr_items(a)?;
            for item in &items {
                if let parse::AttrItem::KeyValue { key, value } = item {
                    if key == "label" {
                        return Ok(InterpolatedString::parse(value));
                    }
                }
            }
            Err(syn::Error::new_spanned(a, "expected `label = \"...\"`"))
        })
        .transpose()?
        .unwrap_or(InterpolatedString::literal(""));

    // Collect suggestions, notes, secondary labels
    let mut suggestion_fields: Vec<(&Field, FieldAttr)> = vec![];
    let mut note_fields: Vec<(&Field, FieldAttr)> = vec![];
    let mut secondary_label_fields: Vec<(&Field, FieldAttr)> = vec![];

    for f in &fields {
        for a in &f.attrs {
            if a.path().is_ident("suggestion") {
                let attr = FieldAttr::parse_suggestion(a)?;
                suggestion_fields.push((f, attr));
            } else if a.path().is_ident("note") {
                let attr = FieldAttr::parse_note(a)?;
                note_fields.push((f, attr));
            } else if a.path().is_ident("secondary_label") {
                let attr = FieldAttr::parse_secondary_label(a)?;
                secondary_label_fields.push((f, attr));
            }
        }
    }

    // Generate the build method
    let severity_ident = format_ident!("{}", diag_attr.severity_str());
    let phase_ident = format_ident!("{}", diag_attr.phase_str());
    let summary_tmpl = diag_attr.summary.generate_format(&fields);
    let span_label_tmpl = span_label.generate_format(&fields);
    let code = diag_attr.code.ok_or_else(|| {
        syn::Error::new_spanned(
            struct_name,
            "#[diag(...)] must have a `code = \"Exxxx\"` attribute",
        )
    })?;

    // Start: Diagnostic::error/warning(Phase::X, self.span, &format!(...))
    //         .code("Exxxx")

    // Suggestion builders
    let suggestion_builders: Vec<TokenStream2> = suggestion_fields
        .iter()
        .map(|(f, attr)| {
            let field_name = f.ident.as_ref().unwrap();
            let msg_tmpl = attr.message.generate_format(&fields);
            let repl_tmpl = attr
                .replacement
                .as_ref()
                .map(|r| r.generate_format(&fields))
                .unwrap_or_else(|| quote! { String::new() });
            let appl = match attr.applicability.as_deref() {
                Some("maybe-incorrect") => {
                    quote! { lang::diagnostic::Applicability::MaybeIncorrect }
                }
                _ => quote! { lang::diagnostic::Applicability::MachineApplicable },
            };
            quote! {
                .suggestion(
                    &#msg_tmpl,
                    self.#field_name.clone(),
                    &#repl_tmpl,
                    #appl,
                )
            }
        })
        .collect();

    // Note builders
    let note_builders: Vec<TokenStream2> = note_fields
        .iter()
        .map(|(_f, attr)| {
            let msg_tmpl = attr.message.generate_format(&fields);
            quote! { .note(&#msg_tmpl) }
        })
        .collect();

    // Secondary label builders
    let secondary_label_builders: Vec<TokenStream2> = secondary_label_fields
        .iter()
        .map(|(f, attr)| {
            let field_name = f.ident.as_ref().unwrap();
            let msg_tmpl = attr.message.generate_format(&fields);
            quote! {
                .secondary_label(
                    self.#field_name.clone(),
                    &#msg_tmpl,
                )
            }
        })
        .collect();

    let suggestions = quote! { #(#suggestion_builders)* };
    let notes = quote! { #(#note_builders)* };
    let secondary_labels = quote! { #(#secondary_label_builders)* };

    Ok(quote! {
        impl #struct_name {
            pub fn build(self) -> lang::diagnostic::Diagnostic {
                lang::diagnostic::Diagnostic::#severity_ident(
                    lang::diagnostic::Phase::#phase_ident,
                    self.#span_field_name.clone(),
                    &#summary_tmpl,
                )
                .code(#code)
                .primary_label(&#span_label_tmpl)
                #secondary_labels
                #notes
                #suggestions
            }
        }
    })
}
