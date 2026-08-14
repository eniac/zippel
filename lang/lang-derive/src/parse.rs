//! Parsing for diagnostic derive attributes and template interpolation.

use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{Field, Ident, LitStr, Token};

/// Parsed `#[diag(...)]` struct-level attribute.
pub struct DiagAttr {
    pub summary: InterpolatedString,
    pub code: Option<String>,
    pub severity: Severity,
    pub phase: Phase,
}

#[derive(Clone, Copy)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Copy)]
pub enum Phase {
    Parse,
    Semantic,
    Type,
}

/// A single item inside an attribute's argument list.
pub enum AttrItem {
    /// A bare string literal: "summary"
    Str(String),
    /// A bare identifier: error, warning, Semantic, etc.
    Ident(String),
    /// A key=value pair: code = "E0001"
    KeyValue { key: String, value: String },
}

/// Parse a comma-separated list of attribute items.
pub fn parse_attr_items(attr: &syn::Attribute) -> syn::Result<Vec<AttrItem>> {
    attr.parse_args_with(|input: syn::parse::ParseStream| {
        let mut items = vec![];
        while !input.is_empty() {
            // Try to parse as key = value first
            if let Ok(ident) = input.parse::<Ident>() {
                if input.peek(Token![=]) {
                    input.parse::<Token![=]>()?;
                    let value = input.parse::<LitStr>()?;
                    items.push(AttrItem::KeyValue {
                        key: ident.to_string(),
                        value: value.value(),
                    });
                } else {
                    items.push(AttrItem::Ident(ident.to_string()));
                }
            } else if let Ok(lit) = input.parse::<LitStr>() {
                items.push(AttrItem::Str(lit.value()));
            } else {
                return Err(input.error("expected identifier, string, or key = value"));
            }

            // Consume trailing comma
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            } else {
                break;
            }
        }
        Ok(items)
    })
}

impl DiagAttr {
    pub fn parse_from_attrs(attrs: &[syn::Attribute]) -> syn::Result<Self> {
        let diag_attr = attrs
            .iter()
            .find(|a| a.path().is_ident("diag"))
            .ok_or_else(|| {
                syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "Diagnostic struct must have a #[diag(...)] attribute",
                )
            })?;

        let items = parse_attr_items(diag_attr)?;

        let mut summary: Option<InterpolatedString> = None;
        let mut code: Option<String> = None;
        let mut severity = Severity::Error;
        let mut phase = Phase::Semantic;

        for item in &items {
            match item {
                AttrItem::Str(s) => {
                    summary = Some(InterpolatedString::parse(s));
                }
                AttrItem::Ident(name) => match name.as_str() {
                    "error" => severity = Severity::Error,
                    "warning" => severity = Severity::Warning,
                    "Parse" => phase = Phase::Parse,
                    "Semantic" => phase = Phase::Semantic,
                    "Type" => phase = Phase::Type,
                    _ => {}
                },
                AttrItem::KeyValue { key, value } => {
                    if key == "code" {
                        code = Some(value.clone());
                    }
                }
            }
        }

        let summary = summary.ok_or_else(|| {
            syn::Error::new_spanned(diag_attr, "#[diag(...)] must have a summary string")
        })?;

        Ok(DiagAttr {
            summary,
            code,
            severity,
            phase,
        })
    }

    pub fn severity_str(&self) -> &'static str {
        match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        }
    }

    pub fn phase_str(&self) -> &'static str {
        match self.phase {
            Phase::Parse => "Parse",
            Phase::Semantic => "Semantic",
            Phase::Type => "Type",
        }
    }
}

/// Parsed field-level attribute (suggestion, note, secondary_label).
pub struct FieldAttr {
    pub message: InterpolatedString,
    pub replacement: Option<InterpolatedString>,
    pub applicability: Option<String>,
}

impl FieldAttr {
    pub fn parse_suggestion(attr: &syn::Attribute) -> syn::Result<Self> {
        let items = parse_attr_items(attr)?;

        let mut message: Option<InterpolatedString> = None;
        let mut replacement: Option<InterpolatedString> = None;
        let mut applicability: Option<String> = None;

        for item in &items {
            match item {
                AttrItem::Str(s) => {
                    message = Some(InterpolatedString::parse(s));
                }
                AttrItem::KeyValue { key, value } => match key.as_str() {
                    "replacement" => replacement = Some(InterpolatedString::parse(value)),
                    "applicability" => applicability = Some(value.clone()),
                    _ => {}
                },
                _ => {}
            }
        }

        let message = message.ok_or_else(|| {
            syn::Error::new_spanned(attr, "#[suggestion(...)] must have a message string")
        })?;

        Ok(FieldAttr {
            message,
            replacement,
            applicability,
        })
    }

    pub fn parse_note(attr: &syn::Attribute) -> syn::Result<Self> {
        let s: LitStr = attr.parse_args()?;
        Ok(FieldAttr {
            message: InterpolatedString::parse(&s.value()),
            replacement: None,
            applicability: None,
        })
    }

    pub fn parse_secondary_label(attr: &syn::Attribute) -> syn::Result<Self> {
        let s: LitStr = attr.parse_args()?;
        Ok(FieldAttr {
            message: InterpolatedString::parse(&s.value()),
            replacement: None,
            applicability: None,
        })
    }
}

/// A string with `{$field}` interpolation placeholders.
///
/// `{$name}` is replaced with `format!("{}", self.name)` in the generated code.
/// Literal `{{` and `}}` are preserved as `{` and `}` for `format!` usage.
pub struct InterpolatedString {
    segments: Vec<Segment>,
}

enum Segment {
    Literal(String),
    FieldRef(String),
}

impl InterpolatedString {
    /// Parse a string into segments, extracting `{$field}` references.
    pub fn parse(s: &str) -> Self {
        let mut segments = vec![];
        let mut chars = s.char_indices().peekable();
        let mut literal = String::new();

        while let Some((_i, c)) = chars.next() {
            if c == '{' {
                if let Some(&(_, '$')) = chars.peek() {
                    chars.next();
                    let mut field = String::new();
                    while let Some(&(_, c)) = chars.peek() {
                        if c == '}' {
                            chars.next();
                            break;
                        }
                        field.push(c);
                        chars.next();
                    }
                    if !literal.is_empty() {
                        segments.push(Segment::Literal(std::mem::take(&mut literal)));
                    }
                    segments.push(Segment::FieldRef(field));
                } else if let Some(&(_, '{')) = chars.peek() {
                    chars.next();
                    literal.push('{');
                } else {
                    literal.push(c);
                }
            } else if c == '}' {
                if let Some(&(_, '}')) = chars.peek() {
                    chars.next();
                    literal.push('}');
                } else {
                    literal.push(c);
                }
            } else {
                literal.push(c);
            }
        }

        if !literal.is_empty() {
            segments.push(Segment::Literal(literal));
        }

        InterpolatedString { segments }
    }

    /// Create a literal string with no interpolation.
    pub fn literal(s: &str) -> Self {
        InterpolatedString {
            segments: vec![Segment::Literal(s.to_string())],
        }
    }

    /// Generate code that produces a `String` with field references interpolated.
    pub fn generate_format(&self, fields: &[&Field]) -> TokenStream2 {
        let mut fmt_str = String::new();
        let mut args: Vec<TokenStream2> = vec![];

        for seg in &self.segments {
            match seg {
                Segment::Literal(s) => fmt_str.push_str(s),
                Segment::FieldRef(name) => {
                    let field = fields
                        .iter()
                        .find(|f| f.ident.as_ref().map(|i| i == name).unwrap_or(false));
                    if let Some(f) = field {
                        let ident = f.ident.as_ref().unwrap();
                        fmt_str.push_str("{}");
                        args.push(quote! { self.#ident });
                    } else {
                        fmt_str.push_str(&format!("{{{}}}", name));
                    }
                }
            }
        }

        if args.is_empty() {
            quote! { #fmt_str.to_string() }
        } else {
            quote! { format!(#fmt_str, #(#args),*) }
        }
    }
}
