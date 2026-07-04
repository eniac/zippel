//! Singular backend: shells out to the Singular CLI for Gröbner basis
//! computation.
//!
//! Translates [`MonoOrder`](crate::frontend::MonoOrder) into a Singular ring
//! declaration, pipes a script via stdin to `Singular -q`, and parses the
//! positional output back into [`Polynomial`](crate::frontend::Polynomial)s.
//!
//! ## Coefficient field
//!
//! Singular's `(p)` prime-field syntax is limited to primes ≤ 2³¹, but the
//! field elements in zippel are 255-bit curve scalars. We therefore use the
//! `(integer, P)` domain — the ring ℤ/Pℤ, which *is* the field 𝔽_P when P is
//! prime — and Singular handles big primes via GMP natively.
//!
//! ## Return path (D4 — positional deserialization)
//!
//! The generated script emits each basis polynomial as a sequence of
//! `coeff exp₁ exp₂ … expₙ` lines (one per term), with an `END` sentinel
//! between polynomials and a `DONE` sentinel after the last. Rust-side parsing
//! is trivial whitespace-separated integer parsing — Singular's polynomial
//! expression syntax is never parsed back.

use std::collections::HashMap;
use std::io::Write;
use std::marker::PhantomData;
use std::process::{Command, Stdio};
use std::str::FromStr;

use crate::PRef;
use ark_ff::PrimeField;
use num_bigint::BigUint;

use super::{GbBackend, GbBasis};
use crate::frontend::{BackendError, BlockKind, MonoOrder, Monomial, Polynomial};

/// Singular CLI backend.
pub struct Singular<F: PrimeField> {
    _phantom: PhantomData<F>,
}

impl<F: PrimeField> Default for Singular<F> {
    fn default() -> Self {
        Singular {
            _phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> GbBackend<F> for Singular<F> {
    fn compute_gb(
        &self,
        ideal: Vec<Polynomial<F>>,
        order: &MonoOrder,
    ) -> Result<GbBasis<F>, BackendError> {
        compute_gb_via_cli::<F>(ideal, order)
    }

    fn reduce(&self, p: Polynomial<F>, basis: &GbBasis<F>) -> Polynomial<F> {
        crate::backend::reduce(p, &basis.polys, &basis.order)
    }
}

// -----------------------------------------------------------------------
// Core: build script, run Singular, parse output
// -----------------------------------------------------------------------

fn compute_gb_via_cli<F: PrimeField>(
    ideal: Vec<Polynomial<F>>,
    order: &MonoOrder,
) -> Result<GbBasis<F>, BackendError> {
    // Filter zero polynomials — they contribute nothing to the ideal.
    let ideal: Vec<Polynomial<F>> = ideal.into_iter().filter(|p| !p.is_zero()).collect();

    // Collect all variables across the ideal.
    let all_vars: Vec<PRef> = {
        let mut vs: Vec<PRef> = ideal.iter().flat_map(|p| p.vars()).collect();
        vs.sort();
        vs.dedup();
        vs
    };

    // No variables → constant-only ideal. GB is [1] if any nonzero constant,
    // else empty. (Mirrors ark-gb's `constant_only_basis`.)
    if all_vars.is_empty() {
        let polys = if ideal.is_empty() {
            Vec::new()
        } else {
            vec![Polynomial::lit(&F::one())]
        };
        return Ok(GbBasis {
            polys,
            order: order.clone(),
        });
    }

    // Build the PRef → x(i) variable map from block_var_assignment.
    // Concatenate block vars in order; this is the order Singular's ring
    // declaration uses.
    let var_map: Vec<PRef> = order
        .block_var_assignment(&all_vars)
        .into_iter()
        .flat_map(|(_, vs)| vs)
        .collect();
    let nvars = var_map.len();

    let script = build_script::<F>(&ideal, order, &var_map);
    let output = run_singular(&script)?;

    let polys = parse_output::<F>(&output, &var_map, nvars)?;
    Ok(GbBasis {
        polys,
        order: order.clone(),
    })
}

// -----------------------------------------------------------------------
// Script generation
// -----------------------------------------------------------------------

/// Render the Singular ordering string from `MonoOrder` blocks.
///
/// `Lex` over `n` vars → `lp(n)`, `GrevLex` over `n` vars → `dp(n)`.
/// Product → `(lp(n₁), dp(n₂), …)`.
fn ordering_string(order: &MonoOrder, all_vars: &[PRef]) -> String {
    let blocks = order.block_var_assignment(all_vars);
    let parts: Vec<String> = blocks
        .iter()
        .map(|(kind, vs)| {
            let n = vs.len();
            match kind {
                BlockKind::Lex => format!("lp({n})"),
                BlockKind::GrevLex => format!("dp({n})"),
            }
        })
        .collect();
    format!("({})", parts.join(", "))
}

/// Render a `Polynomial<F>` as a Singular expression string.
///
/// Terms are joined by ` + `. Coefficients are rendered as canonical `[0, P)`
/// decimal integers via `into_bigint`. Each variable is rendered as `x(i)^e`.
fn poly_to_singular<F: PrimeField>(p: &Polynomial<F>, var_index: &HashMap<&PRef, usize>) -> String {
    if p.is_zero() {
        return "0".to_string();
    }
    let mut terms: Vec<String> = Vec::new();
    for (mono, coeff) in &p.terms {
        let coeff_str = format!("{}", coeff.into_bigint());
        if mono.is_constant() {
            terms.push(coeff_str);
        } else {
            let factors: Vec<String> = mono
                .iter()
                .map(|(v, e)| {
                    let i = var_index[v] + 1; // Singular: x(1)-based
                    if *e == 1 {
                        format!("x({i})")
                    } else {
                        format!("x({i})^{e}")
                    }
                })
                .collect();
            terms.push(format!("{}*{}", coeff_str, factors.join("*")));
        }
    }
    terms.join(" + ")
}

fn build_script<F: PrimeField>(
    ideal: &[Polynomial<F>],
    order: &MonoOrder,
    var_map: &[PRef],
) -> String {
    let nvars = var_map.len();
    let modulus = format!("{}", F::MODULUS);
    let ordering = ordering_string(order, var_map);

    // Build a PRef → 0-based index lookup.
    let index_of: HashMap<&PRef, usize> = var_map.iter().enumerate().map(|(i, v)| (v, i)).collect();

    let mut s = String::new();

    // Ring declaration: (integer, P) for big-prime support.
    s.push_str(&format!(
        "ring r = (integer, {modulus}), (x(1..{nvars})), {ordering};\n"
    ));

    // Polynomial declarations.
    for (i, p) in ideal.iter().enumerate() {
        let expr = poly_to_singular(p, &index_of);
        s.push_str(&format!("poly p{i} = {expr};\n"));
    }

    // Ideal declaration.
    let names: Vec<String> = (0..ideal.len()).map(|i| format!("p{i}")).collect();
    s.push_str(&format!("ideal I = {};\n", names.join(", ")));

    // Compute a *reduced* standard basis (Gröbner basis).
    // Without option(redSB), std returns a non-interreduced basis.
    s.push_str("option(redSB);\n");
    s.push_str("ideal G = std(I);\n");

    // Emission loop: each term as `coeff exp1 exp2 ... expN`, END between polys.
    s.push_str("int i;\n");
    s.push_str("int k;\n");
    s.push_str("poly q;\n");
    s.push_str("intvec e;\n");
    s.push_str("string line;\n");
    s.push_str("for (i = 1; i <= size(G); i++) {\n");
    s.push_str("  q = G[i];\n");
    s.push_str("  while (q != 0) {\n");
    s.push_str("    e = leadexp(q);\n");
    s.push_str("    line = string(leadcoef(q));\n");
    s.push_str(&format!(
        "    for (k = 1; k <= {nvars}; k++) {{ line = line + \" \" + string(e[k]); }}\n"
    ));
    s.push_str("    write(\"\", line);\n");
    s.push_str("    q = q - lead(q);\n");
    s.push_str("  }\n");
    s.push_str("  write(\"\", \"END\");\n");
    s.push_str("}\n");
    s.push_str("write(\"\", \"DONE\");\n");

    s
}

// -----------------------------------------------------------------------
// Subprocess
// -----------------------------------------------------------------------

fn run_singular(script: &str) -> Result<String, BackendError> {
    let mut child = Command::new("Singular")
        .arg("-q")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| BackendError::Other(format!("failed to spawn Singular: {e}")))?;

    // Write the script to Singular's stdin.
    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .map_err(|e| BackendError::Other(format!("failed to write to Singular stdin: {e}")))?;
    }
    // stdin is dropped here, signalling EOF.

    let output = child
        .wait_with_output()
        .map_err(|e| BackendError::Other(format!("failed to wait for Singular: {e}")))?;

    // Singular writes both data and diagnostics to stdout; stderr is usually
    // empty but we include it for debugging if present.
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    // Detect error lines (start with "   ?").
    let errors: Vec<&str> = stdout
        .lines()
        .filter(|l| l.trim_start().starts_with('?'))
        .collect();
    if !errors.is_empty() {
        let msg = if stderr.is_empty() {
            errors.join("\n")
        } else {
            format!("{}\n--- stderr ---\n{}", errors.join("\n"), stderr)
        };
        return Err(BackendError::Other(format!(
            "Singular script error:\n{msg}"
        )));
    }

    // Check for the DONE sentinel (script ran to completion).
    if !stdout.lines().any(|l| l.trim() == "DONE") {
        return Err(BackendError::Other(format!(
            "Singular did not complete (no DONE sentinel). stdout:\n{stdout}\n--- stderr ---\n{stderr}"
        )));
    }

    Ok(stdout)
}

// -----------------------------------------------------------------------
// Output parsing (positional — D4)
// -----------------------------------------------------------------------

fn parse_output<F: PrimeField>(
    stdout: &str,
    var_map: &[PRef],
    nvars: usize,
) -> Result<Vec<Polynomial<F>>, BackendError> {
    let mut polys: Vec<Polynomial<F>> = Vec::new();
    let mut current_terms: Vec<(Monomial, F)> = Vec::new();

    for line in stdout.lines() {
        let line = line.trim();

        // Skip comment/warning lines.
        if line.starts_with("//") || line.is_empty() {
            continue;
        }
        // Completion sentinel — stop.
        if line == "DONE" {
            break;
        }
        // End-of-polynomial sentinel.
        if line == "END" {
            if !current_terms.is_empty() {
                let terms = current_terms
                    .into_iter()
                    .filter(|(_, c)| !c.is_zero())
                    .collect();
                polys.push(Polynomial { terms });
                current_terms = Vec::new();
            }
            continue;
        }

        // Data line: `coeff exp1 exp2 ... expN`
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() != nvars + 1 {
            return Err(BackendError::Other(format!(
                "malformed Singular output line (expected {} tokens, got {}): {line}",
                nvars + 1,
                tokens.len()
            )));
        }

        let coeff = parse_coeff::<F>(tokens[0])?;
        let mut pairs: Vec<(PRef, usize)> = Vec::new();
        for (k, tok) in tokens[1..].iter().enumerate() {
            let exp: usize = tok
                .parse()
                .map_err(|e| BackendError::Other(format!("bad exponent '{tok}': {e}")))?;
            if exp > 0 {
                pairs.push((var_map[k].clone(), exp));
            }
        }
        let mono = Monomial::from(pairs);
        current_terms.push((mono, coeff));
    }

    // In case the output ended without a trailing END (shouldn't happen, but
    // be defensive).
    if !current_terms.is_empty() {
        let terms = current_terms
            .into_iter()
            .filter(|(_, c)| !c.is_zero())
            .collect();
        polys.push(Polynomial { terms });
    }

    Ok(polys)
}

/// Parse a decimal integer string in `[0, P)` into a field element.
fn parse_coeff<F: PrimeField>(s: &str) -> Result<F, BackendError> {
    let big = BigUint::from_str(s)
        .map_err(|e| BackendError::Other(format!("bad coefficient '{s}': {e}")))?;
    let bytes = big.to_bytes_le();
    Ok(F::from_le_bytes_mod_order(&bytes))
}
