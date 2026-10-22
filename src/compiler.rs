//! Source loading, diagnostics and compilation of one protocol.

use crate::{CompiledProver, CompiledVerifier};
use backend::{ArkConfig, HasOpFactory};
use graph::{Relations, UDag, UDags};
use lang::{
    ast::{TypedModule, UModule},
    diagnostic::{Diagnostic, Phase, Severity, render_diagnostic},
    id::Tid,
};
use share::{Ctx, Set};
use std::{fmt, path::Path, path::PathBuf, sync::Arc};

/// An input failure or source diagnostics from parsing and compilation.
#[derive(Debug)]
pub enum CompileError {
    /// The source could not be read.
    Io {
        /// Source path.
        path: PathBuf,
        /// Underlying filesystem error.
        error: std::io::Error,
    },
    /// Source diagnostics, with the context needed to render them.
    Diagnostics {
        /// Source filename or logical name.
        name: String,
        /// Original source text.
        source: Arc<str>,
        /// Diagnostics from the failing stage.
        diagnostics: Vec<Diagnostic>,
    },
}

impl CompileError {
    /// Source diagnostics; empty for a filesystem error.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        match self {
            Self::Io { .. } => &[],
            Self::Diagnostics { diagnostics, .. } => diagnostics,
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, error } => write!(f, "{}: {error}", path.display()),
            Self::Diagnostics {
                name,
                source,
                diagnostics,
            } => {
                for diagnostic in diagnostics {
                    write!(f, "{}", render_diagnostic(diagnostic, name, source))?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CompileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { error, .. } => Some(error),
            Self::Diagnostics { .. } => None,
        }
    }
}

/// Selection and transcript identity for a compilation.
#[derive(Clone, Debug, Default)]
pub struct CompileOptions {
    /// Protocol declaration to select; defaults to the first protocol.
    pub protocol: Option<String>,
    /// Fiat–Shamir session label; defaults to the source filename or logical name.
    pub domain_separator_session: Option<String>,
}

/// Parsed source that can be compiled repeatedly at different sizes or curves.
pub struct ParsedModule {
    name: String,
    source: Arc<str>,
    module: UModule,
    diagnostics: Vec<Diagnostic>,
}

impl ParsedModule {
    /// Read and parse a source file. The path's display string is its source name.
    ///
    /// # Errors
    /// Returns a filesystem error or parse/semantic diagnostics.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CompileError> {
        let path = path.as_ref();
        let source = std::fs::read_to_string(path).map_err(|error| CompileError::Io {
            path: path.to_path_buf(),
            error,
        })?;
        Self::parse(path.display().to_string(), source)
    }

    /// Parse in-memory source with a filename or logical name for diagnostics and transcripts.
    ///
    /// # Errors
    /// Returns parse/semantic diagnostics. Warnings on success are available via [`Self::diagnostics`].
    pub fn parse(name: impl Into<String>, source: impl Into<String>) -> Result<Self, CompileError> {
        let name = name.into();
        let source: Arc<str> = Arc::from(source.into());
        let (module, diagnostics) = UModule::parse(&source);
        if let Some(module) = module
            && !has_errors(&diagnostics)
        {
            Ok(Self {
                name,
                source,
                module,
                diagnostics,
            })
        } else {
            Err(CompileError::Diagnostics {
                name,
                source,
                diagnostics,
            })
        }
    }

    /// Filename or logical name attached to this source.
    #[must_use]
    pub fn source_name(&self) -> &str {
        &self.name
    }

    /// Original source text, for rendering diagnostics or inspecting declarations.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Declared `Size` parameters, before choosing concrete values.
    #[must_use]
    pub fn size_params(&self) -> Set<Tid> {
        self.module.size_params()
    }

    /// Non-fatal diagnostics reported while parsing.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Compile one joint protocol at concrete sizes, ready for projection or analysis.
    ///
    /// The relation is type-checked here. Its graph is lowered explicitly by
    /// [`CompiledProtocol::prepare_analysis`], independently of execution compilation.
    ///
    /// # Errors
    /// Returns source diagnostics for invalid sizes, types, graphs or protocol selection.
    ///
    /// # Panics
    /// If an internal compiler invariant fails.
    pub fn compile<C: ArkConfig + HasOpFactory>(
        &self,
        sizes: &Ctx<Tid, usize>,
        options: CompileOptions,
    ) -> Result<CompiledProtocol<C>, CompileError> {
        let concrete = self
            .module
            .concretize(sizes)
            .map_err(|e| self.error(vec![e.into()]))?;
        let typed = concrete.typecheck().map_err(|d| self.error(d))?;
        let graphs =
            UDags::<C>::lower(&typed, Relations::Skip).map_err(|e| self.error(vec![e.into()]))?;
        let graph = options
            .protocol
            .as_ref()
            .map_or_else(
                || graphs.protocols().first().copied(),
                |name| graphs.protocol(name),
            )
            .ok_or_else(|| {
                let message = options.protocol.as_ref().map_or_else(
                    || "No protocols found".to_owned(),
                    |name| format!("Protocol {name} not found"),
                );
                self.error(vec![Diagnostic::error(Phase::Semantic, 0..0, &message)])
            })?;
        lang::semantic::check_protocol_instances(
            &self.module,
            typed.module(),
            &graph.name(),
            sizes,
        )
        .map_err(|e| self.error(vec![e.into()]))?;
        Ok(CompiledProtocol {
            source_name: self.name.clone(),
            source: Arc::clone(&self.source),
            protocol_name: graph.name().0,
            domain_separator_session: options
                .domain_separator_session
                .unwrap_or_else(|| self.name.clone()),
            graph: graph.clone(),
            typed,
            diagnostics: self.diagnostics.clone(),
        })
    }

    fn error(&self, diagnostics: Vec<Diagnostic>) -> CompileError {
        CompileError::Diagnostics {
            name: self.name.clone(),
            source: Arc::clone(&self.source),
            diagnostics,
        }
    }
}

fn has_errors(diagnostics: &[Diagnostic]) -> bool {
    diagnostics.iter().any(|d| d.severity == Severity::Error)
}

/// A successfully compiled joint protocol with concrete types.
///
/// Constructed by [`ParsedModule::compile`]. Explicit projection produces independent
/// prover and verifier objects; static-analysis preparation is separately measurable.
pub struct CompiledProtocol<C: ArkConfig> {
    pub(super) source_name: String,
    pub(super) source: Arc<str>,
    pub(super) protocol_name: String,
    pub(super) domain_separator_session: String,
    pub(super) typed: TypedModule,
    pub(super) graph: UDag<C>,
    diagnostics: Vec<Diagnostic>,
}

impl<C: ArkConfig> CompiledProtocol<C> {
    /// Joint execution graph, with the relation marked but not lowered.
    #[must_use]
    pub const fn graph(&self) -> &UDag<C> {
        &self.graph
    }

    /// Fiat–Shamir session identity used by both execution graphs.
    #[must_use]
    pub fn domain_separator_session(&self) -> &str {
        &self.domain_separator_session
    }

    /// Non-fatal diagnostics from parsing and type-checking.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

impl<C: ArkConfig + HasOpFactory> CompiledProtocol<C> {
    /// Project an owned prover that can execute independently of this protocol.
    ///
    /// # Panics
    /// If an internal projection invariant fails.
    #[must_use]
    pub fn project_prover(&self) -> CompiledProver<C> {
        CompiledProver {
            graph: self.graph.project_prover().0,
            domain_separator_session: self.domain_separator_session.clone(),
        }
    }

    /// Project an owned verifier that can execute independently of this protocol.
    ///
    /// # Errors
    /// Returns source diagnostics if a verifier check depends on private inputs or randomness.
    ///
    /// # Panics
    /// If an internal projection invariant fails.
    pub fn project_verifier(&self) -> Result<CompiledVerifier<C>, CompileError> {
        let graph = self
            .graph
            .project_verifier()
            .map_err(|error| CompileError::Diagnostics {
                name: self.source_name.clone(),
                source: Arc::clone(&self.source),
                diagnostics: vec![error.into()],
            })?;
        Ok(CompiledVerifier {
            graph,
            domain_separator_session: self.domain_separator_session.clone(),
        })
    }
}
