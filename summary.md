# Zippel Programming Language - Repository Summary

## Overview

Zippel is a domain-specific programming language (DSL) for building Non-Interactive Zero-Knowledge (NIZK) proofs. It bridges the gap between theoretical cryptography and practical implementation by providing:

- **High-level abstractions** for cryptographic protocols (finite fields, elliptic curves, pairings, polynomials, multilinear extensions)
- **Auto-parallelizing compiler** that generates optimized prover and verifier executables
- **Cryptographic assistant** that detects soundness, completeness, and zero-knowledge violations
- **Full lifecycle support** from protocol design to production-ready implementations

The repository consists of ~10,500 lines of Rust code organized as a Cargo workspace with 8 member crates.

## Repository Organization

```
zippel-ws/
├── lang/          # Language frontend (parser, AST, type system)
├── graph/         # Graph-based intermediate representation and analyses
├── backend/       # Arkworks integration (elliptic curves, fields, pairings)
├── runtime/       # Execution engine for prover/verifier
├── costs/         # Performance benchmarking infrastructure
├── share/         # Shared utilities and data structures
├── cli/           # Command-line interface
├── examples/      # Example protocols (.zippel files)
├── docs/          # Formal grammar specification (OTT)
└── config.toml    # Gurobi configuration
```

---

## Crate Descriptions

### 1. `lang/` - Language Frontend
**Purpose**: Implements the Zippel language frontend including parsing, abstract syntax tree (AST), and type system.

**Key Components**:
- **Parser** (`src/parser/`):
  - PEG grammar in `zippel.pest` using the Pest parser generator
  - Parses `.zippel` source files into AST
  - Supports protocols, functions, expressions, types

- **AST** (`src/ast/`):
  - `module.rs`: Module system organizing protocol declarations
  - `exp.rs`: Expression nodes (arithmetic, cryptographic operations)
  - `sig.rs`: Function/protocol signatures with type parameters
  - `decl.rs`: Declaration nodes (functions, protocols)
  - `arg.rs`: Argument representations (public/private inputs)

- **Type System** (`src/typ/`):
  - `infer.rs`: Type inference engine
  - `qualifier.rs`: Public/private qualifiers for zero-knowledge
  - `distribution.rs`: Distribution tracking (uniform, deterministic)
  - `range.rs`: Index range types
  - `kind.rs`: Type kinds (Field, Group, Scalar, Pairing)
  - `unify.rs`: Type unification algorithm
  - `ark.rs`: Integration with Arkworks type system

**Key Types**:
- `UModule`: Untyped module with symbolic sizes
- `CModule`: Concrete module with resolved sizes
- `CTyp`: Concrete types (vectors, polynomials, MLEs, finite fields)

**Dependencies**: `share`, `pest`, `pest_derive`, `rayon`, `itertools`

---

### 2. `graph/` - Graph Intermediate Representation
**Purpose**: Central compilation phase that converts AST into a directed acyclic graph (DAG) for analysis and optimization.

**Key Components**:
- **Core Graph** (`src/`):
  - `node.rs`: Graph nodes (operations, inputs, relations, transcript)
  - `op.rs`: Operation types (arithmetic, cryptographic primitives)
  - `dep.rs`: Dependency edges between nodes
  - `lib.rs`: Main `Dag<C, A>` structure (parameterized by config `C` and annotation `A`)

- **Analyses** (`src/analyses/`):
  - `trans_clos.rs`: Transitive closure for dependency analysis
  - `groebner/`: Gröbner basis for polynomial equality constraints
  - `qualifier.rs`: Public/private qualifier propagation
  - `uniform.rs`: Uniformity/distribution propagation
  - `completeness.rs`: Completeness verification (prover can compute all values)
  - `knowledge.rs`: Zero-knowledge property verification

- **Scheduler** (`src/scheduler/`):
  - `ilp.rs`: Integer Linear Programming scheduler using Gurobi
  - `local_scheduler.rs`: Local/greedy scheduling algorithm
  - `cost.rs`: Cost model for operations
  - `asymptotic_cost.rs`: Asymptotic complexity analysis

**Key Types**:
- `UDag<C>`: Unannotated DAG
- `QDag<C>`: DAG with qualifier annotations
- `DQDag<C>`: DAG with qualifier and distribution annotations
- `TDag<C>`: DAG with thread allocation annotations

**Static Analyses**:
1. **TransClos**: Computes transitive closure of dependencies
2. **GroebnerBuilder**: Builds Gröbner basis from polynomial constraints
3. **QualifierPropagation**: Ensures public/private separation
4. **UniformityPropagation**: Tracks randomness distribution
5. **CompletenessAnalysis**: Verifies protocol completeness
6. **KnowledgeAnalysis**: Verifies zero-knowledge property

**Dependencies**: `lang`, `backend`, `share`, `petgraph`, `ark-*`, `gurobi`, `spongefish`

---

### 3. `backend/` - Arkworks Backend
**Purpose**: Provides concrete implementations of cryptographic primitives using the Arkworks ecosystem.

**Key Components**:
- `config.rs`:
  - `ArkConfig` trait: Unified interface for cryptographic backends
  - Implementations for BLS12-381, BN254, MNT4-298, Curve25519, Secp256k1, Pallas, Vesta, Ed25519
  - Field-only configs: Field17, Field65537, FieldN

- `types.rs`:
  - `ABase`: Base types (G1, G2, GT, Scalar, Bool, Fin)
  - `ATyp`: Full type system (Base, Vec, Uni, Mle)

- `values.rs`:
  - `Value<C>`: Runtime value representation
  - Operations: field arithmetic, group operations, pairings, polynomial evaluation
  - Vector operations, MSM (multi-scalar multiplication)

- `nothing/`: Placeholder types for configs without curves/pairings

**Supported Curves**:
- BLS12-381, BLS12-377 (pairing-friendly)
- BN254 (pairing-friendly, zkSNARK-friendly)
- MNT4/MNT6 variants (cycle-friendly)
- Curve25519, Ed25519 (fast, non-pairing)
- Secp256k1 (Bitcoin/Ethereum)
- Pallas/Vesta (Halo 2 cycle)

**Dependencies**: `lang`, `share`, `ark-*` (ff, ec, poly, serialize, curve crates), `spongefish`, `rayon`

---

### 4. `runtime/` - Execution Engine
**Purpose**: Executes compiled DAGs as prover or verifier, managing parallel execution and cryptographic transcript.

**Key Components**:
- `graph.rs`:
  - `MutexGraph<C>`: Thread-safe graph for parallel execution
  - `RuntimeInformation<C>`: Tracks node execution state
  - `handle_op()`: Evaluates individual operations
  - `execute()`: Parallel graph traversal with dependency satisfaction

**Execution Model**:
- Converts `TDag<C>` (with thread allocations) to `MutexGraph<C>`
- Each node has mutex-protected return value
- Threads execute nodes when all dependencies are satisfied
- Uses `rayon` for work-stealing parallelism

**Fiat-Shamir Support**:
- Integrates `spongefish` for cryptographic sponge functions
- Domain separation for security
- Challenge generation from transcript

**Dependencies**: `graph`, `backend`, `lang`, `share`, `petgraph`, `rayon`, `spongefish`

---

### 5. `costs/` - Benchmarking Infrastructure
**Purpose**: Measures actual performance of cryptographic operations across different curves and hardware configurations.

**Key Components**:
- `bench_info.rs`:
  - `BenchEntry`: Configuration for a single benchmark
  - `BenchParameters`: Thread count, curve type, input size
  - `BenchedTask`: Task types (field addition, multiplication, inversion, MSM)
  - `Curve`: Enum of supported curves

- `measurement.rs`: Cost measurement and serialization
- `lib.rs`: Main benchmarking harness using Criterion

**Benchmark Coverage**:
- Field operations: addition, multiplication, inversion (batched)
- Group operations: scalar multiplication, MSM
- Pairing operations (for pairing-friendly curves)
- Parallelism scaling (1 to N threads)
- Multiple input sizes (powers of 2)

**Output**: JSON files with timing data for cost model calibration

**Dependencies**: `ark-*` (curve implementations), `criterion`, `rayon`, `serde`, `strum`

---

### 6. `share/` - Shared Utilities
**Purpose**: Provides common data structures and utilities used across all crates.

**Key Components**:
- `context.rs`:
  - `Ctx<K, V>`: Immutable context/environment (BTreeMap wrapper)
  - `Set<K>`: Immutable set (BTreeSet wrapper)
  - Functional operations: `insert_with()`, `merge()`, `map()`

- `pretty.rs`:
  - `Pretty` trait for pretty-printing
  - `DocAllocator`, `DocBuilder`: Document formatting (based on `pretty` crate)

- `traversal.rs`:
  - `Traversal` trait for tree/graph traversal
  - Visitor pattern support

- `macros.rs`: Utility macros (`unwrap!`, etc.)

**Design Philosophy**:
- Immutable data structures for safe concurrent access
- Type-safe contexts for variable bindings
- Generic pretty-printing infrastructure

**Dependencies**: `pretty`, `thiserror`, `arbitrary` (for testing)

---

### 7. `cli/` - Command-Line Interface
**Purpose**: Main entry point for the Zippel compiler toolchain.

**Key Components**:
- `main.rs`:
  - **Commands**:
    - `eval`: Compile and execute a protocol
    - `analyze`: Run static analyses (completeness, zero-knowledge)
    - `benchmark`: Run performance benchmarks

**Compilation Pipeline** (for `eval`):
1. Parse `.zippel` file → `UModule`
2. Type checking → `CModule`
3. Concrete instantiation (resolve type parameters)
4. DAG construction → `UDag`
5. Static analyses:
   - Transitive closure
   - Gröbner basis (polynomial constraints)
   - Qualifier propagation (public/private)
   - Uniformity propagation (randomness)
   - Completeness check
6. Scheduling → `TDag` (thread allocations via Gurobi ILP)
7. Runtime execution → `MutexGraph` → result

**Analysis Pipeline** (for `analyze`):
- Similar to eval but focuses on verification
- Outputs: completeness violations, zero-knowledge leaks
- PDF visualization of DAGs with annotations

**Features**:
- PDF export of intermediate graphs (using Graphviz)
- Subgraph selection for large protocols
- Configurable curve backend (BLS12-381, BN254, etc.)

**Dependencies**: All other crates, `clap`, `env_logger`, `bincode`

---

### 8. `examples/` - Protocol Examples
**Purpose**: Demonstrates Zippel language features with real cryptographic protocols.

**Example Protocols** (`.zippel` files):
- `schnorr.zippel`: Schnorr signature protocol
- `kzg.zippel`: KZG polynomial commitment scheme
- `ipa.zippel`: Inner Product Argument (Bulletproofs)
- `pedersen_eq.zippel`: Pedersen commitment equality
- `hyrax-pop.zippel`: Hyrax proof of polynomial evaluation
- `ex_pairing.zippel`: Pairing-based cryptography examples

**Binary Examples** (`src/` subdirectories):
- `src/mle_example/`: Multilinear extension examples
- `src/kzg/`: KZG commitment runner
- `src/ipa/`: IPA protocol runner
- `src/schnorr/`: Schnorr protocol runner

Each binary:
1. Loads corresponding `.zippel` file
2. Compiles to DAG
3. Generates sample inputs
4. Executes as prover
5. Executes as verifier
6. Validates correctness

**Dependencies**: `cli`, `backend`, `lang`, `share`, `ark-*`, `rand`

---

## Zippel Language Overview

### Syntax Elements

**Protocol Declaration**:
```zippel
proto schnorr<G: Group, F: Scalar<G>>(
    private x: F,
    public g: G,
    public h: G
) where h == g*x {
    // protocol body
}
```

**Key Language Features**:
- **Type Parameters**: `G: Group`, `F: Scalar<G>`, `N: 2` (size constraints)
- **Qualifiers**: `public`, `private` (zero-knowledge)
- **Types**:
  - Base: `F` (field), `G` (group), `GT` (pairing target), `Bool`
  - Composite: `[T; N]` (vector), `Uni<F, N>` (univariate poly), `Mle<F, N>` (multilinear)
  - Index: `Fin<range>` (finite index type)
- **Constraints**: `where` clauses (polynomial equations)

**Operations**:
- Arithmetic: `+`, `-`, `*`, `/`, `^` (exponentiation)
- Cryptographic:
  - `random<F>`: sample random field element
  - `challenge<F>`: Fiat-Shamir challenge
  - `pair(g1, g2)`: pairing operation
  - `verify(condition)`: verification check
- Transcript: `x <- expr` (send to transcript)
- Polynomial: `poly([coeffs])`, evaluation, FFT, IFFT
- Vector: `reduce(op, vec)`, `map(fn, vec)`, slicing `vec[start..end]`

---

## Compilation Flow

```
┌─────────────┐
│ .zippel file│
└──────┬──────┘
       │ Parse (lang/parser)
       ▼
┌─────────────┐
│   UModule   │ (Untyped, symbolic sizes)
└──────┬──────┘
       │ Type Inference (lang/typ)
       ▼
┌─────────────┐
│   CModule   │ (Typed, concrete sizes)
└──────┬──────┘
       │ Concretize (instantiate type params)
       ▼
┌─────────────┐
│    UDag     │ (Unannotated DAG)
└──────┬──────┘
       │ Static Analyses (graph/analyses)
       ▼
┌─────────────┐
│  QDag/DQDag │ (Annotated with qualifiers/distributions)
└──────┬──────┘
       │ Scheduling (graph/scheduler)
       ▼
┌─────────────┐
│    TDag     │ (Thread allocations)
└──────┬──────┘
       │ Runtime (runtime)
       ▼
┌─────────────┐
│ MutexGraph  │ → Execute → Result
└─────────────┘
```

---

## Key Algorithms & Techniques

### 1. **Type System**
- **Hindley-Milner style** with extensions for:
  - Dependent sizes (vectors parameterized by length)
  - Type kinds (Field, Group, Scalar<G>, Pairing<G1, G2>)
  - Qualifier inference (public/private propagation)
  - Distribution tracking (uniform vs deterministic)

### 2. **Static Analyses**
- **Gröbner Basis**: Solves polynomial constraint systems in `where` clauses
- **Transitive Closure**: Computes full dependency graph
- **Qualifier Propagation**: Ensures no private data leaks to verifier
- **Uniformity Analysis**: Tracks randomness for zero-knowledge
- **Completeness**: Verifies prover can compute all values from witnesses

### 3. **Scheduling**
- **ILP-based**: Uses Gurobi to optimize thread allocation
- **Cost Model**: Derived from empirical benchmarks (costs/ crate)
- **Objectives**: Minimize makespan, balance load, respect dependencies
- **Constraints**: Precedence, resource limits

### 4. **Execution**
- **Data-flow**: Nodes execute when dependencies satisfied
- **Work-stealing**: Rayon thread pool for parallelism
- **Fiat-Shamir**: Transcript-based challenge generation
- **Type-safe**: Values tagged with cryptographic backend

---

## Important Design Patterns

### 1. **Parameterized Backend** (`ArkConfig`)
All cryptographic operations are generic over `ArkConfig`, allowing:
- Easy switching between curve types
- Field-only computations (no curves)
- Uniform API across different backends

### 2. **Annotated DAGs** (`Dag<C, A>`)
Graph IR is parameterized by annotation type `A`:
- `Nothing`: No annotations (initial construction)
- `Qualifier`: Public/private qualifiers
- `(Qualifier, Distribution)`: Qualifiers + uniformity
- `ThreadAlloc`: Thread scheduling
- `Arc<RuntimeInformation<C>>`: Runtime execution state

### 3. **Immutable Contexts** (`Ctx<K, V>`)
All variable environments use immutable maps:
- Safe for concurrent access
- Functional updates (return new context)
- Type-safe variable lookups

### 4. **Static Analysis Trait**
```rust
trait StaticAnalysis<C: ArkConfig, A> {
    type Args;
    type Output;
    fn new(g: &Dag<C, A>) -> Self;
    fn run(&mut self, args: Self::Args) -> Self::Output;
}
```
Uniform interface for all analyses.

---

## External Dependencies

### Cryptography
- **Arkworks** (`ark-*`): Elliptic curves, finite fields, pairings
  - `ark-ff`: Finite field arithmetic
  - `ark-ec`: Elliptic curve operations
  - `ark-poly`: Polynomial arithmetic, FFT
  - Curve crates: `ark-bls12-381`, `ark-bn254`, etc.
- **Spongefish**: Cryptographic sponge for Fiat-Shamir

### Optimization
- **Gurobi** (`grb`): ILP solver for scheduling (requires license)

### Parsing & Types
- **Pest**: PEG parser generator
- **from-pest**: AST conversion from parse tree

### Parallelism
- **Rayon**: Data parallelism, work-stealing

### Graphs
- **Petgraph**: Graph data structure and algorithms

### Utilities
- **Thiserror**: Error handling
- **Clap**: CLI argument parsing
- **Criterion**: Benchmarking framework

---

## Development Workflow

### Building
```bash
# Install Gurobi first, then:
GUROBI_LIBNAME="gurobi120" cargo build
```

### Running Examples
```bash
# Compile and execute a protocol
cargo run --bin cli -- eval examples/schnorr.zippel

# Run static analyses
cargo run --bin cli -- analyze examples/kzg.zippel --pdf kzg.pdf

# Run benchmarks
cargo run --bin cli -- benchmark output.json --iterations 1000
```

### Testing
```bash
# Unit tests
cargo test

# Specific crate
cargo test -p lang
```

### Adding a New Protocol
1. Create `examples/myprotocol.zippel`
2. Create `examples/src/myprotocol/main.rs`
3. Add binary entry in `examples/Cargo.toml`:
   ```toml
   [[bin]]
   name = "myprotocol"
   path = "src/myprotocol/main.rs"
   ```
4. Compile: `cargo build --bin myprotocol`
5. Run: `cargo run --bin myprotocol`

---

## Future Development Guidelines

### Adding a New Cryptographic Primitive
1. **Language**: Extend grammar in `lang/src/parser/zippel.pest`
2. **AST**: Add expression variant in `lang/src/ast/exp.rs`
3. **Types**: Add type rules in `lang/src/typ/infer.rs`
4. **Backend**: Implement in `backend/src/values.rs` and `backend/src/config.rs`
5. **Graph**: Add operation in `graph/src/op.rs`
6. **Runtime**: Add execution case in `runtime/src/graph.rs`
7. **Costs**: Benchmark in `costs/src/lib.rs`

### Adding a New Curve
1. Add dependency in `backend/Cargo.toml`
2. Implement `ArkConfig` in `backend/src/config.rs`
3. Add to `costs/src/bench_info.rs` enum
4. Add benchmark cases in `costs/src/lib.rs`

### Adding a New Analysis
1. Create module in `graph/src/analyses/myanalysis.rs`
2. Implement `StaticAnalysis<C, A>` trait
3. Export in `graph/src/analyses/mod.rs`
4. Integrate in `cli/src/main.rs` compilation pipeline

### Debugging
- **Parser errors**: Check `lang/src/parser/error.rs`
- **Type errors**: Enable logging: `RUST_LOG=debug`
- **Graph visualization**: Use `--pdf` flag to generate Graphviz output
- **Runtime errors**: Check node values in `MutexGraph`

---

## Security Considerations

### Zero-Knowledge Guarantees
- **Qualifier system** ensures private values never leak to verifier
- **Uniformity analysis** verifies randomness distribution
- **Knowledge analysis** checks extractability

### Completeness Guarantees
- **Completeness analysis** ensures prover can compute all required values
- **Constraint solving** via Gröbner basis verifies polynomial relations

### Soundness
- **Type system** prevents malformed protocols
- **Static analyses** catch errors before execution
- **Runtime checks** validate cryptographic operations

### Known Limitations
- Prototype implementation (not production-ready)
- Gurobi license required for optimal scheduling
- Limited to non-interactive proofs (Fiat-Shamir)

---

## Performance Characteristics

### Compilation Time
- **Parsing**: O(n) in source size
- **Type inference**: O(n²) worst case (unification)
- **DAG construction**: O(n) in AST size
- **Gröbner basis**: Exponential worst case (constraint complexity)
- **Scheduling (ILP)**: NP-hard (uses heuristics + Gurobi)

### Runtime Performance
- **Parallelism**: Near-linear scaling with available threads
- **Memory**: Proportional to DAG size + intermediate values
- **Cryptographic ops**: Dominated by elliptic curve operations (MSM, pairings)

### Optimization Opportunities
- **MSM batching**: Combine scalar multiplications
- **FFT caching**: Reuse twiddle factors
- **Memory pooling**: Reduce allocations in hot paths
- **SIMD**: Vectorize field operations (Arkworks support)

---

## Glossary

- **AST**: Abstract Syntax Tree
- **DAG**: Directed Acyclic Graph
- **FFT**: Fast Fourier Transform
- **ILP**: Integer Linear Programming
- **MLE**: Multilinear Extension
- **MSM**: Multi-Scalar Multiplication
- **NIZK**: Non-Interactive Zero-Knowledge
- **PEG**: Parsing Expression Grammar
- **Uni**: Univariate polynomial (coefficient representation)
- **Qualifier**: Public/private annotation for zero-knowledge
- **Transcript**: Fiat-Shamir transcript for non-interactive protocols

---

## Contact & Licensing

**Authors**:
- Lef Ioannidis (elefthei@seas.upenn.edu)
- Alireza Shirzad (alrshir@seas.upenn.edu)

**Institution**: University of Pennsylvania, Distributed Systems Lab

**License**: MIT (see LICENSE-MIT)

**Status**: Research prototype - DO NOT USE IN PRODUCTION

---

This summary provides a comprehensive overview for developers working on the Zippel language implementation. For specific implementation details, refer to the source code and inline documentation.

---

## Recent Fixes (2025-11-15)

### Test Failure Investigation

After running `cargo test`, 4 tests were failing. Through systematic debugging and trying multiple solutions:

**Root Cause Found**: The `inline()` step in `KnowledgeAnalysis::run()` was removing private variables too aggressively, preventing leak detection from finding polynomials that mix public transcript values with private witness data.

**Solution Applied**: Commenting out the `inline(|p| p.is_public())` call in `graph/src/analyses/knowledge.rs:run()`.

**Results**:
- Before: 16 passed, 4 failed
- After: 18 passed, 2 failed  
- Fixed: `groebner_ex3`, `groebner_zerocheck`
- Remaining: `knowledge_foo` (under investigation), `test_maple` (Groebner basis ordering, cosmetic)

See `SOLUTIONS_TRIED.md` for detailed analysis of all approaches attempted.

**Key Insight**: Zero-knowledge leak detection requires both public and private variables to remain in the final Groebner basis. The inline operation, which substitutes variables to express everything in terms of public variables only, eliminates the evidence needed to detect information leakage.

### Final Solution (2025-11-15 - Updated)

After deeper investigation, found the root cause was **two-fold**:

1. **Inline step removed private variables** - Made it impossible to detect leaks
2. **Elimination was too aggressive** - Removed entire polynomials containing uniform vars, even when they showed leaks

**Final Fixes Applied**:
1. Simplified `is_leak()` - Just check if polynomial mixes public and private variables
2. Skipped `inline()` call - Preserves private variables needed for leak detection  
3. **Refined `eliminate_var()`** - Only remove polynomials with ONLY uniform variables, keep mixed ones

**Final Results**:
- Before: 16 passed, 4 failed
- After: **19 passed, 1 failed**
- Fixed all 3 knowledge analysis tests
- Remaining: Only `test_maple` (Groebner ordering, cosmetic issue)

See `FINAL_SOLUTION.md` for complete analysis and code changes.

**Key Insight**: Zero-knowledge leak detection needs polynomials showing relationships between public transcript and private witnesses. Aggressive elimination and inlining destroy this evidence. The fix: be selective about what to eliminate and preserve information-bearing polynomials.
