<img width="1792" height="592" alt="Gemini_Generated_Image_uv4qywuv4qywuv4q" src="https://github.com/user-attachments/assets/6d58a89f-a92b-4029-9677-83c049254250" />

# Voblint

> **A Generic, Executable, and Machine-Checked Framework for Interprocedural Abstract Interpretation in Isabelle/HOL**

> Master's thesis. Manuel Lerchner, supervised by [@AlexandraGrass](https://www.github.com/AlexandraGrass)

## Abstract


Voblint is a reusable, machine-checked Isabelle/HOL framework for constructing, executing, and verifying generic interprocedural abstract interpreters. Inspired by Goblint's modular D/G architecture, it combines verified compilation from VIMP programs, activation-local operational semantics, executable equation generation, a verified top-down solver, and end-to-end source-level soundness.

Unlike most existing formalizations, Voblint proves properties of the analysis result computed by a verified solver rather than an externally provided fixpoint.

## Why Voblint?

* **Computed results:** The verified solver computes the abstract fixpoint inside Isabelle/HOL. All soundness theorems apply directly to this computed result.
* **Generic by design:** The framework is generic over abstract domains, transfer functions, widening strategies, D/G analyses, and context abstractions.
* **Context-sensitive:** Analyses are parameterized by arbitrary context keys, enabling monovariant, activation-based, call-string, or custom context abstractions without changing the proof infrastructure.
* **Executable:** Analyses are not just specified; they run directly inside Isabelle/HOL.
* **Visualizable:** Executable GraphViz output for certified analysis results.

## Foundations

Voblint is inspired by several complementary lines of work:

* **Goblint** ([Github](https://github.com/goblint/analyzer)) – modular interprocedural abstract interpretation and the D/G analysis architecture.
* **Abstract Interpretation of Annotated Commands** ([ITP 2012](https://doi.org/10.1007/978-3-642-32347-8_9)) – reusable abstract interpretation in Isabelle/HOL.
* **The Top-Down Solver Verified: Building Confidence in Static Analyzers** ([CAV 2024](https://doi.org/10.1007/978-3-031-65627-9_15)) – executable verified fixpoint solving.
* **Mixed Flow-Sensitive Static Analysis: Engineering Modularity** ([FM 2026](https://doi.org/10.1007/978-3-032-26220-2_22)) – engineering modular heterogeneous analyses.

## The Certified Execution Pipeline

Voblint proves one continuous end-to-end execution story. The framework bridges the gap between the concrete source code and the computed mathematical fixpoint:

```text
            VIMP Program
                 │
                 ▼
       Verified CFG Compilation
                 │
                 ▼
      Activation-local Semantics
                 │
                 ▼
      Generic D/G Specification
                 │
                 ▼
    Executable Equation Generation
                 │
                 ▼
          Verified TD Solver
                 │
                 ▼
      Computed Abstract Solution
                 │
                 ▼
        Collecting Semantics
                 │
                 ▼
       Source-Level Soundness

```

## Generic D/G Framework

Voblint's analyses are built on a reusable **D/G framework** inspired by Goblint's modular analysis architecture. Rather than implementing a separate solver and proof for every analysis, Voblint factors analyses into:

- **D** — abstract facts associated with program points,
- **G** — globally shared analysis information published and consumed across program points.

The central abstraction is the `sound_dg_spec` locale, an Isabelle/HOL formalization of Goblint's [`Spec`](https://github.com/goblint/analyzer/blob/1ab59c9c4d9859e9135885d3c9a9aa1a8f3b677e/src/framework/analyses.ml#L168-L263)-interface. An analysis instantiates this locale by providing domain-specific transfer, combine, and communication operations over abstract carriers. From this specification, the framework automatically derives:

- executable equation generation,
- integration with the verified top-down solver,
- reusable collecting-semantics soundness theorems,
- reusable source-level correctness theorems,
- a complete executable analysis pipeline.

This separation allows Sign, Interval, mixed Sign × Interval, and future analyses to reuse the same verified infrastructure while varying only the domain-specific analysis logic.

The executable frontend is provided by `Exec_DG_Bridge.thy`, which implements:

- executable finite-map representations of D/G states,
- the refinement morphism `fun_of_dg_st`,
- executable equation generation via `dg_gen_of`,
- transport of solver-computed results to abstract post-solutions through
  `part_post_solution_dg_st_to_abs`.

Consequently, adding a new D/G analysis requires only instantiating `sound_dg_spec`; equation generation, solver execution, and the end-to-end correctness proof are inherited from the generic framework.

## Extending Voblint

The framework is designed to be highly extensible. Rather than proving a new analysis from scratch, you only need to provide domain-specific components:

| Extension                     | Required work                         |
| ----------------------------- | ------------------------------------- |
| **Abstract domain**           | Define lattice and concretization (γ) |
| **Transfer functions**        | Prove local soundness                 |
| **Goblint D/G specification** | Instantiate the generic interface     |
| **Context abstraction**       | Define a context key                  |
| **Widening**                  | Provide widening/narrowing operators  |

## Repository Structure

```text
VIMP
 │   Source language
 ▼
CFG
 │   Compilation & semantics
 ▼
Core
 │   Generic D/G framework, domains, solver interface
 ▼
Analysis
 │   Concrete domain instances (Sign, Interval, ...)
 ▼
Formalization
 │   End-to-end soundness
 ▼
Examples
     Executable analyses & GraphViz

```

* **`VIMP/`**: Syntax, procedures, globals/locals, small-step semantics
* **`CFG/`**: Procedure-aware CFG compilation, activation-local traces, and collecting semantics
* **`Core/`**: Generic D/G framework, domains, equations, and the TD solver bridge -- no domain-specific content
* **`Analysis/`**: Concrete domain instances (Sign, Interval, Parity, mixed Sign x Interval, ...) built on `Core/`
* **`Formalization/`**: End-to-end solver, collecting-semantics, and source-level soundness
* **`Examples/`**: Executable runs, flagship demos, and GraphViz tooling
* **`vendor/`**: Verified TD solver submodule and Isabelle2025 patches
* **`docs/`**: Proof overview, phase tracking, and agent workflow notes

## Build Instructions

### Requirements

* **[Isabelle](https://isabelle.in.tum.de/)  2025** (or newer)
* **[AFP](https://www.isa-afp.org/)** (Archive of Formal Proofs) checkout containing `Root_Balanced_Tree` and `Dijkstra_Shortest_Path`.
* `make`, `git`, and standard POSIX tools.

### Building

Set `AFP` to your local AFP `thys/` directory (defaults to `~/afp/thys`):

```bash
# 1. Initialize the TD solver submodule and apply compatibility patches
make vendor

# 2. Build the main formalization session (sorry-free)
make AFP=/path/to/afp/thys build

# 3. Launch jEdit with session roots pre-loaded
make AFP=/path/to/afp/thys jedit

```

*Note: For details on agent-assisted development using Isabelle/Q and headless Isabelle/R, see `docs/ISABELLE_AGENT_NOTES.md` and the provided `./scripts/setup.sh`.*

### Executable code generation

Each domain exposes a runtime-program entry point, `analyse_sign` /
`analyse_interval` (`Voblint_Examples.Example_Sign_Codegen`,
`Voblint_Analysis.Interval_Checks`), reusing the same native D/G pipeline as
the soundness theorems -- not a parallel one. `analyse`
(`Voblint_Examples.Example_Analysis_Dispatch`) dispatches on `analysis_kind`
(`Sign_Analysis`/`Interval_Analysis`) to either domain's check report. All
three, plus the VIMP AST constructors, are exported to Haskell and OCaml so
external code can build a program and call `analyse` without touching
Isabelle.

```bash
# Regenerate codegen/generated/ from the export_code declarations
make AFP=/path/to/afp/thys codegen

# Fail if codegen/generated/ has drifted from those declarations
make AFP=/path/to/afp/thys codegen-check

# Compile and run the hand-written Haskell/OCaml drivers under
# codegen/regression/ against codegen/generated/, and check their output
# against the values already proved by Example_Analysis_Dispatch.thy's
# dispatch_demo_sign_unknown / dispatch_demo_interval_precise
make regression
```

Generated sources are tracked under `codegen/generated/`; do not hand-edit
them. `codegen/regression/{haskell,ocaml}/` hold the hand-written drivers
that exercise the generated code and compare it against the Isabelle-proved
expected output -- so the generated Haskell/OCaml is checked against the same
theorems as the Isabelle source, not merely assumed to match it. Both `make
codegen-check` and `make regression` run in CI (`.github/workflows/ci.yml`).

### Vendoring the TD solver

Upstream: [stilscher/td-verification](https://github.com/stilscher/td-verification).
Vendored as a submodule via the private fork
[`ManuelLerchner/td-verification`](https://github.com/ManuelLerchner/td-verification)
(CI + local access). GitHub Actions cannot clone the fork with the default
`GITHUB_TOKEN`; add a classic PAT with `repo` scope as repository secret
`SUBMODULES_TOKEN`, or make the fork public. A small Isabelle2025 compatibility
change lives in `vendor/td-verification.patch`; `make vendor` applies it
(idempotent).

### Agent-assisted development

Proof development experiments with
[Isabelle/Q](https://github.com/awslabs/AutoCorrode/tree/main/iq) (I/Q), an MCP
server for Isabelle/jEdit that lets coding agents edit theories, query proof
states, run Sledgehammer, and explore tactics. Following the autoformalization
workflow of Kappelmann et al.,
[*Just Type It in Isabelle!*](https://arxiv.org/abs/2604.15713) (arXiv:2604.15713,
2026), §6.1. See `AGENTS.md` and `docs/ISABELLE_AGENT_NOTES.md`.

| Script | Role |
| --- | --- |
| `./scripts/setup.sh` | one-shot bootstrap: submodules, venv, I/Q plugin (`--no-iq` to skip) |
| `./scripts/start-iq.sh` | Isabelle/jEdit + I/Q on port 8765 |
| `./scripts/start-ir.sh` | headless Isabelle/R MCP on port 9148 |
| `./scripts/start-both.sh` | I/R background + I/Q foreground; Ctrl+C tears down both |

`start-ir.sh` registers `vendor/td-verification` as an Isabelle component via
`isabelle components -u`. This persistent, idempotent registration lets the
I/R `ML_process` resolve the parent session `TD`; the I/R launcher accepts only
one explicit session directory. Remove the registration, if needed, with:

```bash
isabelle components -x "$(pwd)/vendor/td-verification"
```
