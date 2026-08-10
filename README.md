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

## Tutorial

Voblint programs are written in VIMP, a small IMP-style language with
`__voblint_check(cond)` assertions. Given a counted loop:

```c
void main() {
    x := 0;
    while (x < 10) {
        x := x + 1
    };
    __voblint_check(0 < x)
}
```

running the Interval analysis over it (see "Running the CLI" below) proves
the check on the widened/narrowed fixpoint:

```bash
$ pixi run voblint --analysis interval tests/regression/02-control-flow/precision/02-while_loop.vimp
8:3  pp3        0<x                  PROVED   x=[10,10]
```

`--dot` renders the solved CFG as GraphViz, with the computed abstract state
shown at each check node:

```bash
pixi run voblint --analysis interval --dot tests/regression/02-control-flow/precision/02-while_loop.vimp \
  | dot -Tpng -o while_loop_cfg.png
```

![Solved CFG for the counted-loop example, showing the widened interval x=[10,10] at the check node](docs/images/while_loop_cfg.png)

The same rendering on a branch/join program shows the interval domain merging
both arms:

```bash
pixi run voblint --analysis interval --dot tests/regression/02-control-flow/precision/01-if_else.vimp \
  | dot -Tpng -o if_else_cfg.png
```

![Solved CFG for the if/else example, showing the joined interval y=[1,2] at the check node](docs/images/if_else_cfg.png)

Each rendering embeds the source alongside the CFG, splits nodes into
per-activation clusters (context-sensitivity, see "Why Voblint?" above), and
shades the checked node by its verdict. `--dot-full` renders every node with
its own computed abstract state instead of only check nodes -- useful for
inspecting the fixpoint at a program point with no check at all, e.g. mid-loop.
See "Running the CLI" below for `--graph-snapshot` (a DOT-free textual
alternative) and `--parse-only`.

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

* **D** — abstract facts associated with program points,
* **G** — globally shared analysis information published and consumed across program points.

The central abstraction is the `sound_dg_spec` locale, an Isabelle/HOL formalization of Goblint's [`Spec`](https://github.com/goblint/analyzer/blob/1ab59c9c4d9859e9135885d3c9a9aa1a8f3b677e/src/framework/analyses.ml#L168-L263)-interface. An analysis instantiates this locale by providing domain-specific transfer, combine, and communication operations over abstract carriers. From this specification, the framework automatically derives:

* executable equation generation,
* integration with the verified top-down solver,
* reusable collecting-semantics soundness theorems,
* reusable source-level correctness theorems,
* a complete executable analysis pipeline.

This separation allows Sign, Interval, mixed Sign × Interval, and future analyses to reuse the same verified infrastructure while varying only the domain-specific analysis logic.

The executable frontend is provided by `Exec_DG_Bridge.thy`, which implements:

* executable finite-map representations of D/G states,
* the refinement morphism `fun_of_dg_st`,
* executable equation generation via `dg_gen_of`,
* transport of solver-computed results to abstract post-solutions through
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

## VIMP Grammar Pipeline

VIMP source syntax has a single source of truth: **`grammar/vimp.yaml`**.
Two generators realize it for two independent parser targets:

```text
grammar/vimp.yaml
       │
       ├── scripts/gen_vimp_menhir.py   ──▶ cli/vimp_parser.mly, cli/vimp_lexer.mll
       │
       └── scripts/gen_vimp_isabelle.py ──▶ src/VIMP/VIMP_Grammar_Generated.thy

```

Two generators exist because the CLI frontend and the Isabelle frontend have
fundamentally different parser infrastructures -- Menhir/ocamllex for the
former, Isabelle mixfix syntax and `parse_translation` for the latter (the
generated `VIMP_Grammar_Generated.thy`, imported by `VIMP_Notation.thy`).
Neither can express the other's grammar format, so each generator is
responsible for realizing the shared, neutral grammar into its own idiom
(precedence declarations, numeral decoding, and similar target-specific
mechanics). Both generated outputs are committed, the same convention
`codegen/generated/` uses for Isabelle's own code export; do not hand-edit
`cli/vimp_parser.mly`, `cli/vimp_lexer.mll`, or `VIMP_Grammar_Generated.thy`.

**This pipeline sits outside the proved pipeline above and is untrusted
code.** No soundness theorem in this repository covers lexing or parsing --
the certified pipeline starts at an already-constructed VIMP AST
(`imp_prog`), regardless of whether that AST came from the CLI frontend, a
test driver, or by hand. Confidence in the generated parsers comes from
engineering process rather than proof:

* a single canonical grammar, with deterministic, drift-checked generation
  (`git diff --exit-code` after regenerating);
* the `.vimp` regression corpus (`tests/`);
* AST round-trip and print-stability checks against an independently
  constructed Isabelle AST (`tests/property/ast_driver.ml`);
* Hypothesis-based property tests that fuzz both generated programs and
  mutated source text (`tests/property/`, `pytest tests/property/`).

A `lefthook` pre-commit hook (`.lefthook.yaml`, installed by `./scripts/setup.sh`
or `pixi run lefthook-install`) regenerates both grammar artifacts on every
commit that touches `grammar/vimp.yaml` or a generator script and fails the
commit if that leaves the working tree dirty, so drift is caught locally
before it reaches CI.

## Build Instructions

### Requirements

* **[Isabelle](https://isabelle.in.tum.de/)  2025** (or newer)
* **[AFP](https://www.isa-afp.org/)** (Archive of Formal Proofs) checkout containing `Root_Balanced_Tree` and `Dijkstra_Shortest_Path`.
* **[pixi](https://pixi.sh/)** -- the repository's task runner and Python-side dependency manager (I/R, the grammar generators, the property-test suite, `lefthook`). `pixi.toml` is the single command surface: `pixi run <task>`, `pixi task list` to see all of them.
* `git`, `bash`, and standard POSIX tools.
* OCaml (`ocamlfind`, `menhir`, `ocamllex`, `zarith`) via opam, for the code-generation regression driver -- see "Executable code generation" below. conda-forge's OCaml packages have no osx-arm64 build for `ocaml-findlib`/`ocaml-zarith`, so pixi does not manage this toolchain; opam does.

### Pixi task reference

`pixi.toml` is the single command surface (`pixi run <task>`, `pixi task list`
for the live list). Tasks needing `AFP` fall back to `~/afp/thys` if unset.

| Task | Requires | Description |
| --- | --- | --- |
| `vendor` | -- | Init/update the `td-verification` submodule and apply its Isabelle2025 patch |
| `bootstrap` | Isabelle | One-shot session-root setup, depends on `vendor` |
| `build` | Isabelle, `AFP` | Batch-build the main formalization session (the completion gate -- see "Status reporting" in `AGENTS.md`) |
| `html` | Isabelle, `AFP` | Render the session's Isabelle HTML presentation |
| `jedit` | Isabelle, `AFP` | Launch jEdit with session roots pre-loaded |
| `isabelle-lint` | Isabelle | Run Isabelle's own linter over the session |
| `codegen` | Isabelle, `AFP` | Regenerate `codegen/generated/` from the `export_code` declarations |
| `codegen-check` | Isabelle, `AFP` | Fail if `codegen/generated/` has drifted from those declarations |
| `codegen-ocaml-check` | Isabelle, `AFP`, opam | Compile-check the generated OCaml |
| `codegen-regression` | opam | Run the OCaml driver under `codegen/regression/` against Isabelle-proved expected output |
| `cli-build` | opam (`menhir`, `ocamllex`, `zarith`) | Build the `voblint` CLI binary (`cli/voblint`) from the generated OCaml plus the Menhir/ocamllex VIMP frontend |
| `cli-test` | opam | Run `tests/run.py` against the built CLI, depends on `cli-build` |
| `voblint` | opam | Rebuild (via `cli-build`) and run the CLI; extra arguments pass straight through, e.g. `pixi run voblint --analysis sign FILE.vimp` |
| `gen-grammar-isabelle` / `gen-grammar-menhir` | -- | Regenerate one grammar target from `grammar/vimp.yaml` |
| `grammar-check` | -- | Regenerate both targets and fail on any diff (drift check) |
| `property` | -- | Run the Hypothesis property-test suite under `tests/property/`, depends on `property-build` |
| `lefthook-install` | -- | Install the pre-commit hook (`.lefthook.yaml`) |
| `lint` | -- | Run the pre-commit hook suite over all files |
| `ci` | everything above | Everything CI runs, under one name |

### Building

Set `AFP` to your local AFP `thys/` directory (defaults to `~/afp/thys`):

```bash
# 1. Initialize the TD solver submodule and apply compatibility patches
pixi run vendor

# 2. Build the main formalization session (sorry-free)
AFP=/path/to/afp/thys pixi run build

# 3. Launch jEdit with session roots pre-loaded
AFP=/path/to/afp/thys pixi run jedit

```

*Note: For details on agent-assisted development using Isabelle/Q and headless Isabelle/R, see `docs/ISABELLE_AGENT_NOTES.md` and the provided `./scripts/setup.sh`.*

### Executable code generation

Each domain exposes a runtime-program entry point -- `analyse_sign_report`
(`Voblint_Examples.Example_Sign_Codegen`, the native D/G pipeline) and
`analyse_interval_td_report` (`Voblint_Analysis.Interval_Checks`, the
widening/warrowing-backed solver) -- reusing the exact functions the
soundness theorems are proved about, not a parallel implementation. `analyse`
(`Voblint_Examples.Example_Analysis_Dispatch`) dispatches on `analysis_kind`
(`Sign_Analysis`/`Interval_Analysis`) to either domain's check report. All
three, plus the VIMP AST constructors, are exported to OCaml so
external code can build a program and call `analyse` without touching
Isabelle: `export_code` translates the same executable equations the kernel
checked, so the generated function is not a hand-written stand-in for a
proved one.

`analyse_interval_proved_sound`/`analyse_interval_refuted_sound` and
`analyse_sign_proved_sound`/`analyse_sign_refuted_sound`
(`Example_Analysis_Dispatch.thy`) restate the domains' soundness theorems
directly over `analyse`, so a runtime verdict connects to its soundness proof
without unfolding the dispatcher by hand. These theorems are conditional: a
`Check_Proved`/`Check_Refuted` entry `analyse` returns is not itself a
discharged certificate. Applying its soundness theorem additionally requires,
for that program, a solver-termination witness (no result in this
formalization proves either solver terminates on every input -- termination
is checked per program, typically `by eval`) and a proof that the checked
node reaches `cfg_exit`. `dispatch_demo_first_check_certified` is one
complete, hypothesis-free instance of this chain: a concrete `Check_Proved`
verdict `analyse` actually returns, with both facts discharged and no
assumption left open.

`code_identifier` declarations (`Example_Analysis_Dispatch.thy`) group the
~60 contributing Isabelle theories into two named OCaml modules instead of
one undifferentiated file: `Core` (VIMP/CFG/executable state/generic
analysis plumbing/the vendored solver/both domains' lattices and transfer
functions; these cannot be split further -- real mutual code-level
dependencies, e.g. the executable state is generically instantiated at the
solver's own `widening`/`narrowing` type classes) and `Analyse` (the public
facade: `analysis_kind`, `analyse` itself, ~30 lines). OCaml's serializer
only ever emits one file regardless of `module_name`/`code_identifier`, so
the grouping instead organizes that one file into nested
`module ... = struct ... end` blocks. Splitting `Sign`/`Interval` out of
`Core` passes Isabelle's own `export_code` checks but `ocamlfind ocamlopt`
then rejects an unbound type-class dictionary field the OCaml
module-signature inference doesn't expose across that boundary -- not
fixable by regrouping, so `Core`/`Analyse` is the finest split the OCaml
compiler accepts.

```bash
# Regenerate codegen/generated/ from the export_code declarations
AFP=/path/to/afp/thys pixi run codegen

# Fail if codegen/generated/ has drifted from those declarations
AFP=/path/to/afp/thys pixi run codegen-check

# Compile and run the hand-written OCaml driver under
# codegen/regression/ against codegen/generated/, and check its output
# against the values already proved by Example_Analysis_Dispatch.thy's
# dispatch_demo_sign_unknown / dispatch_demo_interval_precise
pixi run codegen-regression
```

Generated sources are tracked under `codegen/generated/`; do not hand-edit
them. `codegen/regression/ocaml/` holds the hand-written driver that
exercises the generated code and compares it against the Isabelle-proved
expected output -- so the generated OCaml is checked against the same
theorems as the Isabelle source, not merely assumed to match it. Both `pixi run
codegen-check` and `pixi run codegen-regression` run in CI
(`.github/workflows/ci.yml`).

### Running the analyzer (`voblint` CLI)

`voblint` is a thin, unverified adapter (`cli/main.ml`) over the exact
generated `analyse` entry point above -- see its trust-boundary note in
`docs/CLI_DESIGN.md`. `pixi run voblint` rebuilds the binary from
`codegen/generated/ml/Voblint_CLI.ml` via `cli-build` and then runs it, so any
extra arguments after the task name go straight to `cli/voblint`, not to pixi:

```bash
# Check report: one line per __voblint_check, in source order
pixi run voblint --analysis interval tests/regression/00-sanity/precision/01-straight_line_proved.vimp

# Same analysis, GraphViz rendering of the solved, context-split CFG instead
# (state shown at check nodes only)
pixi run voblint --analysis interval --dot tests/regression/02-control-flow/precision/01-if_else.vimp > cfg.dot
dot -Tsvg cfg.dot -o cfg.svg   # requires graphviz's `dot` on PATH

# Same rendering, but every node carries its own computed abstract state,
# not just check nodes -- useful with no check nearby, e.g. mid-loop
pixi run voblint --analysis interval --dot-full tests/regression/02-control-flow/precision/02-while_loop.vimp > cfg.dot

# Deterministic textual CFG snapshot (clusters/nodes/edges) with no GraphViz
# dependency -- what the regression corpus embeds as expected --graph-snapshot output
pixi run voblint --analysis interval --graph-snapshot tests/regression/02-control-flow/precision/01-if_else.vimp

# Parse-only syntax check, no --analysis needed (0 on success, 2 on a parse error)
pixi run voblint --parse-only tests/regression/00-sanity/02-malformed.vimp
```

Run `pixi run voblint --help` for the full flag list, including `--timeout`
(the Interval backend is sound but not proved total, so the analysis itself
runs in a killable subprocess -- see `docs/CLI_DESIGN.md`'s containment note).

### Vendoring the TD solver

Upstream: [stilscher/td-verification](https://github.com/stilscher/td-verification).
Vendored as a submodule via the private fork
[`ManuelLerchner/td-verification`](https://github.com/ManuelLerchner/td-verification)
(CI + local access). GitHub Actions cannot clone the fork with the default
`GITHUB_TOKEN`; add a classic PAT with `repo` scope as repository secret
`SUBMODULES_TOKEN`, or make the fork public. A small Isabelle2025 compatibility
change lives in `vendor/td-verification.patch`; `pixi run vendor` applies it
(idempotent). To regenerate the patch after changing the submodule's working
tree: `git -C vendor/td-verification --no-pager diff > vendor/td-verification.patch`.

`vendor/autocorrode` (the I/Q/I/R MCP servers, see "Agent-assisted
development" below) is a separate submodule. To fast-forward it to upstream
main: `git submodule update --remote --merge vendor/autocorrode`, then review
and commit the pointer update.

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
| `./scripts/setup.sh` | one-shot bootstrap: submodules, pixi environment + lefthook install, I/Q plugin (`--no-iq` to skip) |
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
