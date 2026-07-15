# Voblint: An Executable and Machine-Checked Framework for Abstract Interpretation in Isabelle/HOL

> Master's thesis. Manuel Lerchner, supervised by [@AlexandraGrass](https://www.github.com/AlexandraGrass)

## Abstract

This repository implements an executable framework for certified abstract
interpretation in Isabelle/HOL. Analyses are defined once, executed inside
Isabelle using the verified side-effecting top-down solver of
[stilscher/td-verification](https://github.com/stilscher/td-verification), and
the solver computes analysis results that are certified sound once the analysis
instantiates the framework's soundness obligations. The framework is generic
over abstract domains and transfer functions. The flagship interval analysis
computes the invariant `x ∈ [0,20]` for a counting loop, and Isabelle proves
that this computed result soundly over-approximates every execution of the
original IMP2 program.

**The analysis result is computed, not supplied, and its soundness is proved by
the framework.**

## ⭐ Flagship Example

`src/Formalization/Examples/Executable/Interval/Core/Example_Interval_DG_Flagship.thy`

The flagship theory analyzes a counting loop:

```c
x = 0;
while (x < 20)
  x++;
```

It demonstrates the complete machine-checked chain:

```text
IMP2 source
      ↓
compile_prog
      ↓
CFG
      ↓
D/G equation generation
      ↓
verified solver
      ↓
computed interval solution
      ↓
solver correctness
      ↓
collecting soundness
      ↓
compiler correctness
      ↓
source-level guarantee
```

Computed result:

| Program point | Certified interval |
| --- | --- |
| Loop head | `[0,20]` |
| Loop body | `[0,19]` |
| Exit | `[20,20]` |

Isabelle computes these intervals and proves them sound for every execution of
the flagship source program from a valid initial store.

These intervals are not handwritten; the verified solver produces them during
evaluation inside Isabelle.

## Why This Matters

Many mechanized abstract-interpretation developments prove soundness assuming
an abstract solution. This repository executes the verified solver inside
Isabelle and certifies the computed analysis result. The flagship interval
example is one instance of a generic D/G framework that also supports
executable Sign and mixed-domain analyses.

## Contributions

### Scientific contributions

- Verified execution of abstract interpreters inside Isabelle.
- Machine-checked certification of computed analysis results.
- Generic D/G framework for Goblint-style abstract interpretation.
- Source-level soundness via compiler correctness.

### Demonstrated instances

- Executable Sign analysis.
- Executable Interval analysis.
- Mixed Sign x Interval analysis.
- Certified flagship interval example with GraphViz output.

## What Can I Reuse?

To add a new analysis:

- define the abstract domain;
- define sound transfer functions;
- instantiate the generic D/G interface.

The framework then:

- generates equations,
- executes the verified solver,
- certifies the computed analysis result.

## Certified Execution Pipeline

The repository proves one end-to-end execution story:

Key step: the verified solver computes `σ`.

```text
IMP2 source
  → compile_prog
  → CFG
  → dg_gen_of
  → verified solver computes σ
  → solver correctness yields part_post_solution σ
  → part_post_solution_dg_st_to_abs
  → collecting-soundness theorem
  → compiler-correctness simulation
  → source-level guarantee
```

Four distinct claims are established for the flagship:

1. The interval D/G analysis is executable.
2. The verified solver computes the certified solution.
3. The computed solution soundly over-approximates CFG collecting semantics.
4. Compiler correctness lifts that guarantee to source-level IMP2 executions.

The main executable witness is
`Example_Interval_DG_Flagship.thy`. It proves the computed result non-vacuous,
shows proper bounds at reachable program points, and ends with an
analysis-annotated GraphViz rendering.

## Generic D/G Framework

The flagship is one executable instance of a reusable framework, not a
special-purpose verified analyzer.

The core abstraction is `sound_dg_spec`, the Isabelle image of Goblint's
[`Spec`](https://github.com/goblint/analyzer/blob/1ab59c9c4d9859e9135885d3c9a9aa1a8f3b677e/src/framework/analyses.ml#L168-L263)-style split between per-program-point answers `D` and side-published
facts `G` . An analysis supplies step and combine behavior over opaque carriers;
the framework generates the equation system, runs the solver, and provides the
soundness theorem that connects the computed result back to collecting
semantics.

`Exec_DG_Bridge.thy` gives the executable frontend for this interface:

- executable finite-map carriers for abstract states,
- the refinement morphism `fun_of_dg_st`,
- executable equation generation `dg_gen_of`,
- transport from solver-computed results to abstract post-solutions via
  `part_post_solution_dg_st_to_abs`.

This is what lets Sign, Interval, and mixed analyses reuse the same certified
execution pipeline.

### Adding a domain

To instantiate the framework, supply an abstract value type, a concretization
`gamma`, and sound transfer functions. Sign
(`src/Analysis/Instances/Sign/Sign_Domain.thy`) is the reference instance.

| Step | What | Reference (sign) |
| --- | --- | --- |
| 1 | value type + lattice instance (`bot`, `sup`, `ord`) | `datatype sign`, `instantiation` |
| 2 | define `gamma`, prove `gamma_bot` / `gamma_mono` | `gamma_sign_mono` |
| 3 | `interpretation` of the `abstract_domain` locale | `sign_domain` |
| 4 | define transfer functions, prove they preserve `gamma` | `assign_sign_sound`, `assume_sign_sound` |
| 5 | apply the interprocedural soundness theorem | `side_sign_analysis_sound` |

## Architecture

- `Voblint_IMP2`: IMP2 source semantics, procedures, globals, and the
  source-to-CFG bridge.
- `Voblint_CFG`: CFG construction, paths, and interprocedural collecting
  semantics.
- `Voblint_Analysis`: domains, equation systems, solver wiring, and executable
  D/G infrastructure.
- `Voblint_Formalization`: end-to-end theorems, executable examples, and
  demonstrations.

Four Isabelle sessions build in order:
`Voblint_IMP2` → `Voblint_CFG` → `Voblint_Analysis` → `Voblint_Formalization`.

## Theoretical Foundations

The concrete semantic target is the interprocedural collecting semantics
`cfg_collect`. The strongest reusable source-to-analysis theorem is
`source_reaches_side_analyse_eff`
(`src/Formalization/Pipeline/Compiler_Correctness.thy`): for a real
IMP2 run, the compiled CFG, and a sound solver instance, the abstract result
contains the matched concrete state at some CFG point.

The native D/G soundness endpoints include
`sign_dg_post_solution_collect_sound`,
`ivl_dg_post_solution_collect_sound`, and
`mixed_si_post_solution_collect_sound`. The executable bridge turns computed
solver output into the hypotheses these theorems require, and the flagship
theory instantiates that path for a solver-computed interval result.

For a more theorem-centric overview, see `docs/PROOF_OVERVIEW.md`,
`docs/PROOF_PHASES.md`, and the session entry theory
`src/Formalization/Voblint.thy`.

## Build

### Requirements

- [Isabelle](https://isabelle.in.tum.de/) 2025 or newer, with `isabelle` in `$PATH`.
- A local [AFP](https://www.isa-afp.org/) checkout (`thys/`): transitive deps
  `Root_Balanced_Tree`, `Dijkstra_Shortest_Path`.
- GNU `make`, `git`, POSIX tools.

Set `AFP` to your AFP `thys/` directory (default `~/afp/thys`):

```
make AFP=/path/to/afp/thys build
```

| Target | Role |
| --- | --- |
| `make vendor` | init `vendor/td-verification` submodule + apply Isabelle2025 patch |
| `make build` (default) | build session `Voblint_Formalization` (depends on `vendor`) |
| `make jedit` | launch Isabelle/jEdit with session roots pre-loaded |
| `make html` | browser info → `docs/html/` (CI deploys to GitHub Pages on `main`) |
| `make clean` / `clean-vendor` | remove built heaps / vendored sources |

The checked source tree is sorry-free; `ROOT` files do not enable
`quick_and_dirty`.

## Repository Layout

```
src/
  IMP2/          syntax, procedures, globals/locals, small-step
  CFG/           CFG, IP compilation, paths; Collecting/ - IP collecting semantics
  Analysis/      Generic/ (Domain/ Equations/ Solver/) Instances/ (Voblint_Analysis session)
  Formalization/ Pipeline/ Examples/ (Voblint_Formalization session)
vendor/
  td-verification/         verified TD solver (submodule, AFP session TD)
  td-verification.patch    local Isabelle2025 compatibility patch
  autocorrode/             I/Q + I/R MCP servers (via ./scripts/setup.sh)
docs/          proof overview, phases, roadmap, walkthroughs, generated HTML
```

The analysis rides on the **side-effecting** solver (`TD.TD_side`). An
intra-procedural (classical) formulation is developed separately in the sibling
repo `voblint-formalization-classical`.

## Further Documentation

For deeper theory-level detail, start with:

- `docs/PROOF_OVERVIEW.md` for the big-picture proof story.
- `docs/PROOF_PHASES.md` for phase status and remaining proof work.
- `docs/ROADMAP.md` for active backlog and project direction.
- `src/Formalization/Voblint.thy` for the session-level theory map.

### Verified dependencies

| Dependency | Source | Role |
| --- | --- | --- |
| `HOL-IMP` | Isabelle distribution | session parent; IMP base |
| `TD` (`TD_side`, `Basics`, …) | vendored `stilscher/td-verification` + patch | verified top-down solver |
| `Dijkstra_Shortest_Path` | AFP | CFG graph type |
| `Root_Balanced_Tree` | AFP | transitive dep of TD |

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
