# Voblint formalization (`src/`)

A machine-checked abstract interpreter for VIMP, sound from the source operational
semantics to the *computed* analysis result:

```text
VIMP source -> CFG -> activation-local trace -> collecting semantics
            -> D/G equation system -> verified TD side solver
            -> abstract post-solution -> source-level soundness
```

Each arrow is a theorem. The vendored solver is `vendor/td-verification` (session `TD`).
`src/Examples/Voblint.thy` is the capstone: it imports every example session and the
CLI, and indexes the whole development.

## Sessions

One directory is one session — Isabelle rejects two sessions sharing a directory, so
the folder tree and the session graph are the same thing. `ROOTS` lists them all.

| Folder | Session | Role |
| --- | --- | --- |
| [`Program_Model/VIMP/`](Program_Model/VIMP/) | `Voblint_VIMP` | source syntax, small-step semantics, procedures, the globals/locals split |
| [`Abstract_Interpreter/Domain/`](Abstract_Interpreter/Domain/) | `Voblint_Domain` | what an abstract value and an abstract state are: sound-domain classes, concretization, the dead-code lift, pointwise states |
| [`Abstract_Interpreter/Solver/`](Abstract_Interpreter/Solver/) | `Voblint_Solver` | the strategy-tree equation language of the vendored solver, its monotonicity and post-solution vocabulary. Never sees a CFG. |
| [`Program_Model/CFG/`](Program_Model/CFG/) | `Voblint_CFG` | the graph model and its activation-local collecting semantics — what a soundness claim is stated *about*. Never mentions the compiler. |
| [`Program_Model/Compile/`](Program_Model/Compile/) | `Voblint_Compile` | the VIMP-to-CFG compiler, its structural invariants, forward simulation, and the bridge from a source run to a valid local trace |
| [`Abstract_Interpreter/Framework/`](Abstract_Interpreter/Framework/) | `Voblint_Framework` | the D/G analysis framework: transfer contract, equation generator, collecting soundness for an arbitrary CFG. No domain, no compiler. |
| [`Abstract_Interpreter/Exec/`](Abstract_Interpreter/Exec/) | `Voblint_Exec` | the executable carrier, and transport from the solver's association lists to the function-valued states soundness is stated over |
| [`Analyses/`](Analyses/) | `Voblint_Analysis_*` | one session per domain over a shared base — see below |
| [`Executable_Surface/CLI/`](Executable_Surface/CLI/) | `Voblint_CLI` | the `AnalysisConfig` dispatcher over the domains' entry points, and the GraphViz render surface. Where the domains meet again. |
| [`Examples/`](Examples/) | `Voblint_Examples_*` | one example session per domain, plus the CLI-coupled witnesses and the capstone |
| [`Executable_Surface/Codegen/`](Executable_Surface/Codegen/) | `Voblint_Codegen` | the `export_code` boundary into OCaml |

Dependency shape:

```text
VIMP -+-> CFG ----+-> Compile ---------+
      |           |                    v
      |           +-> Framework ---> Exec -> Routing -> Result -> Nonrelational -> Analyses/* -+
      +-> Domain -------^                                                                      |
TD   ---> Solver -------^                                                                      v
                                                                                  CLI -> Codegen
                                                                                   +--> Examples/*
```

(`CFG` depends on `VIMP` only; `Framework` on `CFG`, `Domain` and `Solver`;
`Compile` on `CFG`; `Exec` on `Framework` and `Compile`.)

The source-level endpoints sit *below* the analysis family, not after it:
`Voblint_Result` holds the domain-free source bridge (`Source_Activation_Sound`)
and the context-insensitive assembly `unit_dg_analysis` whose `source_sound` and
`completed_run_sound` every domain instantiates, so each domain inherits them
from an ancestor heap rather than re-deriving them.

## The analysis and example families

[`Analyses/Shared/`](Analyses/Shared/) holds what every domain reuses, as three
sessions chained `Routing -> Result -> Nonrelational` on top of `Voblint_Exec`: the
routing policies, the publication surface with the source-level endpoints, and the
reuse locales a *non-relational* domain interprets.
`Voblint_Nonrelational` is the parent of [`Sign/`](Analyses/Sign/),
[`Interval/`](Analyses/Interval/), [`Parity/`](Analyses/Parity/),
[`Congruence/`](Analyses/Congruence/) and [`Int/`](Analyses/Int/), the reduced
product of the first four. [`Relational/`](Analyses/Relational/) is the exception:
it is parented on `Voblint_Exec`, below the chain, so the pointwise reuse locales
are out of its reach by construction rather than by convention.

Each domain follows the same layer chain, so a reader who knows one knows them all:

```text
<Domain>_Domain      the lattice and its concretization (Sign's is Sign_Lattice)
<Domain>_Transfer    the transfer functions
<Domain>_Exec        the executable mirror, on the finite-map carrier
<Domain>_Sound       the D/G spec and its soundness; no context, no solver
<Domain>_Assembly    the context-insensitive route, one registration per solver discipline
<Domain>_Analyses    the entry-state and call-string policies over the same spec
<Domain>_Checks      the runtime API over an arbitrary program: solve, result table, report
<Domain>_Entry       that API's soundness theorems
```

The last four are generated from `assembly/analyses.yaml` (each domain's `generated/`
folder); Interval and Int write some of them by hand and add `_Solver_Analyses`
for their widening routes and alternative solver disciplines, and Int adds
`Int_Exec_Sound` to choose its transfer by refinement mode.

Everything under a `generated/` folder is emitted by
`scripts/gen_analysis_assembly.py`: change the yaml or the generator, never the
file. A theory outside `generated/` is hand-written, which is why the folders are
not symmetric across domains.

`Congruence` is both a selectable analysis and the fourth component of `Int`.
`Relational` is a single theory, kept to prove the generic pipeline never assumed
pointwise abstract states.

[`Examples/`](Examples/) mirrors that split one-for-one, so a domain's witnesses cannot
depend on a sibling domain. Its `CLI/` folder is the residue that genuinely reaches the
dispatcher or an entry point.

## Where to start

Read a session's own `README.md` first — each carries its vocabulary, one worked example
carried end to end, and the shape of its dependencies. `src/Examples/Voblint.thy` indexes
every layer above with checked theory references.

Proof status and plans: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
