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
| [`VIMP/`](VIMP/) | `Voblint_VIMP` | source syntax, small-step semantics, procedures, the globals/locals split |
| [`Domain/`](Domain/) | `Voblint_Domain` | what an abstract value and an abstract state are: sound-domain classes, concretization, the dead-code lift, pointwise states |
| [`Solver/`](Solver/) | `Voblint_Solver` | the strategy-tree equation language of the vendored solver, its monotonicity and post-solution vocabulary. Never sees a CFG. |
| [`CFG/`](CFG/) | `Voblint_CFG` | the graph model and its activation-local collecting semantics — what a soundness claim is stated *about*. Never mentions the compiler. |
| [`Compile/`](Compile/) | `Voblint_Compile` | the VIMP-to-CFG compiler, its structural invariants, forward simulation, and the bridge from a source run to a valid local trace |
| [`Framework/`](Framework/) | `Voblint_Framework` | the D/G analysis framework: transfer contract, equation generator, collecting soundness for an arbitrary CFG. No domain, no compiler. |
| [`Exec/`](Exec/) | `Voblint_Exec` | the executable carrier, and transport from the solver's association lists to the function-valued states soundness is stated over |
| [`Analyses/`](Analyses/) | `Voblint_Analysis_*` | one session per domain over a shared base — see below |
| [`Soundness/`](Soundness/) | `Voblint_Soundness` | the two end-to-end endpoints: `source_activation_sound` and the `run_source_sound`/`collect_sound` bundle |
| [`CLI/`](CLI/) | `Voblint_CLI` | per-domain entry points, the `AnalysisConfig` dispatcher, the GraphViz render surface. Where the domains meet again. |
| [`Examples/`](Examples/) | `Voblint_Examples_*` | one example session per domain, plus the CLI-coupled witnesses and the capstone |
| [`Codegen/`](Codegen/) | `Voblint_Codegen` | the `export_code` boundary into OCaml |

Dependency shape:

```text
VIMP -> Domain -+
                +-> CFG -> Framework -> Compile -> Exec -> Analyses/* -+-> Soundness -+
TD   -> Solver -+                                                      |              v
                                                                       +---------> CLI -> Codegen
                                                                                     +--> Examples/*
```

## The analysis and example families

[`Analyses/Base/`](Analyses/Base/) holds what every domain reuses — the reuse locales,
the routing policies, the dispatch config, the reporting layer — and is the parent of
every domain session: [`Sign/`](Analyses/Sign/), [`Interval/`](Analyses/Interval/),
[`Parity/`](Analyses/Parity/), [`Congruence/`](Analyses/Congruence/),
[`Relational/`](Analyses/Relational/) and [`Int/`](Analyses/Int/), the reduced product
of the first four.

Each domain follows the same layer chain, so a reader who knows one knows them all:

```text
<Domain>_Domain      the lattice and its concretization
<Domain>_Transfer    the transfer functions
<Domain>_Exec        the executable mirror, on the finite-map carrier
<Domain>_Sound       the D/G spec and its soundness; no context, no solver
<Domain>_Exec_Sound  the arbitrary-program runtime API: equations, solve, result table
<Domain>_Analyses    the context policies over that route
<Domain>_Checks      check discharge and the published report
```

`Congruence` stops after the lattice, arithmetic and backward filter: it is a product
component, not a selectable analysis. `Relational` is a single theory, kept to prove the
generic pipeline never assumed pointwise abstract states.

[`Examples/`](Examples/) mirrors that split one-for-one, so a domain's witnesses cannot
depend on a sibling domain. Its `CLI/` folder is the residue that genuinely reaches the
dispatcher or an entry point.

## Where to start

Read a session's own `README.md` first — each carries its vocabulary, one worked example
carried end to end, and the shape of its dependencies. `src/Examples/Voblint.thy` indexes
every layer above with checked theory references.

Proof status and plans: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
