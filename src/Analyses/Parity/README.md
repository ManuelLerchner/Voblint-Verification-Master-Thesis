# Analyses / Parity

`Voblint_Analysis_Parity` is the even/odd domain. It reuses the shared
non-relational evaluator and routed analysis spine while retaining its own
lattice, arithmetic, queries, and classification.

It also says things the other domains cannot. `y := x * 2` is even whatever `x` is
— a fact neither Sign nor Interval can express, since neither tracks divisibility.

## Vocabulary

| Term | Meaning |
| --- | --- |
| `parity` | the flat lattice `PEven`/`POdd` with top and bottom. Finite height, so the always-join solver suffices and no widening is needed. |
| `pctx_spec` | Parity's D/G specification at the routed spine (`Parity_Sound`), built from the generic ownership-split construction and Parity's own transfer functions |
| `pctx_eqs_prog` / `pctx_sol_prog` | the equation system a compiled program generates under that spec, and the solver's solution for it. Both are abbreviations for the assembly's own names (`Parity_Checks`) |
| classify | turning a solved abstract value into `Check_Proved`/`Check_Refuted`/`Check_Unknown` for one check condition (`Parity_Classify`) |

## The layer chain

```text
Parity_Domain      the lattice, order, and its concretization
  -> Parity_Special / Parity_Transfer   special calls; the transfer functions
  -> Parity_Exec                        executable transfer, on the finite-map carrier
  -> Parity_Sound                       pctx_spec and its soundness; no context yet
  -> Parity_Numeric_Queries             numeric queries used by check discharge
  -> Parity_Classify                    classification of one check condition
  -> Parity_Assembly                    the context-insensitive route, as one
                                        interpretation of the shared unit_dg_analysis
  -> Parity_Analyses                    the call-string and entry-state policies
  -> Parity_Checks                      the published result table and report
  -> Parity_Entry                       the production endpoint and its soundness
```

`Parity_Assembly` is a single `global_interpretation` of `unit_dg_analysis`
(`Shared/Result/Unit_DG_Analysis.thy`). Parity supplies ten facts — its transfer
contract, two commutation laws, the solver contract, the classifier contract and
the initial-state contract — and gets back the equation system, the solve, the
reader, the result table, the report and every soundness endpoint. Nothing in
this session builds a second copy of that pipeline. `Parity_Analyses` keeps only
the two configurations that route calls to more than one context, which the
assembly's fixed unit route cannot express.

Parity currently has no backward-domain interpretation. Branch transfer is the
conservative identity, so guards do not refine parity facts.

## Worked example

`Example_Parity_DG_Flagship` (Examples/Parity) compiles an even-step loop, generates
its equations through `pctx_eqs_prog`, solves them with the always-join solver, and
closes with `parity_source_run_sound` — the same statement shape Sign's and Interval's
flagships prove. Nothing in that chain is Parity-specific except the lattice.

`Example_Parity_Checks_Store_Only` (Examples/CLI, grouped with the other domains'
members of the same store-only trio) is the check-discharge witness: `y := x * 2` and `z := y + 1` land in
disjoint parity classes whatever the unconstrained `x` is, so one check is proved and
one refuted. A third, against another unconstrained value, is unknown — Parity has no
singleton, so it can never prove a positive equality.
