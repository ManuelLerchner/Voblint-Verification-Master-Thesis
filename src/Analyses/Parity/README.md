# Analyses / Parity

`Voblint_Analysis_Parity` is the even/odd domain. It exists to prove a claim about
the framework rather than about parity: registering a third domain required no new
spine, no copied step or combine proof, and no change to the generator or solver.

It also says things the other domains cannot. `y := x * 2` is even whatever `x` is
— a fact neither Sign nor Interval can express, since neither tracks divisibility.

## Vocabulary

| Term | Meaning |
| --- | --- |
| `parity` | the flat lattice `PEven`/`POdd` with top and bottom. Finite height, so the always-join solver suffices and no widening is needed. |
| `pctx_spec` | Parity's D/G specification at the routed spine (`Parity_Sound`), built from the generic ownership-split construction and Parity's own transfer functions |
| `pctx_eqs` / `pctx_sol` | the equation system a compiled program generates under that spec, and the solver's solution for it (`Parity_Exec_Sound`) |
| classify | turning a solved abstract value into `Check_Proved`/`Check_Refuted`/`Check_Unknown` for one check condition (`Parity_Classify`) |

## The layer chain

```text
Parity_Domain      the lattice, order, and its concretization
  -> Parity_Special / Parity_Transfer   special calls; the transfer functions
  -> Parity_Exec                        executable transfer, on the finite-map carrier
  -> Parity_Sound                       pctx_spec and its soundness; no context yet
  -> Parity_Exec_Sound                  the arbitrary-program runtime API: equations,
                                        solve, termination, result table
  -> Parity_Analyses                    the three context policies over that route
  -> Parity_Classify / Parity_Checks    check discharge and the published report
```

`Parity_Exec_Sound` is the same layer `Sign_Exec_Sound`, `Interval_Exec_Sound` and
`Int_Exec_Sound` occupy in their own domains: it only *computes*. The soundness half
that turns a computed solution into a statement about source runs is downstream, in
`Voblint_CLI.Parity_Entry`.

## Worked example

`Example_Parity_DG_Flagship` (Examples/Parity) compiles an even-step loop, generates
its equations through `pctx_eqs_prog`, solves them with the always-join solver, and
closes with `parity_source_run_sound` — the same statement shape Sign's and Interval's
flagships prove. Nothing in that chain is Parity-specific except the lattice.

`Example_Parity_Checks_Store_Only` (Examples/CLI, because it goes through
`Parity_Entry`) is the check-discharge witness: `y := x * 2` and `z := y + 1` land in
disjoint parity classes whatever the unconstrained `x` is, so one check is proved and
one refuted. A third, against another unconstrained value, is unknown — Parity has no
singleton, so it can never prove a positive equality.
