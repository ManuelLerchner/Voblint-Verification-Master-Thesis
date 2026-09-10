# Examples / Int

The Sign x Interval x Parity x Congruence product domain, run against the same
generic D/G pipeline, solver and CFG shape as the single-domain instances. What
these witness is the reduced product itself: which refinement mode recovers
what, and where componentwise widening and narrowing stop being enough.

| File | Role | What |
| --- | --- | --- |
| `Example_Int_Domain.thy` | executable domain regression | Exact four-component bottom checks, structural fixpoint refinement, mode-aware arithmetic, and executable Once/Fixpoint distinctions |
| `Example_Int_Backward.thy` | executable domain regression | Composite backward guard filtering: `x + 1 = 3 ==> x = 2` under `Once`/`Fixpoint`, distributed-information exact refinement, Congruence-only interval/sign/parity precision, and `Never` contrasts showing what refinement actually buys |
| `Example_Int_Warrowing.thy` | executable domain regression | Composite widening/narrowing are exactly componentwise (Interval's own accelerating widen/narrow surface through, no reduced-product step runs afterward); generic `warrowing` law corollaries at `int_dom`; a concrete counterexample showing why post-narrow refinement would violate the solver's `narrow_ge` bracket |
| `Example_Int_Transfer.thy` | executable domain regression | Composite operations reached through `int_tf_abs`, `enter_int_dom_ci_for`, and `branch_int_dom_for`, rather than the underlying primitives: assignment, procedure entry, the `x + 1 = 3 ==> x = 2` guard under `Once`/`Never`, and `Min`'s special-call dispatch, where mode-aware refinement supplies the congruence component |
| `Exec_Int_DG_Run.thy` | canonical spine + witness | A compiled `if (y + 1 == 3) { x := 1 } else { x := 0 }` run through the vendored TD solver on the composite domain. One projected `solve_c` result for each non-CLI mode shows that `Never` narrows only Congruence while `Once` reaches the exact singleton; the CLI regression covers its fixed `Fixpoint` mode |

Role vocabulary: repository `README.md`.
