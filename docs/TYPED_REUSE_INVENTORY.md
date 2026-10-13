# Typed analyzer: reuse inventory against `main`

Compared on 2026-10-13: branch `feat/typed-ir` against the existing (untyped) analyzer. Each
row names the existing definition, the typed one, whether the algorithms agree, and what
to do. Target: one implementation of each generic algorithm, with thin machine-integer
specializations.

## Duplicates to remove

| Area | Existing | Typed | Same algorithm? | Plan | Proof cost | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| Combining analyses (resolved: the typed analyses interpret `mcp_registry`; the binary product is deleted) | `mcp_combine`, `mcp_step`, `mcp_en_from`, `mcp_qry`, `mcp_comb`, `mcp_combine_sound` (`Framework/Cooperation/MCP_Spec.thy`); fields via `lens_of`, `lift_get`/`lift_put`, `mcp_independent_map`; activation in `mcp_comp`, `mcp_comp_sound` (`Executable_Surface/CLI/MCP_Analyses.thy`) over the generated carrier `MCP_Carrier.thy` | `spec_product`, `pmap`, `pmap2`, `penter`, `spec_product_sound` (`Typed_Nonrel/Spec_Product.thy`); `nonrel_order` (`Typed_Order/Nonrel_Order_Product.thy`); the special-cased dispatch in `run_typed` | Yes, up to representation: componentwise steps, entry alternatives concatenated per component (the cartesian product), answers met, one shared channel. `mcp_combine` is n-ary and already registered at every context policy | Instantiate the carrier/registration layer at `var_id`/`texp` with typed fields (`lens_of` over a lifted record, `with_qry` for answers) and run `mcp_comp` on it. Retire `Spec_Product`, `Nonrel_Order_Product` and the `run_with_order` dispatch once the typed MCP reproduces `Cooperation_Regression` | Medium: field framing and liveness per typed field; `mcp_combine_sound` itself is reused | Low once the regression is reproduced; it pins the cooperative verdicts |
| Boolean backward refinement | `bfilter_st_lift_with` / `afilter_st_lift_with` with `feasible_with` (`Shared/Nonrelational/Exec_Backward.thy`): `And`/`True` and `Or`/`False` sequential, `And`/`False` and `Or`/`True` per-alternative feasibility gate and join | `trefine` / `refine_var` (`Typed_Nonrel/Typed_Transfer.thy`): sequential cases only | No: the typed one lacks `And`/`False` and `Or`/`True`. Goblint's `baseInvariant.ml` refines `Or`/`True` by alternatives (lines 724–731) and does not refine `And`/`False` (line 452) or `Or`/`False` (line 732) | Factor the Boolean decomposition out of `bfilter_st_lift_with` over an expression view (negation, conjunction, disjunction, atom) and a feasibility test; instantiate it with the untyped atoms (`refine_ops`) and the typed atoms (`refine_ik`, casts, non-overflowing `+`/`-`). Add no cases to `trefine` before then | High: `Exec_Backward` commutation proofs (~700 lines) move to the generic decomposition | Medium: untyped branch precision must stay identical; existing regressions cover it |

## Overlap kept on purpose

| Area | Existing | Typed | Why both stay (for now) |
| --- | --- | --- | --- |
| Query consumption in transfers | `ask_assign` (`Cooperation/Channel_Wrappers.thy`): an assignment whose right-hand side gets a constant answer runs on the literal | `taeval_ask` (`Typed_Nonrel/Typed_Nonrel.thy`): every non-constant operand is asked and its value replaced, as `eval_rv_ask_evalint` (`base.ml` 803) | Different algorithms; the typed one is Goblint's and subsumes `ask_assign` on the typed path. `ask_assign` retires with the untyped instance |
| Transfer contract | `sound_nonrelational_ops`, `tf_abs`, `dg_analysis_execI` (`Shared/Nonrelational/Nonrelational_Transfer.thy`) | `typed_spec`, `typed_spec_sound` (`Typed_Transfer.thy`) | Assignment converts to the destination kind, evaluation consults the channel, the return slot has no kind, and actuals must fit formals. The soundness laws are the generic `gsound_*` of `MCP_Spec`, already shared. Revisit after the MCP migration: a typed field may reuse `exec_local_spec` directly |
| Executable state | `Default_St_*`, `transfer_lift`, `combine_default_st`, readback | `tassign_st` … `tcombine_assign_st`, `write_back`, `typed_exec_spec` (`Typed_Exec.thy`) | Already built on the shared dictionary, `transfer_lift` and `combine_default_st`. `write_back` depends on the variables a typed guard reads; that obligation is language-specific |
| Pipeline instances | `dg_analysis` interpretations per policy (e.g. `interval_es_rule`, `interval_cs_rule`) | `typed_nonrel`, `typed_nonrel_es`, `typed_order` (`gdg_analysis` interpretations) | Thin instances of the one D/G pipeline and solver, as intended |

## Domains

| Existing | Typed | Shared | Typed-specific |
| --- | --- | --- | --- |
| Interval (`Interval_Lattice`, `Interval_Arithmetic`) | `Interval_Kind` | arithmetic (`ivl_plus` … `ivl_mod` via `ivl_aop`), comparisons (`interval_less`/`interval_eq` via `cop_of`), `ivl_refine` | kind range `ik_ivl`, normalization `norm_ivl_ik` (wrap), bounded `widen_ivl_ik`/`narrow_ivl_ik` |
| Congruence | `Congruence_Kind` | lattice, `congruence_of_int`, `cong_least_above` | `norm_cong_ik` (modulus under `2^w`), `cong_aop`/`cong_refine` dispatch, comparisons via `cop_of` with the stronger `cong_eq`, `sub_kind` casts |
| Sign, Parity | `Sign_Kind`, `Parity_Kind` | lattices and concretizations | `sign_aop`, `parity_aop` restated per `aop`; comparisons share `cop_of` (`Typed_Nonrel.thy`) with the untyped queries |
| Int (`int_dom`, `Int_Refinement`) | `Int_Tuple_Kind` | `refine_ivl_with_congruence` | `cong_refine_with_ivl` and `it_refine` (Goblint `IntDomTuple.refine` once); compare with `refine_interval`/`refine_congruence` before keeping a second reduction |

## Order of work

1. Typed fields in the registration/carrier layer, `mcp_comp` over them, and the
   cooperation regression reproduced; then retire `Spec_Product` and the special dispatch.
   This is also the step that puts `run_voblint` on the typed pipeline.
2. Generic Boolean decomposition for backward refinement, instantiated twice; the typed
   path gains `Or`/`True` and `And`/`False`.
3. Sign/Parity/Int domain rows above: remove restated operations that match the untyped
   ones exactly.
