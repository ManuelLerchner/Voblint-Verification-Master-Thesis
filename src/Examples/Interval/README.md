# Examples / Interval

Interval-domain witnesses: codegen probes, flagship D/G runs, procedure-call
soundness spines, and backward (guard-refinement) trace soundness.
Context-sensitive (call-string) D/G examples live in `Ctx/` and `CallString/`,
split by concern.

| File | Role | What |
| --- | --- | --- |
| `Exec_Ivl_Run.thy` | precision comparison | bounded loop under every update rule (`join` / `per_origin` / `warrow`) at once; interval narrowing + backward guard filter recover `[0,20]`. `eval`-only — the proved trace-soundness counterpart is `Example_Interval_Loop_Coverage` below |
| `Example_Interval_DG_Flagship.thy` | canonical spine | interval analysis of a counting loop, executed and certified on the D/G spine |
| `Example_Interval_DG_IP_Flagship.thy` | canonical spine | interprocedural: `twice` compiled and analyzed end to end through `FunctionEntry`/`FunctionResult` |
| `Example_Interval_Side_Proc_Global.thy` | canonical spine | interval IP on a global increment call (`Example_Inc_Proc`, see `../CFG/`); `proc_global_side_ivl_analysis` |
| `Example_Proc_Call.thy` | canonical spine | two procedures (`inc` / `sqr`) via a global; `main_prog_interval_analysis` + CFG combine structure |
| `Example_Interval_Loop_Coverage.thy` | canonical spine | bounded loop; backward `assume_ivl` refines the body to `[0,19]`; certified trace soundness `[0,20]` at the loop head (`loop_head_x_bounded`) |
| `Example_Guard_Refinement.thy` | regression | backward guard refinement strictly tighter than identity assume (`backward_analysis_strictly_tighter`) — a precision negative result |

Backward-analysis arc: `Example_Guard_Refinement` (one guard) -> `Example_Interval_Loop_Coverage`
(full CFG + trace soundness). Role vocabulary: repository `README.md`.

## `Ctx/` — context routed by entered value

`twice` analyzed context-sensitively, each call site's context the entry value
of formal `p`. Import chain: `Ctx_Flagship` -> `Ctx_Sound` ->
`Ctx_Multi_Call_Regression`, and `Ctx_Flagship` -> `Ctx_Collect` ->
`Source_Ctx`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Ctx_Flagship.thy` | canonical spine | context-sensitive interval analysis of `twice`; each call site's context is the entry value of formal `p` |
| `Example_Interval_DG_Ctx_Sound.thy` | canonical spine | route consistency: the executable routed equations transport to an abstract context-indexed post-solution |
| `Example_Interval_DG_Ctx_Collect.thy` | canonical spine | activation-indexed collecting soundness for the routed interval solution |
| `Example_Interval_DG_Ctx_Multi_Call_Regression.thy` | regression | a call site with more than one outgoing call edge |
| `Example_Interval_Source_Ctx.thy` | canonical spine | the `twice` program called twice under distinct contexts — interprocedural, repeated-call, context-sensitive; not recursive |

## `CallString/` — context routed by call site

Context routed by call site instead of entered value; `K1`/`K2` parameterize
the call-string bound `k`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_CallString.thy` | canonical spine | a computed 1-call-string context, routed by call site (Seidl et al. 2026, Example 7) |
| `Example_Interval_DG_CallString_K1.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 1` |
| `Example_Interval_DG_CallString_K2.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 2` |
| `Call_String_Solver_Projection.thy` | reusable | fully generic k1<=k2 CallString projection: a finite fine-to-coarse quotient (`proj_P`) plus the packaged `seed_rhs`-based closure theorem (`call_string_projection_refinement`); no concrete program, no `k1`/`k2` value, and no per-hook reasoning appears in its statements or proofs |
| `Call_String_Solver_Refinement_Seeded.thy` | canonical spine | the k=2 to k=1 refinement witness for `nest`, now a thin instantiation of `Call_String_Solver_Projection.thy` at k1=1: a two-line context-merge fact plus solver soundness gives the whole closure, replacing the former hand-unrolled dependency-cone chain |
| `Call_String_Solver_Regression.thy` | regression | exact-tree snapshots (`nest_1_eqs_statement3`, `nest_2_eqs_statement3`) locking in that `routed_cmb`/`side_cfg_T_eff_keyed_seed_dg` still generate the expected equation shape at a genuine call continuation |
