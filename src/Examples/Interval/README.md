# Examples / Interval

Interval-domain witnesses: codegen probes, flagship D/G runs, procedure-call
soundness spines, and backward (guard-refinement) trace soundness.
Context-sensitive (call-string) D/G examples live in `Ctx/` and `CallString/`,
split by concern.

| File | Role | What |
| --- | --- | --- |
| `Exec_Ivl_Run.thy` | precision comparison | `Example_Interval_Loop_Coverage`'s `loop_prog` under three fixpoint engines — bounded Kleene, warrowing TD, and every update rule at once (`join` / `per_origin` / `warrow`); interval narrowing plus the backward guard filter recover `[0,20]` under all of them. Imports the coverage theory rather than restating the program |
| `Example_Interval_DG_Flagship.thy` | canonical spine | interval analysis of a counting loop, executed and certified on the D/G spine |
| `Example_Interval_DG_IP_Flagship.thy` | canonical spine | interprocedural: `twice` compiled and analyzed end to end through `FunctionEntry`/`FunctionResult` |
| `Example_Proc_Call.thy` | canonical spine | two procedures (`inc` / `sqr`) via a global; `main_prog_interval_analysis` + CFG combine structure |
| `Example_Interval_Loop_Coverage.thy` | canonical spine | bounded loop; backward `assume_ivl` refines the body to `[0,19]`; certified trace soundness `[0,20]` at the loop head (`loop_head_x_bounded`) |
| `Example_Guard_Refinement.thy` | regression | backward guard refinement strictly tighter than identity assume (`backward_analysis_strictly_tighter`) — a precision negative result |

Backward-analysis arc: `Example_Guard_Refinement` (one guard) -> `Example_Interval_Loop_Coverage`
(full CFG + trace soundness) -> `Exec_Ivl_Run` (the same witness, executed).

Not tabled above, and grouped by what they pin rather than by domain concern:
`Example_Interval_Checks_Store_Only.thy` (check discharge, the Interval
analogue of Sign's), `Example_Interval_Placement.thy` (the placement/storage
independence skeleton), `Example_Interval_Global_Flow_Sensitivity.thy` (how a declared global is
stored and how flow-sensitively). Role vocabulary: repository `README.md`.

## `Ctx/` — context routed by entered value

`twice` analyzed context-sensitively, each call site's context the entry value
of formal `p`, by the production entry-state analysis
(`Voblint_Analysis.Interval_Ctx_Entry_State_Sound`). Import chain:
`Ctx_Flagship` -> `Ctx_Collect` -> `Source_Ctx`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Ctx_Flagship.thy` | canonical spine | the production entry-state analysis run on `twice`; each call site's context is the entry value of formal `p`, plus the context-expanded GraphViz export |
| `Example_Interval_DG_Ctx_Collect.thy` | canonical spine | activation-indexed collecting soundness: `twice` as a named instance of `entry_state_activation_collect_sound` |
| `Example_Interval_DG_Ctx_Multi_Call_Regression.thy` | regression | a call site with more than one outgoing call edge |
| `Example_Interval_Source_Ctx.thy` | canonical spine | the `twice` program called twice under distinct contexts — interprocedural, repeated-call, context-sensitive; not recursive |

### `Ctx/` — the entry-state family

`rc_program` is the entry-state coverage witness: one call whose argument is
unconstrained, so the routed context is `Top` itself — one context covering
every draw, rather than a family of contexts diverging over them. Import
chain: `EntryState_Base` -> `EntryState_Ctx` -> `EntryState_Collect`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_EntryState_Base.thy` | canonical spine | the compiled base: a call with a `__voblint_nondet_int()` argument |
| `Example_Interval_DG_EntryState_Ctx.thy` | canonical spine | the production entry-state analysis run on it |
| `Example_Interval_DG_EntryState_Collect.thy` | canonical spine | activation-indexed collecting soundness as a named instance of `entry_state_activation_collect_sound` |
| `Example_Interval_DG_EntryState_Result_Regression.thy` | regression | `analyse_interval_entry_state_result`, the context-sensitive reading of the solution as an `analysis_result` |
| `Example_Interval_DG_EntryState_Dead_Check_Regression.thy` | regression | the three shapes a check node takes once contexts are kept apart: live, dead, and disagreeing across contexts |
| `Example_Interval_DG_Ctx_Factorial_Regression.thy` | regression | recursive `factorial` at `n=3` and `n=4`, four distinct entry-state contexts |
| `Example_Interval_DG_Ctx_Globals_Regression.thy` | regression | a declared global crossing a call boundary in the same slot a local does |

## `CallString/` — context routed by call site

Context routed by call site instead of entered value; `K1`/`K2` parameterize
the call-string bound `k`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_CallString_K1.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 1` (Seidl et al. 2026, Example 7) |
| `Example_Interval_DG_CallString_K2.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 2` |
| `Call_String_Solver_Refinement_Seeded.thy` | canonical spine | the k=2 to k=1 refinement witness for `nest`: a thin instantiation of `Voblint_Core.Call_String_Solver_Projection` at k1=1, where a two-line context-merge fact plus solver soundness gives the whole closure |
| `Example_Interval_Call_String_Generic_Parity.thy` | regression | the runtime-`k` generic pipeline (`cs_call_string_sol_prog`) solves the same equation system the hand-built `nest_1_eqs`/`nest_2_eqs` do — same `ectx_spec`, same `cs_route`, same seeds |
| `Call_String_Solver_Regression.thy` | regression | exact-tree snapshots (`nest_1_eqs_statement3`, `nest_2_eqs_statement3`) locking in that `routed_cmb_g_def`/`routed_extra_g_def`/`side_cfg_T_eff_keyed_seed_dg` still generate the expected equation shape at a genuine call continuation |
