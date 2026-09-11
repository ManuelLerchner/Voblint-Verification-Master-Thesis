# Examples / Interval

Interval-domain witnesses: flagship D/G runs, procedure-call soundness spines,
and backward (guard-refinement) trace soundness. Context-sensitive D/G
examples live in `Ctx/` (entry-state contexts) and `CallString/` (call
strings).

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Flagship.thy` | canonical spine | interval analysis of a counting loop, executed and certified on the D/G spine |
| `Example_Interval_DG_IP_Flagship.thy` | canonical spine | interprocedural: `twice` compiled and analyzed end to end through `FunctionEntry`/`FunctionResult` |
| `Example_Proc_Call.thy` | canonical spine | two procedures (`inc` / `sqr`) via a global; `main_prog_result` and the compiled CFG's call/combine structure |
| `Example_Interval_Loop_Coverage.thy` | canonical spine | bounded loop; backward `bfilter_ivl` refines the body to `[0,19]`; `loop_env_post_fixpoint` pins the exhibited `[0,20]` loop-head invariant |
| `Exec_Interval_Run.thy` | precision comparison | The same loop under bounded Kleene, warrowing TD, and every update rule; all recover `[0,20]` |
| `Example_Guard_Refinement.thy` | regression | backward guard refinement strictly tighter than identity assume (`backward_analysis_strictly_tighter`) — a precision negative result |
| `Example_Interval_DG_Seed_Join_Recursion.thy` | regression | a recursive callee activated from `main` once and from its own body five times: the activation seed is joined, never widened, and the callee's entry unknown is exactly what the seed holds |

Backward-analysis arc: `Example_Guard_Refinement` (one guard) -> `Example_Interval_Loop_Coverage`
(full CFG + exhibited post-fixpoint) -> `Exec_Interval_Run` (the same program, analyzed).
The executable step now lives beside the Interval theory it imports. The
store-only check trio's Interval member remains in `CLI/` with the Sign and
Parity members.

Role vocabulary: repository `README.md`.

## `Ctx/` — context routed by entered value

`twice` analyzed context-sensitively, each call site's context the entry value
of formal `p`, by the production entry-state analysis
(`Voblint_Analysis_Interval.Interval_Analyses`). Import chain:
`Ctx_Flagship` -> `Ctx_Collect` -> `Source_Ctx`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Ctx_Flagship.thy` | canonical spine | the production entry-state analysis run on `twice`; each call site's context is the entry value of formal `p` |
| `Example_Interval_DG_Ctx_Collect.thy` | canonical spine | activation-indexed collecting soundness: `twice` as a named instance of `entry_state_activation_collect_sound` |
| `Example_Interval_DG_Ctx_Globals_Regression.thy` | regression | a declared global and return values across three calls under entry-state contexts; a global-valued actual is evaluated against the caller's real state |
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

## `CallString/` — context routed by call site

Context routed by call site instead of entered value; `K1`/`K2` parameterize
the call-string bound `k`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_CallString_K1.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 1` (Seidl et al. 2026, Example 7) |
| `Example_Interval_DG_CallString_K2.thy` | canonical spine | `cs_route`/`cs_context` instance at `k = 2` |
| `Call_String_Solver_Regression.thy` | regression | exact-tree snapshots (`nest_1_eqs_statement3`, `nest_2_eqs_statement3`) locking in that `routed_call_tree_def`/`routed_entry_seed_tree_def`/`routed_node_rhs` still generate the expected equation shape at a genuine call continuation |
| `Example_Interval_Call_String_Generic_Parity.thy` | regression | the runtime-`k` pipeline (`cs_call_string_sol_prog`) reproduces every solved value the K1/K2 instances pin, at the same query points |
