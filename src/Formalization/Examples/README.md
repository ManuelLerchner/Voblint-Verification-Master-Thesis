# Examples

**Main contribution:** Concrete demonstrations — procedural soundness witnesses,
executable analyzer runs, CFG visualisation, coverage tests, and precision
comparisons. Not imported by pipeline theories.

**Theories** (all registered in `ROOT`)

| File | Role |
| --- | --- |
| `Example_Inc_Proc.thy` | Shared `inc_pi` witness: procedure `p` increments global `Gx`; used by sign, interval, and mixed-flow examples |
| `Example_Side_Execute.thy` | Minimal certified sign IP run (`x := 1`); `sign_exec_prog` + annotated DOT |
| `Example_Side_Branch_Calls.thy` | Branching procedure called twice; flow-sensitive locals, globals cluster |
| `Example_Side_Proc_Global.thy` | Sign IP on `inc_pi` / single `Call ''p''`; manual soundness + `sign_exec_prog` + annotated DOT |
| `Example_Interval_Side_Proc_Global.thy` | Interval IP on the same `inc_pi` witness (manual post-fixpoint only) |
| `Example_Mixed_Flow_Sign.thy` | Applies `mixed_flow_analysis_sound` / `mixed_flow_analysis_optimal` to native `sign_etf` on `inc_pi` |
| `Example_Proc_Call.thy` | Interval analysis of `inc`/`sqr` via global `Gx`; plain structural DOT |
| `Example_Interval_Loop_Coverage.thy` | Bounded loop; backward `assume_ivl` refines body to `[0,19]`; certified trace soundness `[0,20]` at loop head |
| `Example_Guard_Refinement.thy` | Backward vs identity assume on `x < 20`; single-guard precision gap (companion to loop coverage) |
| `Example_IMP2_Coverage.thy` | Non-terminating loop; sign coverage via trace soundness |
| `Example_Proc_GraphViz.thy` | Plain procedural CFG DOT (`plain_dot_of_prog_lit`; two demo programs) |
| `Example_Trace_Digest_Precision.thy` | Digest vs flat collecting precision on a two-path program |
| `Example_Trace_Digest_Combine.thy` | Combine-side digest filtering: compiled if/else callee, `cmp` blocks path 3 |
| `Example_Trace_Digest_ReachingCompat.thy` | Reader-side `reaching_compat`: lockset ghost filters global read |
| `Example_Finite_Sign_Context_Analysis.thy` | Finite sign-derived calling contexts (`GZero`/`GPos`/`GNonNeg`/`GOther`); executable keyed `_st` run plus finite-key soundness-facing theorem |
| `Example_Mode_Value_Digest_Showcase.thy` | Guided reading of the value-carried mode digest on the compiled `mode_prog` run |
| `Example_Interval_Mode_Showcase.thy` | Interval counterpart: guided reading of the interval mode-digest run (loop tracking, digest separation, update-rule soundness, context-clustered GraphViz) |
| `Example_Digest_Pipeline_Showcase.thy` | **Canonical end-to-end showcase**: source -> CFG -> equations -> strategy tree -> TD-side solver -> solution -> digest projection -> annotated CFG -> GraphViz -> soundness, all executable on one program |

**GraphViz:** The annotated-DOT renderer (`annotated_dot_of_prog_lit`) is generic over any
`show_val` domain. Sign examples with `Sign_Exec_Sound` use it for per-node sign states +
`cluster_globals`; the interval flagship `Voblint_Analysis.Exec_Ivl_Mode_Compiled_Run`
(`wide_dot`) uses the same renderer on the `ivl` `show_val` instance. Structural-only
examples use `plain_dot_of_prog_lit`.

**Backward analysis arc:** start with `Example_Guard_Refinement` (one guard, identity
contrast), then `Example_Interval_Loop_Coverage` (full CFG + trace soundness). Eval-only
mirror: `Voblint_Analysis.Exec_Ivl_Run`.

**Session entry point:** `Voblint.thy` imports all examples for the umbrella document.
