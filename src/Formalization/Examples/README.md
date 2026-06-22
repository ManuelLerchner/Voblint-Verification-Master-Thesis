# Examples

**Main contribution:** Concrete demonstrations — procedural soundness witnesses,
executable analyzer runs, CFG visualisation, coverage tests, and precision
comparisons. Not imported by pipeline theories.

**Theories** (all registered in `ROOT`)

| File | Role |
| --- | --- |
| `Example_Side_Execute.thy` | Minimal certified sign IP run (`x := 1`); `sign_exec_prog` + annotated DOT |
| `Example_Side_Branch_Calls.thy` | Branching procedure called twice; flow-sensitive locals, globals cluster |
| `Example_Side_Proc_Global.thy` | Sign IP on `inc_pi` / single `Call ''p''`; manual soundness + `sign_exec_prog` + annotated DOT |
| `Example_Interval_Side_Proc_Global.thy` | Interval IP on the same `inc_pi` witness (manual post-fixpoint only) |
| `Example_Proc_Call.thy` | Interval analysis of `inc`/`sqr` via global `Gx`; plain structural DOT |
| `Example_Interval_Loop_Coverage.thy` | Bounded loop; backward `assume_ivl` refines body to `[0,19]`; certified trace soundness `[0,20]` at loop head |
| `Example_Guard_Refinement.thy` | Backward vs identity assume on `x < 20`; single-guard precision gap (companion to loop coverage) |
| `Example_IMP2_Coverage.thy` | Non-terminating loop; sign coverage via trace soundness |
| `Example_Proc_GraphViz.thy` | Plain procedural CFG DOT (`plain_dot_of_prog_lit`; two demo programs) |
| `Example_Trace_Digest_Precision.thy` | Digest vs flat collecting precision on a two-path program |

**GraphViz:** Sign examples with `Sign_Exec_Sound` use `sign_annotated_dot_prog_lit`
(per-node sign states + `cluster_globals`). Interval and structural examples use
`plain_dot_of_prog_lit` (annotated interval DOT is future work; executable interval
analysis lives in `Voblint_Analysis.Exec_Ivl_Run` / `Ivl_Exec`).

**Backward analysis arc:** start with `Example_Guard_Refinement` (one guard, identity
contrast), then `Example_Interval_Loop_Coverage` (full CFG + trace soundness). Eval-only
mirror: `Voblint_Analysis.Exec_Ivl_Run`.

**Session entry point:** `Voblint.thy` imports all examples for the umbrella document.
