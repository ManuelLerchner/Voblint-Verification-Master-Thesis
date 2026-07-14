# Examples

**Main contribution:** Concrete demonstrations — procedural soundness witnesses,
executable analyzer runs, CFG visualisation, coverage tests, and precision
comparisons. Not imported by pipeline theories. Grouped into themed subfolders
(theory names stay flat; `ROOT` declares the directories).

## `Executable/` — code-generated analyzer runs

Executable runs that evaluate the real TD-side solver through generated code.
These are examples even when they expose soundness-facing obligations: they fix a
concrete program, equation system, or precision witness.

| Folder | Role |
| --- | --- |
| `Executable/Common/` | shared scaffolds for small executable witnesses |
| `Executable/Sign/Core/` | basic sign `st` codegen and hand-written equation-system probe |
| `Executable/Sign/Context/` | sign context-sensitive runs and seeded entry witness |
| `Executable/Sign/Keyed/` | sign keyed-global, retain, and mode-value digest runs |
| `Executable/Sign/SeededClean/` | sign D/G/C seeded-clean witnesses |
| `Executable/Interval/Core/` | interval loop solver run and update-rule menu |
| `Executable/Interval/Context/` | interval context-sensitive runs |
| `Executable/Interval/SeededClean/` | interval seeded-clean, keyed DG, derived-global, and return-rehydration runs |

## `Digest/` — context-sensitivity and digests

| File | Role |
| --- | --- |
| `Example_Sign_Mode_Digest.thy` | **Sign flagship**: value-derived digest on a compiled program — call context projected from an ordinary local, global partitioned by the same projection; sound under join / per-origin / warrowing update rules; context-clustered annotated GraphViz (`mode_digest_dot`) |
| `Example_Interval_Mode_Digest.thy` | **Interval flagship**: the sign flagship's sibling at the `ivl` domain, with a **while loop**; digest keeps `G` separated (`[0,5]`/`[9,9]`), a **proven-sound widening loop** (`wide_abstracts`), the update-rule menu, and annotated GraphViz (`iv_digest_dot`, `wide_dot`) |
| `Example_Interval_Recursion_Digest.thy` | Recursive countup; the depth-digest that would recover full precision, with an honest account of the executable wall (P12): join non-terminates, warrowing widens `G` to top |
| `Example_Interval_Recursion_Convergence.thy` | **Recursive interval flagship (1/3)**: the seeded-clean solve on `rdiv` terminates once empty intervals are canonicalised; includes the concrete IMP2 run to `G = 3`; each call site keeps its own context; context-clustered GraphViz |
| `Example_Interval_Recursion_Rehydrate.thy` | **Recursive interval flagship (2/3)**: the rehydrating combine returns the recursive global `[3,3]` to `main` (no return values); a genuine solver post-fixpoint (`rdiv_rehyd_cover_post_fixpoint`) with the return chain and `rdiv_rehyd_main_return_sound` |
| `Example_Rdiv_Twfr_Sound.thy` | **Recursive interval flagship (3/3)**: executable soundness of `rdiv` via the `twfr` witness spine, anchored by the concrete IMP2 execution to `G = 3` — a bottom-up recursive witness reaching `main` continuation and the per-coordinate over-approximation `rdiv_witness_G_over_approximated` (canonical twfr end-to-end result) |
| `Example_Mode_Value_Digest_Showcase.thy` | Guided reading of `Example_Sign_Mode_Digest`'s value-carried digest run |
| `Example_Digest_Pipeline_Showcase.thy` | **Canonical end-to-end showcase**: concrete IMP2 source run → CFG → equations → strategy tree → TD-side solver → solution → digest projection → annotated CFG → GraphViz → soundness, executable on one program |
| `Example_Finite_Sign_Context_Analysis.thy` | Finite sign-derived calling contexts; executable keyed `_st` run + finite-key soundness-facing theorem |
| `Example_Trace_Digest_Precision.thy` | Digest vs flat collecting precision on a two-path program |
| `Example_Trace_Digest_Combine.thy` | Combine-side digest filtering: compiled if/else callee, `cmp` blocks path 3 |
| `Example_Trace_Digest_ReachingCompat.thy` | Reader-side `reaching_compat`: lockset digest filters a global read |
| `Example_Entry_Store_Context_Precision.thy` | Entry-store context precision |
| `Example_Global_Ctx_Read_Precision.thy` | Context-indexed global read precision |

## `Interprocedural/` — procedure-call witnesses

| File | Role |
| --- | --- |
| `Example_Inc_Proc.thy` | The `inc` program (procedure `p` increments global `Gx`) + its run-to-collecting witness lemmas (`cfg_runs_to_pcall_global_increment`) — proves the `cfg_runs_to` the examples below assume |
| `Example_Side_Proc_Global.thy` | Sign IP on a local copy of `inc`; manual soundness + `sign_exec_prog` + annotated DOT |
| `Example_Interval_Side_Proc_Global.thy` | Interval IP on a local copy of `inc` (manual post-fixpoint) |
| `Example_Mixed_Flow_Sign.thy` | `mixed_flow_analysis_sound` / `_optimal` on native `sign_etf`, local copy of `inc` |
| `Example_Proc_Call.thy` | Interval analysis of `inc`/`sqr` via global `Gx`; structural DOT |
| `Example_Side_Execute.thy` | Minimal certified sign IP run (`x := 1`) |
| `Example_Side_Branch_Calls.thy` | Branching procedure called twice; flow-sensitive locals |
| `Example_Seed_Clean_Context.thy` | Seeded-clean context witness on a two-call program |
| `Example_Proc_Recursion_CFG.thy` | Recursive procedure CFG layout regression |

Each of the four `inc`-based examples defines its own program locally (self-contained);
`Example_Inc_Proc` is the standalone witness proving what they assume.

## `Numeric/` — interval / backward numeric

| File | Role |
| --- | --- |
| `Example_Interval_Loop_Coverage.thy` | Bounded loop; backward `assume_ivl` refines body to `[0,19]`; certified trace soundness `[0,20]` at the loop head |
| `Example_Guard_Refinement.thy` | Backward vs identity assume on `x < 20`; single-guard precision gap |
| `Example_IMP2_Coverage.thy` | Non-terminating loop; sign coverage via trace soundness |

## `Tooling/`

| File | Role |
| --- | --- |
| `Example_Proc_GraphViz.thy` | Plain procedural CFG DOT (`plain_dot_of_prog_lit`; two demo programs) |
| `Example_Mixed_Sign_Interval_GraphViz.thy` | Mixed Sign/Interval analysis (`Instances/Mixed`) on `x := -1; x := 2`: solver run + `part_post_solution` + expected values (exit answer `SPos`, side invariant `[-1, 2]`); DOT with Sign answers at nodes and the Interval invariant in its own cluster |

## Cross-cutting notes

**GraphViz:** The annotated-DOT renderer (`annotated_dot_of_prog_lit`) and the
context-clustered `ctx_debug_state_node_label_auto` are generic over any `show_val` domain,
auto-collecting the program's locals. Sign and interval flagships both use them; structural
examples use `plain_dot_of_prog_lit`.

**Backward analysis arc:** `Example_Guard_Refinement` (one guard) → `Example_Interval_Loop_Coverage`
(full CFG + trace soundness). Eval-only mirror: `Exec_Ivl_Run` in
`Executable/Interval/Core/`.

**Seeded-clean D/G/C spine (interval):** the interval context-sliced R_read soundness
is `Exec_Ivl_Cmp_Seed_Sound` (`ivl_clean_ctx_collect_rread`), a thin
instantiation of the generic `Clean_RRead_Sound`; the executable interval runs are
`Exec_Ivl_Cmp_Seed_Clean_Run` (non-recursive two-call program,
`by eval` precision witnesses), `Exec_Ivl_Cmp_Keyed_DG_Run` (DG-native keyed-slot
separation), the DG-native interval context probe in `Voblint_Analysis.Interval_DG`
(`ivl_dg_two_context_sound`), and
`Exec_Ivl_Cmp_Seed_Clean_Derived_Run`
(same spine with a *derived* global `GH := G + 1`: the derived global stays separated
per calling context — `[1,1]` vs `[11,11]` — both as the callee-exit local and as the
context-indexed global side state, with a context-clustered GraphViz `dseed_dot`).
`Exec_Ivl_Cmp_Seed_Rehydrate_Run` adds **return rehydration** (Goblint
`Spec.combine`): the caller continuation is the structural combine `combine_abs_st`
(caller locals + callee globals), so reading a global back after a call recovers the
exact point (`g1=[0,0]`, `h1=[1,1]`, `g2=[10,10]`, `h2=[11,11]`) rather than `bot` —
without a `local ⊔ global` read. Its `rehydrate_caller_continuation_sound` discharges
the `COMB` obligation of the generic `clean_ctx_collect_rread`. The retain / `side_env_cmp` interval examples stay as
the conservative baseline; their loop / recursion imprecision is widening/warrowing-related,
not D/G/C-related. See `docs/M2_EXAMPLE_MIGRATION_REPORT.md` § "Interval D/G/C soundness vs widening precision".

**Recursive interval flagship (`twf`/`twfr` witness calculus):** the canonical
recursive-interval story is a three-theory tower on the `rdiv` program, each
adding one capability: `Example_Interval_Recursion_Convergence` (the seeded-clean
solve terminates, context-sensitive), `Example_Interval_Recursion_Rehydrate` (the
returned global is rehydrated back to `main` as a solver post-fixpoint), and
`Example_Rdiv_Twfr_Sound` (executable soundness via a bottom-up `twfr` witness —
`rdiv_witness_G_over_approximated`). The `twfr` witness calculus is the canonical
recursive proof layer; per-coordinate over-approximation is the non-vacuous
soundness statement (the full-store slot is provably empty for seeded-clean runs).

**Session entry point:** `Voblint.thy` imports the curated example set for the umbrella document.
