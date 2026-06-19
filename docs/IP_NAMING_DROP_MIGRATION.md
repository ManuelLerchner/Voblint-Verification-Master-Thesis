# IP Naming Drop — one interprocedural frame, no `ip` suffix

Status: **PLANNED** (authored 2026-06-19). Follows
`IP_ONLY_CONSOLIDATION.md` (deleted the classical `com`/`to_cfg` spine) and
`IP_COLLECTING_CANONICAL_MIGRATION.md` (removed the dead intra `collecting`
interpretation, freeing the bare `cfg_collect` name).

## Goal

The repository is interprocedural-only. The `ip` / `_IP` suffix everywhere is
now pure noise — there is no intra sibling left to disambiguate from. Drop it.

The few remaining intra-named artifacts are not a parallel spine; they are
either dead, or scaffolding that feeds the IP layer through `*_le_*_ip` bridge
lemmas. Collapse each onto the IP definition, re-prove the bridged facts
directly, and rename the survivor to the unqualified name.

End state: one collecting semantics `cfg_collect`, one path predicate
`cfg_witness`, one trace collecting `cfg_collect_trace`, one constraint RHS
`rhs` / `is_post_fixpoint`, one operational grounding `pruns_to`, one soundness
theorem — none carrying `ip`.

## What is actually being merged

The true intra spine is already gone. What remains:

1. **Redundant suffixes** — `cfg_collect_ip`, `rhs_ip`, `TD_Side_IP_*`,
   `side_*_ip`, `mk_ip_cfg`, `pruns_to_ip`, `Sign_Side_IP_Soundness`, etc.
   Mechanical, except where dropping the suffix collides with a still-present
   intra definition.

2. **Intra scaffolding feeding IP via bridges** — not duplicates, stepping
   stones:
   - `Constraint_System.thy` defines both `rhs` (intra) and `rhs_ip`.
     `rhs_le_rhs_ip` bridges them; `apply_tf_le_rhs_ip` and `s0_le_rhs_ip_entry`
     route the edge/entry bounds through the intra `rhs`.
     `combine_abs_le_rhs_ip` already proves its bound **directly** against
     `rhs_ip` — the edge/entry bounds can be re-proved the same way, after which
     intra `rhs`, `is_post_fixpoint`, `apply_tf_le_rhs`, `s0_le_rhs_entry`,
     `rhs_le_rhs_ip`, `rhs_ip_eq_rhs_if_no_combines` are removable.
     `edge_collect_apply_tf_sound` has no `rhs` dependency — it stays.
   - `CFG_Collect_Edges` carries an intra `cfg_collect_F` whose only consumer is
     the vestigial `cfg_collect_ip_F_ge_cfg_collect_F` bridge.
   - `CFG_Collect_Core` exports only `cfg_collect_paths` (intra, path-based),
     consumed solely by the `alpha_last (cfg_collect_trace ...) = cfg_collect_paths`
     bridge in `CFG_Collect_Trace`.
   - `CFG_Collect_Trace` mixes the **shared** trace machinery
     (`edge_step`, `edges_trace`, `edges_collect_single`, frame lemmas — used by
     `CFG_Collect_Trace_IP`, `Trace_IP_Analysis_Sound`, `Sign_Exec_Sound`,
     `Example_Trace_Digest_Precision`) with the intra `cfg_collect_trace`. Keep
     the machinery; the IP trace `cfg_collect_trace_ip` becomes `cfg_collect_trace`.

3. **A genuine duplicate** — `combine_states_sound` is defined twice, identically
   (`Constraint_System.thy` `sound_domain` context and
   `Constraint_System_IP_Sound.thy`). Keep one.

## Identifier map

| now | after | collision handling |
| --- | --- | --- |
| `cfg_collect_ip` | `cfg_collect` | free since `IP_COLLECTING_CANONICAL` |
| `cfg_collect_ip_F` | `cfg_collect_F` | delete intra `cfg_collect_F` (Edges) + its lemmas + `cfg_collect_ip_F_ge_cfg_collect_F` |
| `cfg_collect_ip_paths` | `cfg_collect_paths` | delete intra `cfg_collect_paths` (Core) |
| `cfg_collect_ip_post` / `_entry` / `_lfp_unfold` / ... | `cfg_collect_post` / `_entry` / ... | — |
| `ip_witness` | `cfg_witness` | not bare `witness` (too generic) |
| `cfg_collect_trace_ip` | `cfg_collect_trace` | delete intra `cfg_collect_trace` + `alpha_last`↔paths bridge; keep shared trace infra |
| `ip_trace_witness` / `ip_trace_witness_d` | `trace_witness` / `trace_witness_d` | — |
| `cfg_collect_trace_ip_d` | `cfg_collect_trace_d` | — |
| `rhs_ip` | `rhs` | delete intra `rhs`; re-prove edge/entry bounds directly (model on `combine_abs_le_rhs_ip`) |
| `is_post_fixpoint_ip` | `is_post_fixpoint` | delete intra |
| `apply_tf_le_rhs_ip` / `s0_le_rhs_ip_entry` / `combine_abs_le_rhs_ip` | `apply_tf_le_rhs` / `s0_le_rhs_entry` / `combine_abs_le_rhs` | replace deleted intra lemmas of these names |
| `collect_pp_abstract_sound_ip` / `post_fixpoint_sound_at_ip` / `post_fixpoint_sound_ip` / `ip_witness_gamma` | drop `_ip` / `ip_` | — |
| `mk_ip_cfg` | `mk_cfg` | — |
| `pruns_to_ip` | `pruns_to` | — |
| `side_rhs_fold_ip`, `side_acc_ip`, `side_glob_ip`, `side_cfg_T_ip`, `side_analyse_ip`, `cfg_side_T_ip_pkg`, `td_cfg_side_ip_solver`, ... (TD_Side layer) | drop `_ip` | — |
| `trace_ip_analysis_sound` | `trace_analysis_sound` | — |

**Not touched** (incidental `ip` substring): `Nipkow`, `nip_aexp`, `nip_bexp`,
`aval_nip`, `triples`, `multiplication`, `multiple`, `participate`, `skip`.

## File map

| now | after |
| --- | --- |
| `CFG/Collecting/CFG_Collect_IP.thy` | `CFG_Collect.thy` |
| `CFG/Collecting/CFG_Collect_Trace_IP.thy` | merge into `CFG_Collect_Trace.thy` |
| `CFG/Collecting/CFG_Collect_Core.thy` | **delete** (sole export folds away) |
| `CFG/Collecting/CFG_Collect_IP_Adeq.thy` | `CFG_Collect_Adeq.thy` |
| `CFG/Collecting/CFG_Collect_Unified.thy` | keep (rename the `ip` interpretation) |
| `Analysis/Equations/Constraint_System_IP_Sound.thy` | merge into `Constraint_System_Sound.thy` (kills duplicate `combine_states_sound`) |
| `Analysis/Solver/TD_Side_IP_Tree.thy` | `TD_Side_Tree.thy` |
| `Analysis/Solver/TD_Side_IP_Mono.thy` | `TD_Side_Mono.thy` |
| `Analysis/Solver/TD_Side_IP_Bounds.thy` | `TD_Side_Bounds.thy` |
| `Analysis/Solver/TD_Side_IP_Interface.thy` | `TD_Side_Interface.thy` |
| `Analysis/Solver/TD_Side_IP_Soundness.thy` | `TD_Side_Soundness.thy` |
| `Analysis/Domains/Sign_Side_IP_Soundness.thy` | `Sign_Side_Soundness.thy` |
| `Analysis/Domains/Interval_Side_IP_Soundness.thy` | `Interval_Side_Soundness.thy` |
| `Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` | `Trace_Analysis_Sound.thy` |

`CFG_Prune.thy` keeps its name; only `mk_ip_cfg` → `mk_cfg` inside.

## Collecting layer import graph (current)

```
CFG_Collect_Edges            (shared: edge_collect, edges_collect, collect_pp, intra cfg_collect_F)
  CFG_Collect_Core           (intra: cfg_collect_paths)            -> DELETE
  CFG_Collect_IP             (cfg_collect_ip, cfg_witness, ...)    -> CFG_Collect
    CFG_Collect_IP_Adeq      (pruns_to_ip, witness program)        -> CFG_Collect_Adeq
    CFG_Prune                (mk_ip_cfg)                            -> rename const only
  CFG_Collect_Trace          (shared trace infra + intra cfg_collect_trace)
    CFG_Collect_Trace_IP     (cfg_collect_trace_ip, ip_trace_witness) -> merge UP into CFG_Collect_Trace
  CFG_Collect_Unified        (locale `collecting` + ip interpretation)
```

## Execution — build-gated slices, bottom-up by session DAG

Each slice: I/Q edit (`write_file` + `normalize_isabelle_ascii.py`) →
`get_diagnostics` clean on every touched file → `isabelle build` green for that
session before advancing. `git mv` for renames (preserve history); ROOT updated
in the same slice.

1. **Voblint_CFG** — collecting merge (`CFG_Collect`, `CFG_Collect_Trace`,
   `CFG_Collect_Adeq`, delete `Core`), `CFG_Prune` const, `CFG_Collect_Unified`
   interpretation, `CFG/ROOT`.
2. **Voblint_Analysis** — `Constraint_System` (delete intra `rhs`/`is_post_fixpoint`,
   re-prove bounds), merge `Constraint_System_IP_Sound` → `Constraint_System_Sound`,
   `TD_Side_*` renames, domain soundness renames, `Analysis/ROOT`.
3. **Voblint_Formalization** — `Trace_Analysis_Sound`, examples, `Voblint.thy`,
   `Formalization/ROOT`.
4. **Docs / READMEs** — `src/**/README.md`, `CLAUDE.md`, `docs/*` cross-refs,
   `docs/GLOSSARY.md`.

## Risk notes

- The only non-mechanical proof work is in `Constraint_System`: dropping intra
  `rhs` means `apply_tf_le_rhs` / `s0_le_rhs_entry` must be re-proved directly
  against the merged (combine-aware) `rhs`. `combine_abs_le_rhs_ip` is the
  template — same `abs_join_set` / `sup_fold_ge_state` argument over `edge_vals`.
- The TD_Side layer has the highest `_ip` density (`side_rhs_fold_ip`,
  `side_acc_ip`, `side_glob_ip`, `side_cfg_T_ip` each appear dozens of times).
  Pure rename, but verify per file with `get_diagnostics` — `_def` / `.simps`
  derived names rename with the constant.
- ROOT lists theory names without the `.thy` extension; keep ROOT and filenames
  in lockstep within each slice or the session won't build.

## Completion record

_(to be filled in as slices land)_
