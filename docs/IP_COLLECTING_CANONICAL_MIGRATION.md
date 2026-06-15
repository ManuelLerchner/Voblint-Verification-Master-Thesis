# IP Collecting Canonical — remove the dead intra layer

Status: **DONE** (executed 2026-06-15; Scope A complete). Tracks
proof-repo issue **#41**; KB open question **OQ-29**
(`research/open-questions/oq-ip-collecting-canonical`). Supersedes the
"deep re-home" framing in `CLASSICAL_SPINE_RETIREMENT.md` (that note predates the
IP-only consolidation; the collision it feared is removable — see below).

## Goal

The repo is IP-only since `IP_ONLY_CONSOLIDATION.md`. The unified `collecting`
locale still carries **two** interpretations:

```
intra:  combine_at = (\<lambda>g rho v. {})       -> cfg_collect      (dead)
ip:     combine_at = collect_combine_pp     -> cfg_collect_ip   (the spine)
```

The `intra` interpretation is **dead downstream**: nothing consumes its
collecting object (`cfg_collect`) or its soundness conclusions. It reads as a
load-bearing second semantics but no longer is one (the intra `com` language was
extracted to `voblint-formalization-classical`). Remove it so the
interprocedural collecting semantics is the only one in the tree.

Two scopes (this doc executes **Scope A**; B is recorded as an optional follow-up):

- **Scope A (chosen).** Delete the dead semantics object + soundness stack +
  dead lfp-level intra bridges. Keep `cfg_collect_F` (the per-node functional)
  and `cfg_collect_ip_F_ge_cfg_collect_F` as honest building blocks of the live
  `cfg_collect_ip_entry`. No proof reconstruction.
- **Scope B (deferred).** Additionally reprove `cfg_collect_ip_entry` directly
  from `cfg_collect_ip_lfp_unfold` so `cfg_collect_F` can also go — then nothing
  intra remains. One easy reprove; cosmetic-purity payoff only.

Out of scope here: the `_ip` -> canonical **rename** (drop the `_ip` suffix so
the IP spine owns the unmarked names). Separate, optional, lower priority.

## Decisions on record

- **Scope A**, not B — `cfg_collect_F` stays as a building block, not a ghost.
- **Keep the generic `collecting` locale and the `ip` interpretation.** Only the
  `intra` interpretation and its consequences go.
- **Keep `Constraint_System_Sound.thy`.** Its head pieces are shared with the IP
  side (verified consumers below); only its tail is dead.
- **Keep `collect_post_fixpoint_sound`** (the `(in collecting)` engine lemma) —
  used by the `ip` soundness path.

## Dependency analysis (verified 2026-06-14, `rg` over `src/`)

### Confirmed dead (consumed only by other dead members, or nothing)

| Item | File:line | Note |
| --- | --- | --- |
| `intra` interpretation, `intra_F_eq`, `intra_collect_eq` | `CFG/Collecting/CFG_Collect_Unified.thy:82-91` | only feed `unified_post_fixpoint_sound` |
| `unified_post_fixpoint_sound` (intra) | `Analysis/Equations/Analysis_Sound.thy:36-60` | zero consumers (only a prose mention at `:8`) |
| `collect_pp_abstract_sound` | `Analysis/Equations/Constraint_System_Sound.thy:134` | consumers only in deleted code; IP uses `collect_pp_abstract_sound_ip` |
| `collect_pp_abstract_sound_rhs_le` | `…/Constraint_System_Sound.thy:159` | no external consumers |
| `edges_collect_gamma_path_aux` | `…/Constraint_System_Sound.thy:184` | no external consumers |
| `edges_collect_gamma_path` | `…/Constraint_System_Sound.thy:226` | no external consumers |
| `post_fixpoint_sound_at` | `…/Constraint_System_Sound.thy:240` | zero consumers |
| `sup_fold_ge_state` (intra dup) | `…/Constraint_System_Sound.thy:274` | live copy is `Constraint_System.thy:443` |
| `post_fixpoint_sound` | `…/Constraint_System_Sound.thy:280` | zero consumers |
| `cfg_collect_le_paths` | `CFG/Collecting/CFG_Collect_Core.thy:63` | consumer was `post_fixpoint_sound_at` |
| `cfg_collect_witness` | `CFG/Collecting/CFG_Collect_Core.thy:79` | zero consumers |
| `cfg_collect_paths_post` | `CFG/Collecting/CFG_Collect_Core.thy:47` | only via `cfg_collect_le_paths` — confirm at build |
| `cfg_collect` (lfp), `cfg_collect_mono_S`, `cfg_collect_lfp_unfold` | `CFG/Collecting/CFG_Collect_Edges.thy:142,175,180` | the dead semantics object |
| `cfg_collect_ip_eq_cfg_collect` | `CFG/Collecting/CFG_Collect_IP.thy:103` | dead lfp-level bridge |
| `cfg_collect_le_cfg_collect_ip` | `CFG/Collecting/CFG_Collect_IP.thy:124` | dead lfp-level bridge |
| `cfg_collect_ip_F_eq_cfg_collect_F` | `CFG/Collecting/CFG_Collect_IP.thy:98` | only feeds `cfg_collect_ip_eq_cfg_collect` |

### Keep — shared / load-bearing

| Item | Why |
| --- | --- |
| `apply_tf_le_rhs` (`Constraint_System_Sound.thy:22`) | used by `Constraint_System_IP_Sound.thy:14` |
| `s0_le_rhs_entry` (`:75`) | used by `Constraint_System_IP_Sound.thy:131` |
| `edge_collect_apply_tf_sound` (`:105`) | used by `Constraint_System_IP_Sound.thy:89,165` |
| `cfg_collect_F` (`CFG_Collect_Edges.thy:138`) + `cfg_collect_F_mono`/`_mono_S` | building block of `cfg_collect_ip_entry` (Scope A) |
| `cfg_collect_ip_F_ge_cfg_collect_F` (`CFG_Collect_IP.thy:120`) | used by `cfg_collect_ip_entry` (`:130`) |
| `cfg_collect_ip_entry` (`CFG_Collect_IP.thy:130`) | live — used by `CFG_Collect_Trace_IP.thy:86`, `CFG_Collect_IP_Adeq.thy:218` |
| `collect_post_fixpoint_sound` (`Analysis_Sound.thy`) | engine lemma used by the `ip` path |
| `collect_pp_abstract_sound_ip`, `collect_combine_pp_abstract_sound` (`Constraint_System_IP_Sound.thy`) | the IP pieces |

### Watch at build

- `cfg_collect_F_mono` / `cfg_collect_F_mono_S` may become orphaned once
  `cfg_collect`/`cfg_collect_lfp_unfold`/`cfg_collect_mono_S` are gone. If the
  build reports them unused, they are not needed by `cfg_collect_ip_entry`'s path
  (which uses `cfg_collect_F_def` + `cfg_collect_ip_F_ge_cfg_collect_F`) — drop
  them too. If `cfg_collect_ip_entry`'s `smt` proof breaks, reprove directly
  (this is the Scope-B step, pulled in only if forced).
- `CFG_Collect_Trace.thy` (intra trace) imports remain; it uses
  `cfg_collect_paths` (not `cfg_collect`). Do **not** touch the trace layer —
  out of scope.

## Execution plan (I/Q, build-gated)

Per `AGENTS.md`: edit `.thy` only via I/Q `write_file`; `get_diagnostics`
(scope=file) clean on each touched theory before moving on; one `isabelle build`
gate at the end. Order bottom-up in the session DAG so each file's deletions land
before its importers re-check.

1. **`CFG_Collect_Edges.thy`** — delete `cfg_collect`, `cfg_collect_mono_S`,
   `cfg_collect_lfp_unfold`. Keep `cfg_collect_F` (+ mono lemmas pending the
   build watch).
2. **`CFG_Collect_Core.thy`** — delete `cfg_collect_le_paths`,
   `cfg_collect_witness`, `cfg_collect_paths_post` (if orphaned).
3. **`CFG_Collect_IP.thy`** — delete `cfg_collect_ip_eq_cfg_collect`,
   `cfg_collect_le_cfg_collect_ip`, `cfg_collect_ip_F_eq_cfg_collect_F`. Keep
   `cfg_collect_ip_F_ge_cfg_collect_F`, `cfg_collect_ip_entry`.
4. **`CFG_Collect_Unified.thy`** — delete the `intra` interpretation,
   `intra_F_eq`, `intra_collect_eq`, and the `intra:` line in the header comment.
   Keep the locale + `ip` interpretation + `ip_F_eq`/`ip_collect_eq`.
5. **`Constraint_System_Sound.thy`** — delete the tail from
   `collect_pp_abstract_sound` (134) through `post_fixpoint_sound` (end). Keep
   `apply_tf_le_rhs`, `s0_le_rhs_entry`, `edge_collect_apply_tf_sound`.
6. **`Analysis_Sound.thy`** — delete `unified_post_fixpoint_sound` (intra);
   update the header comment so it no longer claims an intra/IP pair (state: one
   engine, one live interpretation).
7. **READMEs** — `src/CFG/Collecting/README.md` (drop the "Intra: `cfg_collect`
   … used by `unified_post_fixpoint_sound`" line), `src/Analysis/Equations/README.md`
   if it pairs intra/IP soundness.
8. **Build gate** — `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization`; green + 0 sorries before declaring done.

## Acceptance test

- `rg -n '\bcfg_collect\b' src/ | rg -vw 'cfg_collect_ip|cfg_collect_trace_ip|cfg_collect_trace|cfg_collect_paths|cfg_collect_F'` returns nothing (the intra lfp object is gone).
- No `intra` interpretation / `unified_post_fixpoint_sound` / `post_fixpoint_sound[_at]` in `src/`.
- `Constraint_System_Sound.thy` head pieces still resolve for `Constraint_System_IP_Sound`.
- Full `Voblint_Formalization` build green, sorry-free.

## Follow-ups (not this migration)

- **Scope B.** Reprove `cfg_collect_ip_entry` directly; delete `cfg_collect_F`
  (+ mono) and `cfg_collect_ip_F_ge_cfg_collect_F`.
- **`_ip` -> canonical rename.** `cfg_collect_ip -> cfg_collect`,
  `unified_post_fixpoint_sound_ip -> unified_post_fixpoint_sound`,
  `side_collect_sound_ip_* -> side_collect_sound_*`,
  `trace_ip_analysis_sound -> trace_analysis_sound`, across theories + READMEs,
  respecting session-qualified names. After this migration the name collision
  that `CLASSICAL_SPINE_RETIREMENT.md` flagged is gone, so the rename is
  mechanical (sed-per-file + build), not a re-home.
