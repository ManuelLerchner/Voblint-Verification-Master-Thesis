# IP-Only Consolidation

Status: **DONE** (deletions + `pcom -> com` rename). Authored 2026-06-12,
executed 2026-06-12. Supersedes the draft `TD_SIDE_FOLD_UNIFICATION_MIGRATION.md`.

Phases 1-4 deletions landed in one slice on branch `consolidation/ip-only`:
3908 lines removed across 14 `.thy` files, full `isabelle build` green. The
classical `com` spine (intra side soundness, `to_cfg` cone, intra fold,
`com` datatype + small-step) is gone; the side-effecting IP pipeline (now
renamed `pcom -> com`) is the sole survivor. See "Completion record" below.

## Goal

Collapse the repository onto a single interprocedural pipeline. The intra
(classical, `com`/`to_cfg`) spine duplicates the IP spine and is not used to
prove any IP result. Remove it; rename the surviving `pcom` language to `com`.

End state: one command language (`com`, with procedure calls), one compiler,
one collecting semantics (`cfg_collect_ip`), one operational grounding
(`pruns_to_ip`), one soundness theorem.

Net removal: ~3500 `.thy` lines (~30% of `src/`).

## Decisions on record

- **Option A** (generic base) for the solver fold.
- **Delete the whole classical side spine**, not just the duplicated fold.
- **Drop the `com`-level operational claim.** The IP/`pcom` grounding
  (`pruns_to_ip`) is the only operational grounding kept. No `com ~= pcom`
  simulation lemma is needed: after Phase 4 there is only one language.
- **Expression layer unchanged.** Reusing AFP IMP2's reflected operators
  (`Binop (int=>int=>int)`) is impossible for an executable abstract
  interpreter (operator dispatch needs a matchable tag; a function is not
  matchable). The structural `aexp`/`bexp` + `aval`/`bval` stay as-is. See
  `docs/AFP_IMP2_REUSE_DECISION.md`.

## CAVEAT (recorded once)

Deleting `Sign_Side_Soundness` removes the only `com`-level soundness statement
(`side_sign_analysis_sound`); the IP terminal does not bridge to it. If that
statement must survive, mirror it into the sibling
`voblint-formalization-classical` repo before Phase 1. Otherwise it lives only
in git history.

---

## Phase 1 - delete the intra side spine

Strict linear import chain; nothing else imports these (verified).

| Delete | Lines | ROOT line |
| --- | --- | --- |
| `src/Solver/TD_Side_Interface.thy` | 148 | 22 |
| `src/Solver/TD_Side_Soundness.thy` | 297 | 23 |
| `src/Domains/Sign_Side_Soundness.thy` | 28 | 36 |
| `src/Examples/Example_Side_Global.thy` | 54 | 34 |

Also removes one importer of `CFG_Runs_To_Bridge` (via `Example_Side_Global`),
setting up Phase 2.

**Exit:** 4 files + 4 ROOT entries gone; full build green.

## Phase 2 - delete the `to_cfg` cone

`to_cfg` (intra compile) anchors the intra collecting + path-bridge stack. The
IP spine references `to_cfg`/`cfg_collect`/`runs_to` **zero** times
(`Constraint_System_IP_Sound` is clean); IP is grounded independently by
`CFG_Collect_IP_Adeq` / `pruns_to_ip`.

| Delete | Lines | Note |
| --- | --- | --- |
| `src/CFG/IMP2_to_CFG.thy` | 413 | `to_cfg`, intra `compile`, `to_cfg_finite/simps`; `compile_pcom` does not use it |
| `src/CFG/Collecting/CFG_Compound_Paths.thy` | 926 | 193 `to_cfg` refs; generic `cfg_collect_paths` is in Core, not here |
| `src/CFG/Collecting/CFG_Path_Bridge.thy` | 411 | to_cfg path bridge |
| `src/CFG/Collecting/CFG_Runs_To_Bridge.thy` | 678 | `runs_to`(com) <-> `cfg_collect` grounding |

Trim / repoint:

- `src/Equations/Constraint_System_Sound.thy`: delete the `to_cfg` exit
  corollary (~ll.326-342). KEEP the generic theorem (~l.246, over abstract `g`,
  used by IP). Re-point import `CFG_Runs_To_Bridge` -> `CFG_Collecting_Core`.
- `src/CFG/CFG_GraphViz.thy`: 2 `to_cfg` refs - repoint to `compile_prog` or drop.

**Verification gate (do first):** confirm `cfg_collect_le_paths` (used by the
generic soundness at `Constraint_System_Sound` l.248) lives in
`CFG_Collecting_Core`, not `CFG_Compound_Paths`. If it is in `CFG_Compound_Paths`,
extract it to Core before deleting. `cfg_collect_paths` + `_step/_entry/_post`
are already confirmed in Core.

**Exit:** after re-pointing, the path stack has no importers; 4 files +
ROOT entries gone; generic soundness still builds; full build green.

## Phase 3 - trim the intra fold from `TD_Side_CFG`

After Phase 1, the intra fold quintet has **0** references in `TD_Side_IP_CFG`
(verified). Delete, don't bridge.

- `src/Solver/TD_Side_CFG.thy` (846 -> ~450): delete `side_rhs_fold`,
  `side_acc`, `side_glob`, `make_side_rhs_tree`, `side_cfg_T` and their
  intra-specific denotation/mono lemmas.
- KEEP: lattice base (`restrict_local`/`restrict_global` + mono + join) and the
  generic tree helpers `dep_aux` (46 IP hits), `sides_of_rhs` (16), `side_env`
  (12). `TD_Side_CFG` becomes the Option-A generic base.

**Boundary rule:** a `TD_Side_CFG` declaration is DELETED iff it mentions a
quintet name and has 0 references in `TD_Side_IP_CFG`; else KEEP.

**Exit:** quintet gone from `TD_Side_CFG`; IP spine green; full build green.

## Phase 4 - retire `com`, rename `pcom -> com`

After Phases 1-2 nothing analyzes `com` programs. The `com` command datatype
and its small-step are orphaned; `pcom` becomes the sole language.

- `src/IMP2/IMP2_Expr.thy`: **split**. KEEP `aval`/`bval` (used by
  `pcom`'s `pstep`); DELETE the `com` `(c,s) -> (c',s')` small-step relation and
  its lemmas. (Consider moving `aval`/`bval` into `IMP2_Syntax` so
  `IMP2_Expr` can go entirely.)
- `src/IMP2/IMP2_Syntax.thy`: delete the `com` command datatype (keep
  `aexp`/`bexp`/`store`).
- Rename across the surviving IP spine: `pcom -> com`, `pstep -> ...`,
  `compile_pcom -> compile`, `compile_prog -> ...`, `cfg_collect_ip -> ...`
  (optional; mechanical, separate commits).

**Accepted wart:** the renamed `com` keeps `PRestore` (runtime-only). This is
already true of `pcom` today and managed by the "never in source" convention;
no regression.

**Exit:** no `com` command datatype/small-step; `pcom` renamed; full build
green, zero new `sorry`.

---

## Sequencing & gates

Phase 1 -> 2 -> 3 -> 4, each a green `isabelle build` checkpoint. Phase 4 last
(renaming before deletion would re-thread code about to be deleted). Phase 3
needs Phase 1. Phase 2 is independent but Phase 1 first removes a
`CFG_Runs_To_Bridge` importer.

**`.thy` edits require I/Q** (currently DOWN - start `./scripts/start-both.sh`).
Pure file deletions + ROOT edits are host-safe and git-reversible; content
trims (Phase 2 `Constraint_System_Sound`, Phase 3 `TD_Side_CFG`, Phase 4 splits)
go through I/Q `write_file`.

**Gate is the batch build, not the I/Q checker.** Show a green `-v` log per
phase before moving on.

## Pre-step (housekeeping)

Remove the ~40 stray `*.thy~` jEdit backups; add `*.thy~` to `.gitignore`.

## Running tally

| Phase | Removed (lines, approx) |
| --- | --- |
| 1 | 527 |
| 2 | 2428 + trims |
| 3 | ~400 |
| 4 | com datatype + com small-step + renames |
| **Total** | **~3500 (~30% of src/)** |

---

## Completion record (2026-06-12)

Executed on branch `consolidation/ip-only`. Net: **3908 deletions**, 18 files
changed, full `isabelle build Voblint_Formalization` green after each phase.

**Pre-step:** removed 41 stray `*.thy~` jEdit backups (already in `.gitignore`).

**Phase 1 - intra side spine.** Deleted `TD_Side_Interface`,
`TD_Side_Soundness`, `Sign_Side_Soundness`, `Example_Side_Global` + 4 ROOT
entries. Verified the four form a closed import cluster (the lone outside
mention in `TD_Side_IP_Interface` is a comment). The `com`-level
`side_sign_analysis_sound` now lives only in git history (CAVEAT accepted).

**Phase 2 - to_cfg cone.** Gate confirmed: `cfg_collect_le_paths` and the
`cfg_collect_paths` family live in `CFG_Collecting_Core`. Deleted `IMP2_to_CFG`,
`CFG_Compound_Paths`, `CFG_Path_Bridge`, `CFG_Runs_To_Bridge`. Repointed
`Constraint_System_Sound` import `CFG_Runs_To_Bridge -> CFG_Collecting_Core` and
dropped its `to_cfg` `exit_sound` corollary (generic `post_fixpoint_sound_at`
kept). Found one item the plan missed: `CFG_Edges_Collect` *really* imported
`IMP2_to_CFG` (for `aval`/`bval`); repointed it to `IMP2_Expr`. Cleaned
stale `to_cfg` comments in `CFG_GraphViz` and `IMP2_Proc_to_CFG`.

**Phase 3 - TD_Side_CFG trim.** 846 -> 98 lines. Kept the 9 declarations with
real word-boundary references from the IP spine: `restrict_local`/`_global`
(+ join/mono lemmas), `restrict_combine`, `side_env`, and the generic
`trans_dep\<^sub>L_step_in`/`_trans` (the plan's quintet list omitted these two,
but they are quintet-free and consumed by `TD_Side_IP_Soundness` - the build
caught it). The high apparent ref-counts on `side_cfg_T`/`side_acc`/`side_glob`
were substring matches of the `_ip` variants, not real uses.

**Phase 4 - retire com.** Deleted the `com` datatype from `IMP2_Syntax` and the
`com` small-step (relation, lemmas, `inductive_cases`, `code_pred`) from
`IMP2_Expr`, keeping `aval`/`bval`. `pcom` (separate constructors
`PSKIP`/...) is now the sole command language.

**Rename (follow-up slice, same branch).** Done by host `sed` + per-step build
gate (the mechanical change is safer with `sed` than the desync-prone I/Q):

- `pcom -> com` (datatype + all uses, incl. qualified `pcom.induct` etc.).
  Verified no collisions (nothing live was named `com`) and no stray substrings.
- `compile_pcom -> compile` (the plan's intended compiler name; `compile` was
  freed by the Phase 2 `IMP2_to_CFG` deletion).
- Constructors `PSKIP/PAssign/PSeq/PIf/PWhile/PScope/PCall/PRestore ->
  SKIP/Assign/Seq/If/While/Scope/Call/Restore` (and the derived `pstep` rule
  names `PSeqSE -> SeqSE`, `PIfTrue -> IfTrue`, ...). The `If` constructor
  coexists with `HOL.If` (as the old `com` already did); build is clean.

**Still deferred (deliberately):** `pstep`/`psteps`/`compile_prog`/
`cfg_collect_ip`. The plan leaves their targets as `...`; the obvious drops
collide (`cfg_collect_ip -> cfg_collect` clashes with the live generic
`cfg_collect`; `pstep -> step` clashes with `star.step`), so they need chosen
names and are best left as their own reviewed slice. They are unambiguous as-is.
