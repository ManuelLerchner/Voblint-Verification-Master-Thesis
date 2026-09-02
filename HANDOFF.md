# Handoff: Core cleanup, `core-cleanup` branch

Status as of 2026-09-01 (later same day than the previous version of this
file). Read `docs/CORE_REFACTOR_PLAN.md` first -- this file is a
session-scoped pointer into it, not a replacement. Its own decision log
(`## Decisions and corrections`) has the full rationale for everything below;
this file only says what to do next.

## What landed this session

Six commits on `core-cleanup`, all batch-green, none pushed. The first three
are the same as the previous version of this doc recorded (`2bf029be`,
`56d2f38a`/`4e9a30e5`, `58645233`); three more landed after a four-agent
architecture audit (Solver boundary, `_at` cleanup, Goblint manager
comparison, Phase 2.7 Exec classification) that this doc's own previous
"What's next" section triggered:

4. `905026ea` -- Track A closed: `dg_edge_tree`/`dg_combine_tree`
   (`DG_Constraint_Trees.thy`) are now literal specializations of
   `dg_edge_tree_at`/`dg_combine_tree_at`, not independent `do{}` bodies.
   The "Edge/Combine formers over a solution address" subsections now come
   first in the file; every bare-form characterization lemma is a one-line
   corollary of its `_at` counterpart.
5. `e4ae0177` -- `Voblint_Solver` now owns the generic bridge from the
   vendored TD solver to `part_post_solution`: `TD_Solver_Menu.thy` moved from
   `Voblint_Exec`; `Solver_Side_RG.thy`'s `solve_dom_of_solve_c` (30+
   external citers -- its only fact cited outside its own file) folded in
   alongside it. 19 files retargeted their imports.
6. (pending final commit as this doc is written; verify with
   `git log --oneline -5` before starting new work) -- `Solver_Side_RG.thy`
   deleted whole (confirmed 100% dead by pattern, not just name, after
   `solve_dom_of_solve_c` left it -- this also refuted
   `EXPORT_SURFACE_AUDIT.md`'s claim that its warrowing-apinis half was
   "live via `Interval_Warrowing.thy`": that was a prose mention, not a
   citation). 11 dead lemmas deleted from `Result_Normalization.thy`
   on the same evidence standard. Two now-dead lemmas in
   `Interval_Warrowing.thy` (`ivl_widen_bot_bot`/`ivl_narrow_bot_bot`, whose
   only purpose was feeding `Solver_Side_RG`'s now-deleted invariant) went
   with it. Eight files' prose fixed where it named a lemma that no longer
   exists.

Full rationale, citation evidence, and the exact file list for all three
audit-driven commits: `docs/CORE_REFACTOR_PLAN.md`'s decision log, entry
dated 2026-09-01 "later same day" (right after the seeded-refinement entry).

The manager question was **re-audited against a real clone of
`goblint/analyzer`** (not memory, unlike the first pass) and reconfirmed:
**A -- no manager needed.** `dg_spec`'s fields still receive values, never
solver addresses, and every Goblint `man` capability maps cleanly onto one
of three existing Voblint mechanisms (curried args / the monadic
`QueryG`/`Side` primitives / locale-fixed policy). One honest new gap: real
Goblint `man.split` (multiple successor states + events from one transfer
call) has no Voblint equivalent, and this is a genuine scope limitation, not
merely an encapsulation gap -- noted for the future, not acted on now, since
no current VIMP transfer construct needs more than `tf_branch`'s binary
split.

**Not a scoped or acted-on task, but a live finding worth knowing about:** a
background prototype (`src/Solver/Scratch_CPS_Prototype.thy`, untracked,
not in any `ROOT`, not committed) tested whether a CPS-encoded typed
frontend (`strategy_program`, parametric in a fourth `'a` result type, with
`sp_return`/`sp_bind`/`sp_global`/`sp_local`/`sp_sideg`/`sp_run` compiling
down to the unmodified vendored `strategy_tree`) is workable. It is: every
lemma attempted -- including genuinely polymorphic intermediate types
(`bool`, a record) threaded through `sp_bind` before finally producing a
`'d` -- discharged by trivial definitional `simp`, no `induct`/
`sledgehammer` anywhere. This would be the foundation if a future session
decides a Goblint-shaped `man.global`/`man.sideg` surface (Option C from
that design conversation) is worth building -- it is not currently
authorized or planned work, just a de-risked option sitting in a scratch
file for whoever picks it up next.

## What's next

`docs/CORE_REFACTOR_PLAN.md`'s own phase table, in the order it lists them:

- **2.7** -- now partly landed (see above); what's left: `DG_Coverage.thy`
  (confirmed fully generic Core/DG content, stranded in `Voblint_Exec` only
  by importing `Exec_DG_Generator.thy` for `dg_gen_of`) needs `dg_gen_of`/
  `dg_reader_commute_gen` extracted from `Exec_DG_Generator.thy` first --
  that file has not been audited in full by anyone yet, unlike everything
  else touched this session. `DG_Local_State_Exec.thy`/`routed_dg_domain_exec` and
  most of `Result_Normalization.thy` do **not** move -- they are the
  executable-carrier transport itself (bridging `resolved_st_q`/
  `exec_dg_st` to the abstract framework), not misplaced generic content,
  and stay put until Phase 2's own deferred quotient-carrier restatement
  happens. `Voblint_Exec` does not dissolve from this round.
- **A real but separate consolidation opportunity, not part of 2.7's
  original wording**: the 12 `Analysis/Instances/**/Ctx/*_Sound.thy` files
  each independently re-derive the same `solve_c -> solve_dom ->
  part_post_solution` three-step bridge per domain per update rule. This
  needs a new parametrized lemma/locale (taking a domain's `eqs`/
  `_terminates_c` fact as a parameter), not a move -- real proof
  engineering, scoped but not started.
- **3.3** -- retire `metis`: `Activation_Local_Sound`'s 10 uses and
  `Routed_Domain_Exec`'s 14 first, per the plan doc's own count.
- **3.4** -- hoist `dg_post_solution_postfix` (272 lines) and
  `side_cfg_T_eff_keyed_seed_dg_buffered_correspondence` (249 lines) into
  helper lemmas with named subgoals.
- **3.7** -- run the session-cleanup playbook's style script and update the
  compliance table in `docs/SESSION_CLEANUP_PLAYBOOK.md`.

## Process notes worth keeping in mind

- **Always confirm a diagnostics-clean I/Q edit actually reached disk**
  before trusting it, especially right before a `git rm` of a file the edit
  touched. `mcp__isabelle-iq__list_files`'s `is_modified` field is the
  check.
- **Never call `save_file` with no path** while a file you've `git rm`'d is
  still open in I/Q, or while any other buffer is legitimately mid-edit
  (e.g. a background agent's scratch file) -- a bare `save_file()` saves
  *every* modified buffer, not just the one you mean.
- **Line-range `write_file` edits (`command: "line"`) use line numbers from
  your last read, not from the live buffer.** This session lost a
  function's own definition clauses this way: a big block deletion was
  off by two lines because the read used to compute the range and the edit
  applied to the buffer had drifted (a Bash `sed`/`cat` read of the file on
  *disk* was used to plan a deletion inside content that had already been
  edited but not yet saved -- disk and buffer disagreed). Fix: re-read the
  *exact* range immediately before a `line`-mode deletion using I/Q's own
  `read_file` (which reads the live buffer), never a Bash read of the file
  on disk, if any prior edit in the session might not be saved yet.
- Full batch build (`AFP=$HOME/afp/thys pixi run build`) is the only real
  completion gate; I/Q diagnostics are necessary but not sufficient. Budget
  roughly 5-10 minutes for a full run.
- When a citation-trace-based deletion is proposed, check the *pattern* a
  `[simp]`-tagged fact rewrites, not just its lemma name -- name-grep alone
  would have missed nothing this session, but it's the check that would
  have caught it if there had been a live implicit user.
