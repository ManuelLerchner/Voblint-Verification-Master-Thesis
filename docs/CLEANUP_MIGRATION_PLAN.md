# Cleanup migration plan

Execution plan for `docs/EXPORT_SURFACE_AUDIT.md`. That document is the evidence;
this one is the sequence. Every item names its gate and its risk. Line figures
come from the audit and are measured unless marked *est.*

## Ground rules

**The tree moves.** Three commits landed during the audit itself, one of them
(`8e78f3a6`) touching all nine `*_Ctx_*_Sound.thy` files that Phase 5 wants to
merge. Assume concurrent work: take one phase at a time, rebase before starting,
and prefer batches that touch a directory the other worktree is not in.

**`.thy` edits go through I/Q, never host tools.** That is a project rule, and it
means every Isabelle work item is an interactive session, not a scripted sweep.
The non-`.thy` work (docs, `scripts/`, `.github/`, `cli/*.ml`) has no such
constraint and can proceed in parallel with host tools — see the split below.

**Three gates, in increasing cost.**

| Gate | Cost | Proves |
| --- | --- | --- |
| `pixi run codegen-check` | ~minutes | nothing deleted was reachable from an export root |
| `pixi run codegen-modules` | seconds | the module map still covers every contributing theory |
| `AFP=... pixi run build` | slow, whole tree | the change is actually done |

**Batch by session, because the build is transitive.** The session graph is
`VIMP -> CFG -> Core -> Analysis -> {Soundness, CLI} -> Codegen -> Examples`.
A deletion in `Core` rebuilds Analysis, Soundness, CLI, Codegen and Examples; one
in Examples rebuilds nothing. So: **collect all deletions for a session into one
commit and one build**, and work downstream-to-upstream within a phase so the
expensive builds happen once each.

**What can start today without Isabelle.** Roughly 40% of the audit is outside
`.thy` files: Phase 1 (CI and gates), Phase 4 (documentation), the `cli/*.ml`
half of Phase 3, and the `docs/history/` move. None of it needs I/Q, none of it
can break a proof, and Phase 1 protects everything that comes after.

## Phase 0 — the correctness fix

**0.1 Bridge the CLI's well-formedness gate to its soundness premises.**
Audit §10.1. `cli/main.ml:536` gates on `wf_program_compile_input_exec`, which
unfolds to `wf_compile_input (storage_global p prog_main_name) ...`; every
soundness theorem assumes `wf_compile_input (declared_global p) ...`. No
corollary connects them.

- Where: `src/CFG/Compiler/Compile_Invariants.thy`, beside
  `wf_program_compile_input_exec_sound`.
- Shape: one corollary discharged by `storage_global_iff [simp]`
  (`VIMP_Notation.thy:90`), which already proves the two classifiers equal.
- Then: cite it from at least one CLI-facing soundness theorem so the connection
  is load-bearing rather than merely present, and add a regression that pins it.
- Gate: full build. Risk: low — the mathematics is already there.
- Size: ~15 lines. This is the only item in the audit that touches what the tool
  guarantees.

## Phase 1 — close the gates before changing anything behind them

Do this first. Every later phase is safer with these in place, and none of it
needs Isabelle.

**1.1 Add `grammar-check` and `codegen-modules` to `.github/workflows/ci.yml`.**
Audit §8.4. Verified absent. Consequence today: a hand-edited `.mly` or a
`grammar/vimp.yaml` change committed with `LEFTHOOK=0` reaches `main` green, and
`AGENTS.md`'s claim that the drift check runs "not only in CI" is false.

**1.2 Switch `codegen-check` and `grammar-check` from `git diff --exit-code` to
`git status --porcelain <dir>`.** Audit §8.4. `regenerate-codegen.sh` does
`rm -rf codegen/generated`, and `git diff` does not report untracked files, so a
newly emitted file passes silently.

**1.3 Make `codegen-modules` non-vacuous.** Audit §8.4. It reads the *checked-in*
export, so it is green on a stale one. Live example, found while writing this
plan: `a79862f3` added `src/Core/Solver/Context/DG/DG_Coverage.thy` with no
`code_identifier` entry, and `codegen-modules` passes because the checked-in
export predates it by three commits. **Benign today** — verified that
`DG_Coverage`'s constants are reached only from the Examples session, which no
export root touches — but the gate did not know that. Fix: have the job compare
the theory set contributing to the export against the `code_identifier` list, or
require a regeneration when any `src/**/*.thy` is newer than the export stamp.

**1.4 Widen the `.lefthook.yaml` glob for `codegen-module-map`.** It fires only
when the generated `.ml` or `Analyse_Dispatch.thy` is staged, so committing a new
theory alone triggers nothing.

**1.5 Delete the three dead scripts and the tracked artifact.** Audit §8.1.
`scripts/migrate_pcompletes.py` (targets five files that no longer exist — it
cannot run), `scripts/rename_greek_vars.py`, `scripts/extract_vimp_grammar.py`
(self-declared "feasibility prototype"; the question it asked is settled).
Gitignore `docs/generated/DEFINITIONS_OVERVIEW.md` (1.2 MB, tracked, and its own
generator's docstring says it should not be) and either wire
`extract_definitions.py --lint` to a pixi task or drop it.

## Phase 2 — delete the verified-dead, one session per commit

~6,200 lines. Every item is verified unreferenced with prose stripped. Order is
Examples first (rebuilds nothing) to Core last (rebuilds everything).

Per batch: delete, `codegen-check`, build, commit. A non-empty export diff means
something classified as dead was not — that is the point of the gate.

**2.1 Examples** — `Example_Sign_Codegen_Exec_Consistency.thy` and the
`Sign_Entry` demo lemma it pairs with (audit §2.1). Restate
`Example_Analysis_Result_Regression` and `Example_Int_Refinement_Mode_Regression`
over the routed `analyse_*_ctx_result_for` the CLI actually runs.

**2.2 CLI / Codegen** — `state_report_dot`, `is_bottom_abstract_value`,
`analyse_ctx` + its two lemmas (§11.1 — note it also *disagrees* with
`resolve_analysis_config` on `k = 0`, which is the argument for deleting rather
than keeping), and the seven unconsumed export roots (§2.4). Move
`Sign_Entry.thy:333-489` — 157 lines of demo programs and `by eval` lemmas, 32%
of the file — into the Examples session, where `src/CLI/ROOT`'s own description
says it belongs.

**2.3 Analysis** — **partly done; partly reclassified.**

*Done:* the five `Analysis_GraphViz` constants (60 lines, export byte-identical).
Each was a plain definition — two aliases, a constant `None` annotator, an
alias for `string_of_call_action`, and one config builder — occurring exactly
twice in the tree.

*Reclassified, and **not** mechanical dead code.* On reading them, the five
`*_DG` / `*_Base_DG` files do not belong in Phase 2 at all. §12.1 called them
"whole files with zero external consumers", which is true of their *names* but
misleading about their *content*: what they contain is unconsumed **theorems**,
not scaffolding.

- `Sign_DG` / `Int_DG` / `Interval_DG` carry terminal soundness claims
  (`<d>_dg_post_solution_collect_sound`, over `ltr_collect`) plus, in Sign's
  case, the `sign_dg_privatized` interpretation and three lemmas about the
  keep-all placement. `Example_Placement_Regression.thy:78` says it "validates
  concretely" the exact case that interpretation covers, and that example is one
  of the two the alignment register cites as evidence for the
  `gamma_unit` / `gamma_join` row.
- `Parity_Base_DG` / `Int_Base_DG` each export three `*_dg_spec_*_commute`
  theorems from a `context fixes gs` block. The inner `interpretation` really is
  inert (its facts never escape the context), but the theorems are not — they
  are proved, exported, and cited nowhere.

All five are therefore **decision #4**, not Phase 2. Retiring them deletes
stated theorems; keeping them means instantiating the abstract statements so
some concrete path reaches them. That is a judgement about what the project
claims, not a cleanup.

*Also deferred:* `congruence_fact_of_parity` and its `[simp]` exactness lemma
(9 lines) are genuinely unreferenced, but that lemma is precisely the proof that
parity embeds exactly into congruence — the evidence base for **decision #2**
(whether `int_parity` earns its place in `int_dom`, worth ~250 lines). Deleting
9 lines to destroy the evidence for a 250-line decision is a bad trade. Resolve
decision #2 first.

*Still open in 2.3:* the four proved-never-consumed lemma families
(`fun_of_st_top_<D>_st`, `<D>_tf_st_for_reduces`, `update_*_{exact,le}`,
`first_deciding*`). These need the same read-before-delete treatment: check
whether each is scaffolding or a stated result.

**2.4 Soundness / CFG** — §10.2: `intra_successors`, `cone`, `collect_result`,
`com_stmt_order` + its four lemmas, `frames_match` and its six-lemma inversion
suite, `control_at_call_edge`, and the unconsumed `CFG_Prune` chain. Decide
`wf_cfg` separately (Phase 6).

**2.5 Core — one commit, one build.** §9.1 and §13.1, ~3,500 lines. The four
large severable blocks first: the non-strict `placed_dg_*` family (668, verified
no proof cites it), `Exec_Backward`'s `_st_lift` layer (~480),
`Solver_Side_RG`'s always-join half (176), the `assemble_local_global`
subsystem (~173). Then the locales nobody interprets
(`td_cfg_side_solver_dg` 104, `unit_routed_context_hetero` 76, the two
`resolved_st` refinement locales ~150), the two never-used type classes
(`bounded_widening`, `bounded_narrowing`), `widen_state`, `SPIKE_sup_fin_eval`,
and the ~30 smaller items.

Two judgment calls inside this batch, not mechanical:
- `afilter_st_lift_correct` / `bfilter_st_lift_correct` are named *correctness*
  results. Deleting them removes stated theorems, not scaffolding.
- `Exec_Refinement.thy` has zero external references but eight `[simp]` lemmas
  that may fire implicitly. Settle it by stripping the tags and rebuilding
  before deciding.

**2.6 Retire the Base analysis stratum.** §2.1. Delete `Sign_Exec_Sound.thy`;
rehome the live `int_tf_for` / `int_tf_st_for` / `int_dom_enter_st_for` out of
`Int_Exec_Sound.thy` into `Int_Transfer` / `Int_Exec` beside their Sign and
Parity counterparts; reduce `Interval_Exec_Sound.thy` to whatever survives 2.1.

## Phase 3 — the three things that are wrong, not merely stale

**3.1 One node, two names.** §8.5a. `string_of_cfg_node` renders
`FunctionResult p` as `result_p`; `graphviz_point_label` renders it `exit_p`. Fix
in HOL, add a lemma pinning the two label functions together so it cannot drift
again, add `string_of_cfg_node` to the export roots, and delete the third
hand-rolled copy at `cli/main.ml:153-156`.

**3.2 `--dot-full` silently ignored.** §8.5b. Byte-identical branches under
`--context call-string` and `--context-graph expanded`. Either implement it or
reject it — the CLI's own policy elsewhere is to reject, not fall back. Collapse
the four-way chain into one helper while there; it is written out four times,
which is why the omission was invisible. Add a CLI regression.

**3.3 `publish_seed` encodes the opposite convention from the code.** §9.1.
Definition puts the payload in the `globs` half; `Routed_Context` writes it in
`locals` and `routed_extra_g` reads it back from `locals`. It is dead, its
`_cont` twin is dead, both are textually identical to their `publish_global`
counterparts, and the 20-line doc block above them asserts the wrong convention
twice. Delete the pair and fix the comment.

## Phase 4 — documentation (no Isabelle needed; can run in parallel with Phase 2)

**4.1 Make rename-rot a build error.** §5.1. Convert
`\<open>name\<close>` / `\<^verbatim>\<open>name\<close>` prose references to
`\<^const>\<open>name\<close>` in `Voblint.thy`, `Run_Analysis_Sound.thy` and the
`Exec_DG_*` theories. This is a `.thy` edit, so it needs I/Q — but it converts a
whole class of silent rot into a checked failure, and 44 already-dangling names
will surface as build errors to be fixed with it.

**4.2 Fix the four documents that misdescribe the live system.**
`CHECK_ARCHITECTURE.md` (routes through the retired Base family and a
`<domain>_exec_prog_at` constant that does not exist), `AGENTS.md`'s module map
(twelve `*_dot_auto` that do not exist; "four modules" where the export emits six)
and domain roster ("Sign, Interval, then Octagon" — the tree has four analysis
domains plus Congruence), and `docs/INDEX.md` (omits the living register).

**4.3 `git mv` the ~42 superseded docs to `docs/history/`** and rewrite the 51
path-stale citations. Two need a content edit rather than a move
(`03-recursion.vimp:9`, `NEXT_STEPS.md`). Rename
`PROCEDURE_AWARE_CFG_MIGRATION.md`, which is living, so the `*_MIGRATION.md`
suffix stops meaning two things. Delete the three that are wrong as references
rather than historical: `LOCALES.md`, `PIPELINE_AST_TO_SOLUTION.md`,
`ARRAY_SYNTAX_EXTENSION.md`.

**4.4 Regression corpus.** §8.3. Fix the one genuine duplicate
(`06-reachability` 03/05); move `17-call-string/precision/01` to
`known-imprecision/` (every check UNKNOWN, mechanism already named in its own
header); split the nondeterministic check out of
`05-checks/precision/01`; give the two recursion cases a real mechanism comment
instead of delegating to docs and to each other; rewrite
`03-procedures/precision/09`, which describes a *fixed* defect in the present
tense; fix the two fixtures citing siblings that do not exist and the two
claiming "the only two fixtures with an EXPECT-GRAPH block" when there are 26.

## Phase 5 — unification, highest value first

~7,600 lines *est.* Read these as upper bounds: the dead column in Phase 2 is a
commitment, this one is a projection that assumes each locale refactor goes
through cleanly.

**5.1 U1 — one Core locale for `<D>_Ctx_None_Sound`.** *est.* −1,930 across four
domains. Strongest evidence in the audit: after normalising the domain name,
**377 of 458 lines identical, zero obligations differing, zero proof steps
differing** (re-measured after `8e78f3a6`). The locale fixes four things
(executable transfer mirror, executable enter, abstract transfer record, initial
store) and assumes exactly the four facts each domain already proves. **The
pattern already exists one axis over** — `ictx_solved`
(`Interval_Ctx_None_Sound.thy:152`) factors the *solver* axis this way, with four
`global_interpretation`s over one locale. Do Sign+Parity first as a two-domain
proof of concept, then Interval and Int.

*This is the one item that changes the shipped artifact.* Collapsing the four
identical `gk` datatypes into one `'c gk` removes `gka`/`gkb`/`gkc` and their
`equal_gk*` from the generated OCaml. Land it as its own commit so
`codegen-check` stays a clean signal everywhere else.

**5.2 U5 — collapse the `refine_mode` triplication.** *est.* −600. Byte-verified:
`diff` of `Int_Backward.thy:1022-1210` against `:1211-1399` after substituting
the mode token returns **zero lines**. `Int_Exec.thy` is 332 of 381 lines in
three copies. Every proof already cites lemmas stated uniformly in `mode`; the
only thing forcing the copy is that `global_interpretation` needs ground
arguments for `defines`. One `int_dom_backward_refined_mode` lemma plus three
thin interpretations.

**5.3 The Entry-file locale.** *est.* −1,000. §11.2. Ten of twelve corollaries
are character-identical modulo the domain token, and the generic lemma the bundle
needs already exists (`Sign_Checks.thy:191` re-exports it). Two free wins first,
needing no locale: convert Sign's redundant `proof ... show ... qed` blocks to
the `[OF ...]` form the other three domains use (**−48 lines, no semantic
change**, and it explains 59 of the 71 lines separating Sign from Parity), and
move the demo block out (2.2 above).

**5.4 `Compile_Locality`'s `frag_local_succ`.** *est.* −265. Ten `intra`/`calls`
lemma pairs, diffed: the two largest are 169 and 149 lines for one argument each.
Every lemma touches an edge only through its source and its landing node. The
projection that collapses them **is already in the tree as the dead one** —
`cfg_succ_rel`'s INTRA ∪ COMB_CALLER half (§10.2). Widening it turns a dead
definition into the load-bearing one.

**5.5 `Control_Simulation`.** *est.* −330 of 2,507. `control_at_descend` absorbs
the six-fold `control_at_*_edge` family (what its inductive cases need is pure
monotonicity of the witness in the edge sets — nothing case-specific);
`csim_Nested_lift` absorbs a byte-identical ~10-line tail from four
`csim_*_completion` theorems; `head_of` collapses the three spine classifiers and
the eighteen `seq_after_eq_*_iff` statements together.

**5.6 U3/U4 — `<D>_Transfer` tails and `<D>_Exec`.** *est.* −430. `Numeric_Ops`
already has the right record and its own header diagnoses the duplication; it
stops before the expensive case (the 8-equation `fun <D>_tf_st_for` and its
commute theorem, hand-written four times). Add `n_special` to `numeric_ops` and a
`generic_tf_st_for` + commute theorem.

**5.7 U6, U7 and the Core/Domain items.** *est.* −750. `Int_Backward`'s
five-operator wrapper layer (222 -> ~45); `is_bot_pred` as false abstraction
(~180 — but check first whether the parameter is hoisting
`declared_global_vars p` out of the executable loop, in which case the fix is a
`[code]` equation with a `let`); the three isomorphic `'a lifted` towers
(~240, a real refactor since `fun` pattern matching must be rewritten); the
5 × 5 `inv_*` block (94 -> ~20); the duplicated
`semantic_intersection` / `derived_eq_false_from_intersection` locale (~23); the
four-plus-one masking definitions, where the bridging lemma between
`merge_state` and `combine_env_abs` **does not exist** and their absence is what
lets two masking algebras drift apart in separate soundness proofs.

**5.8 The `_gen`/base folds and the `_lifted` mirror.** *est.* −380. Lowest
value; do last.

## Phase 6 — the register, and the decisions it needs

**6.1 Correct the drifted rows.** §4, §9.3, §10.4, §11.5, §12.4, §13.3.
Highest-value corrections: the source language is VIMP, not IMP2, and the AFP
IMP2 bridge the "why it exists" column rests on **does not exist**;
`combine_env`/`combine_assign` are two `dg_spec` hooks, not a composition;
`input()`/havoc is implemented, not planned; the `D`/`G` payload split has landed
at the type level and what is actually true is the narrower "no live instance
varies the parameter"; `point_digest`/`ENTER_MONO`, cited as the closure path,
occur nowhere in `src/`; M1 landed.

**6.2 Add the rows that do not exist.** No row covers the **value-domain axis**
(zero occurrences of `IntDomain`, `congruence`, `parity`, `ikind`, `overflow`),
the **configuration surface** (a closed 3-field record and a 40-branch resolver
against Goblint's open registration list), `EA_Special` moving library calls onto
`intra` structurally at compile time, the missing `sync` hook — which matters
because the publication-timing row proposes a publish-on-unlock example and there
is no hook at which one could fire — the single global unknown carrying every
program global, the context selector never seeing the resolved callee, and the
absence of `startstate`/`exitstate`/`morphstate`.

## Decisions needed before some of the above can start

1. **The Isabelle DOT emitter** (§2.3). ~313 lines that no shipped artifact runs;
   its only consumers are eight `value`-printing example theories. Keep it and
   say so plainly in the theory text, or move the figures to the CLI and delete
   it. Blocks nothing, but the current bookkeeping — `AGENTS.md` advertising
   twelve `*_dot_auto` that do not exist — should not survive either way.
2. **`int_parity` inside `int_dom`** (§12.4). Parity is congruence with modulus
   pinned to 2, both directions of the embedding are already proved in the tree,
   and Goblint has no parity domain. The open question is whether any forward
   operation makes the parity component strictly more precise than the congruence
   one. A `nitpick`-scale check settles it; if not, removal takes ~250 lines of
   Product plumbing. Independent of `Parity_Analysis` as a standalone domain,
   which stays.
3. **`wf_cfg`** (§10.2). Proved for every compiled program, assumed by no
   soundness theorem. Either wire it into a premise where it belongs or retire it
   and its four uncited consumers.
4. **The `<D>_DG` LTR route and the `*_Base_DG` commutation theorems**
   (§12.1, ~1,000 lines across five files). Real theorems that no concrete path
   reaches — the instantiation gap in reverse. Keep and instantiate, or retire.
   Note the coupling: retiring `Sign_DG` also removes `sign_dg_privatized`,
   which `Example_Placement_Regression` is written against and which the
   alignment register's D/G-reconstruction row leans on. Widened from 429 lines
   after reading the files during Phase 2.3.
5. **The two placement examples** (§7.4). 3,861 lines carrying evidence the
   register genuinely cites. Not deletable, but ~1,500 of it is framework work
   misfiled as an example. Hoisting §7.4(a)'s lemma triple into
   `Exec_DG_Refines` is the tractable first step.

## One precision fix, separate from all of the above

`int_dom_min_raw` / `int_dom_max_raw` set three of four components and leave
`int_congruence` at `top`, where `plus`/`minus`/`times_int_dom_raw` all set four
(§12.3). `int_congruence := sup (int_congruence a) (int_congruence b)` is equally
sound and strictly more precise, and the join lemmas it needs are already proved.
Per the project's regression discipline this needs a `by eval` witness in
`Example_Int_Domain.thy` pinning the improved value, not just the code change.
