# Proof hygiene — skill-compliance audit and migration plan

> **Status:** All stages (0–7) complete and batch-verified (`TD_Side_CFG.thy`,
> `Constraint_System.thy`/`Split_State.thy`, `DG_Soundness.thy`/
> `DG_Ctx_Activation.thy`, `Sign_Local_Effects.thy`,
> `Sign_Named_Global_Eff.thy`/`Interval_Transfer.thy`/`Rel_Order_Domain.thy`/
> `Interval_Lattice.thy`, `CFG/VIMP_Proc_to_CFG.thy`/
> `CFG/Compiler/Compile_Locality.thy`, `Abstract_Domain.thy`/
> `Sign_Transfer.thy`). Stage 4 (`Exec_Bridge.thy`, `TD_Side_Eff_Bounds.thy`)
> checked and found to need no further changes — both already cite Stage 1's
> lemmas and their remaining `unfolding` sites are one-time definitional
> proofs, not re-derivations. Stage 1 also surfaced and fixed a real
> regression (a `[simp]`-tagged distributive law competing with a specific
> combine lemma's normal form) via confluence restoration rather than a
> revert; see Stage 1's writeup for the full mechanism and the durable lesson
> now in `AGENTS.md`. The migration's stop condition (§6) is met: every
> high-density core file identified in §3.2 went through Stages 1–6, Stage 7
> swept every remaining file's `unfolding` density for the anti-pattern
> signature and fixed the two real hits found, and the rest are one-time
> definitional proofs or already-canonical characterization lemmas. Two
> rounds of external review are incorporated below. Round 1
> adjusted the exit criterion's "every definition" language (§7), immediate
> vs. usage-driven tagging (§5, §6), and the Stage 1/2 order (§6) —
> lowest-risk file first to validate the workflow before touching the
> foundational core. Round 2 added a concrete "tag justified" threshold and
> `[intro]`-caution note (§5), a definition-interface template (§5), a
> semantic-documentation requirement for exported definitions (§5, §7), a
> warning-baseline discipline alongside the existing timing regression check
> (§5, §7), and an explicit migration stop condition (§6).

**Question answered here:** does the current theory tree follow the
proof-engineering skills' rules on definitions, theorem tagging, and proof
style, and if not, what changes bring it into alignment without inflating
scope? **Partially.** Documentation, proof structuring, import hygiene, and
statement shape are already compliant. Two independent gaps survive: near-zero
classical-reasoner tagging paired with heavy `unfolding`-based re-derivation,
and (originally reported as 50, corrected to 63 — see §3.3) implicit-method
`proof` steps in exactly the theorems this repo calls its semantic anchors.
The second gap is now closed (Stage 0, §6).

---

## 1. Method

Static `rg` audit over all 111 `.thy` files under `src/` (676
`definition`/`inductive`/`fun`/`abbreviation`, 1576 `lemma`/`theorem`/
`corollary`), cross-checked by reading the worst-offender files directly
rather than trusting raw counts. One noisy signal (object-level quantifiers in
statements) was caught and retracted during the pass — see §2.

## 2. Compliant areas (no action needed)

| Rule | Evidence |
| --- | --- |
| Structured Isar over `apply` scripts | 863 `proof` commands (337 `proof -`, 423 `proof (method)`, 50 bare) vs. 50 `apply` lines |
| `fixes`/`assumes`/`shows` over object-level quantifiers | 0 lemma/theorem statements have an object-level `\<forall>`/`\<exists>` as the outer connective. (Raw grep for `\<forall>`/`\<exists>` anywhere in a file returns 216/170 hits, but those sit inside definition bodies, e.g. `local_bot_on_locals`, not theorem statements — a precise recheck restricted to the string immediately after `lemma name:` found zero.) |
| Session-qualified imports, no absolute file paths | All imports use `Voblint_*.X` / `TD.X` qualifiers; 0 raw file-path imports |
| `section`/`subsection`/`text` exposition | Present in all 111 files, none empty (541 section-level headers, 732 `text` blocks) |
| No leftover exploration commands | 0 stray `sledgehammer`/`try0`/`find_theorems`/`find_consts`/`nitpick`/`quickcheck` in committed theories |
| `simp`/`auto`/`blast` preferred over `metis`/`smt` | 2293/943/537 vs. 78/2 |
| Batch-completion discipline | 0 `sorry`, 0 `oops` anywhere |
| Locale use | 16, proportionate to the codebase's actual context/activation complexity |
| AFP/library reuse | No AFP imports beyond `HOL-IMP`; consistent with the locked decision to vendor the `TD` solver (`docs/AFP_IMP2_REUSE_DECISION.md`). Lattice/order reuse already happens via stdlib typeclasses (`bounded_semilattice_sup_bot`, etc.), not hand-rolled order theory. |

## 3. Findings

### 3.1 Classical-reasoner tagging is near-absent

`[intro]`/`[intro!]`/`[intro?]`: **0** hits repo-wide. `[dest]`/`[dest!]`/
`[dest?]`: **0** hits. `[elim]`/`[elim!]`: 15 hits, 12 of which sit in one file
(`IMP2/VIMP_Proc.thy`, carried over from the AFP IMP2 base — genuinely
original code contributes only 3). `[simp]`: 120. Against 676 definitions,
that is effectively zero classical-reasoner coverage.

This directly contradicts "prove relevant properties of the definitions
first, including intro/elim/dest/simp rules" and "correctly classify rules for
the classical reasoner."

### 3.2 `unfolding X_def` used instead of definition properties

740 occurrences of `unfolding ..._def` across the repo — the exact
anti-pattern the rule names ("avoid unfolding definitions in proofs, prefer to
use the properties of the definitions instead"). Concentrated in the shared
Solver/Domain/Equations core, not the periphery:

| File | `unfolding …_def` hits | What was actually found on inspection |
| --- | --- | --- |
| `Analysis/Generic/Solver/Core/TD_Side_CFG.thy` | 62 | Characterization lemmas **already exist** for the most-unfolded names (`restrict_local_global_join`, `restrict_local_mono`, `local_bot_on_locals` closure under `sup`) but are untagged, so proofs re-derive by unfolding anyway at typed call sites (e.g. lines 479, 481) instead of citing them. |
| `Analysis/Generic/Solver/Context/DG/DG_Soundness.thy` | 41 | `gamma_dg`/`dg_gamma`/`gamma_unit`/`dg_G`/`dg_D`/`dg_cmb` — no companion lemma found before repeated unfolding. |
| `Analysis/Instances/Sign/Sign_Local_Effects.thy` | 35 | Same shape as `DG_Soundness`. |
| `Analysis/Generic/Solver/Exec/Exec_Bridge.thy` | 30 | |
| `Analysis/Generic/Solver/Core/TD_Side_Eff_Bounds.thy` | 29 | |
| `Analysis/Generic/Equations/Constraint_System.thy` | 26 (23 definitions) | `wf_split`/`merge_state`/`split_state`/`abs_join_set`/`glob_env`/`gamma_state` unfolded directly at call sites. |
| `Analysis/Generic/Domain/Split_State.thy` | 25 | Same core definitions as `Constraint_System`, re-unfolded downstream. |
| `Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy` | 24 | |
| `CFG/Compiler/Compile_Locality.thy` | 23 | |

These nine files account for roughly 40% of all unfolding sites and sit
underneath every domain instance (Sign, Interval, Mixed) — fixing them has the
highest leverage per line changed.

**Root cause:** definitions get some hand-proved facts, but rarely a
systematic tagged simp/intro/elim/dest kit at introduction time. Downstream
proof authors then re-derive the same fact via `unfolding` instead of reusing
it (`TD_Side_CFG.thy`), or because no reusable fact was ever proved
(`DG_Soundness.thy` and the `Constraint_System`/`Split_State` cluster).

### 3.3 Implicit-method `proof` (63 sites, corrected from 50)

The style guide is explicit: "do not use implicit proof methods in `proof`;
use `proof -` or `proof <method>`." The original count here was produced by
`rg -n '^\s*proof\s*$'`, which only matches a bare `proof` alone on its own
line. It silently misses `instance ... proof` and `interpret X ... proof`
written on a single line — a common shape in this repo's typeclass instance
and locale-interpretation proofs. The corrected pattern,
`rg -noP '(?<![\w.])proof(?=\s*$)'`, found 13 additional real sites (2 false
positives inside `text` blocks excluded) across `Exec_St.thy` (+3, on top of
the 6 already counted), `Sign_Lattice.thy` (+4), `Interval_Lattice.thy` (+3),
and one file the original sweep missed entirely, `Interval_Warrowing.thy` (1).
63 real sites total, all fixed as of this pass (Stage 0 complete). They were
concentrated in the theorems this repo's own `CLAUDE.md` names as semantic
anchors:

| File | bare `proof` count |
| --- | --- |
| `CFG/Collecting/LTR_Abstract.thy` | 10 (includes steps inside `valid_ltr_subset_gamma_ltr`, `activation_collect_subset_acc`) |
| `CFG/Collecting/CFG_Local_Trace.thy` | 9 |
| `Analysis/Generic/Domain/Exec_St.thy` | 9 |
| `CFG/Compiler/Control_Simulation.thy` | 5 |
| `Analysis/Instances/Sign/Sign_Lattice.thy` | 6 |
| `Analysis/Instances/Interval/Interval_Lattice.thy` | 5 |
| 19 other files | 1–3 each |

Bare `proof` silently applies whichever single introduction rule Isabelle
picks as default — it is not purely cosmetic the way `proof -` (which opens no
goal-changing step) is. Each site needs its actual applied rule checked before
it can be made explicit, so this is mechanical but not a blind
search-and-replace.

### 3.4 Duplicate-fact build warnings

*Pending: a forced clean rebuild of all five sessions is running to surface
real compiler warnings (cached build logs were empty — heaps were already
warm, and `isabelle build` does not re-emit warnings for up-to-date sessions).
This subsection will be filled in with concrete file/theorem evidence once
that build completes.*

## 4. Approaches considered

**A — whole-repo pass.** Tag every existing characterization lemma across all
111 files, then chase all 740 unfolding sites and all 50 bare-`proof` sites in
one sweep. Rejected: touches nearly every file at once, `[simp]` tagging can
loop or silently change other proofs' automation elsewhere, and it cannot be
verified incrementally — violates this repo's own batch-gate discipline ("add
material incrementally," "isolate hard obligations") and its scope-discipline
rule.

**B — targeted, ordered by leverage and risk.** Fix the lowest-risk file first
to validate the recipe (`TD_Side_CFG.thy` — characterization lemmas already
exist, so the stage is mostly tagging plus call-site rewrites), then the
foundational-but-dangerous core (`Constraint_System.thy`/`Split_State.thy`,
which every downstream instance imports), then the architectural core
(`DG_Soundness.thy`), then the remaining density-ordered files. Leave
low-density files (`Examples/*`, single-digit counts) as backlog. Bounded,
reviewable diffs; matches the existing workflow; risk-controlled order so a
bad tag is caught on the file where it's cheapest to diagnose, not the one
where it's most expensive.

**Recommendation: B.**

## 5. Tagging safety protocol

Adding `[simp]`/`[intro]`/`[dest]` is not risk-free. `docs/ISABELLE_AGENT_NOTES.md`
already names two of the five standard slow-build causes as tagging mistakes:
"a recursive `[simp]` declaration" and "a new `[intro]` or congruence rule that
triggers repeatedly." A `[simp]` or `[intro]` attribute changes the default
simp set / claset for **every downstream theory that imports the file**, so a
bad tag on a Stage 2 file (`Constraint_System.thy`, `Split_State.thy`) can
silently slow down or loop proofs in Sign, Interval, Mixed, and every example —
files that are never touched by the diff. This section is binding for every
stage below, not just a suggestion.

**Before tagging a lemma `[simp]`:**

- Confirm it is an oriented, terminating rewrite (LHS strictly more complex
  than RHS under the term ordering the simplifier already uses). Do not tag a
  lemma whose two sides are the same size/shape, an `iff` between two
  similarly-complex predicates, or anything resembling an equivalence written
  for readability rather than reduction.
- Check it does not overlap with an existing `[simp]` lemma on the same head
  symbol in a way that could rewrite in either direction (a classic loop
  source when two files each contribute one direction of an identity).
- Reject general existence/disjunction statements as `[simp]` — they expand
  the search space instead of reducing a term.

**Before tagging a lemma `[intro]`/`[elim]`/`[dest]`:**

- Check how many classical-reasoner calls (`blast`/`auto`/`force`) transitively
  see this file. A new intro rule that unifies broadly is exactly the
  "triggers repeatedly" case in the slow-build note; classical-reasoner search
  is combinatorial in the rule count, so the risk scales with how deep the
  file sits in the import graph, not with how it looks locally.
- Narrowness is not a fixed ranking of `[dest]` over `[elim]` over `[intro]`
  — it depends on the rule's shape. A structural intro for a simple inductive
  predicate (e.g. `wf a ==> wf b ==> wf (a, b)`) is cheap: its premises are as
  specific as its conclusion, so it does not widen search. An intro whose
  premise is a large invariant (e.g. `HugeInvariant x ==> ...`) pollutes
  classical search because `blast`/`auto` will try to prove that invariant
  speculatively at every matching goal shape. Judge each rule by what its
  premises force the reasoner to attempt, not by its `[intro]`/`[dest]`
  category alone.
- If a lemma is only needed at a handful of call sites, leave it untagged and
  pass it explicitly (`simp add: foo`, `intro: foo`) at those sites instead —
  this is the proof-development skill's own fallback ("manually pass the
  rules") for concepts that aren't worked with constantly.

**Tagging is usage-driven, not immediate.** A new characterization lemma does
not get a global attribute the moment it is proved. Sequence:

1. Prove the lemma untagged.
2. Cite it explicitly at its call sites (`simp add: foo`, `intro: foo`,
   `by (rule foo)`) while chasing the current `unfolding` site.
3. Tag once the lemma clears all of: cited explicitly in at least 3 unrelated
   proofs (different theorems, not repeats of the same proof shape), its
   rewrite/inference direction is the one every call site already wants (no
   site fights the direction), and step 4 of the procedure below shows no
   timing regression from the trial tag. Below that bar, keep it explicit —
   an occasional citation is cheaper than a global attribute nobody would
   have chosen from the usage pattern alone.

This avoids the alternative failure mode: proving a lemma once, tagging it
immediately on the assumption it will be canonical, and slowly accumulating a
simp set nobody would have chosen if the usage pattern had been visible
first.

**Definition-interface template.** Not every exported definition needs every
lemma below — this is a search pattern for what to look for, not a checklist
to fill in completely.

- Predicate: `foo_iff`, `foo_cases`, `foo_intro`, `foo_dest`.
- Function: `foo_apply` (unfolding one step, for recursive/pattern-matched
  definitions), `foo_mono`, `foo_cong`.
- Order/domain (lattice, gamma function, abstract state): `foo_bot`,
  `foo_sup`, `foo_mono`, `foo_gamma`.

**Semantic documentation.** Every exported definition, inductive, locale, and
non-trivial characterization lemma introduced or modified during the
migration gets a nearby `text` block stating its semantic role and any
non-obvious design choice — why this representation, not an alternative one.
Purely-internal helpers are exempt, same as the tagging exemption above.
Explain why, not what — restating the definition in prose is redundant with
the definition itself:

```isabelle
text \<open>
  The edge semantics separates executable transfer from feasibility
  checking. An assume edge does not modify the abstract state; it only
  removes states violating the guard, so failure is \<open>None\<close>
  rather than a dedicated error state.
\<close>
definition edge_step where ...

text \<open>
  Kept as the public interface instead of unfolding \<open>edge_step\<close>
  at downstream call sites.
\<close>
lemma edge_step_fail_iff: ...
```

**Warning-baseline discipline.** Duplicate-`[simp]` and similar Isabelle
warnings are the same failure mode as an unjustified tag, one step removed:
they mean two rules rewrite the same head symbol, or an attribute was added
that the simplifier already had covered. Record the baseline warning count
for a theory before a stage touches it; the stage must not increase it. If a
new warning appears, resolve it (drop the redundant tag, pick one canonical
rewrite direction) before moving to the next lemma — do not let migration
work itself accumulate the noise it exists to remove. §3.4 tracks the
repo-wide baseline audit this depends on.

**Procedure, every stage:**

1. Add characterization lemmas untagged first; confirm each proves in
   isolation.
2. Tag **one** lemma (or one small, semantically related group) at a time —
   never tag a whole file's worth of new lemmas in one edit.
3. Re-check the file itself in I/Q, then batch-build every session that
   imports it (for Stage 1, that is all of `Voblint_Analysis` and
   `Voblint_Formalization`, not just the local file).
4. Watch wall-clock time per theory during that build. Per the existing
   slow-build note, more than ~40s of silence on a warm heap signals proof
   search blow-up from the just-added tag, not a legitimate slow proof.
   Record the per-theory timing (`isabelle build -v` already prints it) for
   the file being tagged and its direct importers before and after the tag,
   not just a pass/fail read — a proof that still closes but got noticeably
   slower is a regression the binary gate misses. `isabelle build -v -v`
   additionally prints per-command timings if a single theory's slowdown
   needs to be localized to one proof. Compare the warning count from the
   same build against the pre-tag baseline (§5, warning-baseline discipline)
   — a new duplicate-simp or similar warning is a regression even when
   timing and the pass/fail result look clean.
5. On any regression (new failure, new timeout, a proof that previously took
   seconds now taking much longer, a materially larger simp/classical search
   recorded in step 4, or a new warning), revert that one tag
   (`declare foo[simp del]` or drop the attribute) before continuing — do not
   push forward and "fix it later." Diagnose which downstream proof's
   automation changed before retrying with a narrower attribute (e.g.
   `[dest]` instead of `[elim]`), a `named_theorems`-scoped rule set instead
   of a global one, or no attribute at all.
6. Only move to the next lemma once the full downstream build is green again,
   with no timing regression flagged in step 4.

This makes each stage slower per lemma but keeps blame isolated to one
attribute at a time, which is the entire point of doing this file-by-file
rather than as a whole-repo sweep (§4, Approach A).

**`named_theorems` for locally-scoped automation.** A global `[intro]`/`[simp]`
is not the only option. For rule families that only need to fire within a
specific proof cluster — the DG/context activation machinery is the likely
candidate, since its rules are shaped to unify broadly within that layer but
have no business firing in, say, an Interval domain proof — declare a
`named_theorems` set and tag into that instead of the global claset/simpset:

```isabelle
named_theorems dg_ctx_intros

lemma foo_intro [dg_ctx_intros]: ...
```

then call it explicitly (`blast intro: dg_ctx_intros`) or add it to a local
`simp`/`intro` call at the point of use, rather than to every `auto`/`blast`
repo-wide. This keeps the classical-reasoner search space bounded to the
layer that actually needs the rule, which matters most for exactly the files
this migration is most cautious about (§5 above, Stage 1/2 candidates).

## 6. Migration stages

Each stage ends in a green `isabelle-verify` batch build before the next
starts. Tagging is usage-driven per §5, not automatic on proof — a lemma
proved while chasing an unfolding site is cited explicitly first and only
tagged once its call-site pattern justifies it.

### Stage 0 — implicit-method `proof` cleanup — DONE

Files: `LTR_Abstract.thy`, `CFG_Local_Trace.thy`, `Exec_St.thy`,
`Control_Simulation.thy`, then the 19 single/double/triple-occurrence files
(count corrected mid-stage from 16 — see §3.3). Per site: identify the rule
the bare `proof` currently applies (via `get_state` on the open goal), then
rewrite as `proof (rule ...)`, `proof intro_classes`, `proof unfold_locales`,
or `proof -` as appropriate. Effort: low per site, moderate in aggregate (63
sites, corrected from 50 — see §3.3). Risk: low — purely disambiguating an
existing step, no new proof content. Highest priority because it sits in the
theorems the project calls semantic anchors (`valid_ltr`, `ltr_collect`,
`activation_collect`).

Rules applied, by shape: `ballI` (`\<forall>x\<in>A. P x`), `disjE` (case split
on a disjunctive fact), `subsetI` (`A \<subseteq> B`), `notI` (`\<not> P`),
`iffI` / `allI` / `conjI`, `intro_classes` (typeclass `instance` proofs),
`unfold_locales` (`interpretation`/`interpret` proofs). Batch-verified green
via `rtk make build`.

### Stage 1 — `TD_Side_CFG.thy` — DONE

Validated the recipe: hoisted `inr_slot_locals_bot_imp` above its first
potential call site (it existed but was proved too late in the file to be
citable from `local_edge_invariant_side_env_eq`, forcing a re-derivation
there); added two previously-missing elementary facts,
`restrict_local_sup`/`restrict_global_sup` (join-homomorphism) and
`restrict_local_idem`/`restrict_global_idem`, matching the file's existing
sibling-lemma convention; rewrote 8 call sites that re-derived these via
`unfolding restrict_local_def`/`local_bot_on_locals_def` to cite the
existing or new lemma instead.

Tagged per §5's usage-driven rule once each lemma cleared the ≥3-citation
threshold: `local_bot_on_locals_restrict_global [intro]` (narrow structural
pattern, 3 citations), `inr_slot_locals_bot_imp [dest]` (narrow premise, 7
citations, and all 7 existing citations already supplied the premise
explicitly, matching a dest rule's firing condition). `restrict_local_global_join`
stays untagged (see the regression below — it was briefly tagged `[simp]`,
then reverted, and the revert turned out not to be the actual issue).

**Regression, root cause, and fix (found via a genuine full rebuild, not the
cached batch runs used to confirm the rest of this stage).** `restrict_local_sup`/
`restrict_global_sup` (the join-homomorphism facts added for this stage) were
tagged `[simp]`. Their LHS pattern `restrict_local (_ \<squnion> _)` overlaps with
`restrict_local_combine_eq`'s LHS (`restrict_local (restrict_local A \<squnion>
restrict_global B)`) — a different, specific lemma reaching a different,
*incomplete* normal form once distributed (it stalls at `restrict_local
(restrict_global B)`, since no lemma reduced that further). Making the general
law `[simp]` let the simplifier distribute eagerly and preempt the specific
lemma's one-step closure, breaking three downstream files that relied on it
(`Exec_Bridge.thy`, `TD_Side_Tree.thy`, `Exec_DG_Bridge.thy`) — a real
regression that several apparently-green cached batch builds had missed
(a concurrent-build SQLite lock incident had left the build cache in a stale
state; only a full, non-cached rebuild surfaced the actual failures).

The durable fix restores confluence instead of reverting the tag: added
`restrict_local_restrict_global_bot [simp]` and
`restrict_global_restrict_local_bot [simp]` (`restrict_local (restrict_global
A) = bot` and its mirror). With those in place, distributing via
`restrict_local_sup`/`idem` reaches the *same* normal form as the specific
combine lemma, so both are confluent and `restrict_local_sup`/
`restrict_global_sup` are safely `[simp]` again. `restrict_local_combine_eq`/
`restrict_global_combine_eq`/`restrict_combine` became redundant corollaries
of the confluent algebra and were deleted outright (their 4 citation sites
across `Exec_Bridge.thy`, `Exec_DG_Bridge.thy`, and `TD_Side_Tree.thy` were
trimmed to rely on the base simp set instead) — no code is better than useless
code.

Restoring confluence surfaced one more real gap: `combine_abs`'s primitive
definition is a raw if-then-else lambda (in `Constraint_System.thy`), not
expressed via `restrict_local`/`restrict_global`, so `TD_Side_Tree.thy`'s
`unit_combine_tree_ctx_unit_traverse` had nothing to bridge the two. Added
`combine_abs_eq_restrict: "combine_abs sc se = restrict_local sc \<squnion>
restrict_global se"` in `TD_Side_CFG.thy` — and, while adding it, found a
pre-existing duplicate of exactly this fact under a different name,
`combine_abs_restrict`, already sitting in `DG_Soundness.thy` (needed there
because `TD_Side_Tree.thy` is built before `DG_Soundness.thy` and couldn't see
it). Deleted the duplicate and repointed its two citations
(`DG_Soundness.thy`'s `gamma_unit_combine_sound`, `Exec_DG_Bridge.thy`'s
`unit_combine_step_st_commute`) at the single upstream lemma.

Unlike the restrict-algebra facts, `combine_abs_eq_restrict` is **not** tagged
`[simp]`: doing so broke `DG_Framework.thy`'s `dgs_combine_unit_dg_spec`,
whose proof derives a local fact (`join_back`) about the same
`combine_abs`-shaped term via `sup.commute` before the final `simp` call —
the eager global rewrite preempted that local derivation the same way the
first regression preempted `restrict_local_combine_eq`. It is cited
explicitly at exactly the 3 sites that need it
(`TD_Side_Tree.thy`, `Exec_DG_Bridge.thy`, `DG_Soundness.thy`) and left out
everywhere else.

**Lesson, now in `AGENTS.md`'s Automation section:** before tagging a lemma
`[simp]`, check whether its LHS pattern overlaps with an existing lemma's LHS
serving a different normal form, *or* with a local derived fact inside some
other proof's `have`/`show` chain — not just whether the new lemma's own RHS
looks simpler in isolation. When a conflict surfaces, prefer restoring
confluence (add the missing bridging fact so every rewrite path agrees) over
reverting the tag, and delete anything that becomes a redundant corollary of
the resulting confluent set.

Confirmed via a genuine full (non-cached) rebuild of `Voblint_Analysis`,
`Voblint_Formalization`, and `Voblint_Examples`: 0 errors, 0 failures. I/Q
itself was unreliable for `Exec_Bridge.thy`, `DG_Soundness.thy`,
`Exec_DG_Bridge.thy`, and `DG_Framework.thy` throughout this regression
(`commands_finished: 0` while reporting `errors: 0` — the same false-positive
pattern already documented in Stage 3 below) — the full batch build was the
only real check for those four files. I/Q did stay reliable for
`TD_Side_CFG.thy` and `TD_Side_Tree.thy` (0 errors, `commands_finished`
matching the total command count) throughout.

Finding for Stage 5: `Sign_Local_Effects.thy` repeats the same
unfolding-instead-of-citing pattern roughly 10 times against these same
names (`restrict_local_def`, `local_bot_on_locals_def`,
`local_edge_invariant_def`) — confirms the leverage argument for doing the
shared core first; Stage 5 should cite `restrict_local_sup`,
`restrict_local_idem`, `inr_slot_locals_bot_imp`, and
`local_bot_on_locals_restrict_global` directly instead of re-deriving them.

### Stage 2 — `Constraint_System.thy` + `Split_State.thy` — DONE

Inspected every `unfolding X_def` site in both files (25 in `Split_State.thy`,
46 in `Constraint_System.thy`) rather than assuming the raw counts were all
violations. Result: both files were already largely compliant — nearly every
site is a single-use proof of that definition's own characterization lemma
(the legitimate pattern), not a re-derivation of an already-proved fact.
`Split_State.thy` needed no changes at all: every `wf_split`/`merge_state`/
`split_state`/`gamma_split` fact already has a named lemma, and nothing
re-derives one via unfolding.

`Constraint_System.thy` had one real instance: `se_constraint_holds_def`
(a plain conjunction) was unfolded 3 times in this file alone to extract one
or both conjuncts, with no dest lemma to cite instead. Added
`se_constraint_holds_local` and `se_constraint_holds_sides` right after the
definition and rewrote the one call site inside this file that benefits
(`se_constraint_holds_imp_etf_full_le_env`) to cite them. Both new lemmas
stay untagged — 1 in-file citation each, below §5's threshold.

Confirmed clean via I/Q on `Constraint_System.thy`, `Split_State.thy`, and
`Constraint_System_Sound.thy` (the loaded downstream consumer): 0 errors, no
new warnings (baseline: 5 pre-existing `code del` legacy-attribute warnings
in `Constraint_System.thy`, unrelated to this change).

### Stage 3 — `DG_Soundness.thy` — DONE

**`se_constraint_holds` connector (from Stage 2's finding).** The 4 sites in
`DG_Ctx_Activation.thy` (`pp_eq_bound`, `pp_sides_bound`) and
`DG_Soundness.thy` (`eq_le`, `sides_le`) that unfolded `se_constraint_holds_def`
now cite `se_constraint_holds_local [dest]`/`se_constraint_holds_sides [dest]`
instead. Both tagged: 3 citations each across the two files, narrow premise
(a specific named predicate, not a broad invariant).

**`gamma_dg`/`dg_gamma`/`gamma_unit` family.** Added the missing dest/intro
pairs and rewrote every call site that had been re-deriving them by hand:

- `gamma_dgD1`/`gamma_dgD2` — pointwise duals of the existing
  `gamma_dg_le_D`/`gamma_dg_le_G` subset lemmas; 2 citations each (below the
  tagging threshold, left untagged).
- `dg_gammaD [dest]`/`dg_gammaI [intro]` — bridge `dg_gamma` to `gammaDG`;
  6 of 8 call sites rewritten to cite them (3 and 4 citations respectively,
  both tagged). The other 2 sites keep the original `unfolding dg_gamma_def`
  deliberately: `dg_gamma` there is nested inside `edge_collect a (...)`,
  not the direct membership target, so the dest lemma's premise pattern
  doesn't match — confirmed by re-deriving the type mismatch by hand
  (`edge_collect a (dg_gamma sigma u)` is a different proposition from
  `dg_gamma sigma v`) before reverting that site back. Both new lemmas live
  inside the `sound_dg_spec` locale, so `dg_gammaI`'s `[intro]` only affects
  that locale's context and its interpretations, not the global claset.
- `gamma_unitD [dest]` — 3 citations in `gamma_unit_combine_sound`/
  `gamma_unit_enter_sound`, tagged. This one is top-level (outside any
  locale), so it is a genuinely global `[dest]`; its premise (`gamma_unit d g`)
  is narrow enough that the risk is low.

`dg_D`/`dg_G`/`dg_cmb` were also named in the original audit finding, but
inspection found their `unfolding` sites are each a distinct, one-time proof
of a different fact about a different tree operation (edge/enter/combine) —
the legitimate pattern, not repeated re-derivation of an already-proved fact.
No characterization lemmas were added for them.

Batch-confirmed green twice: once for the un-tagged dest/intro lemmas plus
call-site rewrites, once more after adding the tags (`rtk make build`,
`0:00:07` elapsed, fully cached, 0 errors both times). The first I/Q-based
"confirmed clean" claim made earlier for `DG_Soundness.thy` during this stage
was actually a false positive — `get_state` was returning `commands_finished:
0` (nothing had actually been rechecked yet) while still reporting `errors:
0`, which reads as clean but means nothing. This affected the entire
`DG_Framework`/`DG_Soundness`/`DG_Ctx_Activation` import chain specifically,
independent of which file was being edited — a genuine PIDE scheduling stall,
not a correctness issue with the edits themselves. Batch build is what
actually confirmed this stage; the I/Q inner loop stayed unusable for this
subtree for the remainder of the stage.

### Stage 4 — `Exec_Bridge.thy`, `TD_Side_Eff_Bounds.thy`

Spot-checked both files' `unfolding` sites (37 and 45 respectively) against
Stage 1–3's lemmas before assuming there was work to do. Result: both files
are already largely compliant, and one site already cites Stage 1's
`local_bot_join` directly (`TD_Side_Eff_Bounds.thy`,
`sides_of_rhs_Side_Inr_local_bot`). The remaining `unfolding` sites are each a
one-time proof of that file's own local definitions (`side_acc_eff_def`,
`side_rhs_fold_eff_def`, `side_cfg_T_eff_def`, `make_side_rhs_tree_eff_def`,
`static_deps_def`, `strip_inr_globals_def`, `combine_abs_def`,
`restrict_local_def`/`restrict_global_def` used once each to prove
`fun_of_st`'s own homomorphism lemmas, already tagged `[simp]`) — the
legitimate pattern, not the anti-pattern this migration targets.

### Stage 5 — `Sign_Local_Effects.thy` — DONE

First concrete domain instance; validates the recipe before touching
Interval/Mixed/NamedGlobalSign.

Confirmed Stage 1's finding: `afilter_sign_local_edge_invariant`'s Plus/Minus/
Times induction cases and `bfilter_sign_local_edge_invariant`'s Less/Eq cases
each re-derived `local_edge_invariant`'s quantified definition by hand
(`using <IH-fact>[OF ...] lb unfolding local_edge_invariant_def by blast`) to
extract the same instantiated equation the new `local_edge_invariantD`
(Stage 1, `TD_Side_CFG.thy`) already states directly. Rewrote all 10 sites to
`using local_edge_invariantD[OF <IH-fact>[OF ...] lb] .` — the single highest-
leverage fix in the migration so far, eliminating a 10-times-repeated
re-derivation with one existing lemma citation per site.

Left roughly 10 other `unfolding local_edge_invariant_def` sites untouched:
each is a legitimate intro-direction proof of a *new* `local_edge_invariant`
instance (`assign_sign_local_edge_invariant`, the base cases of the
`afilter`/`bfilter` inductions, `id_local_edge_invariant`'s call site), or a
`g := bot`-instantiated `drule`-based sub-derivation with no matching dest
lemma — the legitimate pattern, not re-derivation of an already-proved fact.

This is the stage where the `TD_Side_CFG.thy` `[simp]`-tag regression (see
Stage 1) first surfaced, via a full rebuild — `Sign_Local_Effects.thy` itself
was never the cause; it only exposed the gap because it was the first file
built after `TD_Side_CFG.thy` to depend on the specific `restrict_local`/
`restrict_global` normal forms upstream files had assumed. With that
regression fully resolved, a genuine full (non-cached) rebuild of
`Voblint_Analysis`/`Voblint_Formalization`/`Voblint_Examples` confirms this
file 100% clean, 0 errors.

### Stage 6 — remaining instances — DONE

Swept `Sign_Named_Global_Eff.thy`, `Interval_Transfer.thy`,
`Rel_Order_Domain.thy`, and `Interval_Lattice.thy` (ranked by `unfolding`
density: 37, 16, 27, 15 sites respectively) with the same recipe as Stage 5.
Result: all four are already compliant — no repeated re-derivation of an
already-proved fact found anywhere.

- `Sign_Named_Global_Eff.thy`: every `unfolding` proves that lemma's own
  definitional characterization once (`route_tree_def`, `named_etf_def`,
  `sideg_tree_def`, etc.); none of it touches `local_edge_invariant` at all —
  that optimization is specific to the Sign domain's `local_edge_tree` path,
  not used by the routed/named-global variant.
- `Interval_Transfer.thy`: sites like `ivl_tf_def`/`enter_ivl_def` recur
  across several lemmas, but each occurrence proves a *different* fact
  (soundness vs. monotonicity, or a different transfer field) about the same
  record/definition — the legitimate pattern already established in Stage 4.
- `Rel_Order_Domain.thy`: same shape — `gammaDG_rel_def`, `dgs_*_rel_def`,
  etc. each unfolded once per distinct edge-soundness theorem
  (nop/assign/assume/assume-not/enter/combine), never to re-derive a fact a
  named lemma already supplies.
- `Interval_Lattice.thy`: `less_eq_ivl_def` unfolded 8 times, `sup_ivl_def` 3
  times — the highest repeat counts found in this stage, and worth checking
  closely. Each occurrence proves a distinct order/lattice axiom
  (reflexivity, transitivity, antisymmetry, join/meet upper/lower bounds,
  least-upper-bound) via case analysis on the `Ivl l u` constructor, each
  needing a different consequence of the underlying `eint_le` facts
  (`eint_le_refl`/`_trans`/`_antisym`/`_linear`). This is the standard,
  unavoidable cost of instantiating an order class per-constructor with no
  higher-level lemma to cite instead — not the anti-pattern this migration
  targets.

`Exec_DG_Bridge.thy` (Mixed, 14 sites) was already reviewed this session
while fixing Stage 1's regression: its sites are one-time record-projection
proofs, matching Stage 4's `Exec_Bridge.thy` finding. Files below 10 sites
(`Mixed_Sign_Interval.thy` and smaller) were spot-checked for any definition
name recurring 3+ times across unrelated sites — none found; per Stage 7's
own criteria (low `unfolding` density, lower payoff), further exhaustive
line-by-line review of these was not pursued.

### Stage 7 — backlog — DONE

`Examples/*`, `CFG/Compiler/Compile_Locality.thy`, and other remaining files.
Ranked all uncovered files by `unfolding` density (`rg -o "unfolding
[a-zA-Z_][a-zA-Z0-9_'.]*" <file> | sort | uniq -c | sort -rn`) and audited
each name recurring 3+ times across unrelated sites — the anti-pattern
signature this migration targets — rather than reading every file
line-by-line. Two real hits found and fixed; the rest checked out compliant.

**`frag_stmts` (home file `CFG/VIMP_Proc_to_CFG.thy`).**
`CFG/Compiler/Compile_Locality.thy` re-derived membership in `frag_stmts E K`
via `unfolding frag_stmts_def by blast/auto` at 10 sites, each extracting one
of the definition's four structural disjuncts (edge source, edge target,
call source, call target) from an already-available tuple-membership fact.
Added the four missing intro lemmas at `frag_stmts`'s definition
(`frag_stmts_E_srcI`, `frag_stmts_E_tgtI`, `frag_stmts_K_srcI`,
`frag_stmts_K_tgtI`) and rewrote all 10 sites to cite them. Tagged
`frag_stmts_E_srcI [intro]` (4 citations) and `frag_stmts_E_tgtI [intro]`
(3 citations) per the usage threshold; `frag_stmts_K_srcI` (2 citations) and
`frag_stmts_K_tgtI` (1 citation) stay untagged. Checked `frag_stmts`'s only
other consumer, `Compile_Invariants.thy`: its one `unfolding` site proves a
distinct fact via the existing `frag_stmts_Un`/`frag_stmts_mono` lemmas
already, not a re-derivation — untouched.

**`gamma_state` (home file `Analysis/Generic/Domain/Abstract_Domain.thy`).**
Both `Abstract_Domain.thy` itself (6 sites, across `afilter_sound`'s
Plus/Minus/Times cases and `bfilter_sound`'s Less/Eq cases) and
`Sign_Transfer.thy` (5 sites, across `assign_sign_sound`,
`enter_frame_sign_sound`, `enter_sign_sound`, `combine_sign_sound`) unfolded
`gamma_state_def` solely to extract the pointwise fact `∀x. s x ∈ gamma
(σ x)` from an `s ∈ ⟦σ⟧` hypothesis — the dest-direction half of the
definition, never previously named. Added `gamma_stateD [dest]` (11 combined
citations across the two files, narrow premise — a specific named predicate,
not a broad invariant) and rewrote all 11 sites to cite
`gamma_stateD[OF <hyp>]` instead. The remaining `gamma_state_def` unfoldings
in both files are intro-direction proofs of a *new* fact each
(`gamma_state_mono`/`_bot`/`_sup_ub1`/`_sup_ub2`'s own characterizations,
and one `CollectI`-based state-membership construction per file) — the
legitimate pattern, left untouched.

**Files checked and found already compliant** (each `unfolding` proves a
distinct fact, no repeated re-derivation): `CFG_Prune.thy` — its
`cfg_succ_rel_def` sites (6, ranked highest after the two fixes above) are
themselves the four canonical intro lemmas
(`cfg_succ_rel_intra`/`_entry`/`_comb_caller`/`_comb_result`, one per
disjunct) plus a `cases`-style elimination lemma; its one external consumer
(`TD_Side_Eff_Cone_Lemmas.thy`) already cites the elimination lemma via
`cases rule:`, not raw unfolding.

Batch-confirmed via a genuine full (non-cached) rebuild of
`Voblint_CFG`/`Voblint_Analysis`/`Voblint_Formalization`/`Voblint_Examples`:
0 errors, 0 failures throughout, including every file touched this stage.

**Second-pass audit.** Stage 7 above sampled the backlog rather than sweeping
it exhaustively (deliberately, per this section's own scope). Re-ran the same
density scan (`unfolding <name>` recurring 3+ times) across every file in the
repo not yet individually audited by Stages 1–7 — roughly 20 files — to check
whether that sample was representative. Eighteen were legitimate: distinct
facts about the same definition (`dg_edge_tree_def`, `cfg_pkg_eff_def`,
`less_eq_eint_def`/`less_eq_sign_def`'s per-axiom order-class proofs,
`sign_etf_st_def`/`sign_etf_unit_def`/`ivl_etf_def`'s per-field bundle
characterizations, `compiled_at_def`'s intro/dest/consequence triple),
already-canonical characterization lemmas
(`cone_compatible_etf_def`'s ten per-conjunct projections in
`TD_Side_Eff_Pipeline.thy`, `static_deps_def`'s own intro lemma), or — for
`Examples/*.thy` and `VIMP_Proc.thy` — `by eval`/operational-semantics proofs
checking distinct concrete facts, which is not the logical-re-derivation
anti-pattern this migration targets at all.

One more real hit: `is_post_fixpoint` (`Constraint_System.thy`, `∀v. rhs g tf
join_abs bot_abs s0 env v ≤ env v`) was re-derived via `unfolding
is_post_fixpoint_def by simp` at exactly 3 sites in `LTR_Analysis_Sound.thy`,
each just specializing the same `∀v` to a different concrete `v` (an edge
target, a callee entry, a call continuation). Added `is_post_fixpointD
[dest]` next to the definition and rewrote all 3 sites to cite it. The two
`Examples/*.thy` sites that construct concrete `is_post_fixpoint` instances
(the intro direction) were left untouched — legitimate, one-time per
example.

Batch-confirmed via a second genuine full rebuild: 0 errors, 0 failures. This
second pass found one real fix in ~20 files sampled — consistent with, not
contradicting, Stage 7's original judgment call; the backlog was mostly
already sound.

### Stop condition

A hygiene pass has no natural end unless one is stated. Stage 7 stops, and
the migration is finished, once all three hold:

- every high-density core file identified in §3.2 has gone through Stages
  1–6;
- every remaining `unfolding X_def` site is a local implementation choice
  inside a definition's own theory, not a re-derivation of a fact usable
  elsewhere (§7's `unfolding` exit criterion already codifies this per-site,
  this is the repo-wide version);
- further extraction of characterization lemmas would not measurably improve
  proof stability or readability at the remaining sites — judged, not
  swept for exhaustively.

Do not keep chasing single-digit backlog files past this point; that is
scope creep the plan itself warns against (§8).

## 7. Exit criteria

- Every definition **used outside its defining theory** in a Stage 1–6 file
  has an appropriate interface: a characterization lemma (tagged per §5's
  usage-driven rule, or explicitly cited if usage doesn't yet justify a
  global attribute) or a documented, judged-not-worth-extracting `unfolding`.
  Purely-internal definitions (helpers that only package an invariant for
  their own theory) are exempt — not every definition earns a public API, and
  requiring one for all 676 would manufacture simp rules nobody would
  otherwise choose.
- `unfolding X_def` remains only where no reusable property exists yet and is
  judged not worth extracting (documented inline, not silently left).
- 0 bare `proof` commands in Stage 0's files.
- Every non-trivial exported definition or characterization lemma introduced
  or modified during the migration has a nearby `text` block explaining its
  semantic purpose and design constraints (§5, semantic documentation) —
  purely-internal definitions are exempt, same as the interface-lemma
  criterion above.
- `Voblint_Analysis` and `Voblint_Formalization` batch-build green after each
  stage, with no per-theory timing regression and no new build warning
  flagged per §5 step 4 (warning-baseline discipline); 0 new `sorry`.

## 8. What not to do

- Do not turn this into a whole-repo mechanical sweep (Approach A) — bounded,
  file-at-a-time diffs only.
- Do not retrofit tags onto lemmas outside the stage currently in progress.
- Do not change any theorem statement's mathematical content while adding
  characterization lemmas or tags — this is a hygiene pass, not a redesign.
- Do not tag more than one lemma (or one small related group) per batch-build
  cycle (§5) — batching tags together defeats the isolation the file-by-file
  order exists to provide.
