# Proof hygiene — skill-compliance audit and migration plan

> **Status:** audit complete, migration not started. This document records a
> static compliance pass against the proof-engineering skills
> (`isabelle-formalization`, `isabelle-proof-development`) and lays out a
> phased, batch-verifiable fix. No `.thy` file has been touched yet.

**Question answered here:** does the current theory tree follow the
proof-engineering skills' rules on definitions, theorem tagging, and proof
style, and if not, what changes bring it into alignment without inflating
scope? **Partially.** Documentation, proof structuring, import hygiene, and
statement shape are already compliant. Two independent gaps survive: near-zero
classical-reasoner tagging paired with heavy `unfolding`-based re-derivation,
and 50 implicit-method `proof` steps in exactly the theorems this repo calls
its semantic anchors.

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
(`IMP2/IMP2_Proc.thy`, carried over from the AFP IMP2 base — genuinely
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

### 3.3 Implicit-method `proof` (50 sites)

The style guide is explicit: "do not use implicit proof methods in `proof`;
use `proof -` or `proof <method>`." 50 bare `proof` commands survive, and they
are concentrated in the theorems this repo's own `CLAUDE.md` names as semantic
anchors:

| File | bare `proof` count |
| --- | --- |
| `CFG/Collecting/LTR_Abstract.thy` | 10 (includes steps inside `valid_ltr_subset_gamma_ltr`, `activation_collect_subset_acc`) |
| `CFG/Collecting/CFG_Local_Trace.thy` | 9 |
| `Analysis/Generic/Domain/Exec_St.thy` | 6 |
| `CFG/Compiler/Control_Simulation.thy` | 5 |
| 16 other files | 1–2 each |

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

**B — targeted, ordered by leverage.** Fix the highest-density files first,
one at a time: add missing characterization lemmas, tag them, replace
`unfolding` at call sites with the tagged lemma or the correct explicit
method, batch-build green before moving to the next file. Leave low-density
files (`Examples/*`, single-digit counts) as backlog. Bounded, reviewable
diffs; matches the existing workflow; highest-leverage fix (the shared core)
lands first.

**Recommendation: B.**

## 5. Tagging safety protocol

Adding `[simp]`/`[intro]`/`[dest]` is not risk-free. `docs/ISABELLE_AGENT_NOTES.md`
already names two of the five standard slow-build causes as tagging mistakes:
"a recursive `[simp]` declaration" and "a new `[intro]` or congruence rule that
triggers repeatedly." A `[simp]` or `[intro]` attribute changes the default
simp set / claset for **every downstream theory that imports the file**, so a
bad tag on a Stage 1 file (`Constraint_System.thy`, `Split_State.thy`) can
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
- Prefer the narrowest applicable variant (`[dest]` over `[elim]` over
  `[intro]`) when the rule's shape allows it — destruction rules only fire
  when their pattern is already present, elimination/introduction rules can
  fire speculatively.
- If a lemma is only needed at a handful of call sites, leave it untagged and
  pass it explicitly (`simp add: foo`, `intro: foo`) at those sites instead —
  this is the proof-development skill's own fallback ("manually pass the
  rules") for concepts that aren't worked with constantly.

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
5. On any regression (new failure, new timeout, or a proof that previously
   took seconds now taking much longer), revert that one tag
   (`declare foo[simp del]` or drop the attribute) before continuing — do not
   push forward and "fix it later." Diagnose which downstream proof's
   automation changed before retrying with a narrower attribute (e.g. `[dest]`
   instead of `[elim]`) or no attribute at all.
6. Only move to the next lemma once the full downstream build is green again.

This makes each stage slower per lemma but keeps blame isolated to one
attribute at a time, which is the entire point of doing this file-by-file
rather than as a whole-repo sweep (§4, Approach A).

## 6. Migration stages

Each stage ends in a green `isabelle-verify` batch build before the next
starts. Any lemma proved while chasing an unfolding site gets `[simp]`/
`[intro]`/`[dest]` immediately, so the gap does not reopen.

### Stage 0 — implicit-method `proof` cleanup

Files: `LTR_Abstract.thy`, `CFG_Local_Trace.thy`, `Exec_St.thy`,
`Control_Simulation.thy`, then the 16 single/double-occurrence files.
Per site: identify the rule the bare `proof` currently applies (via
`get_state`/`explore` on the open goal), then rewrite as `proof (rule ...)`,
`proof (induction ...)`, `proof (cases ...)`, or `proof -` as appropriate.
Effort: low per site, moderate in aggregate (50 sites). Risk: low — purely
disambiguating an existing step, no new proof content. Highest priority
because it sits in the theorems the project calls semantic anchors
(`valid_ltr`, `ltr_collect`, `activation_collect`).

### Stage 1 — `Constraint_System.thy` + `Split_State.thy`

Most foundational: `wf_split`/`merge_state`/`split_state`/`gamma_state`/
`glob_env`/`abs_join_set` feed every downstream instance. Add missing
characterization lemmas (closure, monotonicity, `_iff` forms where the
definition is a predicate), tag `[simp]`/`[intro]`/`[dest]`, replace
`unfolding` at call sites with the tagged lemma.

### Stage 2 — `TD_Side_CFG.thy`

Lowest risk of the large files: characterization lemmas already exist for the
heaviest-unfolded names (`restrict_local`/`restrict_global`/
`local_bot_on_locals`). Mostly tagging plus rewriting call sites to cite the
existing lemma instead of re-unfolding.

### Stage 3 — `DG_Soundness.thy`

Needs new characterization lemmas for the `gamma_dg`/`dg_gamma`/`gamma_unit`/
`dg_G`/`dg_D`/`dg_cmb` family before any de-unfolding is possible — no
companion lemmas exist today.

### Stage 4 — `Exec_Bridge.thy`, `TD_Side_Eff_Bounds.thy`

Solver-core plumbing; apply the same recipe once Stages 1–3 establish the
pattern.

### Stage 5 — `Sign_Local_Effects.thy`

First concrete domain instance; validates the recipe before touching
Interval/Mixed/NamedGlobalSign.

### Stage 6 — remaining instances

Sweep `Sign_Named_Global_Eff.thy`, `Instances/Interval/*`, `Instances/Mixed/*`
with the same recipe.

### Stage 7 — backlog

`Examples/*`, `CFG/Compiler/Compile_Locality.thy`, and other low-density files
(single digit `unfolding` counts). Lower payoff; defer past the core-cluster
work above.

## 7. Exit criteria

- Every definition introduced in a Stage 1–6 file has at least one tagged
  (`[simp]`, `[intro]`, `[dest]`, or explicitly-cited-untagged-with-reason)
  characterization lemma before any proof in that file unfolds it.
- `unfolding X_def` remains only where no reusable property exists yet and is
  judged not worth extracting (documented inline, not silently left).
- 0 bare `proof` commands in Stage 0's files.
- `Voblint_Analysis` and `Voblint_Formalization` batch-build green after each
  stage; 0 new `sorry`.

## 8. What not to do

- Do not turn this into a whole-repo mechanical sweep (Approach A) — bounded,
  file-at-a-time diffs only.
- Do not retrofit tags onto lemmas outside the stage currently in progress.
- Do not change any theorem statement's mathematical content while adding
  characterization lemmas or tags — this is a hygiene pass, not a redesign.
- Do not tag more than one lemma (or one small related group) per batch-build
  cycle (§5) — batching tags together defeats the isolation the file-by-file
  order exists to provide.
