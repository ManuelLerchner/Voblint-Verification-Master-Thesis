# Proof hygiene — skill-compliance audit and migration plan

> **Status:** Stage 0 (implicit-method `proof` cleanup) complete and
> batch-verified. Stages 1+ (classical-reasoner tagging, `unfolding` removal)
> not started. Two rounds of external review are incorporated below. Round 1
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

### Stage 1 — `TD_Side_CFG.thy`

Lowest risk of the large files, and goes first per the external review: it
validates the recipe on a file where the highest-risk step is already
partly done. Characterization lemmas already exist for the heaviest-unfolded
names (`restrict_local`/`restrict_global`/`local_bot_on_locals`). Mostly
tagging plus rewriting call sites to cite the existing lemma instead of
re-unfolding.

### Stage 2 — `Constraint_System.thy` + `Split_State.thy`

Most foundational: `wf_split`/`merge_state`/`split_state`/`gamma_state`/
`glob_env`/`abs_join_set` feed every downstream instance. Highest blast
radius if a tag misfires, so it runs after Stage 1 has confirmed the
tagging-safety procedure (§5) against a real file. Add missing
characterization lemmas (closure, monotonicity, `_iff` forms where the
definition is a predicate), tag per §5's usage-driven rule, replace
`unfolding` at call sites with the tagged lemma or an explicit citation.

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
