# Gap 5: relational domain architecture — design decision document

Status: **Option 4 architecturally validated** — see "Architectural
validation (completed)" at the end of this document. `Rel_Order_Domain.thy`
is a batch-green `sound_dg_spec` interpretation over a non-`abs_state`
relational carrier, with zero changes to the DG framework. The design
analysis below predates that prototype; every claim it makes is traced
against the current tree (`goblint-alignment-mixed-flow-tutorial`) as of the
session that wrote it, not against the prior planning documents' assumptions
about it. Several of those assumptions turned out to be stale — flagged
explicitly where found.

## Executive summary — the finding that changes the shape of the decision

All three existing designs (`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`'s type
class, `RELATIONAL_DOMAIN_PLAN.md`'s locale, issue #19's functor split) scope
their migration to the **flat spine** — `Constraint_System.thy`,
`Constraint_System_Sound.thy`, `LTR_Analysis_Sound.thy`. Per this project's
own contract (`AGENTS.md`: "the procedure-aware CFG and generic D/G route are
the sole analysis path. Sign, Interval, and mixed Sign/Interval instances use
the side-effecting verified solver"), **that is not where Sign, Interval, or
Mixed Sign/Interval actually run.** They run through `DG_Framework.thy` /
`DG_Soundness.thy` / the effectful TD solver.

Tracing the DG layer directly (not assumed — read below) shows:

- `dg_spec`'s carriers `'dl`/`'dg` are already fully opaque type parameters
  (`DG_Framework.thy:242-247`) — no `abs_state`, no pointwise structure baked
  into the record itself.
- `sound_dg_spec` — the soundness locale every DG instance discharges — is
  **already a locale over an arbitrary joint concretization**:

  ```isabelle
  locale sound_dg_spec =
    fixes S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
      and gammaDG :: "'D => 'G => store set"
    assumes gammaDG_mono: ...
      and step_sound: ...
      and combine_sound: ...
      and enter_sound: ...
  ```

  (`DG_Soundness.thy:127-147`). `'D`/`'G` are constrained only to
  `bounded_semilattice_sup_bot` — a generic lattice-with-bottom type class,
  not to functions. This is functionally **Option 2, already built, at
  exactly the layer that matters for execution.**
- The DG layer's own README says this explicitly, unprompted: "Analyses
  choose both carriers, their transfer and communication operations, and an
  optional activation context... Homogeneous analyses use the same carrier
  for D and G; mixed analyses use independent carriers"
  (`src/Analysis/Generic/Solver/Context/DG/README.md`).

What **is** box-only is not the framework — it's every existing
*interpretation* of it: `gamma_dg d g = ⟦d⟧ ∩ ⟦g⟧` (`DG_Soundness.thy:106-109`)
calls `gamma_state`, which is `'a::sound_domain abs_state => store set`
(`Abstract_Domain.thy:58`, "lifts `gamma` pointwise," per the domain README).
`unit_dg_spec`, `indep_dg_spec`, `mixed_si_spec` all choose `'dl = 'a abs_state`,
`'dg = 'b abs_state` — a choice, not a constraint the locale imposes.

**Consequence for the three designs as literally scoped:** each would, if
executed exactly as written, generalize a spine that Sign/Interval/Mixed
don't run through, while leaving untouched the layer that already supports a
relational carrier. None of the three, at their stated scope, is *wrong* —
`RELATIONAL_DOMAIN_PLAN.md` in particular is careful, correct engineering —
but none of them is aimed at the actual remaining blocker. This is the
central "outdated assumption" finding this document is required to surface.

The real remaining blockers, precisely stated:

1. No relational abstract-value type exists yet (an `'a` with a genuinely
   relational join, not `bounded_semilattice_sup_bot`'s pointwise-fun
   instance).
2. No `dgs_assign`/`dgs_assume`/`dgs_assume_not`/`dgs_enter` implementation
   for such a type, and no `gammaDG` interpretation discharging
   `sound_dg_spec`'s four obligations for it.
3. Interprocedural combine for a relational carrier is a genuine semantic
   design problem (projection + meet, not variable selection) — every
   existing document already flags this as the hard part, correctly.
4. The **executable/runnable path** is a separate, real gap no prior document
   named: `Exec_St.thy`'s `'a st` is explicitly documented as "the executable
   representation of the abstract state `vname => 'a`... A state is a triple
   `(dl, dg, ps)`: a default for local variables, a default for global
   variables, and a finite list of explicit per-variable overrides"
   (`Exec_St.thy:12-18`). This is a per-variable association-list
   representation by construction, parametric only in the *value* type, not
   in the state *shape*. A relational domain proven sound via `sound_dg_spec`
   gets no executable/GraphViz/code-gen path from this file — a new
   executable representation and a new `Exec_*_Bridge` (analogous to
   `Exec_DG_Bridge.thy`) is separate, additive work.
5. Context-sensitivity (`DG_Ctx_Activation.thy`) needs its own new
   `gammaDG`-shaped locale if a relational domain wants it — matches Gap 4's
   own finding this session (`gamma_unit d g = ⟦d ⊔ g⟧` needs a unified type,
   ~245-line file's worth of new locale work) — but this is additive and only
   needed if an instance actually wants context-sensitivity.

None of 1-5 requires touching `Constraint_System.thy`, `DG_Framework.thy`,
`DG_Soundness.thy`, or any existing Sign/Interval/Mixed proof. They are new
files interpreting existing locales, exactly the "generalize in place" vs.
"new instance" distinction this project already draws correctly for Gap 3/4.

---

## Investigation: how deep does variable-indexing actually go?

Required by the task before evaluating any option.

### `restrict_local`/`restrict_global` footprint — 399 occurrences, not ~280

```
TD_Side_CFG.thy                    90   (flat-layer / effectful IP combine, abs_state level)
Sign_Local_Effects.thy             75   (Sign-specific instance)
Exec_Bridge.thy                    71   (executable bridge, st level)
Sign_Named_Global_Eff.thy          26   (Sign-specific instance)
Exec_St.thy                        26   (executable representation itself)
TD_Side_Eff_Bounds.thy             25
TD_Side_Tree.thy                   17
TD_Side_Eff_Cone_Lemmas.thy        16
Solver_Side_RG.thy                  7
TD_Side_RHS_Generator.thy           7
Exec_DG_Bridge.thy                  6
DG_Framework.thy                    6
(11 more files, 1-5 each)          20
                                  ---
Total                              399
```

The prior estimate (~280, from `ARCHITECTURE_MIGRATION_PLAN.md`, this
session) undercounted — re-verified via `rg -c` directly. The top 6 files
account for 78% of it.

The operations themselves are irreducibly pointwise:

```isabelle
definition restrict_local :: "'a abs_state => 'a abs_state" where
  "restrict_local sigma = (\<lambda>x. if is_global x then bot else sigma x)"
```

(`TD_Side_CFG.thy:25-27`). This is per-variable selection, not projection. A
relational state's "local part" is not "the same object with globals zeroed
out" — it requires eliminating global dimensions from a relation (existential
projection), a structurally different operation that cannot be written as
`if is_global x then bot else sigma x` for an opaque `'d`.

**But this cuts narrower than it first appears.** `restrict_local`/
`restrict_global` are flat-layer (`TD_Side_CFG.thy`) and executable-bridge
(`Exec_Bridge.thy`, `Exec_St.thy`) constructs. The DG-layer generic interface
(`dgs_combine_env`/`dgs_combine_assign`, split this session in Gap 3 Site A)
does not call them — `indep_dg_spec` and `unit_dg_spec` *choose* to build
their combine via `combine_abs`/`combine_collect_abs`, which is where
`restrict_local`/`restrict_global`-flavored per-variable reasoning enters,
but a **new** `dg_spec` instance for a relational carrier supplies its own
`dgs_combine_env`/`dgs_combine_assign` and is not obligated to go anywhere
near these 399 sites. They are real cost for anyone trying to *generalize
the existing box instances in place*; they are not cost for *adding a new,
separate relational instance*, which is the cheaper of the two shapes this
document ends up recommending.

### `combine_abs` (flat layer) — still pointwise even after this session's Gap 3 Site B

```isabelle
definition combine_abs :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "combine_abs sc se = (\<lambda>x. if is_global x then se x else sc x)"
```

(`Constraint_System.thy:289-290`). Gap 3 Site B made the *environment-merge*
step pluggable (`tf_combine`), but `'a abs_state = vname => 'a` itself is
unchanged, and `combine_assign_abs` — the destination write,
`\<sigma>(x := v)` — remains fixed. `tf_combine`'s type,
`'a abs_state => 'a abs_state => 'a abs_state`, lets an analysis customize
*how two box states merge*; it does not let the state stop being a box. This
is worth being precise about, correcting this session's earlier framing of
`tf_combine` as unqualified "real leverage toward Gap 5" — it is leverage
specifically for a **box-shaped, per-analysis-customized merge**, not a step
toward relational representation. It remains a legitimate, banked,
independent improvement.

### Two prior attempts already exist in this repo's history

- **`docs/DOMAIN_TYPECLASS_MIGRATION.md`** — status "DONE," commit `52d7486`:
  a full locale-to-type-class migration of `sound_domain`/`abstract_domain`
  was built and completed once, under the *prior* `src/Analysis/Domains/`
  layout. The codebase was later restructured (`d91fa93f`, "move analysis
  theories into generic and instance folders," 2026-06-30) into today's
  `src/Analysis/Generic/` + `src/Analysis/Instances/` layout, and
  `abs_state` is once again a plain `type_synonym`
  (`Abstract_Domain.thy:29`), not a type class — verified directly, not
  inferred. No document explains whether the type-class approach was
  actively reverted or simply not carried forward during an unrelated
  restructuring; either way, it is a first-hand data point that a type-class
  `abs_state` did not survive as this project's chosen shape through its own
  next major refactor, and is worth weighing against Option 1's abstract
  appeal.
- **`docs/SPLIT_STATE_MIGRATION.md`** ("migration complete") is the design
  history behind today's DG heterogeneity (`Split_State.thy`, `dg_state`).
  Its own "Remaining limitations toward Goblint" section, written before
  this session's Gap 3/4 work, independently names the same leverage point
  this investigation found: *"`sound_dg_spec` currently fixes `D = 'd
  abs_state` and `G = 'g abs_state`... The highest-leverage next framework
  change is to generalize `sound_dg_spec` from abstract-state-shaped `D`/`G`
  to arbitrary sound lattice carriers with an analysis-supplied joint
  concretization."* That sentence describes exactly what tracing
  `sound_dg_spec`'s current locale signature shows is **already true** —
  `'D`/`'G` are already `bounded_semilattice_sup_bot`, not `abs_state`. This
  doc's limitation list predates the current state of the locale (or was
  scoped more conservatively than the code turned out to require); either
  way, its own top-ranked "next framework change" is closer to done than it
  states.
- `docs/DOMAIN_INTERFACE_MINIMIZATION.md` is self-labeled "SUPERSEDED /
  HISTORICAL" and `docs/THESIS_SCOPE_MEMO.md` describes a scope decision for
  a now-retired "digest"/"trace pivot" architecture (vocabulary — "M4
  precision," "digest-indexed env" — absent from current `AGENTS.md`).
  Neither is live; both were checked and ruled out as current input.

### Staleness in the three existing proposals — checked directly, not assumed

- `RELATIONAL_DOMAIN_PLAN.md`'s "Plan of record" cites
  `TD_Side_IP_Eff_Soundness.thy`, `Trace_IP_Analysis_Sound.thy`,
  `TD_Side_Eff_Soundness.thy`, `Trace_Analysis_Sound.thy` by name for Phase 1
  — **none exist in the current tree** (`fd`/`rg` both empty, re-checked this
  session). The four leverage lemmas it names do exist, just at drifted line
  numbers (`gamma_state_mono`/`_bot`/`_sup_ub1`/`_sup_ub2` now at
  `Abstract_Domain.thy:77/83/87/93`, not the doc's cited 72/77/81/86).
- GitHub issue #19 (functor split) cites `src/Domains/Abstract_Domain.thy`
  and an acceptance test against `sign_pipeline_invariant_sound`/
  `goblint_sign_sound` — both from the same retired `Domains/` layout;
  neither the path nor (unverified, but likely, given the vocabulary)
  those lemma names match the current tree.
- Issue #19's body says "Full prose context: `docs/ROADMAP.md` § 'Octagon /
  relational domains — flagship stretch.'" **`docs/ROADMAP.md` (104 lines,
  checked in full) contains no mention of Octagon or relational domains at
  all.** The section it points to does not exist in the current roadmap.
- Epic #25, by contrast, is current and substantive: still open, still
  explicitly gating the Scope A (~3-4mo)/Scope B (~6-8mo) decision on a
  supervisor meeting that (per its own text) hasn't happened, and it
  independently names the same architectural point this document leads
  with: *"Either the two-layer split lands first (the principled fix) or
  octagon ships with a bespoke pipeline path."* That sentence is itself an
  endorsement of something like Option 3 — worth knowing the project's own
  roadmap already leans that way, even though this document's own finding
  (below) is that the two-layer split isn't the binding constraint at the DG
  layer specifically.

---

## Per-option analysis

### Option 1 — abstract state type class

**Conceptual model.** Replace `'a abs_state = vname => 'a` with a class
`abstract_state` fixing `gamma_state`, `join_state`, `bot_state`,
`apply_assign`, `apply_assume`, `combine`. Every consumer signature
(`domain_transfer`, `rhs`, `TD_Side_CFG.thy`'s combinators, eventually
`dg_spec` if pushed all the way) becomes polymorphic over `'a::abstract_state`.
Interval instantiates the class the way it instantiates `sound_domain` today.
An Octagon domain would define its DBM type and prove the same class axioms
— `join_state` becomes real DBM-join, `gamma_state` a real polyhedron
concretization, no `vname => 'a` anywhere in its type.

**Isabelle/HOL impact.** Ad-hoc polymorphism via `class`/`instance` is
idiomatic Isabelle, but it is *global* — every file that mentions `abs_state`
picks up the class constraint, whether or not that file's proofs actually
need genericity. This project's own prior attempt at exactly this shape
(`DOMAIN_TYPECLASS_MIGRATION.md`) did not survive the codebase's next
restructuring, which is a concrete, not hypothetical, maintainability signal
against a class-wide commitment. Type classes also don't compose well with
this project's existing pattern of *multiple* interpretations of the same
carrier for different purposes (`abs_state` is `sound_domain`-constrained in
`Constraint_System.thy` but wants `bounded_semilattice_sup_bot` in
`Exec_St.thy`) — a class forces one coherent instance per type, where this
codebase currently gets that flexibility from locale interpretation
(`interpretation`/`sublocale`) applied per-file.

**Migration plan (if pursued as scoped by the original doc — the flat
spine).** First file: `Abstract_Domain.thy` (`type_synonym` -> `class`).
Then `Sign_Transfer.thy`/`Interval_Transfer.thy` become `instantiation`
blocks. Then every flat-layer file naming `abs_state` explicitly
(`Constraint_System.thy`, `TD_Side_CFG.thy`, ~399-site footprint). The DG
layer would *not* need to change at all — it already routes through opaque
`'dl`/`'dg`, so a class-ified `abs_state` at the flat layer has zero
obligation to reach `DG_Framework.thy`. This narrows the original 4-6 week
estimate's scope somewhat (DG layer untouched) but the flat-layer +
`restrict_local`/`restrict_global` footprint the estimate didn't budget for
widens it back; net, likely still 4-6 weeks, for a spine generalization that
— per the executive summary — doesn't reach the layer Sign/Interval/Mixed
actually execute through.

**Proof impact.** Unchanged: every DG-layer proof (`DG_Soundness.thy`,
`DG_Ctx_Activation.thy`, all Interval Ctx examples) — they never mention
`abs_state`'s type-class status directly, only `bounded_semilattice_sup_bot`.
Requiring generalization: every flat-layer lemma stated with a bare `'a`
implicitly assumed `sound_domain`-instantiated at `abs_state`'s current
shape; each needs its `'a::sound_domain` constraint re-checked against the
new class's axiom set. New abstraction lemmas: none obviously required
beyond the class's own axioms — this is the option with the least *new*
lemma-writing, at the cost of the widest *touched-file* footprint.

**Cost estimate.** 4-6 weeks matches the original estimate reasonably well
once the DG layer is correctly excluded from scope; risk is medium-high
mainly because of the prior-attempt signal above, not because of proof
difficulty per lemma.

**Recommendation weight.** Weakest of the three as scoped: highest
touched-file cost, does not reach the executed analysis path, and this
project has already tried and not kept this shape once.

---

### Option 2 — Isabelle locale reinterpretation

**Conceptual model.** `RELATIONAL_DOMAIN_PLAN.md`'s Approach A: fix
`gamma_st`/`bot`/`join` as locale parameters (`rel_domain` locale), box
domains `interpretation box: rel_domain gamma_state bot sup` reusing the
existing four `gamma_state_*` lemmas verbatim, a relational domain supplies
its own `'d`/`gamma_st`/`bot`/`join` and proves the same four facts fresh. An
Interval analysis is the existing `interpretation`; an Octagon analysis is a
new `'d = dbm`, a real polyhedral `gamma_st`, and one `interpretation`.

**Isabelle/HOL impact.** This is the pattern this codebase already uses
pervasively and successfully — `sound_transfer`, `sound_dg_spec`, `abstract_domain`
are all "one locale, many `interpretation`s" already. Locales compose with
existing soundness proofs by construction (an `interpretation` just
discharges obligations once, downstream lemmas are unaffected). No global
class-wide commitment; two interpretations of the same carrier for different
purposes are ordinary and already how this project handles `sound_domain`
vs. `bounded_semilattice_sup_bot` today.

**Where the original document's scope is stale, precisely.** `Approach A`
targets `Constraint_System.thy`'s `gamma_state`, i.e. the flat spine. This
document's investigation shows the *locale-over-opaque-carrier* pattern it
wants **already exists**, one layer over, in `sound_dg_spec`. So Option 2's
underlying mechanism is exactly right; its originally-proposed target file
is the less relevant one. A corrected Option 2 retargets Phase 0's spike
(the `x<=y` toy order-constraint domain, `'d = (vname × vname) set`,
`gamma_st d = {s. \<forall>(x,y)\<in>d. s x <= s y}`, `join = \<inter>`) at `sound_dg_spec`
directly: define `'dl`/`'dg` for the order-constraint domain, implement
`dgs_assign`/`dgs_assume`/`dgs_assume_not`/`dgs_enter`/`dgs_combine_env`/
`dgs_combine_assign` for it (small — assign/assume on a pair-set domain is a
handful of set operations), write `gammaDG` for it, and discharge
`sound_dg_spec`'s four obligations. Zero edits to `DG_Framework.thy`,
`DG_Soundness.thy`, or any existing Sign/Interval/Mixed file — an
`interpretation`/new-instance exercise, not a migration.

**Migration plan.** First file: a new
`src/Analysis/Instances/Relational/Rel_Order_Domain.thy` (matching the
original doc's own file-naming instinct). Dependency order: (1) the DBM/pair
type + lattice instance, (2) `dgs_*` transfer implementations, (3)
`gammaDG` + `sound_dg_spec` interpretation for the intraprocedural fragment
only (`dgs_combine_env`/`dgs_combine_assign` deferred or restricted per the
IP-combine caveat below), (4) an executable `Exec_*`-level representation and
bridge only if a runnable/GraphViz path is wanted, deferred as separate
scope. No compatibility strategy needed — nothing existing changes.

**Proof impact.** Unchanged: literally everything under
`src/Analysis/Instances/Sign`, `.../Interval`, `.../Mixed`, and all of
`DG_Framework.thy`/`DG_Soundness.thy`. Requiring generalization: nothing —
this is the point of targeting an already-generic locale. New abstraction
lemmas required: exactly the four `sound_dg_spec` obligations for the new
carrier (`gammaDG_mono`, `step_sound`, `combine_sound`, `enter_sound`) —
`RELATIONAL_DOMAIN_PLAN.md`'s own assessment that the box case's four facts
are "near-trivial" via intersection-monotonicity transfers directly to this
retargeted version; the DG layer's four obligations are the same shape
(monotonicity + one soundness fact per operation), not a harder set.

**Cost estimate.** The spike (Phase 0 equivalent, retargeted): days, not
weeks — a new file, no existing-file edits, four small lemmas. A full
intraprocedural relational analysis with executable path: 2-4 weeks,
dominated by the executable-bridge work (genuinely new, `Exec_St.thy`'s `st`
type doesn't fit) and by however much precision the chosen domain needs
(order-constraints is intentionally minimal; a real octagon DBM is
substantially more). Context-sensitivity: not included, add the
~245-line-file-sized new locale from Gap 4's own estimate if wanted later.
Risk: low — additive, no shared-file blast radius, and the exact
lattice-obligation shape (`bounded_semilattice_sup_bot` + a locale-supplied
concretization) is proven out three times already in this codebase (`unit_dg_spec`,
`indep_dg_spec`, `mixed_si_spec`).

**Recommendation weight.** Strongest of the three, once retargeted at the DG
layer rather than the flat spine — matches this codebase's existing idiom,
lowest cost, lowest risk, and is closest to what the codebase's own
`SPLIT_STATE_MIGRATION.md` independently flagged as the highest-leverage next
step.

---

### Option 3 — functor split (`num_value_domain`/`env_domain`, issue #19)

**Conceptual model.** Split today's collapsed `abstract_domain` into a
scalar interface (`num_value_domain`, `gamma : 'a => int set`) and an
environment interface (`env_domain`, `gamma_state : 'e => store set`),
connected by an explicit functor `non_rel_env` reproducing today's implicit
pointwise lifting. Interval instantiates `num_value_domain` only, gets its
`env_domain` for free via `non_rel_env`. Octagon would instantiate
`env_domain` directly (its "scalar" and "environment" concerns aren't
separable the way Interval's are — an octagon constraint inherently spans
two variables), bypassing `non_rel_env` entirely.

**Isabelle/HOL impact.** Locale-based functor composition (two locales + a
connecting `interpretation`) is idiomatic but has more moving parts than
Option 2's single locale, and — as the issue's own text implicitly concedes
by having Octagon bypass the functor rather than use it — the functor
doesn't actually carry a relational domain through; it exists to make
Interval/Sign's *current* behavior explicit, which is a genuine and useful
refactor for its own sake (documents an implicit lift, matches Blazy et al.
2013's own separation) but is not, by itself, the mechanism that unblocks a
relational domain. Whatever a relational domain instantiates instead of
`non_rel_env` still needs to satisfy `env_domain`'s full interface from
scratch, with no design detail written down in this repo for what that
interface should demand beyond the issue's short exit-criteria list.

**Migration plan.** First file: `src/Analysis/Generic/Domain/Abstract_Domain.thy`
splits into two locales as issue #19 lists (paths there are stale —
`src/Domains/Abstract_Domain.thy` doesn't exist; the real target is
`Abstract_Domain.thy` under `Generic/Domain/`). Then re-interpret
Sign/Interval through `non_rel_env`. This part is exactly Option 1's cost
profile (touches every existing box-domain instance to prove the refactor is
behavior-preserving) plus new functor-composition proof obligations Option 1
doesn't have. A relational domain still needs everything Option 2's
retargeted plan needs (its own `dgs_*`, its own `gammaDG`), since — as with
Options 1 and 3 as originally scoped — this issue's exit criteria never
mention the DG layer at all.

**Proof impact.** Unchanged: DG layer, same as the other two. Requiring
generalization: every existing box-domain file, to prove the split
reproduces current behavior (`sign_pipeline_invariant_sound`/
`goblint_sign_sound`-shaped acceptance tests, per the issue's own text —
names likely stale post-restructuring, unverified). New abstraction lemmas:
the `non_rel_env` functor's own soundness (that pointwise-lifting a sound
scalar domain yields a sound `env_domain`) — a real, nontrivial lemma with
no existing counterpart in this codebase to reuse, unlike Option 2's reuse
of `gamma_state_*`.

**Cost estimate.** 2 weeks for the split itself (issue's own figure) is
plausible for the mechanical part; it does not include what either
Option 1 or Option 2 would need beyond that, since it "gates #15 (Octagon)"
rather than delivering it. Epic #25's 10-12 week total figure spans the
whole octagon track, not this piece specifically. Risk: medium — touches
every existing box instance like Option 1, with a less-precedented
composition pattern in this codebase than Option 2's plain locale reuse.

**Recommendation weight.** Middle: architecturally well-motivated (published
prior art, genuine conceptual clarity for *documenting* today's implicit
lift) but solves a problem adjacent to, not identical with, this document's
identified blocker, and costs roughly as much as Option 1 for a box-side
refactor a relational domain doesn't actually depend on.

---

## Answering "is any of the three sufficient" and the fourth option

**None of the three, executed exactly as scoped in their source documents,
is sufficient** — not because the mechanisms are wrong, but because all
three target the flat spine, which this project's own contract says isn't
the executed analysis path. Option 2's *mechanism* is sufficient once
retargeted; Options 1 and 3 remain real, valuable refactors of the box-domain
side of the codebase (Option 3 especially, as a piece of technical debt
worth paying down on its own literature-motivated merits) but neither is a
precondition for a relational domain to exist and run.

### Option 4 (proposed): no framework migration — add a relational instance directly against the existing `sound_dg_spec` locale

This is Option 2 with its target corrected, stated as its own option because
the correction changes the migration's *shape*, not just its file list: it
is purely additive (new files only), has no "first, generalize the spine"
phase, and is independently useful before any Scope A/B decision on Octagon
specifically, since the order-constraint toy domain from
`RELATIONAL_DOMAIN_PLAN.md`'s own Phase 0 is enough to prove the shape works
at low cost.

Phasing, in dependency order:

1. **Spike** (days): `Rel_Order_Domain.thy` — the `{x <= y}` pair-set domain,
   its `bounded_semilattice_sup_bot` instance, `gammaDG`, and a hand
   discharge of `sound_dg_spec`'s four obligations for an *intraprocedural
   only* transfer set (`dgs_assign`/`dgs_assume`/`dgs_assume_not`; `dgs_enter`
   and `dgs_combine_env`/`dgs_combine_assign` stubbed conservatively — havoc
   local relations at the call boundary, matching `RELATIONAL_DOMAIN_PLAN.md`'s
   own MVP decision, still the right call here). Exit criterion, mirroring
   that plan's own Phase 0 gate: if this does not go through cleanly, Option
   2/4's premise is wrong and needs revisiting before any further step.
2. **A real end-to-end example** (a small program, mirroring
   `Example_Interval_DG_Flagship.thy`'s shape) exercising the new instance
   through the DG post-solution soundness theorem — proves "sound on paper"
   converts to "an example the same way Sign/Interval examples work,"
   without yet needing an executable/code-gen bridge.
3. **Executable bridge** (separate scope, only if a runnable/GraphViz path
   is wanted): a new `'d st`-shaped representation fit for the relational
   carrier and a new `Exec_*_Bridge.thy`, analogous to `Exec_DG_Bridge.thy`.
   `Exec_St.thy`'s two-region association list does not generalize
   verbatim, but its *construction* — a finite representation plus an
   implicit default for everything not explicitly tracked, quotiented by
   `eq_st` down to the values it actually distinguishes — is a reusable
   pattern for building one. Each relational domain still needs its own
   representation and algorithms discharging that pattern: near-trivial for
   order-constraints/difference-bound style domains, substantial for
   octagon closure or polyhedral normalization (see "Known limitations"
   below). The difficulty scales with the domain's own math, not with this
   step of the framework.
4. **Interprocedural combine, precisely** — deferred, matching every
   existing document's own honest scoping (`RELATIONAL_DOMAIN_PLAN.md` line
   115: "research-grade extension, out of MVP scope"). Nothing in this
   session's investigation changes that assessment; it remains the one
   piece where "this is hard" is not an artifact of wrong scoping.
5. **Context-sensitivity** — deferred, additive, ~245-line-file-sized new
   locale (Gap 4's own estimate for the *homogeneous* case; a relational
   `gammaDG`'s version would be comparable), built only when a concrete
   instance needs it — matches how the current Interval flagship itself
   doesn't need it either.

**If Octagon specifically (not just a toy relational domain) is the actual
target**, epic #25's difficulty register (DBM canonical closure, join
non-triviality, widening, backward transformers) is unaffected by any of
this — those costs are intrinsic to Octagon, not to which of the four
architecture options is chosen, and epic #25's Scope A/Scope B supervisor
decision remains the right gate for that question, independent of this
document's recommendation.

---

## Known limitations of Option 4 — traced against actual Goblint source

Checked directly against `src/cdomains/apron/relationDomain.apron.ml` and
`src/analyses/apron/relationAnalysis.apron.ml` on `goblint/analyzer`. These
are genuine gaps between `sound_dg_spec`'s current interface and what
Goblint's own relational analyses do — but each is a **bounded, deferrable
extension**, not evidence against the recommendation. None of them
disqualifies a specific relational instance from being added today; they
constrain what that instance can express, or what a *later* instance might
need.

### A. `sound_dg_spec` says nothing about how `'D`/`'G` are represented internally

The locale only requires `bounded_semilattice_sup_bot` — this is enough for
soundness, but prescribes nothing about variable environments, projection,
removal, or normalization. A relational domain has to build all of that
itself, inside its own `'D`/`'G`:

```text
RelState =
  tracked variables
  + finite constraint representation
  + implicit top/bot for untracked variables
```

This is not a gap in the framework — it is precisely the freedom the opaque
carrier is supposed to grant. It does mean a relational instance carries
real internal complexity that Sign/Interval's `vname => 'a` shape doesn't
have to. Confirmed against Goblint's actual `RD` signature
(`relationDomain.apron.ml`), which threads `vars`/`add_vars`/`remove_vars`/
`keep_vars`/`forget_vars` through nearly every operation — exactly this
bookkeeping, done in OCaml instead of HOL.

### B. `dgs_combine_env` is total; Goblint's `combine_env` is partial

Current signature:

```isabelle
dgs_combine_env :: "'dl => 'dl => 'dg => 'dg * 'dl"
```

Goblint's `combine_env` (`relationAnalysis.apron.ml:385-438`) unifies two
differently-scoped relational states and can discover the result is
infeasible:

```ocaml
let unify_rel = RD.unify new_rel new_fun_rel in
if RD.is_bot_env unify_rel then begin
  raise Deadcode
end;
```

**Not required for soundness.** A conservative relational instance can
always return an over-approximation (e.g. `top`, or the least-precise state
that still satisfies `combine_sound`) instead of detecting infeasibility —
that is strictly sound, just less precise than Goblint. Detecting
infeasibility is a precision/dead-code feature, not a soundness obligation.

**If wanted later**, the natural extension is a return type that can signal
failure —

```isabelle
dgs_combine_env :: "'dl => 'dl => 'dg => ('dg * 'dl) option"
```

or an explicit `Dead | State (...)` result type — threaded through
`dg_spec_combine_tree`/`sound_dg_spec`'s `combine_sound` obligation
(`gammaDG d' g' = {}` on the dead branch). This changes `dg_spec`'s record
shape and every existing instance's combine field, so it is **not** part of
adding one new relational instance — it would be its own, later,
opt-in migration once a domain actually needs to detect infeasible
unification to stay competitive with Goblint's precision.

### C. Goblint's combine uses a cross-analysis query (`MayBeTainted`); the DG layer has no query mechanism

```ocaml
let tainted = f_ask.f Queries.MayBeTainted in
```

(`relationAnalysis.apron.ml:421-422`) — decides which caller-local variables
to conservatively drop based on what another analysis reports as possibly
mutated by the call. `dgs_combine_env`'s signature has no channel for this;
neither does anything else in the DG framework. Matches
`SPLIT_STATE_MIGRATION.md`'s own independent finding: "no Goblint-style
manager/query interface... analyses cannot communicate through typed
queries" (`docs/SPLIT_STATE_MIGRATION.md`, Framework limitations #1 of the
Analysis-limitations table).

**Not required for soundness** — omitting it means keeping more state
conservatively (sound, less precise), never less. **Should not be added to
`sound_dg_spec`** to support one relational instance: a query interface is
infrastructure an arbitrary number of future analyses would share, and
belongs above this locale as its own layer, not folded into the combine
signature of the first relational domain that wants it.

```text
                 DG framework
                      |
              sound_dg_spec  (generic over 'D, 'G; done)
                      |
        +-------------+-------------+
        |                           |
   non-relational              relational
   Sign / Interval /           order-constraints / equalities / ...
   Mixed Sign-Interval              |
                             own lattice + gammaDG
                                     |
                             own executable representation
                             (pattern reused from Exec_St.thy,
                              not the type itself)

Deferred, opt-in, later extensions (not needed to add one instance):
  - partial/failure-aware combine  (dgs_combine_env -> ... option)
  - cross-analysis query manager   (Goblint-parity precision)
  - context-sensitivity locale     (only if an instance wants it)
```

---

## Recommendation

**Option 4 / retargeted Option 2**, ranked against the requested criteria:

1. **Correctness** — reuses `sound_dg_spec`'s existing, proven-three-times
   obligation shape; no new soundness architecture invented, only a new
   interpretation of an existing one.
2. **Isabelle maintainability** — matches this codebase's dominant idiom
   (locale + `interpretation`) rather than introducing type classes this
   project has already tried once and not kept, or a functor pattern with no
   precedent here.
3. **Ability to add relational domains** — direct: a relational domain is a
   `dg_spec` instance plus a `gammaDG`, exactly the shape `unit_dg_spec`/
   `indep_dg_spec`/`mixed_si_spec` already demonstrate for other carriers.
4. **Minimal unnecessary rewrite** — the only one of the four whose first
   phase touches zero existing files.
5. **Preserving existing verified Sign/Interval work** — by construction;
   nothing under `Instances/Sign`, `Instances/Interval`, or the DG framework
   files changes.

Options 1 and 3 remain legitimate, separately-motivated refactors of the
box-domain side of the codebase — worth doing on their own merits (Option 3
especially, for documenting today's implicit pointwise lift against
published prior art) — but neither should be treated as a prerequisite for
Gap 5, and bundling either with the relational-domain question risks the
same outcome `DOMAIN_TYPECLASS_MIGRATION.md` had: real, completed work that
doesn't end up load-bearing for what the project needs next.

**This remains a supervisor-level decision**, per the original instruction —
delivered as design input, not started. The one action item that doesn't
require a decision either way: `RELATIONAL_DOMAIN_PLAN.md`'s and issue #19's
stale file citations should be corrected before anyone treats either as an
executable plan, independent of which option is picked.

**On the three known limitations above:** none of them blocks adding a new,
sound relational analysis under Option 4 — they bound how much Goblint-level
precision that first instance can match, not whether it can exist. Do not
fold `dgs_combine_env`'s optional/failure variant or a query interface into
the initial migration; that would turn "plug in a relational domain" into a
`dg_spec`-record redesign affecting every existing instance, which is
exactly the unnecessary-rewrite risk this document argues against elsewhere.
Revisit both only when a concrete instance's precision, not architecture,
demands it.

---

## Deep dive: a minimal executable octagon-like domain under Option 4

Scoped exactly as asked: efficiency and Goblint/Apron precision parity are
explicitly out of scope; the goal is a verified, executable instance;
`sound_dg_spec` is not touched. Every claim below is checked against an
actual concrete design, not asserted in the abstract — this is the design
`Rel_Order_Domain.thy` would become if pushed one step past a two-variable
toy.

### 1. Minimal executable octagon design

Real DBM-based octagon (Miné) has two jobs bundled together that this task's
constraints let us pull apart: **precision** (closure — deriving implied
constraints via shortest-path propagation) and **representation**
(constraints over a doubled 2n-variable graph, dense matrix). Neither is
needed for soundness. `combine_sound`/`step_sound`/`enter_sound` only ask
that the transfer functions *over-approximate*; closure is what makes a
*non-closed* over-approximation *tighter*, not what makes it *sound*. A
domain that never closes is strictly less precise than real octagon, and
still perfectly sound — matching the task's stated priority exactly.

**Representation.** A finite (via the executable bridge) partial map from
*signed variable pairs* to a bound:

```isabelle
type_synonym svar = "vname \<times> bool"   (* (x, True) ~ +x, (x, False) ~ -x *)
type_synonym 'd oct = "(svar \<times> svar) \<Rightarrow> eint"
```

reusing the extended-integer type already in this codebase
(`Interval_Bounds.thy:9`: `datatype eint = MinInf | Fin int | PlusInf`).
Entry `d ((x, sx), (y, sy))` is the tightest known bound `c` in
`sx*x + sy*y <= c` (`Fin c`), or `PlusInf` (no constraint known) /
`MinInf` (impossible — empty concretization for that constraint alone).
Single-variable bounds are the degenerate diagonal case `x = y`; whether to
support them is a scoping choice, not a design obstacle, so a genuinely
minimal first cut can skip them entirely and only track two-variable
sum/difference constraints — still "octagon-like," and addable later by the
same recipe.

**Do we need DBMs?** No — this *is* a DBM in the loose sense (a map keyed by
variable pairs to a bound), just without the dense n×n array, the
closure algorithm, or the doubled-graph encoding that closure needs. A
plain constraint map is the simpler representation the task's own framing
(no efficiency requirement) calls for. Worth being explicit about what this
costs, not just that it's acceptable: without closure, this is a **raw
constraint table**, not a closed octagon, and the two behave differently on
*inference*, not just performance. `x - y <= 5` and `y - z <= 5` together
imply `x - z <= 10` in a closed octagon; a raw table storing only the two
given entries simply does not have an `((x,+),(z,-))` entry at all —
`PlusInf`, unconstrained — and never derives one. `gamma` of the raw table
is still perfectly sound (it doesn't claim the implied fact, so it can't
claim it wrongly), just weaker than the closed domain's `gamma` would be.
This is the precision the task's constraints explicitly license giving up.

**Join.** Pointwise `max` on `eint` per entry — soundly weakening two
constraint sets to their common upper bound, exactly the shape Interval's
own join already uses at the bound level. Concretely: if one operand knows
`x - y <= 5` and the other knows `x - y <= 10`, the sound merge is `<= 10`
(`max 5 10`), the *looser* of the two — `gamma(<=5) \<subseteq> gamma(<=10)`, so
`10` is the valid upper bound on the union, not `5`. `MinInf` is deliberately
the bottom of this order (an "impossible" bound is the most restrictive
value, `gamma_entry ... MinInf = {}`) and `PlusInf` the top (no constraint,
`gamma_entry ... PlusInf = UNIV`), so "smaller `c` in `Fin c` = more
precise, closer to bottom" throughout — getting this direction backwards
(e.g. treating a tighter bound as "larger") is the easy mistake to make and
the one place in this design worth double-checking against a concrete
numeric example like the one above before trusting it.

**The key structural observation:** this representation has *exactly the
same shape* as `abs_state = vname => 'a`, just reindexed from `vname` to
`svar \<times> svar`. Every argument this document has made about `abs_state`
being "an indexed function into a `sound_domain`-like codomain" applies
verbatim with the index set swapped. This is not a coincidence to route
around — it's the cheapest possible design, and it's why the rest of this
section comes out easier than it might look at first glance.

### 2. Required Isabelle obligations

**`gammaDG`.** Define a per-entry concretization
`gamma_entry :: svar => svar => eint => store set`,
`gamma_entry (x,sx) (y,sy) b = {s. of_sign sx (s x) + of_sign sy (s y) \<le> b}`
(`\<le> MinInf` reads as always-false, `\<le> PlusInf` as always-true — same
convention `eint`'s existing `ord` instance already gives Interval's
bounds), then
`gammaDG d = {s. \<forall>i. s \<in> gamma_entry (fst i) (snd i) (d i)}` — a pointwise
indexed intersection, structurally identical to
`gamma_state \<sigma> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}` (`Abstract_Domain.thy:58-59`).

**`gammaDG_mono`, join soundness.** Traced directly:
`gamma_state_mono`/`gamma_state_bot`/`gamma_state_sup_ub1`/`_sup_ub2`
(`Abstract_Domain.thy:77-97`) are each one line —
`unfolding gamma_state_def le_fun_def` (or `sup_fun_def`/`bot_fun_def`)
`using gamma_mono ... by blast` — because `\<le>`/`\<squnion>`/`bot` on `abs_state`
already come from HOL's pointwise `fun` instance
(`instance "fun" :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot`,
`Abstract_Domain.thy:33`), so the whole-state lemma is just the per-index
lemma pushed through `\<forall>`. The identical move works for `'d oct`, **once
one small prerequisite is discharged**: `eint` currently has only a
`linorder` instance (`Interval_Bounds.thy:36-44`), not
`bounded_semilattice_sup_bot` — that instantiation
(`sup = max`, `bot = MinInf`, `top = PlusInf`, all immediate from `linorder`)
doesn't exist yet and needs writing, but it's standard and small (a handful
of `simp`-closed obligations from `max`'s known algebraic laws), not project
-specific work. Once done, `svar \<times> svar => eint` gets
`bounded_semilattice_sup_bot` **for free** from the same `fun` instance
`abs_state` itself relies on — zero new *algebraic* proof (idempotence,
commutativity, `x \<le> x \<squnion> y`) for the octagon-shaped type itself, since
that's inherited wholesale from the generic `fun` instance.

**This is narrower than "the whole join theorem is free," and worth being
precise about.** The *algebraic* semilattice laws are free; the *semantic*
soundness facts (`gammaDG_mono`, `gamma_sup_ub1`/`_ub2` — "the join
concretization is a genuine over-approximation, not just an
order-theoretic lattice element") still have to be proved, same as
`gamma_state_mono` etc. are proved, not assumed, for `abs_state` today. What
"free" buys is that this proof is the *same one-line pattern* already on
file for the
octagon-shaped type itself. `gammaDG_mono` and the two `sup_ub` facts then
transfer by the exact same one-line unfold-and-blast pattern, parametrized
over the pair index instead of a bare variable.

**Assign soundness.** Same difficulty class as Sign/Interval's own assign
lemmas: a finite case split on the syntactic shape of the right-hand side.
Handle `x := c` and `x := y` precisely (tighten/copy the relevant entries);
fall back to `forget x` (map every entry mentioning `x` to `PlusInf`) for
anything else. `forget`'s soundness is one generic, reusable lemma
("weakening constraints to `PlusInf` only grows `gammaDG`") proved once and
reused by every fallback case — not re-derived per syntactic shape.

**Assume soundness.** Same shape: recognize `x - y <= c`/`x + y <= c`-style
conditions and tighten one entry; no-op (sound, just imprecise) on anything
else. Comparable effort to Sign/Interval's own `assume`/`assume_not`
lemmas — a bounded case list, not open-ended.

**Enter/combine soundness — the one place this task's "don't care about
precision" mandate does real work.** The general relational IP-combine
problem (projection + meet across differently-scoped states) remains
genuinely hard and is *not* solved here, consistent with every prior
document's own scoping. But `sound_dg_spec`'s four obligations don't require
solving it *precisely* — they require it *soundly*. A legitimate minimal
`dgs_enter`: bind the new locals/formals to `PlusInf` (fully unconstrained,
trivially sound — `gammaDG` of an all-`PlusInf` map is `UNIV`). A legitimate
minimal `dgs_combine_env`/`dgs_combine_assign`: forget every entry that
mentions a variable the callee could have touched, keep the rest — the same
"forget is sound" lemma `dgs_assign`'s fallback case already needed, reused
rather than rederived. This discharges `combine_sound`/`enter_sound`
completely, at the cost of near-zero relational precision across calls —
an honest, working, *sound* interprocedural story, not a stub that leaves a
`sorry`. Tightening it later (real projection+meet) is additive, exactly
like the deferred partial-combine/query-interface items above.

### 3. Executability

**Does it need the `Exec_St.thy` trick?** Yes, and for the identical
reason `abs_state` needed it: `svar \<times> svar => eint` is a function from an
infinite index set (`vname` is unbounded), so it isn't directly
code-generatable any more than `vname => 'a` is. The fix is the same
recipe — a `quotient_type` over a finite representation
(default value + explicit finite override list) plus `lift_definition` for
every operation, exactly `Exec_St.thy`'s `'a st_rep = 'a \<times> 'a \<times> (vname \<times> 'a) list`
pattern, reindexed. It is actually **simpler** than `Exec_St.thy`'s own
`st`, which needs *two* region defaults because `is_global` splits `vname`
into two infinite classes that legitimately need different defaults inside
one carrier. A single relational carrier (playing the role of `'dl` or
`'dg` in `dg_spec`, which are already split by the DG layer itself) only
needs **one** default (`PlusInf`, "no constraint") and one finite override
list of `((svar \<times> svar) \<times> eint) list` — one region, not two.

**What's executable, what isn't — same split as every existing instance.**
`gammaDG`/`gamma_entry` are specifications (store-set-valued predicates),
not meant to be executed, exactly like `gamma`/`gamma_state` today. What
needs to be executable is the operational side: `sup`/`bot` on the lifted
`oct st`-analogue, and `dgs_assign`/`dgs_assume`/`dgs_assume_not`/
`dgs_enter`/`dgs_combine_env`/`dgs_combine_assign` as `lift_definition`s
over the finite representation — the same recipe `Ivl_Exec.thy`'s
`enter_ivl_st`/`top_ivl_st`/`cinit_ivl_st` already demonstrate
(`Ivl_Exec.thy:139-168`), connected back to the abstract definitions by a
`fun_of_st`-style commute lemma per operation, exactly as
`enter_frame_ivl_st_commute` does today (`Ivl_Exec.thy:143-146`). `eint`
already has decidable equality and a computable `ord`/`plus`/`minus`, so
nothing about the codomain blocks code generation; association lists and
`eint` are both ordinary code-generatable HOL. `export_code`/`value` work on
this the same way they already do on `ivl st`/`sign st`.

### 4. Scope comparison

| | Minimal executable (this design) | Goblint-compatible octagon | Apron-style octagon |
|---|---|---|---|
| **DG-framework cost** (`sound_dg_spec` itself) | None — interpreted as-is | None — same locale, same four obligations | None — same locale, same four obligations |
| **Abstract-domain math** | Small: no closure, `sup=max`, bounded case-split transfers, conservative combine | Large: real closure (Floyd-Warshall-style shortest-path over the doubled graph), Miné's full transfer-function case table for precision, closure soundness *and* completeness proofs — "no reusable Isabelle prior art... mechanization from scratch" (epic #25's own words) | Not internal — trust question instead: either reduces to the "Goblint-compatible" column's math (if reimplemented natively) or requires inventing a certifying-oracle trust architecture around the real C library (Verasco-style a-posteriori certificate checking) |
| **Executable representation** | Small: one-default finite map, same recipe as `Exec_St.thy`, reused not reinvented | Moderate: the closure algorithm itself must be implemented and shown computable (efficiency still not required, but the algorithm is real work either way) | Either the "Goblint-compatible" column's cost, or FFI/external-library integration entirely outside Isabelle's code generator's normal scope — categorically different engineering, not "more of the same" |
| **Rough scale** | Days-to-low-weeks (comparable to the `Rel_Order_Domain.thy` spike, plus the two-variable indexing) | Weeks-to-months (matches epic #25's own ~4-6 week octagon-specific estimate within its larger Scope B figure) | Not comparably scoped — a different kind of project, not a bigger version of this one |

### Evaluating the expected conclusion

**Holds, with one sharpening worth stating explicitly.** DG-framework
integration cost is flat at zero across all three rows — confirmed by
actually designing the minimal instance, not just argued abstractly: the
same `gammaDG`, the same four obligations, the same `dgs_*` field shapes
apply whether the domain behind them is a two-line toy or a real closure
algorithm. What scales is column two (the domain's own math) and, for a
literal Apron dependency, column three becomes a different *kind* of
problem rather than a harder version of the same one.

The sharpening: "the domain implementation is the hard part" is true, but
*how hard* is a choice this task's own constraints already make for you.
A minimal, sound, executable, octagon-*shaped* domain — not
Goblint-parity, not fast, just real and machine-checked — is not a hard
problem under Option 4. It is the same size of effort as the `Rel_Order_Domain.thy`
spike already scoped earlier in this document, because skipping closure and
accepting a conservative interprocedural story (both explicitly licensed by
"we don't care about efficiency or matching Goblint") removes the two
things that make octagon hard in the literature. What remains genuinely
hard — DBM closure, precision parity, Apron/certificate-based trust — is
optional precision work this task's own framing puts out of scope, not a
prerequisite for "a verified, executable relational analysis instance
exists."

---

## Minimal Isabelle design sketch — an Option 4 feasibility prototype, not Goblint parity

Below is a concrete sketch, not proved or written into any `.thy` file. It
exists to answer one question precisely: *can a nontrivial relational
executable domain be added without touching the DG architecture?* — not
"can we implement octagons." Types and definitions are illustrative Isabelle
syntax; naming, exact case splits, and lemma statements would be settled
during actual development, not fixed here.

### 1. Isabelle datatypes

```isabelle
type_synonym svar = "vname \<times> bool"        (* (x, True) ~ +x, (x, False) ~ -x *)
(* eint reused as-is from Interval_Bounds.thy *)

type_synonym oct = "(svar \<times> svar) \<Rightarrow> eint"  (* abstract carrier, non-executable *)

(* executable representation, Exec_St.thy-shaped: one default + finite overrides *)
type_synonym oct_rep = "eint \<times> ((svar \<times> svar) \<times> eint) list"

fun fun_rep_oct :: "oct_rep \<Rightarrow> (svar \<times> svar) \<Rightarrow> eint" where
  "fun_rep_oct (d, ps) = (\<lambda>k. case map_of ps k of Some b \<Rightarrow> b | None \<Rightarrow> d)"

quotient_type oct_st = oct_rep / "\<lambda>r1 r2. fun_rep_oct r1 = fun_rep_oct r2"
  by (auto intro: equivpI reflpI sympI transpI)
```

`oct_rep` needs only *one* default (unlike `Exec_St.thy`'s `st_rep`'s two
region defaults), because nothing about the `svar \<times> svar` index set
partitions into two differently-defaulted infinite classes the way
`is_global` splits `vname` — a relational carrier used inside `dg_spec`
already gets its local/global split for free from `dg_state`'s two separate
fields (`'dl`, `'dg`), each independently instantiated by this one type.

### 2. Lattice instances needed

```isabelle
instantiation eint :: bounded_semilattice_sup_bot begin
  definition sup_eint :: "eint \<Rightarrow> eint \<Rightarrow> eint" where "sup_eint = max"
  definition bot_eint :: "eint" where "bot_eint = MinInf"
  instance (* idempotence/commutativity/assoc/x \<le> x \<squnion> y, ord already linorder *)
end
```

then `svar \<times> svar \<Rightarrow> eint` inherits `bounded_semilattice_sup_bot` from HOL's
existing `instance "fun" :: (type, bounded_semilattice_sup_bot)
bounded_semilattice_sup_bot"` — no separate instantiation for `oct` itself.
`oct_st` needs its own small `order`/`sup`/`bot` instantiation via
`lift_definition`, the same shape as `Exec_St.thy`'s `less_eq_st`/`sup_st`/
`bot_st` (`Exec_St.thy:187,255,267`).

### 3. `gamma` definition

```isabelle
definition sval :: "bool \<Rightarrow> int \<Rightarrow> int" where
  "sval sgn v = (if sgn then v else -v)"

definition gamma_entry :: "svar \<Rightarrow> svar \<Rightarrow> eint \<Rightarrow> store \<Rightarrow> bool" where
  "gamma_entry i j b s = (case b of
      MinInf \<Rightarrow> False
    | PlusInf \<Rightarrow> True
    | Fin c \<Rightarrow> sval (snd i) (s (fst i)) + sval (snd j) (s (fst j)) \<le> c)"

definition gammaDG_oct :: "oct \<Rightarrow> oct \<Rightarrow> store set" where
  "gammaDG_oct d g = {s. (\<forall>i j. gamma_entry i j (d (i,j)) s)
                        \<and> (\<forall>i j. gamma_entry i j (g (i,j)) s)}"
```

(`gammaDG` for `sound_dg_spec` takes two carriers, `'D`/`'G` — sketched here
as the same `oct` type for both, i.e. a homogeneous instance, the simplest
case; a `'D \<noteq> 'G` instance is a direct extension, not a different design.)

### 4. `assign`/`assume`/`enter`/`combine` definitions

```isabelle
definition oct_forget :: "vname \<Rightarrow> oct \<Rightarrow> oct" where
  "oct_forget x d = (\<lambda>(i,j). if fst i = x \<or> fst j = x then PlusInf else d (i,j))"

fun oct_assign :: "vname \<Rightarrow> aexp \<Rightarrow> oct \<Rightarrow> oct" where
  "oct_assign x (N c) d = (oct_forget x d)  (* + tighten the (x,x)-diagonal entry to encode x = c, optional *)"
| "oct_assign x (V y) d = (oct_forget x d)  (* + copy every (y,*)-entry to the matching (x,*)-entry *)"
| "oct_assign x _     d = oct_forget x d"   (* fallback: sound, imprecise *)

fun oct_assume :: "bexp \<Rightarrow> oct \<Rightarrow> oct" where
  "oct_assume (Le (Plus (V x) (Times (N -1) (V y))) (N c)) d =
     d((( x,True),(y,False)) := min_eint (d ((x,True),(y,False))) (Fin c))"
| "oct_assume _ d = d"                      (* fallback: sound no-op *)

definition oct_enter :: "vname list \<Rightarrow> aexp list \<Rightarrow> oct \<Rightarrow> oct \<Rightarrow> oct \<times> oct" where
  "oct_enter xs es dc g = (g, \<lambda>_. PlusInf)"  (* fresh locals, fully unconstrained *)

definition oct_combine_env :: "oct \<Rightarrow> oct \<Rightarrow> oct \<Rightarrow> oct \<times> oct" where
  "oct_combine_env dc de g =
     (g, \<lambda>k. if fst (fst k) \<in> touched_by_call \<or> fst (snd k) \<in> touched_by_call
              then PlusInf else dc k)"        (* conservative: forget anything the call could reach *)

definition oct_combine_assign :: "vname option \<Rightarrow> oct \<Rightarrow> oct \<Rightarrow> oct \<times> oct \<Rightarrow> oct \<times> oct" where
  "oct_combine_assign dst de g merged = (case dst of
      None \<Rightarrow> merged
    | Some x \<Rightarrow> (fst merged, oct_forget x (snd merged)))"  (* destination gets no relational info: sound *)
```

Every fallback branch (`oct_assign`'s catch-all, `oct_assume`'s catch-all,
`oct_combine_env`'s "forget anything touched") is the *same* `oct_forget`
lemma, proved once. This is deliberate — precision differences between a
"minimal" and a "tighter" version of this domain later would only add more
precise *cases*, never change the soundness argument for the existing ones.

### 5. Expected proof obligations

| Obligation | Count | Difficulty |
|---|---|---|
| `eint :: bounded_semilattice_sup_bot` instance | 1 instantiation, ~4 small lemmas | Easy — standard `linorder`-derived facts |
| `gamma_entry` mono / `Fin`-case sup-soundness | ~3 lemmas | Easy — one arithmetic inequality each |
| `gammaDG_oct` mono / bot / sup-ub (×2 for `'D`,`'G`) | ~4 lemmas | Easy — same `le_fun_def`/`sup_fun_def` unfold-and-`blast` pattern as `gamma_state_mono` |
| `oct_forget` soundness (the one lemma every fallback reuses) | 1 lemma | Easy-moderate — "weakening an entry to `PlusInf` only grows `gamma_entry`" |
| `oct_assign` per-case soundness (`N`, `V`, fallback) | ~3 lemmas | Same class as `Sign_Transfer.thy`'s / `Interval_Transfer.thy`'s existing assign lemmas |
| `oct_assume` per-case soundness (recognized shape, fallback) | ~2-4 lemmas | Same class as existing assume lemmas |
| `dgs_enter`/`dgs_combine_env`/`dgs_combine_assign` soundness | ~3 lemmas | Easy, by construction — each reduces to `oct_forget`'s soundness plus "unconstrained is always sound" |
| `sound_dg_spec`'s four top-level obligations | 4 lemmas | Assembly from the above — comparable to `mixed_si_spec_indep`'s existing proof |

Roughly 20-25 lemmas total, essentially all in the size class this
codebase's existing Sign/Interval transfer-soundness lemmas already are —
no single obligation here is harder than what `Sign_Transfer.thy`/
`Interval_Transfer.thy` already discharge.

### 6. Estimated implementation size

| File (new) | Role | Rough size (comparable existing file) |
|---|---|---|
| `Rel_Octagon_Domain.thy` | `oct` type, lattice instance, `gamma`, `dgs_*`, `sound_dg_spec` interpretation | ~200-300 lines (cf. `Sign_Transfer.thy`) |
| `Rel_Octagon_Exec.thy` | `oct_st`, `lift_definition`s, commute lemmas | ~150-250 lines (cf. `Ivl_Exec.thy`) |
| `Example_Octagon_DG_Flagship.thy` | one worked end-to-end example | ~50-100 lines (cf. `Example_Interval_DG_Flagship.thy`) |

~400-650 lines of new Isabelle total, zero lines changed in any existing
file. Matches the "days-to-low-weeks" estimate given earlier, now
decomposed by file rather than asserted as a single number.

**Conclusion this sketch was built to test:** yes — a nontrivial relational
executable domain fits under `sound_dg_spec` without any change to the DG
architecture. Every piece above is either a direct reuse of an existing
codebase pattern (`fun`-instance lattice inheritance, the `le_fun_def`/
`sup_fun_def` soundness-proof shape, `Exec_St.thy`'s quotient/override-list
executable bridge) or a small, bounded, Sign/Interval-sized proof obligation
— nothing in this sketch required inventing new proof infrastructure.

---

## Architectural validation (completed)

The sketch above was built out as a real, checked prototype:
`src/Analysis/Instances/Relational/Rel_Order_Domain.thy`. It tracks a finite
set of known `x <= y` facts between pairs of variables (`relc`, a wrapped
`(vname * vname) set` with a reverse-subset order, intersection join, and a
`bounded_semilattice_sup_bot` instance), with no closure and no
normalization — the deliberately-minimal, deliberately-imprecise scope this
document's Option 4/2 recommendation called for. The carrier is not
`abs_state` and contains no `vname => 'a` function type anywhere.

```isabelle
interpretation rel_order: sound_dg_spec rel_order_spec gammaDG_rel
proof
  ... (* gammaDG_mono, step_sound, combine_sound, enter_sound *)
qed
```

All four `sound_dg_spec` obligations are discharged. Batch build of
`Voblint_Analysis` (and, incidentally, the downstream `Voblint_Formalization`
and `Voblint_Examples` sessions, which re-verified clean in the same run)
finished exit code 0, zero `FAILED`/error/`sorry` anywhere in the log.
`git diff --stat` against the rest of the framework shows exactly one line
changed outside the new file: `src/Analysis/ROOT` registering the theory
name. `DG_Framework.thy`, `DG_Soundness.thy`, and every existing Sign/
Interval/Mixed instance are untouched.

This empirically validates the architectural claim underlying Option 4:
`sound_dg_spec` admits genuinely relational carriers, and a new relational
analysis is a new interpretation, not a framework migration. Remaining work
toward a useful relational domain (closure/precision, an executable
representation, richer domains such as octagon) is domain-implementation
work, per the "Deep dive" and "Minimal Isabelle design sketch" sections
above — not further architecture work.
