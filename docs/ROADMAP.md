# Roadmap

This file records stable architectural direction. GitHub Project 8 contains
individual work items, dependencies, and scheduling.

## Sources of truth

| Question | Source |
| --- | --- |
| Open work and dependencies | [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8) |
| Current proof statements | `src/**/*.thy` |
| Open proof placeholders | `rg -n '^\s*sorry' src/` |
| Session structure | `ROOTS` and the session `ROOT` files |
| End-to-end proof narrative | `docs/PROOF_OVERVIEW.md` |
| Procedure-aware architecture | `docs/PROCEDURE_AWARE_CFG_ARCHITECTURE.md` |
| Deliberate exclusions | `docs/NON_GOALS.md` |

## Supported architecture

The supported pipeline is:

```text
IMP2 source
  -> procedure-aware CFG
  -> activation-local collecting semantics
  -> generic D/G equations
  -> verified side-effecting TD solver
  -> abstract post-solution
  -> source-level soundness
```

The source language uses explicit procedure calls and returns. Main completes
only by fall-through. Compiler certificates expose node ownership, local ranges,
call continuations, and matching result boundaries.

`valid_ltr`, `ltr_collect`, and `activation_collect` are the concrete semantic
targets. The equation system has three contribution families: ordinary local
edges, procedure entry, and return combination.

The generic D/G interface is the supported modular-analysis architecture. It
permits different local (`D`) and global (`G`) carriers, context-indexed local
unknowns, and analysis-defined shared-state routing. Sign, Interval, and mixed
Sign/Interval instances use the same solver and soundness infrastructure.

## Intentionally retired components

Retain is intentionally retired. Its routing discipline differs from the
Goblint-style D/G interface supported by this repository. Native D/G analyses
replace its intended modular-analysis role; no semantic equivalence with Retain
is claimed.

The live architecture also excludes:

- the plain top-down solver spine;
- the classical intra-procedural analysis pipeline;
- detached combine relations and synthetic call-entry actions;
- command-offset CFG path infrastructure;
- the AFP IMP2 bridge and VCG examples;
- trace-digest and compatibility-read layers.

Version control preserves their history. Live theories, examples, and public
documentation should not depend on them.

## Extension directions

### Context domains

Provide finite, executable context abstractions with a proved relation between
concrete activations and abstract keys. Evaluate precision separately from
soundness, especially for recursion and widening-heavy analyses.

### D/G communication

Extend the analysis-defined reader and publisher interfaces where examples need
more precise shared-state communication. Keep routing generic over the `D` and
`G` carriers.

### Placement-aware D/G generation (settled architecture)

The D/G spine has two abstraction levels over one implementation, not two
competing implementations:

```text
sound_dg_spec / sound_dg_spec_ltr        <- concise adapter, ordinary analyses
        |  sublocale (DG_Soundness.thy, DG_LTR_Sound.thy)
        v
sound_dg_hooks / sound_dg_hooks_ltr      <- framework-construction API
```

`sound_dg_hooks`/`sound_dg_hooks_ltr` (`src/Core/Solver/Context/DG/DG_Soundness.thy`,
`DG_LTR_Sound.thy`) generate D/G equations from arbitrary hook trees and prove
them sound generically. `sound_dg_spec` is `sound_dg_hooks` specialized to
`dg_spec`-record trees: one locale interpretation per analysis instance
(`step_sound`/`combine_sound`/`enter_sound`), no per-CFG-node proof
obligations. Since `sound_dg_spec <= hooks: sound_dg_hooks` is now a proved
sublocale, `sound_dg_spec`'s three obligations *derive* `sound_dg_hooks`'s
three hook obligations rather than re-proving the same soundness shape
independently — `dg_gen = hook_gen` is proved outright for this instance, not
merely approximated. Sign, Interval, Parity, Mixed, CallString, and Ctx all
stay on `sound_dg_spec`/`dg_ctx_activation`/`routed_context` permanently; none
of them needs migration to `sound_dg_hooks` directly, and none is planned.

`sound_dg_hooks` remains the right route only for analyses whose D/G equation
structure genuinely cannot be expressed as a `dg_spec` record — e.g. custom
owner-sensitive placement, where an edge's contribution depends on projecting
a joined D/G read by ownership rather than applying one fixed transfer. Two
worked examples exercise this directly:
`src/Examples/Interval/Example_Interval_Placement.thy` and
`src/Examples/Sign/Example_Sign_Placement.thy`. Treat them as framework
validation, not as templates for an ordinary analysis.

This settles an earlier, incorrect hypothesis: two example flagships
(`src/Examples/Sign/Exec_Sign_DG_Run.thy`,
`src/Examples/Parity/Example_Parity_DG_Flagship.thy`) were migrated onto
`sound_dg_hooks` directly, on the assumption that `sound_dg_spec` was a
duplicate implementation worth retiring. Both grew 5-6x (158->997,
269->1336 lines) for no closed soundness or drift risk — `sound_dg_spec` was
already classifier-generic, and the per-CFG-node proof burden `sound_dg_hooks`
requires is not needed by ordinary analyses. `docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`
documents the audit that found this; both flagships were reverted back to
`sound_dg_spec`. Do not propose migrating any further classic-route example
to `sound_dg_hooks` without new evidence that its D/G structure genuinely
needs the hook-tree level.

### Domain composition

The mixed Sign/Interval instance demonstrates heterogeneous carriers.
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) settled this: no
shared product/reduction layer is planned. `sound_dg_spec`'s carriers are
already opaque, so new heterogeneous or relational analyses (e.g.
`Rel_Order_Domain.thy`) are added directly against it.

### Cross-analysis query composition

Goblint's MCP layer answers expression queries (`EvalInt` and friends) by
meeting responses from every activated analysis, including recursively into
subexpressions and callee-side `combine`. Voblint's expression evaluation is
currently domain-local; the composite `int_dom` reduces internally between
its own Sign/Interval/Parity/Congruence components but has no cross-analysis
query channel. Design investigation tracked in #70; alignment inventory and
staging in #141.

### Numeric precision

Continue improving backward guard refinement, loop precision, widening policy,
and interval execution examples. Refinement work stays within the semantic
reference model of its time; the one sanctioned change to that model is the
machine-integer migration below.

### Machine integers (ikinds)

Give VIMP per-variable machine-integer kinds (width + signedness), wraparound
concrete semantics, and explicit casts, then thread the kind through the
domain interface so transfers can use `range ik` as a hard bound and
width-dependent domains (bitfield, DefExc) become definable. Staged plan and
locked design decisions: `docs/history/IKIND_MIGRATION.md`; register row
"Integer width and wraparound".

Known gap: `sound_transfer_for`'s `tf_sound_branch_for` obligation
(`src/Core/Equations/Constraint_System.thy`) supplies no `styped Gamma s` or
`wt_exp Gamma b (opk (esyn Gamma b))` fact, but each domain's `branch_*_sound`
lemma (e.g. `branch_sign_sound` in `src/Analysis/Instances/Sign/Sign_Backward.thy`)
requires both -- added for the Goblint-faithful backward-narrowing pivot
without updating this obligation or its callers. `sign_is_sound_transfer_for`
carries a `sorry` at this subgoal. Closing it means threading a well-typedness
invariant through the whole `sound_transfer_for` soundness chain, not a local
proof fix; it blocks every domain wired through `sound_transfer_for`
(Sign now, Interval/Parity/Int on the same pattern). Interval's own
`ivl_is_sound_transfer_for` (`src/Analysis/Instances/Interval/Interval_Transfer.thy`)
now carries the same `sorry`, for the same reason. The composite `int_dom`'s
three refinement-mode bundles in `src/Analysis/Instances/Product/Int_Transfer.thy`
(`int_never_is_sound_transfer_for`, `int_once_is_sound_transfer_for`,
`int_fixpoint_is_sound_transfer_for`) each carry the same `sorry` at their own
branch subgoal, for the same reason.

Scope audit (2026-08-26): the generic chain that would need to carry this
invariant is now mapped exactly. `Constraint_System_Sound.thy`'s
`edge_collect_apply_tf_sound_for` (in `context sound_transfer_for`) discharges
the `EA_Assume`/`EA_AssumeNot` cases via `tf_sound_branch_forD`; that feeds
`LTR_Abstract.thy`'s `ltr_collect_semantic_postfix` (`edge` obligation), cited
by `DG_LTR_Sound.thy`'s `dg_postfix_collect_sound_ltr_for` and
`hook_postfix_collect_sound_ltr`, in turn cited by `Run_Analysis_Sound.thy`'s
literal source-facing theorems (`run_source_sound`, `collect_sound`) and by
`DG_Base.thy`/`DG_Soundness.thy`'s context-sensitive siblings (2328 lines, a
dozen direct `sound_transfer_for.*` citations, dozens more derived). Adding
`styped Gamma s` to the branch obligation forces every `B`/`dg_gamma` in that
whole chain to carry a `styped Gamma` conjunct, not just the branch lemma.

Two prerequisites this needs are not built yet. First, no whole-program
well-typedness checker exists: `wf_source_program`/`wf_source_com`
(`src/VIMP/VIMP_Proc.thy`) take no `Gamma`/typing argument at all today, so
there is no fact anywhere that a compiled `EA_Assume`/`EA_AssumeNot` edge's
guard is well-typed -- this is `IKIND_MIGRATION.md`'s B3 stage ("Typing
layer"), not started. Second, `call_enter`/`combine_collect`
(`src/CFG/CFG_Def.thy`) have no `styped`-preservation lemmas; only the plain
per-variable `styped_update_norm`/`styped_update_taval` exist
(`VIMP_Typing.thy`). These look tractable on their own (same shape as the
existing preservation lemmas) but are unproven.

Separately, `src/Soundness/Run_Analysis_Sound.thy` -- the file holding the
actual source-facing endpoints this chain serves -- is itself currently
unbuildable (64 I/Q errors, checked 2026-08-26): a bare
`sound_transfer_for gs tf` assumption missing the now-required `Gamma`
argument, plus an `Unknown ancestor theory Voblint_Core.DG_Base_Exec` session
break. This is `IKIND_MIGRATION.md`'s own B6/B7 gate, recorded there as "not
yet met" -- so a change to the branch obligation cannot be verified end-to-end
against its real consumer until that unrelated breakage is fixed. Closing this
gap should sequence behind ikind migration B3/B6/B7, not attempt in isolation
alongside it.

Known gap: `backward_domain`'s `aval_abs` field
(`src/Core/Domain/Abstract_Domain.thy`) requires a typed evaluator
(`tyenv => ikind => exp => store => 'a`), since its narrowing math
(`inv_plus`/`inv_minus`/`inv_times`) is genuinely `ik`-dependent. Congruence's
`aval_congruence` (`src/Analysis/Instances/Congruence/Congruence_Arithmetic.thy`)
is still the old untyped, unbounded-int evaluator -- its `Plus`/`Minus`/`Times`
cases do not wrap at `ik` at all, and its own soundness fact is stated against
the plain `aval`, not `taval`. `congruence_backward_domain`'s interpretation in
`src/Analysis/Instances/Congruence/Congruence_Backward.thy` passes
`aval_congruence` where the typed `aval_abs` is expected and does not
type-check. A trivial typed wrapper that ignores `Gamma`/`ik` is not sound: it
would need `taval Gamma ik e s \<in> gamma (aval_congruence e sigma)`, strictly
stronger than the already-proven unbounded-evaluator fact, and false wherever
`ik` actually wraps. Closing this means deciding whether Congruence's
arithmetic needs the same elaboration/wraparound treatment Sign, Interval, and
Parity already have, which is a real semantic question, not a mechanical
typing fix. This predates the elaboration migration -- both gaps above trace
to the same commit that made `expression_domain_sound` and `backward_domain`
typed without updating every domain that interprets them.

Closed: Parity's `parity_cast` (`src/Analysis/Instances/Parity/Parity_Domain.thy`)
previously used the generic `a_cast_of` fallback, which widened every cast to
`top` regardless of value (`parity_lt` is unconditionally `None`, so
`a_cast_of`'s boundary-literal guard could never succeed). `parity_cast` is
now the identity: parity's modulus, `2`, divides every machine-width
wraparound modulus this project defines (`ik_bits ik >= 1` for every
`ikind`), so evenness/oddness survives `ik_norm` truncation unconditionally
(`even_ik_norm`), unlike a domain whose modulus does not divide every
wraparound modulus (Congruence, whose narrowing genuinely needs
`cong_cast`/`cong_unwrap`'s `gcd(m, ik_mod ik)` reasoning). The three
`Parity_Checks.thy` example lemmas that had been downgraded to `Check_Unknown`
now recover their original `Check_Proved`/`Check_Refuted` verdicts. `a_cast_of`
itself was removed from `Abstract_Arithmetic.thy` entirely once Sign's own
`sign_cast` (the only other consumer) was migrated off it to a bespoke,
strictly more precise cast: `SZero` stays exact at any kind, and an unsigned
target is always sound at `SNonNeg` (`ik_norm` for an unsigned kind always
lands in `[0, ik_max ik]`) rather than widening to `STop` the way the generic
fallback did for every non-zero sign value regardless of target.

### Source language

Arrays and richer types require explicit syntax, operational semantics,
compiler, and transfer extensions. They are not implicit consequences of the
scalar IMP2 proofs.

## Completion criteria

A feature belongs to the supported pipeline only when:

1. its source or CFG behavior is defined;
2. its equation contribution is executable;
3. its abstract transfer obligations are discharged;
4. its solver result is connected to collecting semantics;
5. its source-facing theorem is stated when applicable;
6. all affected sessions pass the batch build without `sorry`.
