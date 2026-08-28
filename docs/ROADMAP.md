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

Closed (elaboration migration): the `tf_sound_branch_for` gap recorded here --
each domain's `branch_*_sound` needing a `styped Gamma s` / `wt_exp` fact the
obligation did not supply -- no longer exists. The backward analysis was pivoted
to match Goblint's actual placement of the representability question: a variable
*read* applies no cast (`get_var` = `CPA.find`) and `refine_lv`'s `Var` case
applies no gate, so the gate belongs on the one node that is a conversion.
`afilter`'s `TCast` clause now consults the domain's own `a_in_range`, and
`tf_sound_branch_for`, `afilter_sound`, `bfilter_sound` and `branch_sound` carry
no typedness premise at all. Nothing propagates into `Constraint_System_Sound`,
`LTR_Abstract`, `DG_LTR_Sound` or `Run_Analysis_Sound`, and the `sorry`s that
stood at the four domains' `*_is_sound_transfer_for` are gone. `Run_Analysis_Sound.thy`
itself builds.

Closed (elaboration migration): Congruence's evaluator is no longer the untyped,
unbounded-int one. It is `aval_congruence_t :: texp => ...`, wrapping at each
node's own baked kind like every other domain, and `cong_cast`/`cong_unwrap`
carry the `gcd (m, ik_mod ik)` reasoning. `backward_domain`'s `aval_abs` takes a
`texp`, so no domain passes an evaluator of the wrong shape.

The one dynamic contract that remains, deliberately, is `styped Gamma s0` on the
source-facing theorems -- see `docs/PROOF_PHASES.md`. It is a premise on the
caller, not an internal side condition, and stays visible in the final theorems.

Closed (2026-08-26): `kjoin` implemented the usual arithmetic conversions as
"left operand wins", which is not C 6.3.1.8's rank-and-signedness rule. It
disagreed on the six ordered operand pairs whose left operand is the weaker
one, and -- worse than a wrong answer -- it made evaluation depend on operand
order, so `u32 == i64` and `i64 == u32` could disagree. It now delegates to
`usual_kind` (`src/VIMP/VIMP_Ikind.thy`), which writes out all six branches of
the standard's rule, including the final "unsigned counterpart of the signed
kind" case. That case is unreachable at the four kinds promotion can produce,
and `promoted_signed_covers_narrower_unsigned` proves it so for arbitrary
kinds rather than tabulating instances: whenever a promoted signed kind is
strictly wider than a promoted unsigned one it covers that unsigned range,
which is the standard's preceding case. `usual_kind_commute` and
`kjoin_commute` retire the order dependence; the sixteen-pair table
(`usual_kind_reachable_pins`) is regression evidence, not the proof.

Width stands in for C's conversion rank here. That is faithful for this kind
set because, after promotion, each rank class is represented by exactly one
width, with the signed and unsigned counterparts of a class sharing it --
comparing widths therefore compares ranks. It would *not* be faithful for C's
own types, where `int` and `long` may share a width while holding different
ranks. Introducing platform kinds is exactly the change that would invalidate
this, and `usual_kind`'s own comment says so.

Still open, in the same area:

- **Literal kinds are not magnitude-derived.** `esyn (N n) = None`, so `opk`
  defaults a bare literal to `int32`. `wide := 3000000000` with `wide : int64`
  therefore elaborates to `TCast I64 (TN I32 3000000000)` and evaluates to
  `-1294967296`. C 6.4.4.1 gives a decimal constant the first of
  int/long/long long that fits. The CLI lexer additionally caps literals at
  OCaml's 63-bit `max_int`, so `9223372036854775807` cannot be written at all
  and raises `Failure` rather than a structured parse error. Deciding this is
  a prerequisite for removing `opk`.
- **`wt_exp` is not enforced.** It is cited nowhere outside `VIMP_Typing.thy`,
  `exp` has no cast constructor, and `grammar/vimp.yaml` no cast production,
  so the "explicit cast for genuine mismatches" discipline the comments
  describe is neither expressible nor checked. Note that simply enforcing the
  current judgement would be wrong: it would reject `u32 + i64`, which C
  accepts with no cast. The replacement is a deterministic `exp_kind` plus a
  `wf_exp` that checks internal consistency, with elaboration inserting the
  conversions.
- **`ret_kind` is not enforced.** `wf_proc_decl` checks only `distinct`,
  `valid_formal` and `wf_source_com`; it does not relate a procedure's
  declared return kind to the `Return` forms in its body, and call
  destinations are validated through `value_providing body` rather than the
  declared kind.

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
