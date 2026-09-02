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

`sound_dg_hooks`/`sound_dg_hooks_ltr` (`src/Framework/DG/DG_Soundness.thy`,
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
and interval execution examples without changing the semantic reference model.

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
