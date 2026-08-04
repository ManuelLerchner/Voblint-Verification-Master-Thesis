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
| Procedure-aware architecture | `docs/PROCEDURE_AWARE_CFG_MIGRATION.md` |
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

### Placement-aware D/G generation

Hook-parametric D/G equation generation and its soundness proof are generic
(`src/Core/Solver/Context/DG/DG_Framework.thy`,
`src/Core/Solver/Context/DG/DG_Soundness.thy`, locale `sound_dg_hooks`), and
interval transfer and D/G readback are classifier-parametric
(`src/Analysis/Instances/Interval/Interval_Transfer.thy`,
`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy`). End-to-end soundness
through this generic spine is instantiated and batch-verified for two worked
examples, `src/Examples/Interval/Example_Interval_Placement.thy` and
`src/Examples/Sign/Example_Sign_Placement.thy`, plus two migrated flagships
(`src/Examples/Sign/Exec_Sign_DG_Run.thy`,
`src/Examples/Parity/Example_Parity_DG_Flagship.thy`).

`sound_dg_hooks` is deliberately not the general-purpose user-facing API.
`docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md` established that every classic
constant (`sound_dg_spec`, `unit_dg_spec`, `dg_spec`, `dg_gen_of`, ...) is
already architecture-neutral or a thin specialization of the generic layer,
not a duplicate implementation, and that `sound_dg_spec` is itself the
concise adapter: one locale interpretation per instance, no per-CFG-node
proof obligations. `sound_dg_hooks` requires exactly that per-node work
(hook-tree instance, `dg_refines_on`, `se_constraint_holds`, transport per
edge/enter/combine), which is why the two migrated flagships grew 5-6x for no
closed soundness or drift risk. Migrating Interval, Mixed, CallString, or Ctx
examples off the classic route is **not planned** — they stay on
`sound_dg_spec`/`dg_ctx_activation`/`routed_context` permanently. The one
remaining item is a framework-internal one: express `sound_dg_spec` as a
`sublocale`/`interpretation` of `sound_dg_hooks` so the two locales stop being
independently-proved duplicates of the same per-step obligation shape,
without touching any example's public API. Scoping notes are in the audit
document, Section 4.

### Domain composition

The mixed Sign/Interval instance demonstrates heterogeneous carriers.
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) settled this: no
shared product/reduction layer is planned. `sound_dg_spec`'s carriers are
already opaque, so new heterogeneous or relational analyses (e.g.
`Rel_Order_Domain.thy`) are added directly against it.

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
