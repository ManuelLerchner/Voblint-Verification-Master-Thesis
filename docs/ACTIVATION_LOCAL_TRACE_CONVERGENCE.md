# From global witnesses to canonical activation-local semantics

Status: architectural migration design. No `.thy` files changed.

## Why the foundation changed

The earlier activation-sensitive foundation used a global witness:

```text
trace_witness_act
    → cfg_collect_ctx_act
    → Activation_Backbone
```

It was a sound and useful result. The reason to replace its foundation is neither
unsoundness nor vacuity.

The important correction came from Isabelle itself. In the flat program

```text
x := twice(3);
y := twice(10);
```

the second return slot is not empty. A live I/R proof established

```text
cfg_collect_ctx_act … twice_cfg … 7 bot ≠ {}
```

with the expected result `y = 20`. The existing activation soundness theorem therefore does
not merely prove an empty-set inclusion for this example.

The problem is compositionality. At the second return, the current `combine` rule requires a
callee trace whose head is the bound entry store for `twice(10)`. The witness can satisfy this
by constructing a separate whole-program execution re-rooted at a store where `p = 10`, then
splicing that execution into the caller trace.

```text
actual runtime execution

main → call twice(10) → callee activation → return

current witness construction

caller trace → independently re-rooted whole-program callee trace → combine
```

The result is concrete and sound, but it does not follow the source execution's own call stack.
For flat repeated calls, re-rooting can happen to work. It is the wrong shape for a direct
source-to-context-sensitive proof and does not give a satisfactory account of recursive
activations.

## The main insight

We originally treated the activation witness as an auxiliary relation over global executions.
The redesign reverses that perspective:

> Procedure activations are the fundamental concrete semantic objects.

A procedure activation has a concrete entry store, a local path, a concrete sink store, and a
creation history. Calls create nested activations; returns resume the exact suspended caller.
This is the sequential interprocedural analogue of Schwarz et al.'s local-trace architecture:
local traces are the concrete reference semantics and analyses are observations of them.

The old `twf/twfr` material had already exposed half of this insight: a callee must be able
to start at its own frame entry to compose recursive returns. It was not reusable as-is because
it entered with `enter_state` and lost formal-parameter binding. The new design retains the
activation-local shape while using `edge_step (EA_Enter …)`, hence
`bind_formals`, at every call.

For `twice(10)` this means the local callee starts at a store satisfying `p = 10`, rather
than at a locals-zeroed store with `p = 0`.

## Canonical activation-local traces


## Relationship to Schwarz et al.

This redesign follows the semantic philosophy of Schwarz et al.: analyses are defined over a
concrete local-trace semantics rather than over reconstructed global executions.

The difference is what “local” denotes:

| Schwarz et al. | This formalization |
| --- | --- |
| one local trace represents a thread-local execution | one local trace represents a procedure activation |
| creation starts a new thread-local trace | a call starts a parameter-bound callee activation |
| synchronization relates local thread traces | return composes the callee trace into its suspended caller |

Procedure calls create nested activation traces from concrete stores produced by
`edge_step (EA_Enter …)`; returns compose exactly those traces back into their callers.
The local-trace method is therefore adapted from concurrency to sequential interprocedural
analysis, not introduced as an ad hoc repair of a witness proof.

## Architectural consequence

Defining collecting semantics over activation-local traces removes the need for a separate
activation witness relation. The source-to-context-sensitive correctness proof follows the
runtime call stack directly:

```text
source call push    → concrete callee activation
source return pop   → concrete Resume caller callee
```

It no longer reconstructs a callee through an independently re-rooted global execution. This
is the practical thesis benefit: one concrete semantic object supports the source bridge,
monovariant collection, digest views, context-sensitive collection, and DG soundness.

## Migration philosophy

The migration is deliberately narrow. It does not rewrite the generic CFG/dataflow framework
or remove the broad `cfg_collect` / `trace_witness` layer.

During migration, the existing broad collecting semantics and the old activation witness
remain only as compatibility and regression mechanisms. The redesign replaces the
activation-sensitive foundation: `valid_ltr` becomes concrete, `cfg_collect_ctx_act`
becomes its projection, and the existing backbone theorem is reproved over it. Once the
stack-faithful source bridge, DG flagship, and deletion gate are satisfied, the old activation
witness is removed. It is scaffolding, never a competing final foundation.


For compiled IMP2 CFGs, `valid_ltr` is the planned canonical concrete semantics. Its values
represent one activation and its concrete ancestry:

```isabelle
datatype ltr =
    Root "(pp * store) list"
  | Call ltr "(pp * store) list"
  | Resume ltr ltr "(pp * store) list"
```

- `Root` represents the main activation.
- `Call caller path` represents a callee whose local path starts at the bound entry store;
  the embedded caller is the exact suspended activation.
- `Resume caller callee path` represents the exact caller after that exact callee returned.

The closure has four concrete operations: initial trace, intra extension, call creation via the
enter edge, and return composition. No rule permits an arbitrary callee root. A callee exists
only because a concrete caller took a concrete `EA_Enter` edge, and a return is legal only
when the callee's ancestry identifies that caller.

This makes the relation mirror the existing CFG stack machine directly:

```text
cstep.Intra   ↔ extend the innermost local trace
cstep.Call    ↔ create Call caller [(entry, bound-store)]
cstep.Return  ↔ construct Resume caller callee …
```

The desired source bridge is therefore a stack decomposition, rather than a construction of an
independent re-rooted witness.

## One concrete semantics, many views

The final architecture for compiled, well-bracketed IMP2 programs is:

```text
source pstep
      ↓
CFG cstep
      ↓
valid_ltr
      ├── flatten
      ├── mono_collect
      ├── digest_collect
      └── ctx_collect
      ↓
abstract analyses
```

There is one activation-sensitive semantic spine. The earlier possibility of retaining a local
collecting relation and backbone beside `cfg_collect_ctx_act` is rejected.

The public activation API remains familiar:

```text
cfg_collect_ctx_act : … → pp → context → store set
activation_collect_sound :
  cfg_collect_ctx_act … v c ⊆ γ (sg (Inl (v, c)))
```

but after migration both are defined and proved from `valid_ltr`. The existing
`ENTRY_G`, `EDGE`, `SEED_G`, and `COMB` interface remains the single generic soundness
contract. `DG_Ctx_Activation` remains its DG-native discharge; it is not duplicated by a
local-trace sibling theorem.

The context projection is computed after the concrete trace exists. In particular, a
`Resume` value retains both caller and callee ancestry so a general return-context function
can be recovered:

```isabelle
key … (Root _) = seedc
key … (Call parent p) = enterc (key … parent) (entry_store p)
key … (Resume caller callee _) = combc (key … caller) (key … callee)
```

Thus generic `combc` does not force abstract contexts into the foundational trace relation.

## Whole-program traces are derived, not lost

A whole-program history is a view of an activation-local trace:

```text
flatten : valid_ltr → whole execution trace
```

For example, the local representation of `y := twice(10)` has this shape:

```text
Resume
├── caller: Root [main-entry, call-node]
├── callee: Call caller [twice-entry(p = 10), …, twice-exit(ret = 20)]
└── resumed caller path: [main-entry, call-node, return-node(y = 20)]
```

Flattening recovers the ordered inlined execution. It forgets activation ancestry, caller
identity, and the exact return relationship. It therefore loses information rather than
creating it.

This supplies the right home for the current whole-trace facilities:

- monovariant state collection projects sinks of `valid_ltr`;
- a history-sensitive digest reads `flatten t`;
- a context-sensitive collection groups traces by a context key derived from their ancestry;
- trace examples can state `flatten t = expected_store_trace`.

No semantic property of a real, well-bracketed global execution should require a separate
global witness relation once flattening has been defined.

## Scope: compiled programs versus arbitrary graph records

This decision is deliberately scoped.

For CFGs generated by `compile_prog`, calls and returns are well-bracketed and obey LIFO
stack discipline. `valid_ltr` is the canonical concrete semantics for that domain.

The existing `cfg_collect` is more general. It is defined for an arbitrary `cfg` record
containing edges and combine triples, with no stack-discipline predicate. Its combine
functional may pair a caller state at `c` with an exit state at `ex` because the graph has
a matching triple, even if no concrete LIFO execution connects those two states.

That broader graph/dataflow denotation may remain useful for generic CFG theorems. It is not a
second activation-sensitive semantics for compiled IMP2 programs. It has a different scope:

```text
compiled, stack-disciplined CFGs     → valid_ltr is canonical
arbitrary raw CFG records            → cfg_collect remains broad graph denotation
```

This is a semantic distinction, not an argument from migration cost or existing proof count.

## Migration destination

The old `trace_witness_act` relation is migration scaffolding and a finite regression oracle,
not a permanent parallel route.

The destination has:

- one activation-sensitive collecting definition: `cfg_collect_ctx_act`, projected from
  `valid_ltr`;
- one generic activation backbone theorem: `activation_collect_sound`, induced over
  `valid_ltr`;
- one DG discharge path: `DG_Ctx_Activation`;
- one source bridge: `pstep → cstep → valid_ltr → cfg_collect_ctx_act`.

After the new source bridge and backbone are established, delete the old activation witness,
its collecting definition, collapse lemmas, temporary comparison lemmas, and temporary
duplicate proof bodies. No new theorem may acquire a dependency on the old witness while the
migration is underway.

## What remains to prove

This is an architectural commitment, not yet a completed semantic consolidation. The decisive
proof obligations are:

1. Compiled CFGs satisfy the stack-discipline assumptions needed by `valid_ltr`.
2. `cstep` configurations correspond to nested local activation traces. The desired result is
   an adequacy/correspondence theorem, not only a one-way soundness simulation.
3. `flatten` reconstructs the ordered execution history represented by a local trace.
4. `mono_collect` is derived from `valid_ltr` and supports the monovariant analysis
   theorems.
5. `cfg_collect_ctx_act` is derived from `valid_ltr` and supports the existing
   `Activation_Backbone` and DG result.
6. Digest reasoning is reformulated as projections or filters over `flatten`.

Until the `cstep`/local-trace correspondence is proved, this remains a strong semantic
hypothesis. If that theorem requires arbitrary callee roots, loses parameter binding, cannot
represent a general `combc` through concrete return metadata, or needs obligations beyond
`ENTRY_G`, `EDGE`, `SEED_G`, and `COMB`, stop and reassess. Those would be evidence
against convergence, rather than routine proof engineering.

## Thesis formulation

For CFGs generated from the procedural source language, activation-local traces are the
canonical concrete reference semantics. They retain the call and return structure of
executions. Whole-program traces, monovariant collecting semantics, history-sensitive digest
semantics, and context-indexed collecting semantics are projections of this common object.
The broader graph-based collecting semantics is retained only for generic CFG records that
need not satisfy procedural stack discipline.


## Concrete definition proposed for the implementation

The following is the intended Isabelle-level shape. It is a design specification, not
implemented source.

```isabelle
inductive_set valid_ltr :: "cfg => store set => ltr set" for g S where
  init:
    "s \<in> S
     ==> Root [(cfg_entry g, s)] \<in> valid_ltr g S"

| intra:
    "t \<in> valid_ltr g S
     ==> (sink_node t, a, v) \<in> edges g
     ==> \<not> is_enter_action a
     ==> edge_step a (sink_store t) = Some s'
     ==> extend t (v, s') \<in> valid_ltr g S"

| call:
    "caller \<in> valid_ltr g S
     ==> (sink_node caller, EA_Enter xs es, fe) \<in> edges g
     ==> (sink_node caller, ex, ret, dst) \<in> combines g
     ==> edge_step (EA_Enter xs es) (sink_store caller) = Some se
     ==> Call caller [(fe, se)] \<in> valid_ltr g S"

| ret:
    "Call caller cp \<in> valid_ltr g S
     ==> (sink_node caller, sink_node (Call caller cp), v, dst) \<in> combines g
     ==> r = combine_collect dst (sink_store caller) (sink_store (Call caller cp))
     ==> Resume caller (Call caller cp) (path caller @ [(v, r)])
           \<in> valid_ltr g S"
```

The extra combine premise in `call` is deliberate. It matches `cstep.Call`, which
requires both an enter edge and its matching combine triple. This prevents the local semantics
from inventing an activation for a raw enter edge that the CFG stack machine cannot call.

The public collecting projection keeps the existing API:

```isabelle
cfg_collect_ctx_act enterc combc seedc g S v c =
  {sink_store t | t. t \<in> valid_ltr g S /\<and> sink_node t = v /\<and>
                     key enterc combc seedc t = c}
```

The analogous monovariant view is:

```isabelle
mono_collect g S v =
  {sink_store t | t. t \<in> valid_ltr g S /\<and> sink_node t = v}
```

## Migration proof boundary and deletion gate

The migration has a deliberately narrow consumer boundary. In the current tree, only these
live theories mention the activation API or its constructors:

| theory | migration role |
| --- | --- |
| `CFG_Collect_Activation` | currently defines the old witness and will expose the new projection |
| `Activation_Backbone` | only proof that directly inducts over the old witness |
| `DG_Ctx_Activation` | consumes the backbone theorem, not witness constructors |
| `Example_Interval_DG_Ctx_Collect` | consumes the public collecting API and backbone theorem |

Thus the final refoundation changes one proof principle, not the solver interface, equation
system, domains, or DG obligations. During the transition, the old witness may prove finite
regression facts such as the existing `twice` inhabitance result. It must not become a new
dependency.

Each stage ends with a green build of the affected session:

1. Introduce `ltr`, `valid_ltr`, observers, `key`, and inversion lemmas in the CFG
   session. No second public collecting name.
2. Establish the internal local projection and its inclusion in broad `cfg_collect`.
3. Reprove the existing backbone statements from `valid_ltr` using exactly
   `ENTRY_G`, `EDGE`, `SEED_G`, and `COMB`.
4. Replace the implementation of `cfg_collect_ctx_act` while retaining its name and replace
   the bodies of the existing backbone theorems.
5. Prove stack decomposition and the recursive source bridge.
6. Delete the old witness, its collecting definition, collapse/comparison lemmas, temporary
   projection names, and duplicate temporary proof bodies.

Deletion is permitted only when the final backbone and interval flagship build, the recursive
source bridge reaches the new `cfg_collect_ctx_act`, and no consumer of
`trace_witness_act` remains outside its defining theory.

## Documentation map

This is the authoritative architectural document.

- `ACTIVATION_WITNESS_RECONCILIATION.md` preserves the mechanical correction that the second
  `twice` return is non-empty.
- `SOURCE_ACTIVATION_BRIDGE_DESIGN.md`, `ORIGIN_WITNESS_DESIGN.md`, and
  `LOCAL_ACTIVATION_TRACE_DESIGN.md` are historical design stages. Their alternatives are not
  implementation targets.
- `ACTIVATION_SPINE_CONSOLIDATION.md` records the completed cleanup of the old activation
  family. Its description of `trace_witness_act` is a record of the currently implemented
  code, not the planned semantic endpoint.
- `PROOF_OVERVIEW.md` distinguishes the current batch-green path from this planned
  refoundation.


## Fresh-agent handoff

Start from this document, not from the historical design records. The first implementation task is small and isolated:

1. Create `src/CFG/Collecting/CFG_Local_Trace.thy` in the CFG session. It defines only `ltr`, observers, `extend`, `key`, and `valid_ltr`; it does not change any existing collecting definition.
2. Use I/Q to check the four constructor goals individually: nonempty paths, `Call` entry equals the `edge_step` result, `extend` preserves entry/ancestry, and `Resume` computes the concrete combine store.
3. Add the new theory to the session ROOT and batch-build `Voblint_CFG`. Do not touch `trace_witness_act`, `Activation_Backbone`, or any solver theory in this first commit.
4. Only after that green commit, prove the local-trace soundness induction against the existing four obligations. Keep it internal until it has exactly the public statement of `activation_collect_sound`.
5. Replace the old public implementation only after the DG locale and interval flagship build against the unchanged public theorem names. The source bridge and recursive example precede deletion of the old witness.

Non-negotiable invariants:

- every callee is created by a concrete caller and an `EA_Enter` edge;
- that entry store is the result of `edge_step`, retaining `bind_formals`;
- every return identifies its exact caller structurally;
- contexts are computed by `key`, never stored in `valid_ltr`;
- `Resume` remains available so generic `combc` can inspect both caller and callee keys;
- no second public activation collecting API or sibling backbone theorem is introduced.

Stop and report if any invariant cannot be expressed by the four constructors, if the generic backbone needs an obligation beyond `ENTRY_G`, `EDGE`, `SEED_G`, and `COMB`, or if the `cstep` correspondence requires an arbitrary callee start. Those are architecture failures, not invitations to restore the old witness or `twf/twfr`.
