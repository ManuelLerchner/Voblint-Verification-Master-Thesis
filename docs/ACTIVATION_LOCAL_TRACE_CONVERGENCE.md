# From global witnesses to canonical activation-local semantics

Status: **implemented and batch-green.** Stages 1–5 plus the concrete instantiation are landed
(`Voblint_CFG` → `Voblint_Soundness` clean, no `sorry`). The activation-local trace semantics
`valid_ltr` is the concrete foundation, `cfg_collect_ctx_act` is its sink/`key` projection,
`activation_collect_sound` rides the four generic obligations, and the recursive source bridge
`source_activation_sound` closes `source pstep → cstep → valid_ltr → cfg_collect_ctx_act → γ`
(recursive interval `twice` flagship certified end-to-end). The old whole-program witness
`trace_witness_act` is deleted. **Deliberately deferred:** `flatten` (whole-program trace view) and
the `mono_collect` / digest reformulations that ride on it — optional, not on the soundness path.
This document is retained as the architectural narrative; the "design" framing below is historical.

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

## Relationship to Schwarz et al

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
  the embedded `caller` is the exact suspended caller activation, **frozen at the call node**
  (the value it had when it took the enter edge; it is never mutated while suspended).

  Distinguish two invariants of `Call`, so the creation rule is not misread as a shape
  constraint:
  - *Creation invariant*: a newly created activation has path `[(fe, se)]`, the single bound
    entry step produced by the `call` rule (`se = edge_step (EA_Enter ...) ...`).
  - *Representation invariant*: subsequent intra transitions extend that path, so a valid `Call`
    has a **non-empty** path whose head is the bound entry store — not necessarily a singleton.

  The Stage-1 theorem is the representation invariant (`valid_ltr_Call_path_nonempty`); the
  singleton form holds only at the instant of creation. Reading `Call caller [(fe,se)]` in the
  `call` rule as "every valid `Call` is a singleton" is the misreading this note prevents.
- `Resume caller callee path` represents the caller activation continued past a completed call.
  Its fields carry distinct, load-bearing roles:
  - `caller` — the **frozen caller at its call node**, exactly the value that spawned `callee`
    (the same `caller` the `ret` rule read via `caller_of callee`); it is *not* the
    already-continued caller, and it may itself be a `Call` or a nested `Resume`;
  - `callee` — the completed callee subtree (retained so `key` can read `key callee` for a
    general `combc`);
  - `path` — the caller's **continued** path: `path caller @ [(return_node, return_store)]`.
  So the "continuation" of the caller lives in the `path` field, while the `caller` field stays
  the frozen snapshot. This is what lets `caller_of` descend the `caller` field to find the
  activation that spawned *this* caller: `caller_of (Resume caller _ _) = caller_of caller`.

The closure has four concrete operations: initial trace, intra extension, call creation via the
enter edge, and return composition. No rule permits an arbitrary callee root. A callee exists
only because a concrete caller took a concrete `EA_Enter` edge, and a return is legal only
when the callee's ancestry identifies that caller.

A return must compose **any** completed callee, including one that itself called and resumed
(the recursion / nested-call case). The return rule therefore recovers the creating caller
through a structural observer rather than by pattern-matching the callee's outer constructor:

```isabelle
fun caller_of :: "ltr \<Rightarrow> ltr option" where
  "caller_of (Root _)           = None"
| "caller_of (Call caller _)    = Some caller"      -- the frozen caller at the call node
| "caller_of (Resume caller _ _) = caller_of caller"  -- Resume's caller field is frozen-at-call; descend it
```

`caller_of` is invariant under `extend` (which never touches the outer constructor's caller
field) and strictly descends the ancestry, so it is total and well-founded. An activation that
called and returned is a `Resume`; its caller_of is still recovered, so it can itself be returned
to *its* caller — this is what makes nested and recursive returns compose (see the worked
nested example below). Matching the callee as a bare `Call caller cp` would only permit
returning callees that never called anything, silently excluding recursion.

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

The context projection is computed after the concrete trace exists. The activation context is
**activation-stable**: it is fixed at creation and unchanged by the calls an activation later
makes and returns from.

```isabelle
key enterc seedc (Root _) = seedc
key enterc seedc (Call parent p) = enterc (key enterc seedc parent) (entry_store p)
key enterc seedc (Resume caller callee _) = key enterc seedc caller
```

This matches Goblint's solver indexing: `Spec.context` is call-only, and `Spec.combine` merges
abstract *states* but not function contexts, so a resumed caller keeps its own creation context.
The `Resume` node's retained `callee` subtree plays **no role** in this context. It is kept for
trace flattening, history projections, and a possible later return-sensitive history *digest*
computed by a separate map — deliberately distinct from the solver context, which does not depend
on completed calls.

**Why not a general `combc`-combined context.** An earlier draft set
`key (Resume caller callee _) = combc (key caller) (key callee)`, retaining the callee subtree so
`combc` could read `key callee`. That is incompatible with the existing `COMB` obligation for a
*general* `combc`: `COMB` binds the completed callee at its routed entry context `enterc c1 es`,
whereas a callee that itself called and resumed would carry `key callee = combc (…)`. The old
`trace_witness_act` backbone never exposed this because its combine rule structurally required the
callee sub-witness to *end at* context `enterc c1 (hd rho)`, so a context-changing nested return
was **unrepresentable** — its `combc`-generality was vacuous on exactly the recursion case. Making
those traces representable in `valid_ltr` surfaced the choice; the stable model is the
Goblint-faithful resolution. The alternative (general evolving contexts: keep the `combc` clause,
generalise `COMB` to a free callee context `c2`, and generate `(v, combc c1 c2)` return-slot
variables) is a return-sensitive partitioning analysis beyond Goblint's current model, recorded as
a possible future extension, not the migration target.

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

The decisive obligations are **discharged**; what is left is the optional `flatten` view:

1. **(done)** Compiled CFGs satisfy the stack discipline `valid_ltr` needs — the source bridge
   reuses the compiler's existing `frames_match` / `concrete_program_match` invariants; no new
   stack-discipline predicate was required.
2. **(done)** `cstep` configurations correspond to nested local activation traces
   (`cstep_preserves_ltr_repr`, `source_run_has_ltr`, `Located_LTR.thy`) — a constructive
   forward correspondence, closed via the existing `pstep → cstep` simulation.
3. **(deferred)** `flatten` reconstructs the ordered execution history — optional, not started.
4. **(deferred)** `mono_collect` is derived from `valid_ltr` for the monovariant view — rides on
   `flatten`; deferred.
5. **(done)** `cfg_collect_ctx_act` is the sink/`key` projection of `valid_ltr` and supports
   `Activation_Backbone` (`activation_collect_sound`) and the DG result (`DG_Ctx_Activation`,
   unchanged).
6. **(deferred)** Digest reasoning as projections/filters over `flatten` — deferred with `flatten`.

The `cstep`/local-trace correspondence is proved (item 2), so the convergence is no longer a
hypothesis. None of the stop conditions materialised: no arbitrary callee roots, parameter binding
retained via `edge_step (EA_Enter …)`, the general-`combc` question resolved by the
**activation-stable** `key` (call-only, not evolving), and no obligation beyond
`ENTRY_G`/`EDGE`/`SEED_G`/`COMB` was needed.

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
    "callee \<in> valid_ltr g S
     ==> caller_of callee = Some caller
     ==> (sink_node caller, sink_node callee, v, dst) \<in> combines g
     ==> r = combine_collect dst (sink_store caller) (sink_store callee)
     ==> Resume caller callee (path caller @ [(v, r)])
           \<in> valid_ltr g S"
```

The `ret` rule takes an arbitrary completed `callee` and recovers its `caller` by
`caller_of callee = Some caller`, not by matching `Call caller cp`. This is the fix for nested
and recursive returns: a callee that itself called another procedure has outer constructor
`Resume`, which the old `Call caller cp` pattern rejected, so the old rule silently admitted
only leaf callees (the flat `twice` example never produced a nested `Resume`, which is why it
appeared to work). The combine triple `(sink_node caller, sink_node callee, v, dst)` still
pins `sink_node caller` to the call node and `sink_node callee` to the callee exit, and
`caller = caller_of callee` is uniquely determined by the callee's own ancestry — so no arbitrary
caller/callee pairing is possible (unlike the broad `cfg_collect` combine functional).

The extra combine premise in `call` is deliberate. It matches `cstep.Call`, which
requires both an enter edge and its matching combine triple. This prevents the local semantics
from inventing an activation for a raw enter edge that the CFG stack machine cannot call.

### Worked nested return (`main` -> `f` -> `g`, both return)

```text
main = Root [(m0, s), (mc, s1)]                     -- main suspended at its call node mc
f    = Call main [(fe, sef), (fc, s2)]              -- caller_of f = Some main; f at its call node fc
g    = Call f [(ge, seg), (gx, s3)]                 -- caller_of g = Some f; g at its exit gx
ret g: caller = caller_of g = f
       Resume f g (path f @ [(fr, rg)])  = f'       -- caller_of f' = caller_of f = Some main
f'   = extend f' (fx, s4)                           -- f' now a Resume, at f's exit fx
ret f': caller = caller_of f' = caller_of f = main      -- KEY: recovered through the Resume
        Resume main f' (path main @ [(mr, rf)])     -- main resumes; well-formed
```

The old rule stalls at `ret f'` because `f'` is a `Resume`, not `Call main _`. With `caller_of`
the caller `main` is recovered from `f'`'s ancestry and the return composes. The construction
is uniform in recursion depth: each activation, however deeply nested, exposes its caller_of.

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

The migration has a deliberately narrow consumer boundary. After Stage 4 the activation API is
these theories:

| theory | role |
| --- | --- |
| `CFG_Local_Trace` | defines `valid_ltr`, `key`, and the sole public projection `cfg_collect_ctx_act` |
| `Activation_Local_Sound` | the domain-level engine `valid_ltr_ctx_sound` (internal) |
| `Activation_Backbone` | the public `activation_collect_sound`, one line from the engine |
| `DG_Ctx_Activation` | consumes the backbone theorem |
| `Example_Interval_DG_Ctx_Collect` | consumes the public collecting API and backbone theorem |

The refoundation changed one proof principle, not the solver interface, equation system, domains,
or DG obligations.

Each stage ends with a green build of the affected session:

1. **(done)** Introduce `ltr`, `valid_ltr`, observers, `key`, and inversion lemmas in the CFG
   session. No second public collecting name.
2. **(done)** Establish the internal local projection and its inclusion in broad `cfg_collect`.
3. **(done)** Reprove the backbone statement from `valid_ltr` using exactly `ENTRY_G`, `EDGE`,
   `SEED_G`, and `COMB` (with the stable-context `COMB` output at the caller context).
4. **(done)** Replace `cfg_collect_ctx_act` with the local-trace projection (retaining the name),
   redirect `activation_collect_sound` to the engine, and delete the old witness family.
5. **(done)** Prove the stack representation invariant (`stack_repr`/`ltr_repr`, `Located_LTR.thy`)
   and the recursive source bridge `source_activation_sound` onto the new `cfg_collect_ctx_act`,
   plus the concrete interval-flagship instantiation (`Example_Interval_Source_Ctx.thy`).
6. **(subsumed by Stage 4)** the old witness, its collecting definition, and helper lemmas are
   gone; no compatibility layer remains.

The Stage-4 deletion was safe because an audit confirmed every consumer of the old
`cfg_collect_ctx_act` / `activation_collect_sound` used only the soundness *upper bound*
(`\<subseteq> \<gamma>`), which the sink/key projection satisfies under the same four obligations. No
committed theorem asserted membership or non-emptiness of the old witness collecting, so no
downstream result depended on behaviour present only in the old semantics. See the Stage-4 note.

### Stage 1 landed (`CFG_Local_Trace.thy`)

Stage 1 is implemented and builds green through `Voblint_Soundness`. The design
invariants are theorems of `valid_ltr`, not comments:

- `valid_ltr_Call_caller_valid` — a valid `Call` has a valid caller (survives the callee's
  intra steps);
- `valid_ltr_Resume_fields` — for any valid `Resume cc dd q`, `dd \<in> valid_ltr` and
  `caller_of dd = Some cc`: the frozen caller is **forced** by the callee's ancestry, so a
  return cannot invent a caller;
- `valid_ltr_caller_valid` — every caller recovered by `caller_of` from a valid trace is valid;
- `valid_ltr_path_nonempty` / `valid_ltr_Call_path_nonempty` — the representation invariant;
- `caller_of_extend` — `extend` preserves ancestry.

The "returns cannot invent callers" guarantee is carried by `valid_ltr_Resume_fields` composed
with `valid_ltr_caller_valid`. Note that `caller_of_unique`
(`caller_of t = Some c1 \<Longrightarrow> caller_of t = Some c2 \<Longrightarrow> c1 = c2`) is
**only functional uniqueness** — `caller_of` is a function — and carries no semantic weight; it
is not the source of the non-invention property.

### Stage 2 landed (`CFG_Local_Trace.thy`)

The internal projection `ltr_ctx_collect` and its inclusion in the broad graph collecting
semantics are proved:

- `valid_ltr_sink_in_cfg_collect` — the sink store of a valid trace at its sink node lies in
  `cfg_collect`. Proof: reduce a valid trace to a `cfg_witness` derivation along the finite
  `callers` chain (needed because `ret` recovers its caller structurally, not as a recursive
  premise), reusing `cfg_collect = {s. cfg_witness …}`. The `Resume` case discharges the broad
  combine directly from the frozen caller and retained callee — no re-rooting.
- `ltr_ctx_collect_le_cfg_collect` — the `key` filter is a trivial outer restriction of that
  key-free inclusion.

### Stage 3 landed (`CFG_Local_Trace.thy`, `Activation_Local_Sound.thy`)

The context-sensitive soundness backbone is reproved over `valid_ltr` with the stable `key`,
using exactly the four obligations `ENTRY_G`, `EDGE`, `SEED_G`, `COMB` (with the `COMB` output
reshaped to the caller context `c1`, since the resumed activation keeps its creation context — no
fifth obligation, no free callee-context parameter):

- `callee_entry_invariant` (CFG session, domain-free) — the load-bearing fact: for every valid
  callee, leaf or nested, and its structurally-recovered creator `c`, the callee's stable context
  is `enterc (key c) (entry_store callee)` and it was born from a concrete `EA_Enter` edge at `c`
  (`call_enter_store`). This is why the *existing* callee slot `enterc c1 es` fires for nested
  `Resume` callees without a `combc`-shaped context.
- `valid_ltr_ctx_chain` / `valid_ltr_ctx_sound` — the soundness induction along the caller chain
  and its sink corollary.
- `ltr_ctx_collect_sound` — `ltr_ctx_collect enterc seedc g S v c ⊆ γ (sg (Inl (v, c)))`, the
  Stage-3 statement (folded into the public `activation_collect_sound` at Stage 4).

At Stage 3 `Activation_Local_Sound` was internal scaffolding beside the untouched old witness.

### Stage 4 landed — the local semantics is the single public collecting

The activation-local semantics is now the *only* public activation collecting semantics.

**Old / new correspondence.** No equality or inclusion between the old `trace_witness_act`
collecting and the new `valid_ltr`+`key` projection was established or required. The two use
materially different witness structures: the old combine obtained a callee as an *independently
re-rooted* callee derivation (see `ACTIVATION_WITNESS_RECONCILIATION.md`), whereas `valid_ltr`
requires explicit stack-faithful caller linkage (`caller_of callee = Some caller`). Whether either
semantic inclusion holds would require a separate reconstruction theorem or a concrete
counterexample — a direct syntactic node-for-node translation failing in one direction does not by
itself settle the existential question of whether some trace of the other kind reaches the same
sink. (Note in particular that under the accepted activation-stable `key` a valid trace has no
context-changing nested return, so the old rule's callee-context-equality restriction is *not* a
reason `valid_ltr → trace_witness_act` fails; that earlier argument applied only to the rejected
evolving-context design.)

The migration does not depend on this: the swap is **sound-preserving, not equality-based**. Every
consumer used only the upper bound `\<subseteq> \<gamma>`, which the sink/key projection satisfies under the
same four obligations, and an audit found no committed theorem asserting membership or
non-emptiness of the old collecting. Replacing one sound concrete semantics with the intended one
is legitimate; the green DAG confirms no formal dependency on the retired witness remains — it does
not, and need not, prove semantic equivalence.

**What changed.**

- `cfg_collect_ctx_act` is now defined in `CFG_Local_Trace` as the sink/key projection of
  `valid_ltr` (the Stage-2/3 `ltr_ctx_collect`, renamed to the public name; `combc` dropped). Single
  public collecting API; `cfg_collect_ctx_act_le_collect` retained.
- `activation_collect_sound` (public, `Activation_Backbone`) keeps its name; its statement now uses
  the new `cfg_collect_ctx_act` and the stable-context `COMB`, and its proof is one line from
  `valid_ltr_ctx_sound`. The engine `valid_ltr_ctx_sound` lives in `Activation_Local_Sound`.

**Retired.** `CFG_Collect_Activation.thy` deleted in full: `trace_witness_act`,
`cfg_collect_trace_act`, the old `cfg_collect_ctx_act`, `act_step_preserves_ctx`,
`act_enter_routes_ctx`, `act_combine_ctx`, `act_combine_resumes_caller`,
`trace_witness_act_imp_trace_witness`, `act_recursion_*`, and `activation_trace_sound`
(`Activation_Backbone`). No compatibility layer remains; `combc` is gone from every activation
context theory. The `Example_Interval_DG_Ctx_Collect` flagship discharges the caller-context `COMB`
from its existing `ivl_ctx_sg_comb` (since `ivl_combc` is the caller projection). Stage 5 (the
recursive source bridge) targets this sole `cfg_collect_ctx_act`.

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

1. Create `src/CFG/Collecting/CFG_Local_Trace.thy` in the CFG session. It defines only `ltr`, observers (`sink_node`, `sink_store`, `entry_store`, `path`, `caller_of`), `extend`, `key`, and `valid_ltr`; it does not change any existing collecting definition.
2. Use I/Q to check the four constructor goals individually: nonempty paths, `Call` entry equals the `edge_step` result, `extend` preserves entry/ancestry/`caller_of`, `caller_of` recovers the caller through a `Resume` (nested case), and `Resume` computes the concrete combine store.
3. Add the new theory to the session ROOT and batch-build `Voblint_CFG`. Do not touch `trace_witness_act`, `Activation_Backbone`, or any solver theory in this first commit.
4. Only after that green commit, prove the local-trace soundness induction against the existing four obligations. Keep it internal until it has exactly the public statement of `activation_collect_sound`.
5. Replace the old public implementation only after the DG locale and interval flagship build against the unchanged public theorem names. The source bridge and recursive example precede deletion of the old witness.

Non-negotiable invariants:

- every callee is created by a concrete caller and an `EA_Enter` edge;
- that entry store is the result of `edge_step`, retaining `bind_formals`;
- every return identifies its exact caller structurally, through `caller_of callee = Some caller`,
  for a completed callee of **any** constructor (`Call` or `Resume`) — never by requiring the
  callee to still be a bare `Call`;
- contexts are computed by `key`, never stored in `valid_ltr`;
- `Resume` remains available so generic `combc` can inspect both caller and callee keys;
- no second public activation collecting API or sibling backbone theorem is introduced.

Stop and report if any invariant cannot be expressed by the three constructors, if the generic backbone needs an obligation beyond `ENTRY_G`, `EDGE`, `SEED_G`, and `COMB`, if the `cstep` correspondence requires an arbitrary callee start, or if `caller_of` cannot recover the caller of a nested/recursive callee. Those are architecture failures, not invitations to restore the old witness or `twf/twfr`.
