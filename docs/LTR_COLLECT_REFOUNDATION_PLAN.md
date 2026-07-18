# Local-trace collecting refoundation plan

Status: **proposed; no migration has started.** This is the live plan for making
stack-faithful local traces the concrete semantics of compiled IMP2 programs. It
does not alter the completed activation-local migration recorded in
`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`, and it does not revive the retired
digest spine.

## Decision

For CFGs produced by `compile_prog`, relative to the proved source-to-CFG
adequacy assumptions, the canonical stack-faithful concrete carrier becomes:

```text
valid_ltr g S :: ltr set
```

`cfg_collect` remains available during migration as the broad graph
over-approximation. It is not the target semantics for compiled,
stack-disciplined executions after the refoundation.

The distinction is deliberate:

```text
compiled IMP2 CFGs                 arbitrary cfg records
valid_ltr is exact                 cfg_collect remains useful
```

The old combine closure may pair a reachable caller with an independently
reachable callee exit. A `valid_ltr` return recovers the caller from the
callee's own activation ancestry, so it represents only matched returns.

## Target architecture

```text
Exact execution semantics
    valid_ltr :: cfg => store set => ltr set
        |
        +-- ltr_collect          :: cfg => store set => pp => store set
        |
        +-- ltr_collect_keyed    :: (ltr => 'c) => cfg => store set
                                  => pp => 'c => store set
        |
        v
Finite analysis representations
    pp => abstract state
    (pp, analysis key) => abstract state
```

An analysis key is a quotient of activation structure. It is never an exact
activation identity unless that is proved separately. In particular, a finite
call-only key may merge two callers; it must not be used as the carrier of the
exact return semantics.

## Semantic interface

`LTR_Collect` introduces the constructor transformer below, with no solver or
domain dependency.

```isabelle
ltr_F g S T =
    {Root [(cfg_entry g, s)] | s. s : S}
  Un {extend t (v, s') | t a v s'.
        t : T & (sink_node t, a, v) : edges g &
        ~ is_enter_action a & edge_step a (sink_store t) = Some s'}
  Un {Call caller [(fe, se)] | caller xs es fe ex ret dst se.
        caller : T &
        (sink_node caller, EA_Enter xs es, fe) : edges g &
        (sink_node caller, ex, ret, dst) : combines g &
        edge_step (EA_Enter xs es) (sink_store caller) = Some se}
  Un {Resume caller callee (path caller @ [(v, r)]) | callee caller v dst r.
        callee : T & caller_of callee = Some caller &
        (sink_node caller, sink_node callee, v, dst) : combines g &
        r = combine_collect dst (sink_store caller) (sink_store callee)}
```

The return clause deliberately mirrors `valid_ltr.ret` literally. It requires
only `callee : T` plus `caller_of callee = Some caller`, because that is the
constructor's actual premise. The separately proved caller-chain invariant may
later establish `caller : T`; it must not strengthen or replace this first
transformer.

The first milestone proves:

```isabelle
mono (ltr_F g S)
valid_ltr g S = lfp (ltr_F g S)
```

The equality has two small, explicit obligations:

1. `ltr_F g S (valid_ltr g S) <= valid_ltr g S`, by the four existing
   introduction rules; `lfp_lowerbound` gives `lfp (ltr_F g S) <= valid_ltr g S`.
2. `valid_ltr g S <= lfp (ltr_F g S)`, by `valid_ltr` induction and
   `lfp_unfold` for the monotone transformer.

The public projections are exact forgetful views:

```isabelle
ltr_collect g S v =
  {sink_store t | t. t : valid_ltr g S & sink_node t = v}

ltr_collect_keyed key g S v c =
  {sink_store t | t. t : valid_ltr g S &
                     sink_node t = v & key t = c}
```

For every total key, without a finiteness assumption:

```isabelle
ltr_collect g S v = Union (range (ltr_collect_keyed key g S v))
```

`cfg_collect_ctx_act` becomes a compatibility abbreviation for the activation
keyed projection. It is not renamed to an exact context semantics.

The union law says only that every trace has a key. It does not say that an
individual keyed bucket preserves activation precision.

## Why the legacy combine is too broad

Consider two calls to the same procedure from distinct caller states:

```text
C0 -> E0
C1 -> E1
```

The broad combine closure may form all four caller/exit pairs:

```text
C0 + E0    C0 + E1  (unmatched)
C1 + E0    (unmatched) C1 + E1
```

`valid_ltr` permits only `C0 + E0` and `C1 + E1`, because each return recovers
the caller from the completed callee's activation ancestry. This is the
semantic property the migration must preserve through every abstraction.

## Migration stages

### Stage R0 — freeze the boundary

Document the current meaning of `cfg_collect` as a broad graph denotation and
the current meaning of `valid_ltr` as the stack-faithful compiled-program
semantics. Add no compatibility equality.

Exit gate: a source audit identifies every theorem stated directly over
`cfg_collect`, `cfg_collect_ctx_act`, and `valid_ltr`.

### Stage R1 — add `LTR_Collect`

Add a CFG-session theory after `CFG_Local_Trace` containing `ltr_F`, its
monotonicity, the fixed-point theorem, and the two projections. Do not change
an existing soundness statement.

Exit gate: `Voblint_CFG` batch-green; no new `sorry`; an intraprocedural,
single-call, and nested-return witness each reach the corresponding projection.

### Stage R2 — establish projection laws

Prove:

```isabelle
ltr_collect_keyed key g S v c <= ltr_collect g S v
Union (range (ltr_collect_keyed key g S v)) = ltr_collect g S v
ltr_collect g S v <= cfg_collect g S v
```

The final inclusion is the migration bridge only. Do not attempt its converse.

Exit gate: `Located_LTR` obtains source adequacy for `ltr_collect` and preserves
the existing keyed source theorem.

### Stage R3 — build the correlation-preserving abstract interface

First specify a proof-level correlation carrier that keeps a return
continuation correlated with its callee. Candidate carriers include abstract
activation records or abstract continuations. Then define a separate finite
executable solver carrier with an explicit abstraction relation to that proof
carrier. A finite `(pp, key)` map may be the executable abstraction; it is not
the exact or proof-level carrier itself.

Required theorem shape:

```isabelle
lfp (ltr_F g S) <= gamma_ltr A
```

where `gamma_ltr A` is closed under the four `ltr_F` clauses. The closure proof
must make return matching explicit.

Exit gate: a small recursive program proves the theorem without reconstructing
an unrestricted caller/callee cross product.

### Stage R4 — migrate the activation and DG client

Redirect `Activation_Backbone` and `DG_Ctx_Activation` through the new generic
trace abstraction theorem. Keep their public activation-keyed statement as a
corollary. This is the first downstream consumer because it already reasons
over `valid_ltr`.

Exit gate: `Voblint_Analysis` and the interval DG context flagship are
batch-green with the old broad semantics used only as an optional comparison.

### Stage R5 — migrate generic solver soundness

Migrate compiled-program equation-system and TD-side soundness statements to
the correlation-preserving trace abstraction theorem. Derive monovariant store
results through `ltr_collect`. Retain `cfg_collect_F` proofs where they state
generic raw-CFG or purely intraprocedural facts; they must not remain the
concrete correctness target of a compiled-program theorem.

Exit gate: the generic solver theorem, source bridge, and a recursive program
are batch-green without a direct dependency on `cfg_collect` as the canonical
compiled-program semantics.

### Stage R6 — migrate domain corollaries

Move Sign, Interval, Mixed, and DG theorem statements to the projected
trace-derived collecting views. Their transfer proofs should remain domain-local
corollaries of the generic interface.

Exit gate: all five sessions are batch-green; the theorem statements retain
their existing user-facing plain and keyed result shapes.

### Stage R7 — retire the legacy semantic target

Delete uses of `cfg_collect` as the canonical compiled-program target only
after every consumer has migrated. Retain it if generic raw-CFG results still
need it; otherwise move it to an explicitly legacy theory.

Exit gate: no compiled IMP2 soundness theorem depends on unmatched-combine
collecting, and the full clean build is green.

## Dependency destination

During R1–R4:

```text
CFG_Collect -> CFG_Local_Trace -> LTR_Collect
                                      |
                              Activation / DG migration
```

After R5, a clean architecture may split common CFG structure from the two
semantic views:

```text
CFG core -> CFG_Local_Trace -> LTR_Collect -> Analysis -> Formalization
       \-> CFG_Collect_Legacy (raw-CFG compatibility only)
```

Do not introduce a session split before R5 proves that the generic solver
interface needs it. Avoid a session cycle by moving any theory that imports
local traces with the local-trace session.

## Risks and stop conditions

Stop and reassess rather than weakening the semantics if any of these occurs:

- The `ltr_F` least-fixed-point theorem requires an arbitrary callee root or
  loses a nested `Resume` caller.
- A proposed finite carrier resumes a callee through an unrelated continuation.
- The generic abstraction theorem needs an unbounded concrete trace in the
  executable solver representation.
- The source bridge cannot establish adequacy for the plain `ltr_collect`
  projection.
- A domain-specific proof needs information absent from the proposed abstract
  continuation interface.

These are design failures in the abstraction boundary. They are not reasons to
restore `cfg_collect` as the canonical compiled-program semantics.

## Verification policy

Each stage uses I/Q for theory edits and diagnostics, then the relevant session
build. R6 and R7 require the full clean session DAG build. Every migration PR
must state whether `cfg_collect` appears as a legacy comparison, a raw-CFG
theorem, or an accidental canonical dependency.
