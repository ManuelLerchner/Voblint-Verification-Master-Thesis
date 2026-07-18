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

## Stage R0 audit — frozen boundary (done)

No theorem was migrated in R0. This section records the classification the exit
gate requires and freezes the intended meaning of each boundary symbol.

### Frozen meanings

- `cfg_collect` (`CFG_Collect.thy`) is the **broad graph closure**: the least
  cenv closed under `cfg_collect_F` = entry seed `+` `collect_pp` (edge transfer)
  `+` `collect_combine_pp`. Its combine component pairs *any* reachable caller
  store at a call node with *any* reachable callee-exit store sharing that
  combine triple. It therefore contains **unmatched combine pairs** (`C0 + E1`,
  `C1 + E0` in the two-call picture). It stays the semantics of arbitrary CFG
  records and the migration bridge.
- `cfg_collect_F` is that transformer; its `collect_combine_pp` summand is the
  unmatched-return over-approximation, by design.
- `valid_ltr` (`CFG_Local_Trace.thy`) is **stack-faithful**: an inductively
  closed set of local traces. Its `ret` rule recovers the caller through the
  completed callee's own activation ancestry (`caller_of callee = Some caller`),
  so it admits **only matched returns** (`C0 + E0`, `C1 + E1`).
- `caller_of` is the structural activation-parent recovery, descending the frozen
  `caller` field of a `Resume`. It is the mechanism that makes returns matched;
  it must not be weakened.
- No equality `valid_ltr = cfg_collect` is expected or claimed. The only proved
  relation is one-directional sink inclusion
  (`valid_ltr_sink_in_cfg_collect`): every matched-trace sink is a broad-closure
  state. The converse is false in general and is not a goal.
- `cfg_collect_ctx_act` is the activation-keyed forgetful projection of
  `valid_ltr` (`key`-filtered sinks). It is a compatibility view, never an exact
  activation identity.

### Consumer classification (file-level)

| Class | Files | Boundary symbol |
| --- | --- | --- |
| Raw-CFG semantics | `CFG/Collecting/CFG_Collect.thy`, `CFG_Collect_Runs.thy`, `CFG/CFG_Prune.thy` | `cfg_collect`, `cfg_collect_F` |
| Stack-faithful carrier | `CFG/Collecting/CFG_Local_Trace.thy` | `valid_ltr`, `caller_of`, `key` |
| Migration bridge | `CFG_Local_Trace.thy` (`valid_ltr_sink_in_cfg_collect`) | `valid_ltr` -> `cfg_collect` |
| Compiled-program correctness target | `CFG/Compiler/Located_Reaches.thy`, `Located_LTR.thy`; `Formalization/Pipeline/Compiler_Correctness.thy`, `Source_Activation_Sound.thy`, `Mixed_Flow_Sound.thy` | `cfg_collect`, `cfg_collect_ctx_act` |
| Activation / keyed compatibility | `Analysis/.../Activation/Activation_Backbone.thy`, `Activation_Local_Sound.thy`; `Analysis/.../DG/DG_Context_Soundness.thy`, `DG_Soundness.thy`; `Examples/.../Example_Interval_DG_Ctx_Collect.thy`, `Example_Interval_Source_Ctx.thy` | `cfg_collect_ctx_act`, `valid_ltr` |
| Source bridge | `IMP2/IMP2_Bridge.thy`; `Formalization/Pipeline/Source_Activation_Sound.thy` | `cfg_collect` |
| Domain / solver consumer | `Analysis/Generic/Solver/**`, `Analysis/Generic/Equations/**`, `Analysis/Instances/**`, most `Examples/**` | `cfg_collect` |

### Theorem-level anchors stated directly over the boundary

- `valid_ltr`: `valid_ltr_sink_in_cfg_collect`, `valid_ltr_sink_witness`,
  `nested_valid_ltr_example`, and the structural cluster
  (`valid_ltr_Call_caller_valid`, `valid_ltr_Resume_fields`,
  `valid_ltr_caller_valid`, `valid_ltr_path_nonempty`,
  `valid_ltr_Call_path_nonempty`) in `CFG_Local_Trace.thy`;
  `valid_ltr_ctx_chain`, `valid_ltr_ctx_sound` in `Activation_Local_Sound.thy`.
- `cfg_collect_ctx_act`: `cfg_collect_ctx_act_collect_by`,
  `cfg_collect_ctx_act_le_collect` (`CFG_Local_Trace.thy`);
  `source_store_in_cfg_collect_ctx_act`,
  `source_toplevel_in_cfg_collect_ctx_act` (`Located_LTR.thy`).
- `cfg_collect`: the raw-CFG cluster in `CFG_Collect.thy` (its own fixpoint /
  witness / paths lemmas) is the definitional home; every compiled-program
  soundness theorem in the `Formalization/Pipeline` and `Analysis` trees states
  its concrete target as `cfg_collect g S v`. Migrating those to `ltr_collect`
  is R5/R6, not R0.

No R0 edit touched any of these statements.

## Progress log

### R1 — `LTR_Collect` (complete)

`src/CFG/Collecting/LTR_Collect.thy`, imports `CFG_Local_Trace` only, listed in
`src/CFG/ROOT` after `CFG_Local_Trace`. Batch-green in `Voblint_CFG`; no `sorry`.

Definitions: `ltr_F`, `ltr_collect`, `ltr_collect_keyed`.

Theorems: `ltr_F_mono`, `ltr_F_lfp_fold`, `ltr_F_valid_ltr_closed`,
`lfp_ltr_F_subset_valid_ltr`, `valid_ltr_subset_lfp`, **`valid_ltr_eq_lfp`**
(`valid_ltr g S = lfp (ltr_F g S)`), `ltr_collect_I`,
`ltr_collect_keyed_le_collect`, and the three witnesses
`ltr_collect_intra_witness`, `ltr_collect_call_return_witness`,
`ltr_collect_nested_witness`.

One naming adaptation from the proposal: the keyed projection binds its reader as
`keyf`, not `key`, because `key` already names the activation context function in
`CFG_Local_Trace` and reusing it clashes. `ltr_F`'s four clauses match the
proposal literally (return premise: `callee : T` and
`caller_of callee = Some caller`, no `caller : T`).

### R2 — projection laws (complete)

Batch-green in `Voblint_CFG` (which contains both `LTR_Collect` and
`Located_LTR`); no `sorry`.

- `ltr_collect_keyed_le_collect` retained unchanged.
- **Union law** (`LTR_Collect.thy`): `ltr_collect_keyed_Union`:
  `(\<Union>c. ltr_collect_keyed keyf g S v c) = ltr_collect g S v`, i.e.
  `Union (range (ltr_collect_keyed keyf g S v)) = ltr_collect g S v`. Proved for
  any total key by `blast`; no finiteness assumption.
- **Migration bridge** (`LTR_Collect.thy`): `ltr_collect_le_cfg_collect`:
  `ltr_collect g S v \<subseteq> cfg_collect g S v`, derived from the existing
  `valid_ltr_sink_in_cfg_collect` (no re-proof of broad reachability). This
  inclusion is **migration-only and intentionally one-directional**: the converse
  is false in general because `cfg_collect` admits unmatched combine pairs. It is
  neither stated nor attempted.
- **Compatibility** (`LTR_Collect.thy`): `cfg_collect_ctx_act_eq_ltr_collect_keyed`:
  `cfg_collect_ctx_act enterc seedc g S v c = ltr_collect_keyed (key enterc seedc) g S v c`.
  `cfg_collect_ctx_act` is a *direct* keyed projection — its definition body is
  literally `ltr_collect_keyed`'s with `keyf := key enterc seedc` — so the
  equality holds by unfolding both definitions. No mismatch in argument order,
  store projection, or key definition. Its public name and existing theorems are
  unchanged. The activation key stays a quotient of activation structure, not an
  exact activation identity; a single keyed bucket is not claimed to preserve all
  activation correlation.
- **Source projection bridge** (`Located_LTR.thy`, which now also imports
  `LTR_Collect`): `source_store_in_ltr_collect`. Under exactly the assumptions of
  the existing local-trace adequacy result (`wf_compile_input Pi ps main`,
  `source_com main`, `s0 : S`, `star (pstep Pi) (main, s0, []) (residual, s, frs)`),
  a reached source store `s` lies in `ltr_collect (compile_prog Pi ps main) S v`
  at the matched target node `v`. Routed source-run → `source_run_has_ltr`
  `valid_ltr` witness → `ltr_collect_I`; it does not pass through `cfg_collect`.
  The keyed source theorems `source_store_in_cfg_collect_ctx_act` and
  `source_toplevel_in_cfg_collect_ctx_act` are unchanged.
- **Matched-return regression** (`LTR_Collect.thy`): `valid_ltr_Resume_caller_matched`:
  `Resume caller callee p : valid_ltr g S ==> caller_of callee = Some caller`
  (corollary of `valid_ltr_Resume_fields`). Every reachable `Resume` recovers its
  caller from the completed callee, so a return cannot select its caller
  independently — the property separating `ltr_collect` from the unmatched-combine
  `cfg_collect`.

No stop condition triggered: the union law needed no finiteness, the bridge used
only the forward inclusion, `cfg_collect_ctx_act` was a direct keyed projection,
source adequacy avoided `cfg_collect`, the source theorem reused the existing
assumptions, and no dependency cycle appeared (`LTR_Collect` sits between
`CFG_Local_Trace` and `Located_LTR`).

### R3 — not started

The correlation-preserving abstract interface (`gamma_ltr`, the abstraction
theorem `lfp (ltr_F g S) <= gamma_ltr A`) is deliberately unstarted.
