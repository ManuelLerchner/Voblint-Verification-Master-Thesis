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
corollaries of the generic interface. "Migrate" means the flagship and
source-level chains *terminate* in `ltr_collect` / `ltr_collect_keyed`; the
raw-`cfg_collect` theorems are retained as compatibility results, not deleted.

Exit gate: all five sessions are batch-green; the theorem statements retain
their existing user-facing plain and keyed result shapes.

Done — see "R6 — flagship + source chain terminate in the trace semantics" below.

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

### R3 — correlation-preserving abstract interface (design spike complete)

`src/CFG/Collecting/LTR_Abstract.thy`, imports `LTR_Collect` only; domain-free
(no `sound_domain`/`abs_state`/solver/DG). Batch-green in `Voblint_CFG`; no
`sorry`.

Carrier: a context-indexed concretization `acc :: pp => 'c => store set` inside
`locale ltr_gamma` with the four closure axioms `ROOT / EDGE / SEED / COMB`.
Selected design is Candidate A (abstract continuation) collapsed to its
functional core: the continuation of an activation is its context slot, and the
callee is bound to the caller by the *derivable* law
`callee-ctx = enterc (caller-ctx) (entry_store callee)` (`callee_entry_invariant`,
a theorem of `valid_ltr`) — no stored continuation object or activation record.

Theorems: four closure lemmas `root_closed / intra_closed / call_closed /
return_closed`; `gamma_chain`; **`valid_ltr_subset_gamma_ltr`** and its
fixed-point form **`lfp_ltr_F_subset_gamma_ltr`** (`lfp (ltr_F g S) <= gamma_ltr`
via `valid_ltr_eq_lfp`); validation `return_uses_matched_callee`,
`two_callers_separated`; non-vacuity `ltr_gamma_UNIV`. The correlation originates
in `valid_ltr` (through `return_closed`/`callee_entry_invariant`), **not** in key
injectivity — the key may merge activations; the interface only asserts every
matched trace lands in some bucket.

### R4 — migrate the activation and DG client (complete)

Both consumers now ride on the domain-free interface; batch-green across
`Voblint_Analysis` and the full dependent DAG including the interval DG context
flagship; no `sorry`.

- **Activation.** `Activation_Local_Sound` imports `Voblint_CFG.LTR_Abstract` and
  re-derives the engine `valid_ltr_ctx_sound` by interpreting `ltr_gamma` at
  `acc v c = [[sg (Inl (v, c))]]` (discharging `ROOT/EDGE/SEED/COMB` from the
  existing `ENTRY_G/EDGE/SEED_G/COMB`) and projecting
  `valid_ltr_subset_gamma_ltr`. The duplicate four-case induction
  (`ret_bound`, `valid_ltr_ctx_chain`) is deleted. `valid_ltr_ctx_sound` keeps
  its exact statement; `Activation_Backbone.activation_collect_sound` is
  unchanged and now transitively consumes `LTR_Abstract`.
- **DG.** `DG_Ctx_Activation` is unchanged in proof; its `dg_ctx_act_edge` /
  `dg_ctx_act_comb_covered` transport discharges the `EDGE` / `COMB` premises of
  the now-`LTR_Abstract`-backed `activation_collect_sound` (assembled at the
  interval flagship, which stays green). DG performs no caller/callee matching —
  `dg_ctx_act_comb_covered` transports abstract states at whatever slots the
  backbone hands it; the matched relation is `valid_ltr`'s.

Assumption comparison (public engine): the new `valid_ltr_ctx_sound` has the
**identical** assumptions and conclusion as before
(`ENTRY_G/EDGE/SEED_G/COMB/t`); no assumption strengthened or newly exposed. The
locale `ltr_gamma` axioms are the same four obligations at the concretization
`acc = (\<lambda>v c. [[sg (Inl (v,c))]])`. `activation_collect_sound` and the
`cfg_collect_ctx_act` compatibility results keep their names and statements.

No stop condition triggered: the interpretation does not strengthen any public
theorem; the key is not assumed injective; DG reconstructs no caller/callee
pairs; no executable solver equation changed; no concrete trace enters executable
state; no dependency cycle (`LTR_Abstract` sits in `Voblint_CFG`, below the
analysis layer).

### R5 — migrate generic solver soundness (first migrated theorem landed)

The monovariant compiled-program carrier now has a trace-based sibling stated
directly over `ltr_collect`, proved through `LTR_Abstract`, beside the retained
raw-CFG results. Batch-green across `Voblint_Analysis` and the full DAG; no
`sorry`.

Audit (generic solver spine → `cfg_collect`):

- **raw-CFG generic:** `cfg_collect_F` / `cfg_collect` fixpoint, witness, and
  `paths` lemmas (`CFG_Collect.thy`); `cfg_collect_post_fixpoint_sound`,
  `post_fixpoint_sound`, `unified_post_fixpoint_sound` (`Analysis_Sound` /
  `Constraint_System_Sound`). Retained unchanged.
- **compiled-program target (monovariant):** `post_fixpoint_sound_at` and the
  effectful `post_fixpoint_sound_at_eff` used by
  `side_collect_sound_exit_pruned_eff` (`TD_Side_Eff_Soundness`). These conclude
  `cfg_collect g S v <= gamma`.
- **context/keyed target:** `activation_collect_sound` — already over
  `cfg_collect_ctx_act` (= `ltr_collect_keyed`), trace-based since R4.
- **executable solver bridge:** the `sound_effectful_transfer` eff spine.
- **domain-specific:** Sign / Interval / Mixed corollaries (not touched — R6).

Smallest theorem whose conclusion should move: `post_fixpoint_sound_at` (the
monovariant abstract carrier). Migration boundary chosen there.

New theorems (`Analysis_Sound.thy`, in `sound_transfer`):
`ltr_post_fixpoint_sound_at` — `ltr_collect g S v0 <= [[env v0]]` from the
per-step domain premises, via a `ltr_gamma` interpretation at the context-free
`acc v _ = [[env v]]`; and `unified_ltr_post_fixpoint_sound` — the same from an
`is_post_fixpoint` witness. The `ROOT/EDGE/SEED/COMB` obligations are discharged
from the existing `edge_of_bound` / `combine_collect_sound` bounds; `COMB` sees
only the caller and callee-exit slots of a single combine triple. The proof does
**not** route `ltr_collect <= cfg_collect` then old `cfg_collect` soundness — that
bridge is compatibility only. The raw-CFG `post_fixpoint_sound` /
`unified_post_fixpoint_sound` are kept unchanged beside it.

Recursive validation: `Example_Proc_Call_LTR.thy` (new leaf) restates the
interval exit result of `Example_Proc_Call` — whose program calls `inc` from two
sites — over `ltr_collect` via `unified_ltr_post_fixpoint_sound`. It calls
neither `ltr_collect_le_cfg_collect` nor the broad combine soundness, assumes no
key injectivity, and changes no solver equation. It lives in a separate leaf
because importing the trace stack shadows `Example_Proc_Call`'s bare `Call`
constructor with `ltr.Call`.

No stop condition triggered: the generic per-step premises discharge matched
`COMB`; the result is not proved by the old `cfg_collect` theorem; no
caller/callee reconstruction; no concrete trace enters executable state; public
solver assumptions are unchanged; no domain fact is needed at the generic level.

### R5b — effectful / TD-side solver soundness (trace theorem complete)

The effectful monovariant compiled-program carrier now has a trace-based sibling, beside the
retained raw-CFG effectful results. Batch-green across `Voblint_Analysis` and the full DAG; no
`sorry`.

Effectful audit (spine → `cfg_collect`):

- **smallest generic compiled-program theorem:** `post_fixpoint_sound_at_eff`
  (`TD_Side_Eff_Sound`, in `sound_effectful_transfer`) — from full-`g` per-edge / per-combine
  effectful bounds it concludes `cfg_collect g S v0 <= [[side_env sigma v0]]`. Its consumers
  (`side_collect_sound_exit_pruned_eff`, `side_analyse_eff_collect_sound_at`,
  `side_collect_sound_exit_pruned_eff_cone`) add exit-pruning via `cfg_collect_prune_to_query` /
  `cfg_collect_prune_exit`.
- **executable solver bridge:** `side_analyse_eff` / `td_cfg_side_solver_eff` wrappers.
- **keyed/context system:** already trace-based since R4 (`activation_collect_sound`).

The solver here is genuinely **monovariant**, so the trace target is `ltr_collect g S v`, not the
keyed `ltr_collect_keyed`.

New theorems:

- `ltr_post_fixpoint_sound_at_eff` (`LTR_TD_Side_Eff_Sound.thy`, in `sound_effectful_transfer`):
  `ltr_collect g S v0 <= [[side_env sigma v0]]` from the *same* hypotheses as
  `post_fixpoint_sound_at_eff`, via a `ltr_gamma` interpretation at
  `acc v _ = [[side_env sigma v]]`. `ROOT/EDGE/SEED/COMB` discharged from
  `edge_collect_etf_sound` / `etf_collecting_full_le_side_env` / `etf_sound_combine` (helper
  `edge_step_sound_eff`); `COMB` binds `cl`/`ex` from one combine triple. No `cfg_witness`
  induction, no `cfg_collect` step.
- `side_collect_sound_exit_pruned_eff_ltr` and its cone form
  `..._ltr_cone` (`LTR_TD_Side_Eff_Pruned.thy`): the trace analogue of
  `side_collect_sound_exit_pruned_eff`. Same cone bound-derivation, ending in
  `ltr_post_fixpoint_sound_at_eff`, concluding
  `ltr_collect (prune_cfg g) S (cfg_exit g) <= [[side_env sigma (cfg_exit g)]]`.

**Deferred: the over-`g` lift.** `side_collect_sound_exit_pruned_eff` frames `cfg_collect g <=
cfg_collect (prune_cfg g)` (`cfg_collect_prune_exit`) to state its result over `g`. The trace
analogue `ltr_collect g S (cfg_exit g) <= ltr_collect (prune_cfg g) S (cfg_exit g)` is **not a
pure graph lemma**: `valid_ltr`'s `call` rule couples a callee-enter edge with its matching
combine triple, so a bare `ltr.Call` lands in the pruned trace set only when the return node also
reaches the exit — a well-bracketing property, established structurally by `Located_LTR` (source
runs), not by graph reachability. The pruned trace theorem is therefore stated over
`prune_cfg g` (the graph the demand-driven solver covers); lifting it to `g` is a source-bridge
task. The raw-CFG `side_collect_sound_exit_pruned_eff` (over `cfg_collect g`) is retained
unchanged for that route. This is the R5b boundary, reported rather than routed around by the
`cfg_collect` bridge.

Recursive validation: `Example_Mixed_Flow_Sign_LTR.sign_mixed_flow_sound_ltr_from_pp` restates the
self-recursive `inc` procedure's effectful sign exit soundness over
`ltr_collect (prune_cfg (compile_prog ...))`, via `side_collect_sound_exit_pruned_eff_ltr_cone`,
from the same post-solution hypotheses as the raw-CFG `sign_mixed_flow_sound_from_pp`. Its proof
references none of `ltr_collect_le_cfg_collect`, `cfg_collect_post_fixpoint_sound`,
`post_fixpoint_sound_at_eff`; no key injectivity; no solver-equation change. (A separate leaf: the
example's compiled terms use a bare `Call`, shadowed by `ltr.Call` under the trace import — the
statement qualifies `com.Call`.)

No stop condition triggered for the delivered theorems; the over-`g` pruned lift is reported as
the boundary (per "the source bridge cannot establish adequacy" class), not forced through
`cfg_collect`.

### R5c — cone-guarded exit soundness over the original CFG (pruning retired)

R5c/R5d first attempted a graph-pruning frame; R5d found its bridge `call_return_reaches` **false**
for compiled programs (uncalled procedures leave call sites whose continuation cannot reach the
exit). The resolution was to recognize that pruning was a `cfg_collect`-era artifact: the
demand-driven solver is cone-restricted, but the *semantics* need not be. Instead of shrinking the
graph, the cone restriction moves into the abstract guarantee. Batch-green across the full DAG; no
`sorry`.

Mechanism (`LTR_TD_Side_Eff_Exit.thy`, `Voblint_Analysis`): interpret `ltr_gamma` at the
cone-guarded concretization

```text
acc v _ = (if cfg_reaches g v v0 then [[side_env sigma v]] else UNIV)
```

Each closure axiom splits: off the cone the slot is `UNIV` (trivial); on the cone the source is on
the cone too (`cfg_reaches_edge_src` / `cfg_reaches_combine_exit_src`, now in `CFG_Prune`), so the
real `side_env` bound applies — exactly the bound the cone solver computed. `cfg_exit g` reaches
itself, so the conclusion is unguarded there.

New theorems (`LTR_TD_Side_Eff_Exit.thy`):

- **`ltr_post_fixpoint_sound_at_eff_cone`** — `ltr_collect g S v0 <= [[side_env sigma v0]]` from
  cone-restricted per-edge / per-combine bounds (hypotheses guarded by `cfg_reaches g _ v0`),
  precisely what the solver proves. The COMB case derives caller (`cfg_reaches_combine_call` +
  trans) and callee-exit (`cfg_reaches_combine_exit_src`) cone facts, so both abstract premises use
  real slots — not just `ret` reachability.
- **`side_collect_sound_exit_eff_ltr_cone`** — the primary compiled-program corollary, directly
  over the original `g`: `ltr_collect g S (cfg_exit g) <= [[side_env sigma (cfg_exit g)]]` from the
  cone post-solution (`side_cone_in_vars_eff` supplies the guarded bounds). **No `prune_cfg`, no
  `call_return_reaches`, no `cfg_collect`, no compiled-CFG restriction** — holds for arbitrary CFGs.

Validation (`Example_Mixed_Flow_Sign_LTR.sign_mixed_flow_sound_ltr_from_pp`): the recursive `inc`
procedure's effectful sign exit soundness over `ltr_collect (compile_prog ...)`, over the original
graph, **with no pruning bridge**. The R5d counterexample is subsumed automatically: a dead
procedure's call site is off the exit cone, where the guard makes its obligation vacuous, so no
`call_return_reaches` is needed.

Retired (deleted, all uncommitted from R5c/R5e): `LTR_Prune.thy` (`call_return_reaches`,
`valid_ltr_prune_to`, `ltr_collect_prune_exit`), the R5e dead-end `LTR_Prune_Exit.thy`
(`subacts` / `comb_all` trace-local frame), and `LTR_TD_Side_Eff_Pruned.thy` (the pruned-graph
theorems + the `wb`-conditioned lift). The two reachability helpers moved to `CFG_Prune`. The
full-graph `ltr_post_fixpoint_sound_at_eff` (`LTR_TD_Side_Eff_Sound.thy`) is kept as the general
"all edges bounded" effectful trace theorem.

Architecture: `cone-restricted solver post-fixpoint -> cone-guarded concretization -> LTR_Abstract
over g -> ltr_collect g S exit`. No pruning transformation, no pruning adequacy, no
`call_return_reaches`, no compiled-CFG restriction, no source-completeness, no change to
`valid_ltr`, no trace object in executable solver state.

### R6 — flagship + source chain terminate in the trace semantics

The flagship and source-level correctness chains now terminate in `ltr_collect`
(monovariant) or `ltr_collect_keyed` (context-sensitive), never routing through
`ltr_collect_le_cfg_collect`. The raw-`cfg_collect` theorems stay as compatibility
results.

Keystone: `ltr_collect_semantic_postfix` (`LTR_Abstract`) — the trace-native twin of
`cfg_collect_semantic_postfix`, same set-valued entry/edge/combine premises, concluded
over `ltr_collect` through the context-free `ltr_gamma` instance `acc v _ = B v`.

`DG_Soundness` was refactored to expose the three `dg_postfix_gamma_{entry,edge,combine}`
closure obligations; both the `cfg_collect` endpoint (`dg_postfix_collect_sound`) and the
trace-native one share them. Trace-native DG endpoints:

- `DG_LTR_Sound` — generic `dg_post_solution_collect_sound_ltr`.
- `Interval_DG_LTR` / `Sign_DG_LTR` — `ivl_dg` / `sign_dg` endpoints (kept in leaves
  because importing the trace stack shadows the bare `Call` constructor).

Domain path map (per the R6 goal table):

| path | trace endpoint |
| ---- | -------------- |
| monovariant Sign/Interval (plain post-fixpoint) | `unified_ltr_post_fixpoint_sound` (`Example_Proc_Call_LTR`) |
| effectful Sign/Mixed | `side_collect_sound_exit_eff_ltr_cone` (`Example_Mixed_Flow_Sign_LTR`) |
| monovariant DG flagships | `ivl_dg`/`sign_dg` `dg_post_solution_collect_sound_ltr` (`Example_Interval_DG_Flagship_LTR`, `Example_Interval_DG_IP_Flagship_LTR`, `Exec_Sign_DG_Run_LTR`) |
| context-sensitive Interval / DG-context | `activation_collect_sound` -> `cfg_collect_ctx_act` = `ltr_collect_keyed` (already trace-native: `Example_Interval_DG_Ctx_Collect`, `Example_Interval_Source_Ctx`) |

Source chain: `source_reaches_ltr_collect` (`Source_Activation_Sound`) is the monovariant
source->trace bridge (`source pstep -> valid_ltr -> ltr_collect`), reused by
`flagship_source_run_sound_ltr` / `twice_source_run_sound_ltr`. The context-sensitive
source chain (`source_activation_sound`) already terminates in `cfg_collect_ctx_act`.

Review invariants held: executable post-solution reused unchanged; no
`ltr_collect_le_cfg_collect` in any flagship proof; the single-caller `COMB` obligation
reads one combine triple, so DG adds no second caller/callee matching; keyed `twice` still
reads/returns through distinct caller contexts; raw-CFG theorems retained.

### R7 — consolidation (editorial)

R0–R6 are complete and batch-green. R7 is cleanup only: no semantics, solver equations,
executable results, domain operations, or public theorem assumptions change.

**Canonical naming.**

```text
compiled IMP2 programs:
  valid_ltr / ltr_collect / ltr_collect_keyed are canonical.

arbitrary CFG records:
  cfg_collect remains the broad graph semantics (unmatched-combine closure).
```

- `cfg_collect_ctx_act` is definitionally the keyed LTR projection
  (`cfg_collect_ctx_act_eq_ltr_collect_keyed`): a name, not a separate semantics.
- `ltr_collect_le_cfg_collect` is a one-way compatibility bridge, `ltr_collect g S v <=
  cfg_collect g S v`. Equality with `cfg_collect` is neither claimed nor desired; the
  matched-return discipline of `valid_ltr` is strictly sharper.
- The cone restriction lives in the abstract guarantee (`ltr_post_fixpoint_sound_at_eff_cone`
  guards `acc` by `cfg_reaches`), never in a graph transformation. There is no LTR pruning.

**Canonical theorem index** (actual names in-tree):

| intended use | theorem | theory |
| ------------ | ------- | ------ |
| generic monovariant post-fixpoint | `unified_ltr_post_fixpoint_sound` | `LTR_Analysis_Sound` |
| generic effectful exit (cone-guarded) | `side_collect_sound_exit_eff_ltr_cone` | `LTR_TD_Side_Eff_Exit` |
| generic set-valued closure | `ltr_collect_semantic_postfix` | `LTR_Abstract` |
| generic keyed / context-sensitive | `activation_collect_sound` | `Activation_Backbone` |
| generic D/G trace endpoint | `dg_post_solution_collect_sound_ltr` | `DG_LTR_Sound` |
| interval / sign D/G trace endpoint | `ivl_dg_post_solution_collect_sound_ltr` / `sign_dg_post_solution_collect_sound_ltr` | `Interval_DG_LTR` / `Sign_DG_LTR` |
| source -> plain LTR | `source_reaches_ltr_collect` | `Source_Activation_Sound` |
| source -> keyed LTR | `source_activation_sound` | `Source_Activation_Sound` |
| raw / arbitrary CFG | `unified_post_fixpoint_sound`, `dg_post_solution_collect_sound`, `cfg_collect_semantic_postfix`, `ltr_collect_le_cfg_collect` | `Analysis_Sound` / `DG_Soundness` / `LTR_Collect` |

**Compatibility retained (raw-CFG, not deleted):** `cfg_collect` and its endpoints,
`cfg_collect_ctx_act`, `ltr_collect_le_cfg_collect`, the cfg-level effectful pruning spine
(`prune_cfg`, `side_analyse_eff_collect_sound_exit_pruned{,_gen}`,
`side_analyse_eff_collect_sound_at_pruned`), and all `*_collect_sound` example witnesses.

**Removed:** none. No dead theory was found. (`TD_Side_Eff_Ctx_Shared.thy` looks orphaned by
the top-level ROOT `theories` list, but `TD_Side_Eff_Keyed_Gen` imports it and uses
`inr_slot_locals_bot_ctx` / `inl_slot_globals_bot_ctx` / `pull_ctx`; it is built as a
transitive dependency, so it stays.)

**Not retired:** `cfg_collect` stays the canonical *arbitrary-CFG* semantics; only its role as
the *compiled-program* correctness target is superseded by `ltr_collect`. Deferred to a future
stage (was "R7 retire the legacy target") — no compiled soundness theorem depends on
unmatched-combine collecting, but the raw infrastructure is deliberately kept.
