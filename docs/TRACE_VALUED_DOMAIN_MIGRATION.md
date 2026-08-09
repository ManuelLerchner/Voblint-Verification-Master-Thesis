# Migration — trace-valued abstract domain (Approach B revisited)

Status: **PROPOSED.** Not started. Challenges the Approach-B rejection recorded
in `TRACE_BASED_FORK_MIGRATION.md` (2026-06-19). That rejection cited two
blockers — "loses the finite-height lattice" and "loses `TD_side`
termination/executability guarantees." This document argues both are addressable
and proposes a concrete path.

KB: `concepts/semantics-style-tradeoffs.md` §"Can the analyzer be trace-based
directly?" and §"Two senses of trace-based".

---

## Why the rejection was premature

`TRACE_BASED_FORK_MIGRATION.md` dismissed Approach B in one sentence. The
argument assumed that a trace-valued domain requires the *lattice elements* to
be raw trace sets — an infinite-height lattice over which no widening is
definable and no solver terminates. That assumption is false.

The current state domain works as follows:

```
class sound_domain:
  carrier type 'a (the abstract value — sign, interval, ...)
  gamma     :: 'a => int set     (concretization to integers)
  lattice structure on 'a, not on int set
```

The lattice lives on `'a`, not on `int set`. Nothing stops us from defining a
trace-valued domain analogously:

```
class trace_domain:
  carrier type 'b (the abstract trace value)
  gamma_trace :: 'b => trace set   (concretization to traces)
  lattice structure on 'b, not on trace set
```

Whether `'b` has a finite-height lattice is a question about the *carrier*, not
about trace sets. A carrier that encodes bounded call histories is finite. The
"infinite-height lattice" concern evaporates as soon as we pick a concrete `'b`.

---

## The concrete carrier: history-indexed state environments

Fix a bound `k : nat`. Define:

```isabelle
type_synonym call_string_k = "proc_name list"   (* length ≤ k *)

type_synonym 'a trace_abs = "call_string_k => 'a abs_state"
```

An element `f :: 'a trace_abs` maps each reachable call context (a k-bounded
call string) to an abstract state at that context. The concretization is:

```isabelle
definition gamma_trace :: "'a::sound_domain trace_abs => trace set" where
  "gamma_trace f = {t. last t ∈ gamma_state (f (call_string_k_of t))}"
```

where `call_string_k_of t` extracts the k-truncated call string of trace `t`
(the last `k` procedure names on the call stack at the trace endpoint).

**Lattice structure on `'a trace_abs`.**  `call_string_k => 'a abs_state`
inherits the pointwise lattice from `'a abs_state`. HOL's `fun` instance gives
`bot`, `sup`, and the order for free. Widening lifts pointwise too:

```isabelle
definition widen_trace_abs ::
    "'a::abstract_domain trace_abs => 'a trace_abs => 'a trace_abs" where
  "widen_trace_abs f g = (λcs. widen_state (f cs) (g cs))"
```

**Finite height.** The number of distinct call strings of length ≤ k over a
finite set of procedure names is bounded by `|Procs|^0 + ... + |Procs|^k`.
Combined with the finite-height (or widening) of `'a`, the pointwise lattice
`call_string_k => 'a abs_state` has finite height or admits the pointwise
widening. `solve_dom` follows by the same argument as the flat domain — no new
termination obligation beyond the flat case.

---

## Why TD_side compatibility is preserved

`TD_side` is generic over the unknown type and the value type. It requires:

1. `is_mono_eq` — the constraint system is monotone in the unknown map.
2. `mono_sides` — side effects are monotone.
3. `mono_deps` — dependencies are monotone.
4. A `solve_dom` witnessing termination via finite ascending chains.

None of these inspect the *internal structure* of the value type. For Approach
B, the unknowns remain `pp + global` (identical to the current indexed system);
each unknown now holds a `'a trace_abs` value instead of a `'a abs_state`. The
constraint system's RHS functions are more complex (see transfer functions
below), but their monotonicity follows from the pointwise lattice and the
monotonicity of the per-context transfer.

The per-`(pp, digest)` unknown multiplication that Approach A (`TRACE_BASED_FORK_MIGRATION.md`
S3) introduces is **not needed here**. History lives *inside* the value at each
`pp`, not in the unknown index. TD_side's lazy demand-driven solving discovers
active call strings by propagation, not by pre-enumeration.

---

## Transfer functions for trace-valued AI

The transfer functions must evolve `'a trace_abs` values along CFG edges while
maintaining the call-string context. The key operations:

**Assignment / guard edge** (no call-stack change):

```isabelle
definition tf_assign_trace :: "vname => aexp => 'a trace_abs => 'a trace_abs" where
  "tf_assign_trace x e f = (λcs. assign_tf x e (f cs))"
```

Each context's state is updated independently. Monotone because `assign_tf` is
monotone and the pointwise order on `call_string_k => 'a abs_state` is monotone.

**Enter (call) edge** (push callee procedure name `p`):

```isabelle
definition tf_enter_trace :: "proc_name => 'a trace_abs => 'a trace_abs" where
  "tf_enter_trace p f = (λcs.
     case un_push_k p cs of
       Some cs' => enter_tf p (f cs')
     | None     => bot)"
```

`un_push_k p cs` recovers the caller's call string `cs'` such that
`push_k p cs' = cs`; it returns `None` when `cs` has no `p`-prefixed entry (so
the abstract state at inaccessible contexts is `bot`). This is the incremental
call-string push, with truncation at depth `k` (same truncation logic as
Approach A S2 — see R2/R3 in the review findings of that doc).

**Combine (return) edge** (pop callee frame):

```isabelle
definition tf_combine_trace ::
    "'a trace_abs => 'a trace_abs => 'a trace_abs" where
  "tf_combine_trace caller_f callee_f =
     (λcs. ⊔ {combine_tf (caller_f cs) (callee_f cs') |
               cs'. cmp_k cs' (push_k callee cs)})"
```

For each caller call string `cs`, join over all callee call strings `cs'` that
are `cmp_k`-compatible with `push_k callee cs`. This is the k-CFA
over-approximation at return edges: because truncation may have discarded the
oldest frame, we cannot recover the exact caller from the callee string; instead
we join all `cmp_k`-compatible callers. Exactly the sound over-approximation
described in R3 of `TRACE_BASED_FORK_MIGRATION.md`, now applied at the value
level rather than the index level.

---

## Soundness contract

The new headline theorem replaces `trace_ip_analysis_sound`:

```isabelle
theorem trace_valued_ip_analysis_sound:
  "td_analyse_trace g S pp ≤ env_trace pp
   ⟹ ∀t ∈ cfg_collect_trace_ip g S pp. t ∈ gamma_trace (env_trace pp)"
```

where `td_analyse_trace` is the analyzer operating on `'a trace_abs` unknowns.
This is a *strictly stronger* statement than the current `trace_ip_analysis_sound`
because `gamma_trace` captures full trace history, not just the last store:

```
current:   (last t) ∈ gamma_state (env pp)        (alpha_last projection)
trace-val: t ∈ gamma_trace (env_trace pp)          (full history covered)
```

Every property expressible as a trace predicate — the "last write" property,
call-context sensitivity, thread-history for concurrency — falls directly out of
the soundness contract without an auxiliary reaching-trace lemma.

---

## Relationship to Approach A (digest partitioning)

Approach A (`TRACE_BASED_FORK_MIGRATION.md`) and Approach B are **computationally
equivalent** for k-call-string digests. The difference is packaging:

| | Approach A | Approach B |
| --- | --- | --- |
| Unknown type | `(pp × call_string_k) + global` | `pp + global` |
| Value type at each local unknown | `'a abs_state` | `call_string_k => 'a abs_state` |
| History lives in | *unknown index* | *abstract value* |
| TD_side unknown count | ` | pp | × | call_strings | ` | ` | pp | ` |
| TD_side value complexity | simple | richer (function type) |

The `envd :: pp => call_string => abs_state` from Approach A and the
`env_trace :: pp => (call_string => abs_state)` from Approach B are
definitionally the same object, just curried differently. The call-string
push/pop at call/return edges is the same logic; it surfaces in Approach A as
the `step_digest_refines_dg` obligation and in Approach B as the `tf_enter_trace`
/ `tf_combine_trace` transfer functions.

Choosing between them is therefore an **engineering tradeoff**, not a
fundamental distinction:

- Approach A exposes the call-string structure to TD_side; the solver may
  exploit laziness to avoid evaluating inaccessible call-string partitions.
- Approach B hides the structure inside the domain value; the solver operates
  over fewer unknowns but each RHS computation is more expensive.

Neither is strictly better for all programs. Approach B is arguably cleaner from
a domain-theory perspective: the domain carries its own context-sensitivity
without requiring a modified unknown index.

---

## Pre-conditions for viability (resolve before building)

**P1 — `call_string_k_of` is well-defined on `cfg_collect_trace_ip` traces.**
Traces produced by the concrete semantics are IMP2 execution traces; the call
stack is a list of active procedure frames. `call_string_k_of` must extract and
truncate this list. Confirm the concrete trace type carries enough call-stack
information (check `CFG_Collect_Trace_IP.thy` trace definition).

**P2 — `push_k` / `un_push_k` truncation is consistent with `cmp_k`.**
Same obligation as Approach A R2: the incremental push used in transfer
functions must agree with whole-trace `call_string_k_of` on truncation
boundaries. State as `call_string_k_of (t @ [e]) = push_k p (call_string_k_of t)`
for call edge `e` entering procedure `p`. Prove before S2.

**P3 — `tf_combine_trace` is sound at returns.**
Show that for any caller trace `τ` and callee trace `ρ` such that
`hd ρ = enter_state (last τ)` (the junction condition from `cfg_collect_trace_ip`),
the combined trace `τ @ ρ'` satisfies
`combined_last ∈ gamma_state (tf_combine_trace f_caller f_callee (call_string_k_of τ))`.
This is the Approach A R3 obligation rephrased for the value-level combine.

**P4 — Pointwise widening is sufficient for `'a trace_abs`.**
`call_string_k => 'a abs_state` has finitely many keys (bounded call strings).
Confirm that pointwise `widen_state` per key gives a `warrowing` instance; no
new widening theory needed beyond the per-key instance.

**P5 — Constraint system RHS is expressible in `TD_side`'s format.**
`TD_side` expects a `rhs` function `(pp + global => 'a) => pp + global => 'a`.
The Approach-B RHS at a call edge involves computing `tf_enter_trace` from the
callee-pp value. Confirm this stays within TD_side's dependency model (no
circular dependency on the unknown it is computing that would prevent scheduling
— the same check as S3 in Approach A).

---

## Slices (additive; each build-gated)

**S1 — `TraceAbs` locale and call-string type.**
Define `call_string_k` (k-bounded list over `proc_name`), `push_k`, `un_push_k`,
`cmp_k`. Define the `trace_domain` locale extending `sound_domain` with
`gamma_trace`. Prove the lattice instance for `call_string_k => 'a abs_state`.
Exit: locale + instance, no `sorry`.

**S2 — Transfer functions and their soundness.**
Define `tf_assign_trace`, `tf_enter_trace`, `tf_combine_trace`. Prove P2 (push
consistency) and P3 (combine soundness). Exit: `tf_enter_sound` /
`tf_combine_sound`, no `sorry`. This is the hardest slice — the k-CFA
truncation consistency is the known-hard part.

**S2.5 — Conservativity at `k = 0`.**
For `k = 0`, every call string is the empty string `[]`; `call_string_k_of t = []`
for all `t`. Show that the `k = 0` instance reproduces `alpha_last` projected to
the flat `env pp`:

```isabelle
gamma_trace_k0 f = {t. last t ∈ gamma_state (f [])} = alpha_last_sound_set (f [])
```

This confirms the generalization is conservative. Gate on this before S3.

**S3 — Trace-valued constraint system.**
Define `side_rhs_trace_fold` (the per-pp RHS combinator over `'a trace_abs`
values), prove `mono_sides_trace` / `mono_deps_trace` / `is_mono_eq_trace`.
Discharge P4 and P5. Deliverable: executable `side_analyse_trace` producing
`env_trace`.

**S4 — Soundness.**
Prove `trace_valued_ip_analysis_sound` from the TD_side post-fixpoint of
`side_analyse_trace`. Baseline: `gamma_trace_k0_sound` (the `k = 0` instance
implies the current `trace_ip_analysis_sound` via `alpha_last`). The `k > 0`
instance strictly strengthens it.

**S5 — Witness example.**
A twice-called procedure where two callers write different values to the same
global. Show that `env_trace` (for `k ≥ 1`) distinguishes the two callers
while `env` (flat) joins them. State as
`gamma_trace (env_trace pp) ⊊ alpha_last_preimage (gamma_state (env pp))` at
the read point — a certified precision theorem, not an evaluated inequality.

---

## Relationship to existing infrastructure

- **`cfg_collect_trace_ip`** — the concrete ground truth; becomes the direct
  soundness target without `alpha_last` on the spine.
- **`alpha_last`** — relegated to the `k = 0` conservativity corollary (S2.5);
  no longer a structural step in the main soundness proof.
- **`digest_env_sound` / `digest_read_sound`** — superseded by
  `trace_valued_ip_analysis_sound`; the history-sensitive read is an immediate
  corollary (`gamma_trace` covers the trace directly).
- **`flat_env_is_digest_sound`** — becomes the `k = 0` instance of
  `S2.5`; still holds, still the conservativity baseline.
- **`TD_side` vendored solver** — untouched; unknown type and solver interface
  unchanged (unknowns remain `pp + global`).
- **Existing domain instances** (sign, interval, parity) — plug into
  `'a trace_abs` for free; they provide the per-context `abs_state`, not the
  context-indexing itself.

---

## Exit criteria

- `isabelle build` green, sorry-free, for a new `Voblint_TraceValued` session.
- `side_analyse_trace` code-generates and runs on the vendored `TD_side` solver.
- `gamma_trace_k0_sound` holds: the flat analyzer is the `k = 0` instance.
- S5 witness discharges a certified precision theorem (not just a print-out).
- `trace_valued_ip_analysis_sound` subsumes `trace_ip_analysis_sound` as a
  corollary through `alpha_last`.

---

## Out of scope (here)

- **Approach A (digest partitioning)** — `TRACE_BASED_FORK_MIGRATION.md`.
  The two approaches are equivalent for k-call-strings; this doc does not
  supersede that plan — they can coexist or be unified.
- **Thread-modular / concurrency.** History-sensitivity generalizes to
  thread histories (locksets, thread IDs), but that is a downstream direction.
- **Infinite-history domains** (e.g., regular language domains, full trace
  partitioning without a `k` bound). Those need a separate widening theory and
  are not addressed here.
- **`_ip` -> canonical rename** — orthogonal; tracked separately.
