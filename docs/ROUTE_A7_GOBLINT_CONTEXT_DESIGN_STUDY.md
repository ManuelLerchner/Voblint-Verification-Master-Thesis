# A7 design study: Goblint D/G/C context interface

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` path discussed here has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

Design review only. No theory changes are prescribed here.

> **Status (2026-07-08) — reconciliation.** The `(node, context)` unknown
> mechanism this study analyses is **already modeled and verified**, not pending.
> Goblint solves over `(node, context)` unknowns (`type lv = MyCFG.node * S.C.t`,
> `FromSpec` in
> [`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml)),
> call-only context selection, separate flow-insensitive `V.t -> G.t` globals.
> The formalization captures that shape: the `context_domain` locale mirrors
> `Spec` (`start_context`/`prep`/`ctx_sel`/`entdg`/`cmp`); the semantic
> entry-state instance is **sound, strictly precise, and computed**
> (`semantic_entry_store_ctx_analysis_sound`,
> `entry_store_context_precision_witness`); the contract is
> `cfg_collect_ctx` + `context_analysis_sound` / `digest_env_sound` /
> `digest_read_sound`. **This is sufficient for the core thesis claim.**
>
> The `D/G/C` boundary described below (feed `ctx_sel` a pre-loss `R_read`
> instead of the joined `side_env_cmp` view; add `publish`/`read_global`) is
> **faithfulness polish, POSTPONE** — its payoff is dissolving the `fctx`
> negative result, not enabling context-sensitivity, which already works. It is
> genuine soundness research (changes `ENTER_MONO`/`CMP_SOUND`), not a blocker.
> Sibling optional items: computed k-call-string breadth
> (`TRACE_BASED_FORK_MIGRATION.md`, Track A) and context-bounding lifters
> (Context Gas / Loopfree Callstring — future). See `docs/NEXT_STEPS.md`
> "Context-sensitivity status".

Upstream Goblint correction (2026-07-02): Goblint does **not** update contexts on
ordinary CFG edges. Its `Spec.context` receives a `D.t` local abstract state. In
the base analysis, that `D.t` store may still contain C globals
flow-sensitively under some configurations; those values can later be published
to the separate `G.t` global side store. This is evidence for the general
architectural invariant, not the invariant itself: context selection must observe
a state that has not yet lost the information used to compute the context.

This changes the A7 conclusion. The primary Goblint-like redesign is a real
`D/G/C` split in the Isabelle interface, with an explicit boundary between
routing information and published global side information. A `step_ctx` or
`context_intra` function on normal edges can still be explored as a precision
mechanism, but it is not the Goblint model and should not be the main route.

---

## 1. Upstream facts

Goblint's analysis interface has three relevant domains:

| Component | Meaning |
| --- | --- |
| `D.t` | local, flow-sensitive abstract state at a CFG node and context |
| `G.t` | global side-effect domain, addressed by analysis-defined `V.t` names |
| `C.t` | context domain |

The manager passed to transfer functions contains `local : D.t`,
`global : V.t -> G.t`, and `sideg : V.t -> G.t -> unit`. The `context` callback
has the shape:

```ocaml
val context : (D.t, G.t, C.t, V.t) man -> fundec -> D.t -> C.t
```

For `base`, `D.t` is a store. Its `context` implementation filters the supplied
store to obtain the callee context. Reads of globals use `man.global` only in
early-global or multithreaded modes; otherwise the store can still carry globals
flow-sensitively. This is Base behaviour, not a requirement that all analyses
retain globals in `D`.

Consequence: Goblint's context mechanism is call-only, but the value supplied to
it is chosen by the analysis and may contain the information needed to distinguish
calls before that information is published, widened, or joined away.

---

## 2. Current mismatch

Current keyed soundness routes through a combined read:

```text
side_env_cmp gcmp sigma (v, ctx)
  = sigma (Inl (v, ctx)) joined with compatible global slots
```

The exact names vary by theorem, but the pressure points are:

- `TD_Side_Eff_Cmp_Sound.thy`: `post_fixpoint_sound_at_ctx_semantic_cmp_final`
  and its `ENTER_MONO`/`CMP_SOUND` obligations.
- `TD_Side_Eff_Cmp_Gen.thy` / `Global_Cmp_Read.thy`: `side_env_cmp` and
  `glob_env_cmp`.
- `Exec_Cmp_Bridge.thy`: `switching_combine_st`, which computes the target
  context after `QueryL (cc, ctx)` and `QueryG ctx`.
- `Context_Domain.thy`: current `route cc ctx a = ctx_sel cc ctx (prep cc a)`.

The bad coupling is not just that the old kernel `ec` lacked `cc` or `prep`.
The deeper issue is that the state passed to context selection has already been
assembled from local plus global side slots. If a C global is represented only
in `Inr g`, context selection sees the joined side-store value.

The architectural issue is therefore not specifically "`ctx_sel` receives local
joined with global." The issue is that the current transfer layer removes the
context-relevant part of a state from the local result before context selection
can observe it:

```text
transfer state
  -> Side(global contribution)
  -> Answer(local contribution)
```

For a variable represented only by the side contribution, later routing can read
it only through the side store. That store has forgotten which program point
produced each contribution.

---

## 3. `step_ctx` is not the primary route

The previous option A said: update context on intra edges so `ctx =
digest(current state)`. That can separate phases, but it is not Goblint-like:

- Goblint context changes at call/entry selection, not after every ordinary
  edge.
- Goblint's precision comes from the state supplied to `context`, not from making
  the context itself flow on normal edges.
- Intra-edge context updates risk data-dependent read dependencies and would
  reopen the `static_deps` proof shape.

Keep `step_ctx` as a fallback experiment for an explicitly different analysis.
Do not present it as the Goblint-aligned solution.

---

## 4. Refined `context_domain`

The design target is a locale that exposes the `D/G/C` split directly.

```isabelle
locale context_domain =
  fixes start_context :: "'c"
    and enter_d       :: "pp => 'd => 'd"
    and ctx_sel       :: "pp => 'c => 'd => 'c"
    and publish       :: "pp => 'c => 'd => ('g => 'gstate option)"
    and read_global   :: "'g => 'gstate"
    and entdg         :: "store => 'c"
    and cmp           :: "'c => 'c => bool"
```

This is schematic, not final Isabelle syntax. The important changes are:

- `ctx_sel` consumes a routing state: the callee-entry abstract state produced
  by `enter`, or the caller state after the call-entry transform.
- The global side store remains separate: `G` is read and written through named
  slots, not folded into the value passed to `ctx_sel`.
- Context is derived from a state that still contains the routing information,
  not from `side_env_cmp` after the relevant information has been joined away.
- Publication to `G` is explicit and analysis-controlled, matching Goblint's
  `sync`/`sideg` discipline.

For the current formalization, the smallest usable approximation is likely:

```isabelle
ctx_sel :: pp => 'c => 'a abs_state => 'c
```

with a side condition that the `'a abs_state` argument has not lost the
information used by `ctx_sel`; it must not be forced to be
`side_env_cmp sigma (cc, ctx)`. That keeps the existing uniform state type while
correcting the interface boundary.

---

## 5. Generator change

The generator should compute the callee context from the routing state before the
relevant information is published, widened, or joined away:

```text
QueryL (cc, ctx) (fun d_call ->
  let d_enter = enter_d cc d_call in
  let callee_ctx = ctx_sel cc ctx d_enter in
  publish selected global contributions to G slots;
  read callee exit at (ex, callee_ctx);
  combine return)
```

What changes from `switching_combine_st`:

- `QueryG ctx` must not be part of the value consumed by `ctx_sel`.
- `QueryG` may still be used by transfer functions that model Goblint
  `man.global`, but that is separate from context selection.
- Information that should influence context must be present in
  `d_call`/`d_enter`. It may be a local, a global retained by the analysis, an
  argument abstraction, heap/alias information, or any other analysis-chosen
  component. If it has already been represented only by a joined `G` side slot,
  the precision is gone.

This is the crucial design rule: **context selection reads a pre-loss routing
state; global side slots are for published flow-insensitive information.**

---

## 6. Re-evaluating `fctx`

Under the current model, `fctx` fails because both call sites read `G` through
the same merged side-store information:

```text
G := 0; f(); G := 1; f()
caller read of G = SZero join SPos = SNonNeg
```

With a Goblint-style `D/G/C` model, the witness changes:

- The sign of `G` must remain available in the routing state at the two call
  sites.
- `ctx_sel` reads that sign before it is represented only by the joined side
  store.
- The first call selects `GZero`; the second selects `GPos`.
- Publication to `G` slots happens after, or independently of, context
  selection.

So the old negative result becomes conditional:

- It still refutes the current side-slot-based design.
- It does **not** refute Goblint-style call-only context selection, because that
  model supplies a different state to `context`.

The revised witness should be phrased as:

```text
If G is represented only as a flow-insensitive side global before ctx_sel,
ENTER_MONO fails. If the sign of G remains available in the routing state at the
call, call-only ctx_sel can separate the two calls without normal-edge context
updates.
```

---

## 7. Smallest formal change

The smallest formal change that represents Goblint's `D/G/C` split is **not** a
full per-domain refactor. It is a boundary change:

1. Distinguish the state used for context selection from the state used for
   global reads.
2. State `ctx_sel` over a routing value queried from `Inl (cc,ctx)`.
3. Keep `G` as `Inr g` side slots for published global information.
4. Add an explicit condition saying what information remains available to
   routing at calls and when publication to `G` occurs.

In current types, that can be approximated by reusing `'a abs_state` for both
`D` and `G` payloads but separating the reads:

```text
R_read sigma (cc,ctx) = sigma (Inl (cc,ctx))
G_read sigma ctx      = glob_env_cmp gcmp sigma ctx
ctx_sel cc ctx        consumes R_read after enter/prep
transfer reads        may consume R_read joined with selected G_read
```

This is less pure than Goblint's actual per-domain `D.t`/`G.t`, but it captures
the missing information-hiding boundary: context selection cannot depend on the
joined side-store value.

Design score: 8/10. It hides the key decision at the right boundary (`ctx_sel`
gets `D`), preserves the existing solver shape, and avoids the non-Goblint
`step_ctx` detour. The remaining complexity is the uniform `'a abs_state`
payload; a 10/10 design would eventually separate local and global domains in
the types.

---

## 8. Updated migration plan

1. Mark `step_ctx` / intra-edge context updates as a non-primary fallback.
2. Refactor `Context_Domain.thy` conceptually so `ctx_sel` consumes the routing
   state, not `side_env_cmp`.
3. Add two read combinators in the design:
   `R_read` for context selection and `G_read` for published globals.
4. Restate `ENTER_MONO`/`ENTER_COMPAT` over `R_read`:

   ```text
   s in gamma (enter_d cc (R_read sigma (cc,ctx)))
   ==> cmp (entdg s) (ctx_sel cc ctx (enter_d cc (R_read sigma (cc,ctx))))
   ```

5. Keep `CMP_SOUND`/return-read obligations over the appropriate global
   compatibility read, because return combination still needs published global
   soundness.
6. Before changing the transfer layer, audit Goblint's call protocol:
   when exactly is `context()` invoked, what `D` value does it receive, and which
   analysis invariants guarantee that routing-relevant information is still
   available?
7. Rework the `fctx` witness only after that audit. The witness should model the
   discovered invariant, not hard-code "globals remain in `D`" unless Goblint
   relies on that invariant.
8. Only if this fails, revisit `step_ctx` as a separate analysis design, with a
   clear statement that it is not Goblint's mechanism.

---

## 9. Recommendation

Adopt the `D/G/C` boundary first.

The core abstraction should be: **context is selected from a routing state that
has not yet lost the context-relevant information; global side slots are separate
publication targets.** This matches the upstream interface shape without
overfitting to Base's current treatment of globals.

Do not pursue normal-edge context updates as the default A route. They solve a
symptom by moving context everywhere. Goblint solves the cause by passing a
richer `D` state to the call-site context selector.

See also: `ROUTE_A7_DECISION_A_vs_C.md`,
`ROUTE_A_SWITCHING_COMBINE_MIGRATION.md`, `GLOBAL_CONTEXT_REDESIGN.md`.
