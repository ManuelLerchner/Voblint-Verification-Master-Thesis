# Source -> activation-indexed collecting bridge: design note

Status: DESIGN (pre-implementation). No code changed yet.

Goal: from a concrete source run of a compiled procedural program, derive
membership in the activation-indexed collecting semantics
`cfg_collect_ctx_act` at the right activation context, then compose with
`twice_ctx_collect_ctx_act_sound` for an end-to-end source-level
context-sensitive soundness theorem.

---

## 0. Headline finding (decisive, blocks the naive plan)

`cfg_collect_ctx_act` as currently defined is **uninhabited at every
call-return node except returns of calls whose call site is `cfg_entry g`.**
The `trace_witness_act` `combine` constructor requires an *independent* callee
sub-trace `rho` whose head store `hd rho` is the callee **entry** store
(forced by `call_enter_store g cl (last tau) (hd rho)`, which pins
`hd rho = bind_formals ... (enter_state (last tau))`). The only fresh-start
constructors are:

* `entry` — fresh `[s]` at `cfg_entry g` only;
* `proc_entry` — fresh `[s]` at the target of an enter edge **from `cfg_entry g`**
  (`(cfg_entry g, EA_Enter xs es, v) \<in> edges g`).

A callee entered from any *non-entry* call node can only be reached by the
`enter` constructor, which carries the caller prefix: its trace head is the
program-start store, not the callee entry store, and its threaded context is
`enterc c s'` (routed on the entry store) rather than `enterc c (hd rho)`.
Neither matches the `combine` premise. So `combine` never fires for such a
call, and the return-node slot stays empty.

### Instantiation on `twice` (nodes from `twice_edges` / `twice_combines`)

```
cfg_entry = 4, cfg_exit = 7
edges:    (4, EA_Enter [p] [N 3],  0)   -- call 1, site = cfg_entry
          (0,Nop,1)(1,Nop,2)(2,Assign #ret (p+p),3)   -- callee body 0..3
          (5,Nop,6)
          (6, EA_Enter [p] [N 10], 0)   -- call 2, site = node 6 (NOT cfg_entry)
combines: (4,3,5,Some x)   (6,3,7,Some y)
```

* Return **node 5** (call 1): inhabited. `proc_entry` seeds `[es3]` at node 0
  (edge from `cfg_entry = 4`), context `enterc bot es3`; intra to node 3;
  `combine (4,3,5,x)` fires because `c1 = bot`, `hd rho = es3`,
  `call_enter_store 4 s0 es3` holds. Matches `covered_ret5 = (5, bot)`.
* Return **node 7** (call 2 = `cfg_exit`): **empty**. `combine (6,3,7,y)` needs
  `rho` at node 3 with `hd rho = es10` (`p = 10`) and context `enterc c1 es10`,
  `c1 = ` context at node 6. No constructor produces a node-0 witness with head
  `p = 10`: `proc_entry` is hardwired to the `N 3` enter edge (heads have
  `p = 3`), and `enter`-from-6 gives head = program start with context
  `enterc (ctx@6) es10 \<noteq> enterc c1 (program-start)`. So the slot is empty.

Consequence: `twice_ctx_collect_ctx_act_sound` at `v = 7` reads
`{} \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (7, ctx))\<rbrakk>` — **vacuous at the program
exit**, exactly where the interprocedural return matters. The "canonical
context-sensitive result" currently asserts nothing at second/nested returns.

> Verify first: `cfg_collect_ctx_act` is an inductive set, **not** executable in
> this form, so `eval` cannot decide emptiness. Prove a focused
> constructor-inversion lemma:
> `trace_witness_act ivl_enterc ivl_combc bot twice_cfg cinit_stores 7 ctx tr \<Longrightarrow> False`
> (node 7 empty under the current semantics), and exhibit a witness at node 5
> (inhabited). The structural argument above (value mismatch `p=3` vs `p=10`) is
> the proof skeleton.

### Why no enriched simulation alone can fix this

A simulation lands the concrete return store into the target slot. If the
target slot is *empty*, no simulation can succeed — the obstruction is in the
**semantics**, not the bridge. Therefore a framework change to the collecting
semantics is a genuine prerequisite, not proof-avoidance. This is precisely the
recursion/repeated-call risk flagged in the task brief.

---

## 1. Required framework change (minimal)

Add a sound fresh-start constructor at **arbitrary** procedure entries. The
fresh callee seed must be **context-indexed** — justified by a caller witness in
the *same* activation context, not drawn from the monovariant `cfg_collect g S cl`
(which would let a store reachable under context A be seeded under any context B,
replacing vacuity with cross-context pollution). Vocabulary for the enter target
already exists: `proc_entry_pps g` (CFG_Collect_Trace).

Activation `trace_witness_act` gains (context threaded from the caller witness,
`hd = s`, so `combine` accepts it with `c = c1`):

```
proc_entry_nested_act:
  trace_witness_act enterc combc seedc g S cl c tau
  \<Longrightarrow> (cl, EA_Enter xs es, pe) \<in> edges g
  \<Longrightarrow> edge_step (EA_Enter xs es) (last tau) = Some s
  \<Longrightarrow> trace_witness_act enterc combc seedc g S pe (enterc c s) [s]
```

The caller premise pins the *exact* caller context `c`, the matching caller
store `last tau`, and the entry store `s = edge_step (EA_Enter xs es) (last tau)`
— so `s` is only ever seeded under `enterc c s` for the caller that actually
reaches it. No free context. This is essentially the `enter` constructor with a
**fresh** singleton `[s]` in place of the prefix-carrying `tau @ [s]`, which is
exactly what `combine`'s `rho` needs (`hd rho = s`).

Monovariant `trace_witness` gains the analogous caller-witness-derived rule
(no external `cfg_collect` consultation):

```
proc_entry_nested:
  trace_witness g S cl tau
  \<Longrightarrow> (cl, EA_Enter xs es, pe) \<in> edges g
  \<Longrightarrow> edge_step (EA_Enter xs es) (last tau) = Some s
  \<Longrightarrow> trace_witness g S pe [s]
```

Soundness (`trace_witness_last_in_cfg_collect` new case) is short:
`last tau \<in> cfg_collect g S cl` (IH) and `edge_step` give
`s \<in> edge_collect (EA_Enter xs es) (cfg_collect g S cl) \<subseteq> cfg_collect g S pe`
via `cfg_collect_edge`. The existing `cfg_entry`-only `proc_entry` is subsumed
(take `cl = cfg_entry g`, `tau` an `entry` witness).

Justification vs. an adapter: the target set is empty without this; an adapter
theorem cannot manufacture members of an empty set. The change is a localized
*widening* of the existing `proc_entry` rule, not a parallel semantics, and it
is context-faithful by construction.

Downstream to re-check after the widen: `trace_witness_ext_edges`,
`trace_witness_mono_initial`, `cfg_collect_ctx_act_le_collect`,
`trace_witness_act_imp_trace_witness`, and any `trace_witness.induct` /
`trace_witness_act.induct` proof (each gains one case).

---

## 2. The bridge (after the widen)

Reuse the existing source -> CFG stack-machine simulation **unchanged**:
`compiled_source_simulation` locale / `source_steps_match` /
`concrete_program_step_match` produce `star (cstep g)` from `psteps`, with
`cstep` (Located_Exec) carrying the runtime frame stack
`stk :: (call, ret, s_caller) list`.

Add a **context-indexed located soundness** invariant over `cstep`, mirroring
the monovariant `located_sound` (Located_Reaches), but indexing slots by
activation context and carrying an auxiliary context stack `cstk` parallel to
`stk`:

```
stack_act_sound g S (zip cstk stk):
  each frame (cl_i, ret_i, sc_i) paired with (c1_i, es_i) satisfies
    sc_i  \<in> cfg_collect_act ... cl_i c1_i               (caller store sound)
    call_enter_store g cl_i sc_i es_i                    (entry store recorded)
    (tail sound recursively)
located_act_sound g S (v, s, stk) ctx cstk \<equiv>
  s \<in> cfg_collect_act ... v ctx  \<and>  stack_act_sound ...
  \<and>  ctx recorded as enterc (top c1) (top es) when stk nonempty
```

Here `cfg_collect_act` is the set-level activation collecting (least fixpoint
over `(pp \<times> 'c)` with the four rules ENTRY / EDGE / SEED / COMB — the exact
set analogue of the four `trace_witness_act` constructors, including
`proc_entry_nested_act`). `cstk` is auxiliary (ours to shape); it stores the
caller context `c1` and the entry store `es` per open call, which `cstep`
frames do not.

Preservation by `cstep`:

* **Intra**: EDGE rule, `ctx` unchanged.
* **Call** (`(cl, EA_Enter, en)`, push `(cl, ret, s)`, store -> `s'`): SEED rule
  gives `s' \<in> slot(en, enterc ctx s')`; push `(ctx, s')` on `cstk`; new
  `ctx' = enterc ctx s'`; `call_enter_store g cl s s'` holds by `edge_step`.
* **Return** (pop, exit `ex`, store `t` -> `r`): COMB rule with `c1 = ` popped
  caller ctx, caller store `sc \<in> slot(cl, c1)` (from stack soundness),
  `t \<in> slot(ex, ctx)`, `ctx = enterc c1 es` and `call_enter_store g cl sc es`
  (both recorded on `cstk` at the matching Call). Yields
  `r \<in> slot(ret, combc c1 (enterc c1 es))`.

Then: `psteps -> star (cstep g) -> located_act_sound` at the final config gives
`t \<in> cfg_collect_act ... v ctx`.

Compose with the analyzer soundness. Two ways to close:

* **A (recommended)**: prove a generic `activation_set_collect_sound` —
  the four obligations (ENTRY_G / EDGE / SEED_G / COMB, already the premises of
  `activation_collect_sound` in `Activation_Backbone`) imply
  `cfg_collect_act ... v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>` by
  fixpoint induction. Instantiate at the *same* `ivl_ctx_sg` obligations already
  discharged in `Example_Interval_DG_Ctx_Collect`. Avoids proving
  `cfg_collect_act = cfg_collect_ctx_act`.
* **B**: prove `cfg_collect_act ... v ctx \<subseteq> cfg_collect_ctx_act ... v ctx`
  and reuse `twice_ctx_collect_ctx_act_sound` verbatim. Needs the set -> trace
  direction; feasible only *after* `proc_entry_nested_act` (the combine case
  builds `rho` via it). More work than A; keep as optional.

The generic backbone (`activation_trace_sound` / `activation_collect_sound`) and
`DG_Ctx_Activation` are **untouched**; `activation_set_collect_sound` is a new
sibling lemma with the same obligation interface.

---

## 3. Answers to the pre-implementation checklist

* **Exact missing invariant**: a context-indexed located soundness
  (`located_act_sound`) tying the `cstep` frame stack to an activation-context
  stack, plus the semantics gap in section 0 — `cfg_collect_ctx_act` has no
  fresh-start constructor at non-entry callee entries, so it is uninhabited at
  their returns. The invariant is unprovable until the semantics is widened.
* **Does the source configuration carry enough call-stack info?** Yes. `cstep`'s
  `stk` records `(call, ret, s_caller)` per activation. The caller context and
  entry store are *not* in `stk`, but they are deterministically reconstructible
  and carried in the auxiliary `cstk` we thread alongside — no change to `cstep`
  or to the source semantics.
* **Can `enterc` be reconstructed deterministically at source call steps?** Yes.
  At a Call step the entry store is `s' = edge_step (EA_Enter xs es) s` and the
  current context is `ctx`; `enterc ctx s'` is a total function application.
* **How does combine/return recover the caller context?** Pop `cstk`: the caller
  context `c1` and entry store `es` were pushed at the matching Call; the return
  context is `combc c1 (enterc c1 es)`, and `call_enter_store g cl sc es` was
  recorded then. Deterministic.
* **Which existing simulation theorem is reused unchanged?**
  `compiled_source_simulation` / `source_steps_match` /
  `concrete_program_step_match` (source `psteps` -> CFG `star (cstep g)`), and
  the monovariant `located_sound` proof pattern as the template for
  `located_act_sound`. `control_step_simulation` is reused verbatim via the
  locale.
* **Required generic framework change (minimal, justified)**: the
  `proc_entry_nested` / `proc_entry_nested_act` constructors (section 1). Needed
  because the target slots are otherwise empty; an adapter/enriched relation
  cannot populate an empty set. It is a widening of the existing `proc_entry`,
  already anticipated by `proc_entry_pps`.

---

## 4. Staging (revised)

1. **Verify** the emptiness finding by a constructor-inversion lemma
   (`trace_witness_act ... 7 ctx tr \<Longrightarrow> False`; node 5 inhabited).
   Then check the revised rule makes the `p = 10` callee-entry witness derivable
   **and** does not make that entry store derivable under unrelated caller
   contexts. Gate the rest on all four checks.
2. Widen `trace_witness` with `proc_entry_nested` (caller-witness premise); fix
   the ~5 downstream induction proofs and soundness lemma. (CFG session.)
3. Widen `trace_witness_act` with `proc_entry_nested_act` (caller-witness
   premise, context `enterc c s`); re-close `trace_witness_act_imp_trace_witness`,
   `cfg_collect_ctx_act_le_collect`.
4. Define `cfg_collect_act` (set fixpoint) + `activation_set_collect_sound`
   (generic, four obligations). (Analysis session, sibling to
   `Activation_Backbone`.)
5. `located_act_sound` + `cstep`-preservation (one-step, then `star`). (CFG /
   Analysis boundary — place with the located-soundness infrastructure.)
6. Compose: `psteps -> cfg_collect_act -> \<lbrakk>sg\<rbrakk>`. Instantiate for
   `twice` at the discharged `ivl_ctx_sg` obligations; now non-vacuous at node 7.
7. End-to-end `twice_source_ctx_sound`: `psteps twice_pi (twice_main, s, [])
   src' \<Longrightarrow> match ... (v, t, stk) \<Longrightarrow>
   t \<in> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>`.

Do **not** route through `cfg_collect_ctx_act \<subseteq> cfg_collect` (useless
direction). Keep the monovariant source lift (`twice_source_run_sound`) intact.
