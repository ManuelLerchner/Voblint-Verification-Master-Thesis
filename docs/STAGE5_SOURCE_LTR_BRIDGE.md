# Stage 5 design — source execution to activation-local traces

Status: **design only**. No `.thy` changed by this document. Deliverable requested before
implementation: the representation invariant and the theorem dependency graph.

## Goal

Connect recursive source execution to the canonical activation-local collecting semantics:

```text
psteps (source)  ->  valid_ltr  ->  cfg_collect_ctx_act  ->  activation_collect_sound
```

so that every reachable source store is bounded by the abstract analysis at the **stable
activation context** of the activation that produced it.

## Key design decision: bridge through `cstep`, not raw `pstep`

The source semantics `pstep` (`IMP2_Proc`) runs configurations `com x store x frame list` with
`frame = Frame store (vname option)`. Its call/return rules already match the CFG combine
primitives exactly:

- `Call`: `(Call dst p as, s, frs) -> (..., bind_formals fs vals (enter_state s), Frame s dst # frs)`
  — the callee store is `edge_step (EA_Enter ...) s`, and `Frame s dst` freezes the caller store.
- `RestoreStep`: `(Restore, s, Frame fr dst # frs) -> (SKIP, combine_assign dst (s ret_var) <fr|s>, frs)`
  — the result store is `combine_collect dst fr s`.

But `pstep` is coarse: one source step may compile to several CFG edges (scope entry, `Seq`
navigation, nop glue). The project **already** proves a simulation to the CFG-located small step
`cstep` (`Located_Exec`), which advances **one CFG edge at a time**:

```text
cstep.Intra   (u,s,stk) -> (v,s',stk)                         non-enter edge, edge_step a s = Some s'
cstep.Call    (call,s,stk) -> (en,s',(call,ret,s)#stk)        enter edge + combine triple
cstep.Return  (ex,t,(call,ret,s)#stk) -> (ret,combine_collect dst s t,stk)
```

with `cconf = pp x store x cframe list`, `cframe = pp x pp x store = (call, ret, saved_store)`.

Reused, already proved:

- `concrete_program_initial_match` (`Located_Exec`): initial source config matches the initial
  `cconf` at `cfg_entry`.
- `concrete_program_step_match` (`Control_Simulation`): `pstep Pi src src'` gives
  `star (cstep (compile_prog ...)) cf cf'` with `concrete_program_match` preserved.
- `located_sound` / `cstep_preserves_located_sound` (`Located_Reaches`): the invariant template we
  retarget from `cfg_collect` to `valid_ltr`.

**Consequence.** `cstep` updates map 1:1 onto `valid_ltr` constructors, so we never face "one
source step, several incompatible `ltr` updates": a source step is a *sequence* of `cstep`s, each
extending the same accumulated trace. The `cframe` stack is precisely the runtime caller chain.

## The representation invariant

The `cconf` retains, per suspended frame, only `(call, ret, saved_store)` — not the caller's path
history. The `ltr` carries the full caller activations. So the correspondence is a **refinement
relation** with the `ltr` as the richer object; the `cconf` is its forgetful projection. Existence
(not uniqueness) of the richer witness is all we need.

```text
stack_repr :: cfg => store set => cframe list => ltr => bool
  stack_repr g S []                     t = (caller_of t = None)
  stack_repr g S ((call,ret,saved)#stk) t =
      (EX c. caller_of t = Some c
             AND sink_node c = call
             AND sink_store c = saved
             AND (EX ex dst. (call, ex, ret, dst) : combines g)   -- a pending return triple exists
             AND stack_repr g S stk c)

ltr_repr :: cfg => store set => cconf => ltr => bool
  ltr_repr g S (v,s,stk) t =
      (t : valid_ltr g S
       AND sink_node t = v
       AND sink_store t = s
       AND stack_repr g S stk t)

located_ltr g S cf = (EX t. ltr_repr g S cf t)
```

`stack_repr` walks `caller_of` in lockstep with the `cframe` list — the invariant is deliberately
**stack-indexed**, as anticipated. It is the `valid_ltr` analogue of `stack_sound`, replacing
"`saved : cfg_collect g S call`" with "there is a caller activation `c` whose sink is `(call,
saved)`."

### The requested five-point correspondence, at every execution state

For the current source config matched to `cf = (v,s,stk)` with witness `t` (`ltr_repr g S cf t`):

1. **which `ltr` is the current activation** — `t` itself (its innermost constructor / path).
2. **suspended source frames ↔ caller chain** — `frames_match sites frs stk` (existing) composed
   with `stack_repr g S stk t`: the `i`-th `cframe` is the `i`-th `caller_of` iterate of `t`; the
   whole stack is an initial segment of `callers t`.
3. **source store ↔ `sink_store`** — `sink_store t = s` (and `s = t`-store via
   `concrete_program_match`).
4. **source control point ↔ `sink_node`** — `sink_node t = v`, and `control_at ... residual v`
   (existing) ties `v` to the residual command.
5. **call entry stores ↔ `entry_store`** — for each caller `c` in the chain, its callee was created
   by `valid_ltr.call` with head `(fe, se)`, `se = edge_step (EA_Enter ...) (sink_store c)`; hence
   `entry_store (callee-of c) = se = bind_formals ... (enter_state saved)`, matching the source
   `Call` rule's `callee` store. (This is `callee_entry_invariant`, reused.)

## Step correspondence (each `cstep` preserves `ltr_repr`)

| `cstep` | `ltr` update | discharge |
| --- | --- | --- |
| `Intra (u,s,stk)->(v,s',stk)` | `t' = extend t (v,s')` | `valid_ltr.intra`; `sink_*_extend`, `caller_of_extend` keep `stack_repr`; `key_extend_nonempty` keeps context |
| `Call (call,s,stk)->(en,s',(call,ret,s)#stk)` | `t' = Call t [(en,s')]` | `valid_ltr.call` (enter edge + combine triple both present); `caller_of t' = Some t`, `sink t' = (en,s')`, new frame matches (`sink_node t = call`, `sink_store t = s`) |
| `Return (ex,t0,(call,ret,s)#stk)->(ret,r,stk)` | `t' = Resume c t0 (path c @ [(ret,r)])`, `c = caller_of t0` | `valid_ltr.ret` with `caller = caller_of t0 = c` (from `stack_repr`), triple `(call,ex,ret,dst)`; `r = combine_collect dst s (sink_store t0)` equals the `cstep` store; `caller_of t' = caller_of c` pops the frame |

**Return is load-bearing and it closes:** `stack_repr` supplies `caller_of t0 = Some c` with
`sink_node c = call`, `sink_store c = s` — exactly the caller the `cstep.Return` pops. So the
source stack and `caller_of` identify the *same* caller; no reconstruction, no re-rooting.

## Theorem dependency graph

```text
REUSED (no change)
  CFG_Local_Trace:      valid_ltr.{init,intra,call,ret}, caller_of, callers_*, sink_*_extend,
                        key_extend_nonempty, callee_entry_invariant,
                        cfg_collect_ctx_act(_def), cfg_collect_ctx_act_le_collect
  Located_Exec:         cstep.{Intra,Call,Return}, concrete_program_(initial_)match
  Control_Simulation:   concrete_program_step_match           (pstep -> star cstep)
  Located_Reaches:      located_sound pattern (template only)
  Activation_Backbone:  activation_collect_sound              (four obligations -> subseteq gamma)

NEW  (CFG session: e.g. Compiler/Located_LTR.thy, imports Located_Reaches + CFG_Local_Trace)
  def stack_repr, ltr_repr, located_ltr
  L1 located_ltr_entry:            s:S ==> located_ltr g S (cfg_entry g, s, [])
        <- valid_ltr.init, sink_*_def, stack_repr.simps
  L2 cstep_preserves_ltr_repr:     ltr_repr g S cf t ==> cstep g cf cf' ==> EX t'. ltr_repr g S cf' t'
        <- step-correspondence table (valid_ltr.{intra,call,ret}, caller_of/callers lemmas,
           combine_collect_def)
  L3 csteps_preserve_located_ltr:  located_ltr g S cf ==> star (cstep g) cf cf' ==> located_ltr g S cf'
        <- L2, star.induct     (mirrors csteps_preserve_located_sound)

NEW  (CFG session: T1,T2 are domain-free; e.g. Compiler/Source_LTR_Bridge.thy)
  T1 source_run_has_ltr:
        wf_compile_input Pi ps main ==> source_com main ==> s0 : S ==>
        psteps Pi (main,s0,[]) (residual,s,frs) ==>
        EX v stk t. concrete_program_match Pi ps main (residual,s,frs) (v,s,stk)
                    AND ltr_repr (compile_prog Pi ps main) S (v,s,stk) t
        <- concrete_program_initial_match, concrete_program_step_match, L1, L3, star.induct
  T2 source_store_in_cfg_collect_ctx_act:
        (T1 hyps) ==> s : cfg_collect_ctx_act enterc seedc (compile_prog ...) S v (key enterc seedc t)
        <- T1, cfg_collect_ctx_act_def

NEW  (Analysis/Formalization session: final abstract step; e.g. Source_Activation_Sound.thy)
  T3 source_activation_sound:
        (T1 hyps) + ENTRY_G + EDGE + SEED_G + COMB ==>
        s : gamma (sg (Inl (v, key enterc seedc t)))
        <- T2, activation_collect_sound

SECONDARY (CFG session, domain-free; after T1..T3)
  def flatten :: ltr => trace           (whole-program store sequence)
  F1 valid_ltr t ==> <flatten t is a valid whole execution>   (target: trace_witness OR cfg_collect member)
  F2 sink preserved: last (flatten t) = sink_store t          (and node bookkeeping)
        <- valid_ltr.induct
  NOTE: flatten forgets caller structure; it is NOT used in the return proof (L2/T1).
```

## Stop-condition analysis (none fire)

- *Frozen caller not identifiable* — `cframe` stores `(call, saved)`; combined with `stack_repr`'s
  caller activation `c` (`sink = (call, saved)`), the frozen caller is fully identified. The
  caller's path lives in the `ltr` witness, accumulated during the run, not demanded from the
  `cconf`. **No stop.**
- *Return cannot reconstruct `caller_of`* — `caller_of t0 = Some c` is supplied by `stack_repr` and
  is exactly the popped `cframe`. **No stop.**
- *One source step, incompatible `ltr` updates* — dissolved by routing through `cstep`: a source
  step is `star (cstep)`, each `cstep` extends the same trace; witnesses are non-unique but
  compatible (existential invariant). **No stop.**
- *Recursion needs a source-semantics change or a stack-indexed invariant* — no source change; the
  invariant **is** stack-indexed (`stack_repr` on `caller_of`), which is the expected shape, not a
  blocker. Recursion is a deeper `cframe` stack = deeper caller chain. **No stop.**

## Order of work

1. `Located_LTR`: `stack_repr` / `ltr_repr` / `located_ltr`, L1, L2 (Return case first — it is the
   load-bearing one), L3. Green `Voblint_CFG`.
2. `Source_LTR_Bridge`: T1, T2. Green `Voblint_CFG`.
3. `Source_Activation_Sound`: T3. Green `Voblint_Formalization`.
4. `flatten` + F1/F2 as a separate, lower-priority theory. **Not** a substitute for the
   constructive bridge — it forgets exactly the caller structure the return proof needs.

No DG, solver, generator, or context-key changes. `cstep`, `concrete_program_match`, and the
compiler are consumed as-is.
