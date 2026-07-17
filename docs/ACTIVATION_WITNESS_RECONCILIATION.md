# Activation witness reconciliation

Status: ANALYSIS (pre-implementation). No `.thy` changed or restored. Supersedes the
central claim of `SOURCE_ACTIVATION_BRIDGE_DESIGN.md` (which asserted node-7 vacuity —
now refuted; see item 1).

Scope: decide the canonical witness architecture for the source -> activation-indexed
bridge, given that the consolidation deleted the `twf`/`twfr` from-node calculus that the
earlier `WITNESS_CALCULUS_REPAIR.md` had introduced specifically to represent
recursive/repeated-call returns.

---

## 1. Is `cfg_collect_ctx_act` empty at the second `twice` return? (mechanical)

**No. Proved in Isabelle (I/R REPL, session `Voblint_Formalization`).**

- `w5`: `trace_witness_act ivl_enterc ivl_combc bot twice_cfg cinit_stores 5 bot [...]`
  — node 5 (first return) inhabited.
- `node7_nonempty`:
  `cfg_collect_ctx_act ivl_enterc ivl_combc bot twice_cfg cinit_stores 7 bot \<noteq> {}`
  — node 7 (second return) inhabited, with the genuine value `y = 20`.

The earlier "provably vacuous at node 7" reasoning was **wrong**. It assumed the callee
`rho` for `combine(6,3,7)` had to be an `enter`-from-6 trace headed by the program-start
store. In fact `rho` can be an independent **re-rooted whole-program run** headed by the
callee entry store: with root `e10 = (\<lambda>_.0)(''p'':=10)` (which lies in `cinit_stores`
because all globals are 0), the run `4 ->(call1) ...-> 5 -> 6 ->(call2) 0..3` reaches node 3
with head `e10`, context `ivl_enterc bot e10 = ctx_call2`, and exit `#ret = 20`. `combine`
then fires (`call_enter_store twice_cfg 6 (last tau) e10` holds because
`e10 = bind_formals [''p''] [10] (enter_state (last tau))`), landing `y = 20` at node 7.

**Refined deficiency.** `cfg_collect_ctx_act` is non-empty and sound
(`cfg_collect_ctx_act \<subseteq> cfg_collect`), but at nested returns it is inhabited **only**
via re-rooted runs, never via the source execution's own sub-activation. The obstruction is
`trace_witness_act.combine`'s premise `call_enter_store g cl (last tau) (hd rho)`, which pins
`hd rho` to the callee entry store; the source run's second callee is entered from the
caller continuation, so its trace is headed by the program-start store, not the entry store.
Hence **source-run induction into `cfg_collect_ctx_act` is non-compositional** — you cannot
map a source activation homomorphically to the required `rho`; you must synthesise a fresh
re-rooted run. For genuine (unbounded-depth) recursion the re-rooting cannot reconstruct the
call stack, so there the slot is expected to be genuinely empty — consistent with
`WITNESS_CALCULUS_REPAIR.md`'s `rdiv` observation. (`twice` has two flat, non-recursive
calls, so re-rooting succeeds there. The recursive case is not yet mechanically settled.)

## 2. Minimal `twf`/`twfr` definitions, imports, assumptions

Recovered from `Activation_Witness_From.thy` (deleted commit `129e0b15`), imports were
`Seeded_Activation_Sound Seeded_Activation_Reach` (both deleted).

`twf enterc combc g w wc v ctx tr` — from-node witness (starts at node `w`, ctx `wc`,
arbitrary head store):

```
start:   twf enterc combc g v ctx v ctx [s]
intra:   (u,a,v) in edges, ~is_enter a, twf ...w wc u kc tr, edge_step a (last tr)=Some s'
             ==> twf ...w wc v kc (tr@[s'])
enter:   (u,EA_Enter xs es,v) in edges, twf ...w wc u kc tau
             ==> twf ...w wc v (enterc kc (last tau)) (tau @ [enter_state (last tau)])
combine: (cl,ex,v,dst) in combines, (cl,EA_Enter xs es,fe) in edges,
         twf ...w wc cl kc1 tau,
         twf ...fe (enterc kc1 (last tau)) ex (enterc kc1 (last tau)) rho,
         hd rho = enter_state (last tau)
             ==> twf ...w wc v (combc kc1 (enterc kc1 (last tau))) (tau @ tl rho @ [<last tau|last rho>])
```

`twfr` = `start`/`intra`/`combine` only (drops `enter`); "every terminating / recursive-return
run is a `twfr`".

`twf_sound` assumptions: `sound_domain` reader `sg :: pp x 'c + 'g => 'a abs_state`, plus
`EDGE`, `SEED_G`, `COMB` (the exact three semantic obligations), and the conditional premise
`hd tr \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk>`; conclusion `last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>`.
There is **no** `ENTRY_G` — the start-store hypothesis replaces it. Proof: induction on
`twf.induct`, discharging each rule off the three obligations.

`twfr_sound_seeded` (the heavy variant) additionally assumes `part_post_solution` of
`side_cfg_T_eff_cmp_seed`, `cover_seed`, and dependency-reachability premises, inside
`context sound_transfer`.

## 3. Dependency of the lightweight core on deleted infrastructure

- `twf`, `twf_nonempty`, `twf_combine_reuses_callee_suffix`, `twfr`, `twfr_nonempty`,
  `twf_sound`: depend only on **live** infrastructure — CFG (`edges`, `combines`,
  `edge_step`, `is_enter_action`, `enter_state`, `<_|_>` = `combine_states`) and
  `Abstract_Domain` (`sound_domain`, `abs_state`, `gamma_state`). The file's stated imports
  (`Seeded_Activation_*`) are inherited, not used by these items.
- `twfr_sound_seeded`: depends on the **deleted** seeded cluster
  (`part_post_solution`, `side_cfg_T_eff_cmp_seed`, `cover_seed`, `seeded_activation_seed`,
  `seeded_activation_edge`, `enter_state_in_cover_seed`). Not resurrectable without that
  cluster, and its full-store conclusion is the one `WITNESS_CALCULUS_REPAIR.md` flags as
  RHS-vacuous. It should stay deleted.

So the lightweight core is recoverable against the current tree by re-homing it on
`Abstract_Domain` + `CFG_Collect_Activation`; the heavy seeded theorem is not.

## 4. Constructor-by-constructor comparison

| capability            | `trace_witness_act` (canonical)                         | `twf` / `twfr` (deleted)                                  |
| --------------------- | ------------------------------------------------------- | -------------------------------------------------------- |
| globally rooted start | `entry` (at `cfg_entry`), `proc_entry` (entry-enter)    | absent (not needed)                                      |
| arbitrary-activation start | **absent**                                         | `start` at any `(w, wc)` with any head store            |
| intra steps           | `intra`                                                 | `intra` (carries origin `w wc`)                          |
| calls (enter)         | `enter` via **`edge_step` = `bind_formals`** (faithful) | `enter` via **`enter_state (last tau)`** (formals dropped) |
| repeated calls        | `combine` needs re-rooted independent `rho`             | `combine` builds `rho` from frame entry `fe` via `start` |
| recursion             | re-rooting cannot reconstruct unbounded depth           | `start`-at-`fe` handles each frame directly              |
| returns / combine     | `combine` (rho globally reachable, contorted)           | `combine` (rho `fe`-rooted, compositional)               |
| context routing       | `enterc c s'` on the **entered** store `s'`             | `enterc kc (last tau)` on the **caller** store           |

Two orthogonal capabilities are split across the two calculi: `trace_witness_act` is
**faithful to parameter passing** but **non-compositional at nested returns**; `twf`/`twfr`
is **compositional at nested returns** but **drops formal binding** (callee starts with
locals zeroed, `xs`/`es` used only for the edge, not the store). Neither is a superset of the
other. This is why `twf`'s examples retreat to per-coordinate *global* soundness — the
dropped formals make per-local claims unavailable.

## 5. Precise deficiency in the base semantics

Not "a missing context-preserving constructor." The base issue is representational:

- A globally rooted trace headed at the program entry cannot double as an independently
  summarised callee activation, because the two roles disagree on the head store
  (`combine` wants `hd rho` = callee entry store; a globally rooted trace's head is the
  program start). The semantics *can* be inhabited at nested returns (item 1), but only by
  re-rooting, which is not a homomorphic image of a source execution.
- Consequently there is no source-run induction that lands `cfg_collect_ctx_act` membership
  compositionally, and recursion likely breaks inhabitance entirely.
- The clean generalization is a witness carrying an **origin** `(w, wc)` and an
  **admissible origin-store** condition, so a callee summary can start at its frame entry —
  *and* retaining `edge_step`/`bind_formals` at `enter`/`combine` so parameter passing stays
  faithful. This subsumes both globally rooted traces (origin = `cfg_entry`, seed condition
  = `S`) and the useful `twf`/`twfr` fragment (arbitrary origin), without the formal-dropping
  regression of `twf`.

## 6. Does a nested-entry constructor genuinely repair the base, or embed `twf.start`?

A bare "context-preserving nested-entry constructor" (my earlier `proc_entry_nested_act`)
only embeds an ad hoc `twf.start` inside the globally rooted relation. It papers over the
representational mismatch: it still cannot express a callee summary as an independent object
usable by an outer `combine` without re-rooting, and it does not give recursion a base case.
It is a patch, not a repair. The repair is to make the witness itself origin-parameterised.

## 7. A single generalized witness calculus

Proposal (shape to validate, not to adopt verbatim):

```
witness enterc combc g S  (w :: pp) (wc :: 'c)  (v :: pp) (ctx :: 'c)  (tr :: trace)
```

reading: `tr` starts at origin `(w, wc)` and reaches `(v, ctx)`, with an **admissible origin
predicate** `adm w wc (hd tr)` fixing what may seed each origin:

- global origin: `w = cfg_entry g`, `adm` = `hd tr \<in> S`, `wc = seedc`  (recovers `entry`);
- frame origin:  `w` a `proc_entry_pps` node, `adm` = "entry store bound from a covered
  caller", derived via `bind_formals`  (recovers a faithful callee start);
- `intra`, `enter` (via `edge_step`/`bind_formals`, faithful), and `combine` (callee taken as
  a **frame-origin** sub-witness, `hd rho` = the bound entry store) as usual.

`cfg_collect_ctx_act` becomes the `w = cfg_entry`, `adm = (_ \<in> S)` instance; the `twf`/`twfr`
role becomes the frame-origin instance; forgetting `('c, wc, ctx)` recovers the monovariant
`trace_witness`. Soundness is one induction over the generalized rule set discharging
`ENTRY_G` (global origin), `EDGE`, `SEED_G`, `COMB`; the frame-origin base case uses the
`SEED_G` obligation on the caller store (as `twf_sound` already does), so the existing
`Activation_Backbone` / `DG_Ctx_Activation` obligation interface is reused unchanged.

Caveat: this must keep `bind_formals` at `enter`/`combine` (unlike `twf`) so it does not
inherit the formal-dropping regression. If a single readable inductive cannot hold both the
global and frame origins without becoming opaque, fall back to option (c) below rather than
shipping an unreadable definition.

## 8. Can the generalized base support everything without parallel semantics?

Targets and feasibility:

- ordinary globally rooted collecting: yes (global-origin instance = current
  `trace_witness` / `cfg_collect`).
- activation-indexed collecting: yes (global-origin, `'c`-indexed = current
  `cfg_collect_ctx_act`).
- nested / recursive return composition: yes (frame-origin `combine`, the `twf` capability),
  now with faithful parameters.
- source-run induction: yes — the source's second activation maps to a frame-origin
  sub-witness (its natural entry store), not a re-rooted run.
- forgetting contexts to monovariant: yes (drop `'c`, `wc`, `ctx`).
- generic EDGE / SEED_G / COMB proof: yes — same obligation interface; the global-origin
  case additionally needs `ENTRY_G`.

The one genuine risk is readability (item 7 caveat): two distinct origins in one inductive.

## 9. Does `twf_sound` use the current EDGE / SEED_G / COMB interface?

**Yes.** `twf_sound`'s three obligations are, verbatim up to naming, `Activation_Backbone`'s
`EDGE`, `SEED_G`, `COMB`. It omits `ENTRY_G` (replaced by the start-store hypothesis).
`DG_Ctx_Activation` already discharges all four for the interval solution, so the generalized
calculus's soundness reuses those discharges directly.

## 10. Full-store vs per-coordinate conclusion

`WITNESS_CALCULUS_REPAIR.md` argues the full-store conclusion
`last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>` is vacuous once globals are present, because
`gamma_state` ranges over infinitely many `G`-names and any unmentioned global at `\<bottom>`
empties the concretization. For `twice` (no real globals) this was **not** conclusively
settled here — the check is `eval`-heavy (`gamma` over `int` is not enumerable) and the slot
reduces to a solver computation I did not force to a normal form. Recommendation for the
bridge conclusion:

- **per-coordinate / read** soundness (`last tr qv \<in> gamma (sg (Inl (v,ctx)) qv)`) as the
  primary end statement — robust to the global-at-bottom emptiness and matching
  `Trace_Analysis_Sound.reaching_global_read_sound`;
- **full-store** soundness only under an explicit finitely-supported / top-outside-support
  assumption on `sg`, offered as a corollary where that holds.

## Recommendation (one canonical architecture)

**Option (a): generalize the fundamental trace semantics to an origin-parameterised witness
that subsumes both globally rooted collecting and the `twf`/`twfr` frame-origin fragment,
keeping `bind_formals` faithful; migrate the surviving activation proofs onto it.**

Rationale: it removes the parallel-calculus smell the user flagged, gives source-run
induction a compositional target and recursion a base case, reuses the existing
EDGE/SEED_G/COMB discharge, and — unlike restoring `twf` verbatim — does not reintroduce the
formal-dropping regression. Restore `twf`/`twfr` **only as reference/proof material**
(the `twf_sound` induction transfers almost directly to the frame-origin case), not as a
standing second semantics.

Fallbacks, in order:
- (b) if (a)'s single inductive proves unreadable, keep `trace_witness_act` as-is and add a
  frame-origin **companion** relation with an explicit adapter lemma to `cfg_collect_ctx_act`
  — two relations, but one obligation interface and a proven bridge, roles formally distinct.
- (c) do **not** merely add `proc_entry_nested_act` to `trace_witness_act` (item 6: patch,
  not repair) unless (a) and (b) are both rejected.

Do **not** restore lightweight `twf`/`twfr` as a permanent parallel semantics; its
formal-dropping `enter` makes it strictly weaker than the base on parameter passing.

## Inventory

- **Deleted the reusable material:** commit `129e0b15`
  (`refactor(activation): delete plain-abs_state activation family`) removed
  `Activation_Witness_From.thy` (`twf`/`twfr`/`twf_sound`) and `Seeded_Activation_Reach.thy`;
  the probe/example cluster went in `8dbe4be4`; `WITNESS_CALCULUS_REPAIR.md` was removed with
  the cluster. All three recovered to the scratchpad.
- **Recover as guidance / migrate:** `twf` + `twfr` inductives, `twf_nonempty` /
  `twfr_nonempty`, `twf_sound` (its EDGE/SEED_G/COMB induction is the frame-origin base case),
  and the reuse lemma `twf_combine_reuses_callee_suffix`.
- **Keep deleted:** `twfr_sound_seeded` and the seeded cluster (`cover_seed`,
  `Seeded_Activation_*`, `side_cfg_T_eff_cmp_seed` seed path); the RHS-vacuous full-store
  conclusion; the plain-`abs_state` probe examples.
- **Expected proof / dependency impact of repairing the base:** touches
  `CFG_Collect_Trace` / `CFG_Collect_Activation` (the inductive gains an origin parameter;
  each existing `.induct` proof gains an origin case) and their forgetful lemmas
  (`trace_witness_act_imp_trace_witness`, `cfg_collect_ctx_act_le_collect`). `cfg_collect` and
  the solver interface are untouched.
- **`Activation_Backbone` impact:** `activation_trace_sound` / `activation_collect_sound`
  become the global-origin instance of the generalized soundness; the obligation interface
  (ENTRY_G/EDGE/SEED_G/COMB) is unchanged, so `DG_Ctx_Activation` and
  `Example_Interval_DG_Ctx_Collect` need at most a re-statement against the instance, not new
  obligations. A frame-origin soundness corollary (the `twf_sound` shape) is added beside it.
```
