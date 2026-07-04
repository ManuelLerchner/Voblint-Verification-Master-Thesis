# D/G/C alignment analysis: is the Route A obstruction fundamental?

> **Investigation only. No theory changes.** Validates the architecture before any
> soundness-kernel change. Companion to `CONTEXT_DOMAIN_ARCHITECTURE.md` (the landed
> locale), `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` (the corrected Goblint model),
> and `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` (Route A phases / A7 obstruction).

**Verdict up front.** The A7 obstruction is **not fundamental to context-sensitivity**.
It is an artifact of a specific design choice in our formalization: context-relevant
information is *published to a per-context side slot and removed from the routing
state before `ctx_sel` can observe it* (`unit_edge_tree` + the
`inl_slot_globals_bot_ctx` invariant in the current sign instance). Goblint's
framework contract is more general: `Spec.context` receives a `D.t` produced by the
call protocol, and an analysis may keep whatever routing information it needs in
that `D.t` (locals, globals, arguments, heap, aliases, etc.). Base sometimes keeps C
globals in `D`, but "globals always remain in `D`" is **not** the architectural
invariant.

**Route A correction:** `ctx_sel` must consume the `D`/routing state produced by
`enter`, not `side_env_cmp`; the transfer layer must preserve routing-relevant
information until that point; normal-edge `step_ctx` is not introduced. The fix is
still not a small kernel tweak: the transfer layer and the kernel read contract both
change, because the current `side_env_cmp` read reintroduces the information loss.

---

## 1. Goblint call-protocol audit

Verified upstream sources:

- `src/framework/analyses.ml`: the manager exposes `local : D.t`,
  `global : V.t -> G.t`, and `sideg : V.t -> G.t -> unit` (GitHub lines
  1362-1385).
- `src/framework/analyses.ml`: `Spec.context` has type
  `man -> fundec -> D.t -> C.t` (lines 1435-1444).
- `src/framework/analyses.ml`: `Spec.enter` returns `(D.t * D.t) list`, described
  as caller state plus initial callee state (lines 1491-1498).
- `src/framework/analyses.ml`: `combine_env` / `combine_assign` receive the callee
  context and returned `D.t` (lines 1500-1514).
- `src/analyses/base.ml`: Base `sync` publishes via `Priv.sync ... man.global ...
  man.sideg ... man.local` only when `earlyglobs` or multithreaded mode applies;
  otherwise it returns `man.local` (lines 3075-3105).
- `src/analyses/base.ml`: Base reads globals through `Priv.read_global` only under
  `earlyglobs` or multithreaded mode; otherwise it reads the local CPA store (lines
  3113-3125).
- `src/analyses/base.ml`: Base `context` filters the supplied store; under
  `earlyglobs`, syntactic globals are dropped from the context (lines 3407-3424).

Call-flow shape from the interface:

```text
caller D at call node
  -> enter man lval callee args
       returns (caller_after_enter_D, callee_entry_D)
  -> context man callee callee_entry_D
       selects callee C from the D-state supplied by enter
  -> solve/read callee return at (return_node, callee_C)
  -> combine_env / combine_assign with callee_C and return_D
  -> sync/sideg at framework-triggered publication points
```

Framework contract vs Base behavior:

| Question | Framework contract | Base behavior |
| --- | --- | --- |
| Does `context` update on normal edges? | No evidence; context is selected by the call protocol. | Same. |
| What does `context` receive? | A `D.t` argument supplied by the framework around `enter`. | A `store` filtered by `Base.context`. |
| Is this necessarily pre-publication? | The interface permits it; exact `FromSpec` ordering should be re-checked in `constraints.ml` before implementation. | Base can retain globals in the local store until `sync`, but `earlyglobs` drops syntactic globals from context. |
| Are globals guaranteed in `D`? | No. The analysis chooses what `D` contains. | Sometimes, configuration-dependent. |
| What invariant matters? | `context` sees enough routing information before it is lost to global-side joining. | For Base this may be a global value in the store, unless `earlyglobs` removes it. |

The exact body of `src/framework/constraints.ml` was not live-fetched during this
audit. Existing repository notes cite `constraints.ml` for `LVar = node * C`
(`:37`), `sync` events (`:50-56`), and context-set tracking (`side_context ...`,
`:179`). Before theory implementation, re-open `constraints.ml` and verify the
precise ordering of `enter`, `context`, side-effecting of the callee entry, and
`sync`.

---

## 2. Goblint D/G/C architecture

| Goblint | Isabelle (current) | Intended meaning | Where used |
| --- | --- | --- | --- |
| `D.t` local state | `σ (Inl (v, ctx))`, one per `(pp, C)` | flow-sensitive abstraction at a node+context. It must contain whatever information the analysis uses for routing until `context` is computed. | edge/combine transfer, routing input, collecting-soundness gamma |
| `G.t` global side domain | `σ (Inr k)`, one slot per global key `k` | flow-**insensitive** cross-procedure global effect, joined on read | `glob_env` / `glob_env_cmp`, side contributions |
| `C.t` context | `'c` (e.g. `sign_gctx`) | calling context, keys the local unknowns | `pull_gk`, `side_env_cmp` index |
| `context man f d` | `ctx_sel :: pp => 'c => 'a abs_state => 'c` (`Context_Domain.thy`) | callee context selected from caller state | `route`, kernel `ENTER_MONO`/`CMP_SOUND` |
| `enter` (pre-call transform) | `prep :: pp => 'a abs_state => 'a abs_state` | argument / global pinning before context read | `route cc ctx a = ctx_sel cc ctx (prep cc a)` |
| `combine_env`/`combine_assign` | `unit_combine_tree` / `switching_combine_st` (`TD_Side_CFG.thy:129`, `Exec_Cmp_Bridge.thy`) | reassemble caller-locals + callee-globals at return | combine branch of the soundness backbone |
| `man.global : V.t -> G.t` | `glob_env_cmp cmp ctx σ` (`Global_Cmp_Read.thy:19`) | read the global side store (cmp-filtered join) | `side_env_cmp` |
| `man.sideg : V.t -> G.t -> unit` | `Side k (restrict_global res)` inside `unit_edge_tree` (`TD_Side_CFG.thy:123`) | publish a global contribution to the side store | every edge/combine tree |

**The one structural divergence.** Goblint's `sideg`/`sync` is selective and
analysis-controlled: routing-relevant information may remain in `D` until
`context` is computed. Our current `unit_edge_tree` publishes global information
on every edge and immediately erases it from the local answer. In the `fctx`
witness, that removes the sign of `G` from the only program-point-specific slot
before routing can see it.

---

## 3. Current Isabelle architecture — the transfer discipline

`unit_edge_tree f u` (`TD_Side_CFG.thy:116-124`):

```isabelle
QueryL u (λsu. QueryG () (λg.
  let res = f (su ⊔ g) in                 -- read local ⊔ global, apply transfer
  Side () (restrict_global res)           -- PUBLISH globals to Inr, unconditionally
    (Answer (restrict_local res))))       -- KEEP only non-globals in the local slot
```

with `restrict_local σ = (λx. if is_global x then bot else σ x)` (`:25`). Consequences,
each machine-checked:

- **Globals never persist in a local slot.** The per-`(pp,C)` slot `σ(Inl(v,ctx))` has
  every global at `⊥`. This is not incidental: it is the maintained invariant
  `inl_slot_globals_bot_ctx σ` that `side_cfg_T_eff_cmp_enter_le` and the entry bound
  rely on (`TD_Side_Eff_Cmp_Gen.thy:308, :480`).
- **Globals live only in the side store, keyed by context.**
  `pull_gk_Inr` (`TD_Side_Eff_Cmp_Gen.thy:127`): `pull_gk gkey ctx σ (Inr y) = σ(Inr(gkey ctx))`.
  The global slot is indexed by the **context** `gkey ctx`, *not* by program point.
- **The read is a join.**
  `side_env_cmp cmp σ (v,ctx) = σ(Inl(v,ctx)) ⊔ glob_env_cmp cmp ctx σ` (`Global_Cmp_Read.thy:75`),
  and `glob_env_cmp` joins *all* cmp-compatible global keys
  (`abs_join_set` over `{k. cmp ctx k}`, `:23`). Reading a global at a program point
  yields the flow-insensitive join over its context class.

The context backbone (`post_fixpoint_sound_at_ctx_semantic_generic`,
`TD_Side_Eff_Cmp_Sound.thy:23-45`) is parametric in the read `renv` and the router
`rt`, and routes callee reads through `rt cl ctx (renv σ (cl, ctx))` (`:36, :42`). The
keyed instance (`collect_ctx_sound_route`, `:443`) fixes `renv = side_env_cmp gcmp`,
so both the soundness gamma and the routing input are the **joined** read.

---

## 4. Information-flow trace: where `G:=0; f(); G:=1; f()` collapses

Follow one call site. Concrete driver: `G := 0; f(); G := 1; f()` at call sites
`cc = 4` and `cc = 7`, both in caller context `GOther`.

```
  write G:=0 at pp p            write G:=1 at pp q
        │                             │
  unit_edge_tree:                unit_edge_tree:
    res.G = SZero                  res.G = SPos
    Side Inr(GOther) SZero  ◄── PUBLISH ──►  Side Inr(GOther) SPos
    Answer local, G ↦ ⊥            Answer local, G ↦ ⊥
        │                             │
        └──────────────┬──────────────┘
                       ▼
        σ(Inr GOther).G = SZero ⊔ SPos = SNonNeg     ← MERGE happens here
                       │
   call site 4 read of G:                call site 7 read of G:
     σ(Inl(4,GOther)).G = SBot             σ(Inl(7,GOther)).G = SBot
     ⊔ glob_env_cmp .G  = SNonNeg          ⊔ glob_env_cmp .G  = SNonNeg
   ─────────────────────────────         ─────────────────────────────
     side_env_cmp read .G = SNonNeg        side_env_cmp read .G = SNonNeg
                       │                             │
                  prep (fctx_call_state pins G)   ── ec/ctx_sel ──►  route
                       ▼                             ▼
        entdg over γ(read) ∈ {GZero, GPos}   route must (=)-match BOTH → impossible
```

Preserved / merged / discarded:

- **Preserved** through the write: the *concrete* `G` value in the trace store (the
  digest `entdg` still reads it precisely — `DG_CALLEE`, `TD_Side_Eff_Cmp_Sound.thy:459`).
- **Discarded** at the `Answer (restrict_local res)` step: `G` is erased from the
  per-`pp` local slot. After this, no per-program-point abstract record of `G` exists.
- **Merged** at `Side Inr(GOther) …`: both writes publish to the *same* context-keyed
  slot `Inr GOther`; the solver joins them to `SNonNeg`.

**First point of indistinguishability:** the two calls become indistinguishable the
moment `G` is published to the shared `Inr GOther` slot and erased from the per-`pp`
local slot — i.e. at the `Side`/`Answer` split of the *writing* edge, **before** either
call is reached. It is not the call, not `prep`, not `ctx_sel`: by the time control
reaches a call site the per-`pp` `G` is already `⊥` and the shared slot already
`SNonNeg`. This is exactly `fctx_caller_read_G_imprecise`
(`Example_Finite_Sign_Context_Analysis.thy`, eval): `σ(Inl(4,GOther)) ⊔ σ(Inr GOther)`
reads `G = SNonNeg`, and `sign_zero_pos_join`: `SZero ⊔ SPos = SNonNeg`.

---

## 5. Root cause — is it `ctx_sel(local ⊔ global)`? No: it is more subtle.

The naive framing "kernel computes `ctx_sel(local ⊔ global)` where Goblint computes
`ctx_sel(local D)`" is **only half true**, and fixing just that half does nothing.

- **Half that is true.** `route` is fed `side_env_cmp gcmp σ (cl,ctx)`
  (`collect_ctx_sound_route` CMP_SOUND/ENTER_MONO, `TD_Side_Eff_Cmp_Sound.thy:455, :461`),
  which is literally `σ(Inl(cl,ctx)) ⊔ glob_env_cmp` — the joined read. Goblint feeds
  `context` the local `D.t`.
- **Why fixing only that half fails.** Replace the routing input with the *local-only*
  read `D_read σ (cl,ctx) = σ(Inl(cl,ctx))`. By `inl_slot_globals_bot_ctx`, that slot
  has `G = ⊥`. So `ctx_sel(D_read)` sees **no `G` information at all** — strictly worse
  than the joined read. The obstruction does not move; it worsens.

**The actual root cause is two coupled facts, both in the transfer layer, not the
context kernel:**

1. **Immediate publication + erasure** (`unit_edge_tree`, `restrict_local`): the
   sign of `G` used by the `fctx` router is removed from the flow-sensitive per-`pp`
   state on every edge. There is no routing state that still contains that sign.
2. **Context-keyed (not pp-keyed) globals** (`pull_gk_Inr`): the surviving global lives
   in `Inr(gkey ctx)`, shared by *all* program points of that context, so the two call
   sites — distinct `pp`s, same context — collide even though their per-`pp` locals
   would differ.

Goblint escapes when the analysis keeps the routing-relevant information in the
`D.t` supplied to `context`. For Base, that information can be the sign/value of a C
global in the store under some configurations; for other analyses it may be locals,
arguments, heap, aliases, or a derived summary. The distinguishing information our
model needs already has a natural home — the per-`(pp,C)` local/routing slot
`Inl(4,GOther)` vs `Inl(7,GOther)` are different unknowns — but the current sign
transfer erases the global part there and shunts it into a shared slot.

So: the obstruction is an **artifact of the publish-and-erase global discipline**, not
of the context mechanism, and not merely of the joined read.

---

## 6. Minimal Route A correction (design only — not implemented)

The minimal change that matches Goblint's D/G/C split, by layer:

### 6a. Transfer layer (the substantive change)

Let the routing state retain **context-relevant information** until `ctx_sel` has
seen it. For the current sign `fctx` witness this likely means keeping the relevant
global sign in the local/routing answer at call sites, but the interface should not
hard-code "globals remain in `D`." Replace the unconditional `Side/restrict_local`
split with a discipline where ordinary edges preserve a routing projection and
publication to `Inr` happens at explicit publication/sync points. This drops or
qualifies the `inl_slot_globals_bot_ctx` invariant and introduces a publication
predicate.

| Item | Change | Proof status |
| --- | --- | --- |
| `unit_edge_tree` / `mixed_etf_edge_tree` | new preserve-routing variant + explicit publication point | **new definitions** |
| `restrict_local`/`restrict_global` | unchanged as operators; no longer the only per-edge split | unchanged |
| `inl_slot_globals_bot_ctx` invariant | **dropped or weakened** for slots used as routing `D` | invariant + every lemma using it (`enter_le`, entry bound) **re-proved** |
| edge soundness (`EDGE`, `side_cfg_T_eff_cmp_edge_le`) | restated so routing information remains in `D` until `ctx_sel` | **new proof** |
| **cross-procedure global visibility** | publication no longer automatic ⟹ must re-supply how a callee's global write reaches the caller | **new proof, genuinely hard** |
| collecting-semantics correspondence (`cfg_collect`/`γ`) | routing-relevant information now remains in the local/routing state until `ctx_sel` | **new proof** |

### 6b. Read layer

Split the single `renv` into at least two reads:

```text
R_read  σ (v,ctx) = routing projection of σ (Inl (v,ctx))  -- for ctx_sel
G_read  σ ctx     = glob_env_cmp cmp ctx σ                  -- published globals
Obs     σ (v,ctx) = observation state for γ                 -- not necessarily current side_env_cmp
```

`Obs` must not blindly reintroduce incompatible joined global information for the
variables that determine context. Otherwise the old `SNonNeg` obstruction returns
through the soundness gamma even if `ctx_sel` reads `R_read`.

| Item | Change | Proof status |
| --- | --- | --- |
| `side_env_cmp` | keep for the old published-only model; add `R_read` and an `Obs`/policy read for Route A | partly additive, partly new theorem instantiation |
| `glob_env_cmp` | reused as `G_read` | unchanged |

### 6c. Context backbone (cheap shape, new obligations)

`post_fixpoint_sound_at_ctx_semantic_generic` takes `renv` and `rt` as parameters. The
structural change is to separate the state used for routing from the state used for
the collecting/gamma bound.

| Item | Change | Proof status |
| --- | --- | --- |
| backbone `ENTER_MONO`/`COMB_SEM` (`:34-42`) | route arg `rt cl ctx (R_read σ (cl,ctx))`; gamma uses `Obs σ (cl,ctx)` with an explicit compatibility obligation | **mechanical shape**, substantive obligations |
| `collect_ctx_sound_route` (`:443`) | re-instantiate with the split read | **replay** |
| `context_domain` locale | `ctx_sel` already typed `pp => 'c => 'a abs_state => 'c`; add a side condition "argument is `R_read`, before information loss" | signature already fits (see `CONTEXT_DOMAIN_ARCHITECTURE.md`) |

Proposed theorem-interface shape:

```text
R_read  :: sigma => (pp * c) => abs_state
Obs     :: sigma => (pp * c) => abs_state
route   :: pp => c => abs_state => c

ENTER_COMPAT:
  s in gamma (Obs sigma (cl, ctx))
  ==> cmp (entdg (enter_state s)) (route cl ctx (R_read sigma (cl, ctx)))

COMB/CMP_SOUND:
  returned/published effects are bounded using the appropriate G_read/Obs policy,
  not by feeding side_env_cmp to ctx_sel.
```

This says exactly what Isabelle needs from Goblint's call protocol: every concrete
call state covered by the observation read must have a digest compatible with the
context selected from the routing read.

### 6d. Unchanged

- The `context_domain` interface shape, `route = ctx_sel ∘ prep`, `start_context`,
  `cmp`, `entdg` typing.
- Stack B (`entry_store_ctx` interpretation, `semantic_entry_store_ctx_analysis_sound`):
  it uses `cmp = (⊆)` with a **unit** global pot and entry-store contexts — it does not
  route on a keyed global, so it is untouched by 6a/6b.
- `glob_env_cmp` monotonicity/collapse lemmas.

---

## 7. Definitions likely affected

Theory implementation is explicitly deferred. Likely affected definitions and lemmas:

| Area | Likely affected names |
| --- | --- |
| Context interface | `Context_Domain.context_domain`, `route` documentation/locale assumptions |
| Global reads | `Global_Cmp_Read.glob_env_cmp`, `side_env_cmp` users; new `R_read` / `Obs` definitions |
| Tree builders | `TD_Side_CFG.unit_edge_tree`, `unit_combine_tree`; `TD_Side_Tree.side_cfg_T_eff`; cmp variants in `TD_Side_Eff_Cmp_Gen` |
| Transfer invariants | `restrict_local`, `restrict_global` usage; `inl_slot_globals_bot_ctx`, `inr_slot_locals_bot`, local/global bot lemmas |
| Soundness kernel | `TD_Side_Eff_Cmp_Sound.post_fixpoint_sound_at_ctx_semantic_generic`, `_final`, `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`, `collect_ctx_sound_route`, `ENTER_MONO`, `CMP_SOUND`, `COMB_SEM` |
| Executable bridge | `Exec_Cmp_Bridge.switching_combine_st`, `abs_switching_combine`, `traverse_/sides_/dep_switching_combine_st_fun_of_st` |
| Witness | `Example_Finite_Sign_Context_Analysis`, `fctx_call_state`, `fctx_ec_call`, `fctx_caller_read_G_imprecise`, `fctx_keyed_sound_if_post_fixpoint` |
| Domain instances | `Sign_Side_Soundness.sign_etf`, `Interval_Side_Soundness` if reused under Route A |

Definitions that should **not** be introduced for the primary Route A correction:
normal-edge `step_ctx`, `context_intra`, or a context update in the ordinary edge
map. Those remain a separate, non-Goblint fallback.

---

## 8. Re-evaluating A7 under the correction

Assume 6a–6c land (routing-relevant information survives in `R_read`; `ctx_sel`
does not read `side_env_cmp`).

- **Does the obstruction disappear?** For `fctx`: **yes, in principle** — the two call
  sites are distinct unknowns `Inl(4,GOther)` and `Inl(7,GOther)`; if `R_read` still
  contains the sign used for routing, it selects `GZero` at site 4 and `GPos` at site
  7. **Conjectured, not proven** — it depends on 6a actually preserving that
  information until the call.
- **`ENTER_MONO` (`:460-461`)** — becomes provable **for `fctx`** once `R_read` at a
  call site is exact on the routing digest (single sign, not the `SNonNeg` join). The
  current refutation (`fctx_caller_read_G_imprecise`) is specifically about the
  *joined* read; it does not apply to a pre-loss routing read. **Conjectured**,
  contingent on 6a/6b.
- **`CMP_SOUND` (`:454-456`)** — the return read. Already known fixable by a cc-aware
  `route` (the earlier A7.4 analysis: the call-state pin is fresh at the return). Under
  D/G/C it stays provable; **low risk**, but still requires the new combine soundness.
- **What remains genuinely difficult (the real work, all *new* proof):**
  1. **Cross-procedure global soundness without automatic publication.** Publication is
     currently what makes a callee's global write visible to the caller and to the
     flow-insensitive semantics. A selective-publication model must re-establish that
     every concrete global effect is still soundly propagated — this is the substance
     of interprocedural global soundness, not a replay.
  2. **Re-proving the collecting correspondence** with routing information carried in
     the local/routing slot (the whole `EDGE`/entry/combine chain and the `γ` bound).
  3. **Modeling `sync`/`sideg` precisely** enough to state *when* routing-state
     information is published, and proving that the published join is still an
     over-approximation.
  4. **Termination/precision of the keyed local slots** now that they carry more
     information (larger state, but no new fixpoint-theory obstacle expected).

Proven vs conjectured summary: *proven today* = the obstruction under the **current**
joined/publish-erase model (`fctx_caller_read_G_imprecise`, `sign_zero_pos_join`).
*Conjectured* = that the D/G/C correction removes it; the conjecture is architecturally
well-founded (the distinguishing state has a per-`pp` home) but its soundness proof is
new and non-trivial, concentrated in 6.(1)–(2).

---

## 9. Risk assessment

| Risk | Severity | Note |
| --- | --- | --- |
| Dropping `inl_slot_globals_bot_ctx` cascades | **High** | it is load-bearing in `enter_le`, entry bound, and the `pull_gk` invariants; every consumer re-proves |
| Cross-procedure global visibility regression | **High** | publication currently guarantees it; a selective-publication model can silently lose a global effect, which is unsoundness, not just imprecision |
| Collecting-correspondence rework | **Medium-High** | `cfg_collect`/`γ` soundness restated with routing information in local/routing state |
| Context backbone change | **Medium** | shape is parametric, but `Obs` vs `R_read` compatibility is new proof content |
| `context_domain` interface churn | **Low** | signature already fits; only a side condition + possible `publish`/`read_global` fields |
| Stack B regression | **Low** | untouched (unit global, `⊆`, no keyed-global routing) |
| Scope creep into a general `sync` semantics | **Medium** | tempting to model full Goblint `sync`; keep to the minimal preserve-routing + publication discipline needed for `fctx` |

**Soundness-direction caveat.** The current publish-erase discipline is
*conservative*: it over-approximates globals by a flow-insensitive join. A
preserve-routing model is more precise, but the extra precision is only sound if the
publication discipline still dominates every concrete cross-procedure global flow.
The single most dangerous failure mode is a callee global write that the new model
forgets to publish — that is a soundness bug, and the proof obligation guarding it is
the crux.

---

## 10. Recommendation

1. **Record the finding:** the A7 obstruction is an artifact of the publish-and-erase
   global discipline (`unit_edge_tree` + `inl_slot_globals_bot_ctx`), *not* of
   context-sensitivity and *not* merely of the joined `side_env_cmp` read. Feeding
   `ctx_sel` a local-only read without first changing the transfer discipline would
   make precision strictly worse.
2. **Change transfer layer and kernel read together.** Splitting the kernel read
   without preserving routing information makes `ctx_sel` see too little; preserving
   routing information while leaving `side_env_cmp` as the router keeps the old join.
   Route A needs both: (a) preserve routing information until `ctx_sel`, (b) add
   explicit publication, (c) route from `R_read`, and (d) prove `Obs` compatibility for
   the collecting gamma.
3. **Prototype the soundness of preserve+publish on a minimal fragment before
   committing.** The high-severity risks are in cross-procedure global visibility.
   Validate on a two-procedure, one-global fragment (the `fctx` shape) that a callee
   global write remains sound under the new publication discipline before touching the
   full keyed generator.
4. **Keep Stack B (`C`) as the shipped soundness result** meanwhile: it already
   certifies value-dependent context-sensitivity (`semantic_entry_store_ctx_analysis_sound`)
   and is orthogonal to this rework. The D/G/C correction is a **precision** upgrade of
   the keyed route (`A`), not a soundness prerequisite.
5. **Ship the obstruction characterization as a result regardless:** "a finite keyed
   `(=)` context cannot separate a global-derived split under a publish-and-erase global
   discipline; the routing-relevant information must remain available in the
   per-program-point routing state until `ctx_sel`." That is a precise, defensible
   boundary statement.

Bottom line: **not fundamental — artifact.** Removing it is a transfer-layer research
task with a real soundness obligation at its core (cross-procedure global visibility
under selective publication), while the context interface we just landed is already
shaped to accept the corrected read.
