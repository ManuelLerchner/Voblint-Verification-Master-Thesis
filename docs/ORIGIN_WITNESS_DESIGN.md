# Origin-parameterised witness calculus — design

Status: DESIGN (pre-implementation). No `.thy` edited or restored. Option (a) of
`ACTIVATION_WITNESS_RECONCILIATION.md`: one canonical fundamental witness that subsumes
globally rooted collecting and the frame-origin (former `twf`) role, keeping parameter
binding faithful.

Central idea: a witness carries an explicit **origin activation** `(w, wc)` and a **current**
point `(v, ctx)`. There are exactly two ways an origin comes into being, and **neither is a
free arbitrary-store start**:

* a *program* origin at `cfg_entry g` seeded from the initial set `S`;
* a *frame* origin at a callee entry, **born from a caller witness** by the call's
  `EA_Enter` edge via `edge_step` / `bind_formals`.

Because the frame origin is born by a rule that consumes a caller witness (not a free
`start`), invalid frame origins are unrepresentable, parameter binding is retained, and the
callee witness begins exactly at the bound entry store — so `combine` never needs a re-rooted
whole-program run.

---

## 1. Exact inductive proposal

Fixed parameters: graph `g`, initial set `S`, routing `enterc :: 'c => store => 'c`, return
map `combc :: 'c => 'c => 'c`, root context `seedc :: 'c`. Varying:
origin `(w :: pp, wc :: 'c)`, current `(v :: pp, ctx :: 'c)`, trace `tr`.

```
witd enterc combc seedc g S :: pp => 'c => pp => 'c => trace => bool

program_base:
    s \<in> S
  ==> witd ... (cfg_entry g) seedc  (cfg_entry g) seedc  [s]

enter_frame:                                   -- births a frame origin at a callee entry
    (cl, EA_Enter xs es, fe) \<in> edges g
    witd ... w wc  cl c  tau                    -- caller witness, ANY origin (w,wc)
    edge_step (EA_Enter xs es) (last tau) = Some s
  ==> witd ... fe (enterc c s)  fe (enterc c s)  [s]

intra:
    (u, a, v) \<in> edges g      \<not> is_enter_action a
    witd ... w wc  u ctx  tr
    edge_step a (last tr) = Some s'
  ==> witd ... w wc  v ctx  (tr @ [s'])

combine:                                        -- return: glue caller + callee frame witness
    (cl, ex, v, dst) \<in> combines g
    (cl, EA_Enter xs es, fe) \<in> edges g
    witd ... w wc  cl c1  tau                    -- caller, origin (w,wc)
    edge_step (EA_Enter xs es) (last tau) = Some s
    witd ... fe (enterc c1 s)  ex (enterc c1 s)  rho   -- callee, FRAME origin (fe, enterc c1 s)
    hd rho = s
  ==> witd ... w wc  v (combc c1 (enterc c1 s))
            (tau @ tl rho @ [combine_collect dst (last tau) (last rho)])
```

Per-rule reading:

| rule | origin `(w,wc)` | current `ctx` | parameter binding | trace head `hd tr` | execution fragment |
| --- | --- | --- | --- | --- | --- |
| `program_base` | `(cfg_entry g, seedc)`, fresh | `seedc` | n/a | `s \<in> S` | the program's initial configuration |
| `enter_frame` | **new** `(fe, enterc c s)` | `enterc c s` | `s = edge_step (EA_Enter xs es) (last tau)` = `bind_formals xs (map (aval·es) (last tau)) (enter_state (last tau))` | the bound entry store `s` | a call opening a callee activation |
| `intra` | unchanged | unchanged | n/a | unchanged | one non-call CFG edge |
| `combine` | caller's `(w,wc)` | `combc c1 (enterc c1 s)` | via `edge_step` at the matching enter edge | unchanged (= caller's) | a callee returning into its caller |

The origin is threaded unchanged by `intra` and `combine` (the returned activation keeps the
*caller's* origin); only `enter_frame` mints a new (frame) origin. There is no `enter`
(inlining) rule and **no free `start`**: reaching a callee interior mid-execution is a frame
origin (`enter_frame` then `intra`), which is the faithful representation of an active,
not-yet-returned frame.

## 2. Origin representation — three options

1. **Plain `(w, wc)` + structured base rules (recommended).** No separate origin datatype and
   **no free admissibility predicate**: `program_base` and `enter_frame` are the only ways to
   introduce an origin, and each carries its own admissibility structurally
   (`program_base`: `w = cfg_entry g`, `hd \<in> S`; `enter_frame`: born from a caller witness by
   an enter edge). Invalid origins are unrepresentable because there is no rule that starts a
   frame at an unjustified store.
2. **Origin datatype** `origin = POrigin | FOrigin pp 'c`. Makes origin a first-class value,
   convenient for indexing the collecting semantics. But it duplicates information already
   determined by `(w, wc)` and the birth rule, and forces case analysis the two base rules
   already give. Adds a datatype for no proof strength.
3. **Origin evidence carries the caller witness.** This is exactly what `enter_frame` already
   does (the caller witness is a premise). Realising it as a datatype *field* (an embedded
   witness) would make the witness a tree and complicate the `last`-projection.

**Recommendation: option 1.** It is the most readable, gives the strongest induction (each
rule is a genuine constructor with its admissibility inline), structurally forbids spurious
frame starts, threads cleanly through the source-run induction (§7), and forgets to the
monovariant semantics by erasing `'c` (§5) with no datatype to collapse. If a later proof
genuinely needs origins as data (e.g. an origin-indexed collecting map, §9), derive the
datatype view as a definition over `(w, wc)` rather than baking it into the inductive.

## 3. Combine design (the key point) + worked `twice(10)`

* The **caller prefix** is the caller witness `witd ... w wc cl c1 tau` at the call node `cl`,
  origin `(w,wc)` — the activation that will resume.
* The **callee** is a **frame-origin** witness `witd ... fe (enterc c1 s) ex (enterc c1 s) rho`:
  it was born by `enter_frame` at the callee entry `fe` and traced to the callee exit `ex`.
* `hd rho = s` where `s = edge_step (EA_Enter xs es) (last tau)` is the **bound entry store**.
  This is a premise, but it holds *by construction* because the same `enter_frame` that bore
  `rho` used exactly this `s`.
* The callee context is `enterc c1 s` — routed from the **caller** context `c1` and the
  **bound** entry store `s`.
* The return restores the caller context via `combc c1 (enterc c1 s)`; with the caller
  projection `combc c1 _ = c1` this is `c1`.
* Nested/recursive calls compose because the callee `rho` is itself an ordinary `witd`
  witness that may contain its own `enter_frame`/`combine` steps — **no re-rooted
  whole-program run is ever synthesised**; the callee simply starts at its own entry store.

Worked derivation, second call `y := twice(10)` (nodes from `twice_edges`; `enterc c s =
ivl_decode (s ''p'')`, `combc c1 _ = c1`, `seedc = bot`):

```
1  program_base:  witd ... 4 bot  4 bot  [s0]                         (s0 \<in> cinit)
2  ... (call 1 as below) ... intra Nop:  witd ... 4 bot  6 bot  tau6   (last tau6 = r5, x:=6)
3  enter_frame (6, EA_Enter [p][10], 0):
       edge_step (EA_Enter [p][10]) r5 = Some es10,  es10 ''p'' = 10   (bind_formals: FAITHFUL)
       ==> witd ... 0 ctx2  0 ctx2  [es10]           (ctx2 = ivl_decode 10 = enterc bot es10)
4  intra*3 (0->1->2->3):  witd ... 0 ctx2  3 ctx2  [es10, es10, es10, es10rr]   (es10rr ''#ret'' = 20)
5  combine (6,3,7,Some y):
       caller  witd ... 4 bot 6 bot tau6         (last = r5)
       callee  witd ... 0 ctx2 3 ctx2 rho2       rho2 = [es10, es10, es10, es10rr], hd = es10
       ==> witd ... 4 bot  7 bot  (tau6 @ tl rho2 @ [combine_collect (Some y) r5 es10rr])
           with  combine_collect (Some y) r5 es10rr = (...)(''y'' := 20)
```

Call 1 (`x := twice(3)`) is the symmetric derivation at nodes `4 ->(enter) 0..3 ->(combine
4,3,5) 5`. Contrast the current semantics, where the call-2 callee had to be a re-rooted
whole-program run rooted at `(''p''\<mapsto>10)` (10 stores); here `rho2` is the 4-store callee
trace born directly at `es10`.

## 4. Parameter faithfulness

Second call produces `p = 10`, not `p = 0`:

```
enter_frame uses  s = edge_step (EA_Enter [''p''] [N 10]) (last tau)
                    = bind_formals [''p''] [aval (N 10) (last tau)] (enter_state (last tau))
                    = (enter_state (last tau))(''p'' := 10)
so  s ''p'' = 10.
```

`twf`/`twfr` instead used `enter_state (last tau)` in both `enter` and the `combine` premise
`hd rho = enter_state (last tau)`, dropping the formal binding (`s ''p'' = 0`). The exact loss
is the `bind_formals xs (map (aval·es) …)` layer: `twf` kept the enter *edge* (`xs`, `es`) only
to name the frame, never applying it to the store. The new `enter_frame`/`combine` apply
`edge_step (EA_Enter xs es)`, which *is* `bind_formals ∘ enter_state`, so formals carry their
argument values. This is why the new frame path can state per-**local** soundness (e.g. about
`#ret`), which `twf`'s examples could not, forcing them to per-**global** claims.

## 5. Specialisation theorems

Write `witd_c` for the fixed instance at `enterc/combc/seedc/g/S`.

* **`cfg_collect_ctx_act`** — the program-origin, context-kept projection:
  `cfg_collect_ctx_act enterc combc seedc g S v ctx = {last tr | witd_c (cfg_entry g) seedc v ctx tr}`.
  This *replaces* `trace_witness_act` as the underlying witness. Now compositional and
  faithfully inhabited (§3).
* **`trace_witness` / `cfg_collect`** (monovariant) — erase `'c` (`'c = unit`, `enterc = _`,
  `combc = _`, `seedc = ()`): `witd_unit w wc v () tr`. `program_base` = `entry`, `intra` =
  `edge`, `enter_frame` = a **generalised** `proc_entry` (any enter edge, not only
  `cfg_entry`), `combine` = `combine` with a frame-origin callee. Target theorem:
  `alpha_last {tr. \<exists>w wc. witd_unit w wc v () tr} = cfg_collect g S v`
  (`\<subseteq>` by the generic soundness at the identity reader; `\<supseteq>` by induction on the
  `cfg_collect` fixpoint, `enter_frame` supplying the callee seed the old `proc_entry` could
  not). `cfg_collect` itself (a set fixpoint) is **unchanged**; only its witness bridge moves
  from `trace_witness` to `witd_unit`.
* **frame-origin / former `twf` reasoning** — the frame-origin instance: for any caller-born
  origin `(fe, kc)`, `witd_c fe kc v ctx tr`. The `twf_sound` conclusion is the generic
  soundness (§6) restricted to a frame origin; no separate relation.
* **forgetting activation contexts** — the erasure `'c := unit` above (a functor on the
  relation, one lemma).
* **forgetting origins** — existential over `(w, wc)`:
  `reachable g S v tr \<equiv> \<exists>w wc ctx. witd_c w wc v ctx tr`; used only where the origin
  is irrelevant (e.g. the monovariant bridge). Not used in the source proof (§9).

Migration disposition (avoid permanent wrappers): `trace_witness_act` is **replaced** by
`witd_c` (program-origin projection renamed to `cfg_collect_ctx_act`). `trace_witness` is
**replaced** by `witd_unit` with a temporary equivalence lemma to `cfg_collect` that is
**deleted at stage 9**. `twf`/`twfr` are **not** reintroduced. No standing `_v2`/adapter
survives migration.

## 6. Soundness interface

Reader `sg :: pp \<times> 'c + 'g => 'a::sound_domain abs_state`, obligations exactly the current
four:

```
ENTRY_G:  s \<in> S ==> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>
EDGE:     (u,a,v) \<in> edges g ==> \<not> is_enter_action a
          ==> s \<in> \<lbrakk>sg (Inl (u,c))\<rbrakk> ==> edge_step a s = Some s'
          ==> s' \<in> \<lbrakk>sg (Inl (v,c))\<rbrakk>
SEED_G:   (u, EA_Enter xs es, v) \<in> edges g ==> s \<in> \<lbrakk>sg (Inl (u,c))\<rbrakk>
          ==> edge_step (EA_Enter xs es) s = Some s' ==> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>
COMB:     (cl,ex,v,dst) \<in> combines g ==> s \<in> \<lbrakk>sg (Inl (cl,c1))\<rbrakk>
          ==> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 s'))\<rbrakk> ==> call_enter_store g cl s s'
          ==> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 s')))\<rbrakk>
```

Generic theorem (**unconditional** — no start-store hypothesis):

```
assumes ENTRY_G EDGE SEED_G COMB   and   witd_c w wc v ctx tr
shows   last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>
```

Proof by induction on `witd_c`. Obligation usage per case:

* `program_base` (program-origin base): `last [s] = s \<in> S`, discharge by **ENTRY_G**.
* `enter_frame` (frame-origin base): IH gives `last tau \<in> \<lbrakk>sg (Inl (cl, c))\<rbrakk>`; then
  **SEED_G** on the enter edge gives `s \<in> \<lbrakk>sg (Inl (fe, enterc c s))\<rbrakk>`, i.e.
  `last [s]` sound. The frame entry store's soundness is thus **derived from the caller
  witness + SEED_G**, never assumed — satisfying the item-6 requirement.
* `intra` (call-free step): **EDGE**.
* `combine` (return): caller IH + callee IH + **COMB**.

Crucially, because `enter_frame` is a *rule of the relation* (not an external hypothesis), the
theorem needs **no** `hd tr`-soundness premise (unlike `twf_sound`). `DG_Ctx_Activation`
already discharges ENTRY_G/EDGE/SEED_G/COMB for the interval solution, so the interval
soundness re-proves verbatim.

## 7. Source-bridge invariant

Reuse `cstep` (Located_Exec) and the existing source→`cstep` simulation unchanged. Relate the
runtime frame stack to a stack of **frame-origin witnesses**. `cstep` frame `i` is
`(cl_i, ret_i, s_cl_i)`; alongside it record `(c_i, fe_i, es_i)`:

| recorded | meaning |
| --- | --- |
| `cl_i` | caller (call) node | (from `cstep` frame) |
| `ret_i` | return node | (from `cstep` frame) |
| `s_cl_i` | caller store at the call | (from `cstep` frame) |
| `c_i` | caller context | (auxiliary) |
| `fe_i` | callee entry node | (from the enter edge) |
| `es_i` | bound callee entry store `= edge_step (EA_Enter ...) s_cl_i` | (auxiliary) |
| callee context | `enterc c_i es_i` | (auxiliary) |
| witness | `witd_c fe_i (enterc c_i es_i) — —` for this frame's activation-so-far | (auxiliary) |

Invariant `sim (v, s, stk) (ctx, cstk)`:

* the **innermost** activation has a witness `witd_c w0 wc0 v ctx tr` with `last tr = s`, where
  `(w0,wc0)` is the program origin if `stk = []`, else the frame origin `(fe_top, enterc
  c_top es_top)`;
* each **suspended** frame `i` has a witness `witd_c w_i wc_i cl_i c_i tau_i` with
  `last tau_i = s_cl_i` (its activation paused at its call node), and
  `es_i = edge_step (EA_Enter ...) s_cl_i`, `call_enter_store g cl_i s_cl_i es_i`;
* consecutive frames are linked: frame `i`'s callee is frame `i-1` (its origin store `es_{i-1}`
  is the enter-image of frame `i`'s call store).

Transitions:

* **normal step** (`cstep.Intra`): extend the innermost witness by `intra`; `ctx`, `cstk`
  unchanged.
* **call push** (`cstep.Call`, push `(cl, ret, s)`, store → `s'`): apply **`enter_frame`** with
  the innermost witness as the caller, `s' = edge_step (EA_Enter xs es) s`; push
  `(c_top, fe, s')` and set the new innermost witness to the born `witd_c fe (enterc c_top s')
  fe (enterc c_top s') [s']`; new `ctx = enterc c_top s'`.
* **return pop** (`cstep.Return`, pop `(cl, ret, s_cl)`, exit store `t` → `r`): apply
  **`combine`** with the popped caller witness (suspended at `cl`, context `c1`) and the
  completing innermost callee witness (frame origin, at `ex`, `last = t`); the result is the
  caller's witness extended to `ret`, origin = caller's, `ctx = combc c1 (enterc c1 es)`,
  `last = r`.

Then `psteps -> star (cstep g) -> sim` gives, at the final configuration,
`witd_c (cfg_entry g) seedc v ctx tr` with `last tr = t`, i.e.
`t \<in> cfg_collect_ctx_act ... v ctx`. The `cstep` stack depth equals the witness nesting
depth — the invariant is structural, needing **no** re-rooting and **no** change to `cstep`.

## 8. Recursion example (the discriminating case)

Flat `twice` can be faked by re-rooting; genuine recursion cannot. Minimal recursive CFG for
`f(n){ if n>0 then f(n-1) else skip }`, `main{ f(2) }` (schematic node numbers):

```
edges:    (10, EA_Enter [n][2],  0)         -- main calls f(2)
          (0,  EA_AssumeNot (0<n), 4)        -- base case -> f-exit 4
          (0,  EA_Assume    (0<n), 1)        -- recursive case
          (1,  EA_Enter [n][n-1], 0)         -- f calls f(n-1): enters its OWN entry 0
          (3,  EA_Nop, 4)                     -- after recursive return -> f-exit 4
combines: (10, 4, 11, ...)                    -- main's return
          (1,  4, 3,  ...)                    -- recursive return
```

Two `f` activations, distinct **frame origins**:

* Outer `f(2)` is born by `enter_frame` at `(10, EA_Enter [n][2], 0)`: origin
  `FO_out = (0, enterc c_main es2)`, `es2 ''n'' = 2`, head `es2`.
* Inner `f(1)` is born by `enter_frame` at `(1, EA_Enter [n][n-1], 0)` **from the outer
  activation's witness at node 1**: origin `FO_in = (0, enterc c_out es1)`, `es1 ''n'' = 1`,
  head `es1`.

`FO_out \<noteq> FO_in`: the origin stores differ (`n = 2` vs `n = 1`), and if `enterc` reads
`n` the contexts differ too. The inner activation runs `0 -> 4` (base case, `n-1 = 0`) as a
`witd_c FO_in — —` witness. The outer `combine (1,4,3)` consumes the **inner** frame-origin
witness (callee) together with the **outer** frame-origin witness at node 1 (caller). The
outer then reaches `3 -> 4`, and `main`'s `combine (10,4,11)` consumes the outer frame-origin
witness. Each callee witness starts at its *own* entry store (`es1`, `es2`), born from its
*actual* caller — no whole-program re-rooting, and the construction is uniform in the
(unbounded) recursion depth. Re-rooting fails here precisely because pinning the inner callee
to the outer caller's continuation would require reconstructing the entire outer frame as a
program-origin run, which cannot be done uniformly in depth.

## 9. Collecting semantics — keep the origin visible

Define the internal collecting **origin-indexed**:

```
cfg_collect_org enterc combc seedc g S v ctx w wc = {last tr | witd_c w wc v ctx tr}
```

Projections:

* analyzer / source target: `cfg_collect_ctx_act ... v ctx = cfg_collect_org ... v ctx (cfg_entry g) seedc`
  (program origin);
* frame summaries: `cfg_collect_org ... v ctx fe kc` for `(fe, kc)` a frame origin.

Do **not** erase the origin early. The source run is program-origin, so the source-level
theorem lands in the program-origin projection; but the *derivation* of a return-node store
consumes frame-origin summaries via `combine`. If we existentially projected over origins
before the combine (as a plain `(v, ctx)`-indexed set), the combine would lose the link
between a callee summary and its caller and we would be back to matching arbitrary re-rooted
stores — the exact defect this design removes. Keeping `cfg_collect_org` origin-indexed and
projecting to the program origin only at the top-level statement preserves the compositional
structure the source proof needs. (For analyzer soundness the origin index is harmless: the
generic theorem holds at every origin, so the program-origin projection inherits it.)

## 10. Concretisation target

Primary source-level conclusion is **per-coordinate / read** soundness:

```
psteps Pi (main, s, []) src'   ==>   sim-matched at (v, ctx) with store t
  ==>   t qv \<in> gamma (sg (Inl (v, ctx)) qv)
```

robust to the global-at-`\<bottom>` emptiness of the full-store concretisation
(`WITNESS_CALCULUS_REPAIR.md`). Full-store corollary only under an explicit support
assumption:

```
assumes  finitely-supported sg, i.e.  \<forall> but finitely many x. sg (Inl (v,ctx)) x = \<top>
   (equivalently: every global unmentioned by the analysis maps to \<top>, not \<bottom>)
shows    t \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>
```

Derive per-coordinate from the generic §6 theorem by reading a single coordinate `qv`; the
full-store version is the finite-support strengthening.

## 11. Migration plan (independently green commits)

1. **Introduce `witd` beside the current definitions** in `CFG_Collect_Activation` (or a new
   `CFG_Collect_Origin`), plus `cfg_collect_org`. Prove `witd`-basic (nonempty, origin
   threading). *Affected:* CFG collecting layer; induction fallout: none yet (new relation).
2. **Generic soundness** (§6) in `Activation_Backbone` beside `activation_collect_sound`.
   *Affected:* `Activation_Backbone`; one induction over `witd`.
3. **Derive the globally rooted monovariant instance**: `witd_unit` and
   `alpha_last (…) = cfg_collect`. *Affected:* `CFG_Collect_Trace` bridge lemmas; induction on
   the `cfg_collect` fixpoint for `\<supseteq>`.
4. **Frame-origin reasoning + recursion example**: prove the §8 recursive CFG inhabits and is
   sound via `witd`. *Affected:* a new example theory; no core fallout.
5. **Migrate `Activation_Backbone`**: re-express `activation_trace_sound` /
   `activation_collect_sound` as the program-origin instance; keep the obligation interface.
   *Affected:* `Activation_Backbone`, `DG_Ctx_Activation` (re-statement, same obligations),
   `Example_Interval_DG_Ctx_Collect` (target now `witd`-backed `cfg_collect_ctx_act`).
6. **Forgetful / projection lemmas**: context erasure, origin projection, the temporary
   `cfg_collect_ctx_act`(new)≈(old) equivalence. *Affected:* CFG + Analysis boundary.
7. **Source bridge** (§7): `sim` invariant + `cstep` preservation + `psteps -> membership`.
   *Affected:* `Compiler_Correctness` / a new bridge theory; reuse existing simulation.
8. **Migrate the flagship**: instantiate for `twice` (per-coordinate, §10) and prove the
   recursive flagship end-to-end. *Affected:* interval example theories.
9. **Delete superseded definitions and temporary adapters**: retire `trace_witness_act`, the
   old `cfg_collect_ctx_act` witness, and the stage-3/6 equivalence lemmas once no consumer
   remains. *Affected:* CFG collecting, Analysis; grep-clean.

## Architectural stopping conditions

Stop and report rather than implement if any holds:

* the single inductive requires an unconstrained predicate that admits invalid frame origins
  (design intent: **no** free `start`; `enter_frame` must carry a caller witness);
* `combine` still needs a re-rooted global execution for the callee (design intent: callee is
  a frame-origin witness headed at the bound entry store);
* parameter binding cannot be retained through `enter_frame`/`combine` (design intent:
  `edge_step` = `bind_formals`, never `enter_state` alone);
* projecting away origins is forced before the combine and breaks the source induction (design
  intent: `cfg_collect_org` stays origin-indexed; project only at the top statement);
* the one inductive becomes less readable than two relations with formally distinct roles — in
  which case fall back to option (b) of the reconciliation (keep `trace_witness_act`, add a
  frame-origin companion + adapter), reporting why.

The four-rule shape above is the readability bar: `program_base`, `enter_frame`, `intra`,
`combine`, one origin pair, no datatype, no predicate parameter. If the implementation cannot
stay within it, that is a stop-and-report signal, not a licence to grow the definition.
