# Migration — reaching-definition global reads (writer re-keying + digest-indexed reader)

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` path discussed in this migration has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

> **RETIRED — the reaching-definitions digest family was removed from the tree (commit
> `92739cf`).** It was a demonstration-only instance, off the value-derived thesis. The
> generic `obs_digest` kernel survives (the mode family uses it); the RD instance section of
> `Digest_Global_Read`, `Reaching_Defs`, `RD_Set_Edge_Backbone`, the `Exec_Sign_RD_Keyed_*`
> witnesses, and `Example_Config_Mode_Digest_Precision` are gone. This whole document is
> historical: the constants it names no longer exist. Kept for provenance of the reader
> soundness argument.

> **Status: CMP_SOUND CLOSED — migration proof spine complete.** The generic read
> interface (`digest_global_read`, `obs_digest`), its kernel-over-interface theorems,
> the RD instance (may-def + kill routes), the semantic path reader, and an
> executable-and-sound concrete example all land as additive theories; the existing
> `side_env_cmp` spine, generator, and executable transport are untouched. The last
> recurring open premise — `CMP_SOUND` — is now discharged **generically** for the RD
> reader (`rd_obs_cmp_sound_from_incl`): at a global it reduces to `Inl`-bot-on-globals
> plus a reaching-set inclusion, independent of any solved solution. Every collecting
> theorem has a `CMP_SOUND`-free variant (`reaching_def_collect_sound_bot_incl`,
> `reaching_def_collect_sound_paths_incl`), and the concrete witness
> `rd_collect_sound_witness` routes through it. This supersedes the switching-combine
> abstract-bound route (`rd_switching_combine_le`): read soundness no longer needs to
> match a strategy-tree's single-key write to the set-valued read.
>
> **Read-soundness spine complete (both inclusions discharged).** Both per-combine
> reader inclusions now reduce to interprocedural-summary `RUN` premises of equal
> maturity: the return inclusion (`reach_paths_return_incl`) to a no-kill callee run,
> and the callee-exit inclusion (`reach_paths_CALLEE_incl`) to its dual — a must-write
> callee run with a matching caller. The must-write half is irreducible (the fixed
> `d0`-seed leaves a stale def under a non-writing callee), proven via
> `path_def_key_write_seed_indep` / `path_rd_key_write_absorb`. What remains is **not**
> a read-soundness, kernel, or reader obligation: it is the concrete interprocedural
> summary that supplies the two `RUN` witnesses (§12, "Interprocedural RD computation").
> The concrete example is already fully closed — `Exec_Sign_RD_Keyed_Run` (sound) +
> `Exec_Sign_RD_Keyed_Solve` (executable) analyze it context-sensitively and provably.
>
> **Semantic reader: complete modulo two named per-instance facts.**
> `reaching_def_collect_sound_paths_mustwrite` is the path-backed collecting theorem with
> **no reach obligation**: `CALLEE_INCL` is discharged in-place from the generic decidable
> CFG summary `must_write_to` and the per-digest contract `combine_backward_realizable`
> (`REAL`, named, proven consistent via `combine_backward_realizable_vacuous`). So the
> read-soundness spine holds **modulo exactly** those two — no `CMP_SOUND`, no reach
> inclusion, no monotone reader.
> Every claim is tagged
> **[proven]** (batch-checked in the tree), **[validated]** (eval or REPL-local this
> session), or **[conjectured]** (reasoned, not yet checked).
>
> **Architecture validated (this session).** A theorem-shape audit confirmed the
> interface is sufficient, with two corrections now folded in: (i) the *read*
> interface needs only `reader_digest` + `compatible` (+ `finite 'g`) — `writer_key`
> is a generator-layer parameter, not a kernel-read one; (ii) the point-dependent
> reader adds exactly one per-combine obligation, `READER_INCL` (caller-node reader
> subset return-node reader), beside the existing `LOCAL_POST` / `CMP_SOUND`. No
> theorem is inexpressible through the interface.
>
> **Supersedes the reader-only version.** The earlier draft assumed a digest-indexed
> *reader* alone was the fix and modeled the reaching digest as a monotone union
> (may-def). That was wrong: proper reaching definitions have kill/gen, and the
> precision is already destroyed at *publication*, not at the read. See the executive
> summary at the end for the exact deltas.

Related: `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` (Fix A / A' / cstep probes),
`SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` (paper notation), `OPEN_PROBLEMS.md` P11,
`CFG_Collect_Trace.thy` (digest trace layer), `Trace_Analysis_Sound.thy`
(`digest_env_sound`).

---

## 1. Motivation

The kernel's `ENTER_MONO` cannot be discharged on the flat two-call program
(`Example_Finite_Sign_Context_Analysis`, `fctx_prog`):

```
f():   GH := G
main:  G := 0;   f();    -- call node 4
       G := 1;   f()     -- call node 7
```

**The precision loss is at publication, not at the read.** Under one call-only
context `GOther`, every write to `G` is published to the *same* global slot `Inr
GOther`, so the slot holds `SZero ⊔ SPos = SNonNeg` [proven: `fctx_GOther_slot_joins_G`].
Both writes are joined **at write time**. Once joined into one writer slot, **no
reader — however refined — can recover them.** The observation read
`side_env_cmp (=) σ (v,ctx) = σ(Inl(v,ctx)) ⊔ σ(Inr ctx)` then pins `G` to `SNonNeg`
at both call nodes [proven: `fctx_caller_read_G_imprecise`, `..._imprecise8`], and
`ENTER_MONO` fails.

This reframes the problem. A digest-indexed *reader* was necessary but **not
sufficient**: the writer key must change too, so that distinct definitions land in
distinct slots and there is something for the reader to select. Prior probes of
reader-only or local-read fixes:

- **retain / local-read (Fix A, A')** — insufficient: retain re-injects the joined
  global slot at every non-writing edge, so even the local summand is `SNonNeg` where
  needed [validated].
- **`cstep` / intra-edge context update** — works, by refining the *context*
  (`GZero`/`GPos`) so writes land in separate per-context slots
  [proven: `fctxu_caller_read_G4_exact`, `fctxu_fGZero_GH_zero`]. But it changes the
  context on ordinary edges, contradicting the paper's call-only model.

This document specifies the paper-faithful alternative: **re-key writers by definition
site and read through a reaching-definition digest**, with contexts kept call-only.

## 2. Current limitation (precise)

```
side_env_cmp gcmp σ (v, ctx) = σ(Inl(v,ctx)) ⊔ glob_env_cmp gcmp ctx σ
```
(`Global_Cmp_Read.thy:70`). Two independent facts combine:

1. **Writer side.** The generator tags every global contribution with `gkey ctx`
   (`Exec_Cmp_Bridge`, `map_gtree (λ_. gkey c)`), so all writes under one context
   share one global key `Inr ctx`. They are **joined at publication** — flow-insensitively.
2. **Reader side.** `glob_env_cmp gcmp ctx σ` filters by `ctx` **only**, never by the
   program point `v` (`:19`). Two points under one context read the identical global.

`'g` is already decoupled from `'c` (via `gkey`, `gcmp`); the only class constraint on
`'g` is `finite` [proven]. So the limitation is **not** `'g = ctx` per se — it is that
the writer key is *too coarse* (one slot per context, joined at write time) **and** the
reader filter is context-only. Fixing the reader without splitting the writer key
changes nothing, because the join has already happened.

## 3. Why `cstep` is unnecessary — and non-faithful

The paper (Seidl/Vojdani/Erhard/Schwarz, "Mixed Flow-Sensitive Static Analysis:
Engineering Modularity", FM 2026), per `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md`:

- **Contexts are call-only.** A non-call edge keeps the same context (doc lines
  116–119). `cstep` changes `c` on ordinary edges → contradicts the paper [proven,
  from the doc's rendering]. Goblint computes `context : D.t → C.t` only at calls.
- **Precision comes from digests on the global.** "Global reads may use a
  compatibility relation on digests, so a reader with digest `a` only joins global
  components whose writer digest is compatible with `a`" (doc lines 160–163). Listed
  digests include **"global modification counts"** and **trace/def partitions** (lines
  165–173).

`cstep` and the digest achieve the *same* separation (`GZero`/`GPos` vs `Inr d1`/`Inr
d3`); the digest keeps contexts call-only, so it is the faithful carrier. `cstep`
becomes a fallback for precision no digest can express.

## 4. Relation to Goblint

Goblint's public interface is `context : D.t → C.t` (call-only) plus a global store `G`
whose reads are refined by digests. Our `Inl`/`Inr` split is the `D`/`G` split. A
definition-site (or mod-count) digest on `G` is exactly the flow-sensitive refinement
of a nominally flow-insensitive global that Goblint performs to recover cross-write
precision — transported here.

## 5. Relation to the TD paper

| paper | here | status |
| --- | --- | --- |
| call-only context, `context d c` at calls | `context_domain`, `route = ctx_sel ∘ prep` | [proven] present |
| digest-refined domain `D[x]^A = A → D[x]` | `cfg_collect_ctx dg cmp`, `digest_env_sound envd :: pp⇒'d⇒state` | [proven] semantic layer present |
| compatible global read (reader digest `a` joins writer-compatible components) | **read interface present** — `obs_digest` (point-dependent filter) with kernel soundness; `side_env_cmp` is its degenerate `ctx` instance | [proven] `Digest_Global_Read.thy` |
| writer digest tags on global contributions | **not present** — writes keyed by `gkey ctx`, joined per context | staged (generator, B1) |
| "global modification counts" / def-partition digest | not instantiated; `head_digest` too weak (per-activation constant, `Sound.thy:421`) | [validated] gap |

The semantic contract is done; the missing pieces are **both** solver-level writer
re-keying **and** a digest-indexed read (`SEIDL_2026` doc line 253 flags "solver-level
digest-indexed globals remain staged").

## 6. Design — a generic digest interface (RD as first instance)

Two coordinated changes; **both are required.** A reader change alone reads a
pre-joined slot; a writer change alone has no reader that selects the right slot. But
neither should hard-code reaching definitions. Reaching definitions are **one**
digest; the paper lists several (mod-counts, thread mode, locksets). So the kernel is
parameterized over a **digest interface**, proved once, and each analysis instantiates
it.

**The interface (locale, landed in `Digest_Global_Read.thy`).** The *read* interface
fixes only `reader_digest` and `compatible`; `finite 'g` is carried as a sort on the
key type, the sole kernel assumption. `writer_key` is **not** a read-interface
parameter — no read or soundness theorem mentions it (validated: `obs_digest`
expands to `reader_digest`/`compatible` only); it lives on the *write*/generator side
(§ B1), supplied per instance.
```isabelle
locale digest_global_read =
  fixes reader_digest :: "pp ⇒ 'c ⇒ 'd"           -- the reader's digest at a program point
    and compatible    :: "'d ⇒ 'g::finite ⇒ bool"  -- reader accepts writer key?
```
Generator side (per instance, not in the kernel locale):
```isabelle
writer_key :: "pp ⇒ vname ⇒ 'g"   -- tag a global write at (pp, var) with a writer key
```

**The generic read** (replaces `side_env_cmp`):
```isabelle
obs_digest σ (v, ctx)
   = σ (Inl (v, ctx))  ⊔  ⨆ { σ (Inr g) | compatible (reader_digest v ctx) g }
```
i.e. `σ(Inl(v,ctx)) ⊔ glob_env_cmp (λ_ g. compatible (reader_digest v ctx) g) ctx σ`.
Only `glob_env_cmp`'s filter argument changes; `glob_env_cmp` is reused unchanged — its
filter argument is already free (`Global_Cmp_Read.thy:19`) [proven]. `obs_digest`
strictly generalizes `side_env_cmp`: with `reader_digest v ctx = ctx`,
`compatible = gcmp`, the two coincide [proven: `obs_digest_collapse_shape`].

**The generic write.** The generator tags each global contribution at a write node by
`writer_key pp var` instead of the current `gkey ctx`, so distinct writes land in
distinct slots `Inr g` — joined only if a reader's `compatible` accepts several.

**Proved once over the interface** (analysis-independent, now landed): the COMB split
(`combine_case_obs_sound`, byte-identical to the `ctx` version), the `CMP_SOUND`
reduction (`combine_read_obs_le`), the read-agnostic trace backbone reused verbatim
(`post_fixpoint_sound_obs_digest` is a one-line instantiation of
`post_fixpoint_sound_at_ctx_semantic_generic`), and the collecting wiring (§9).
**Proved per instance**: `writer_key` tagging, `reader_digest`, and its soundness
(§ "reader_digest soundness" below), plus the per-combine `READER_INCL` inclusion.

**Instantiations.**

| instance | `'g` | `'d` | `compatible d g` | reader-digest soundness obligation |
| --- | --- | --- | --- | --- |
| **reaching definitions** (first) | `def_site` | `def_site set` | `g ∈ d` | `reader_digest v ctx` ⊇ all defs that may reach `(v,ctx)` (interprocedural, §8) |
| modification counts | `nat` | `nat` | `g ≤ d` (or `g = d` exact) | reader count bounds every writer's count reaching the point |
| thread mode | `thread_mode` | `thread_mode` | `ST↦{ST}`, `MT↦{ST,MT}` | an `ST` reader needs no `MT` write |
| locksets | `lockset` | `lockset` | `compatible_locksets d g` | only lockset-compatible writes affect the read |
| **current read (degenerate)** | `ctx` | `ctx` | `gcmp` | `reader_digest v ctx = ctx` — recovers `side_env_cmp` [validated: `obs_digest_collapse`] |

The current context-only read is the instance `writer_key _ _ = ctx`, `reader_digest v
ctx = ctx`, `compatible = gcmp` — so `obs_digest` strictly generalizes `side_env_cmp`.

Interactions (instance-independent unless noted):
- **`route_read_cmp`** (R_read) — the routing read becomes digest-indexed too, so the
  callee context is routed from the exact per-point global. Context still computed at
  the call (call-only) [conjectured].
- **`context_domain`** — unchanged; the digest is orthogonal to the context.
- **`'g`** — abstract, only `finite`. No new class constraint.
- **retain** — still holds the flow-sensitive local summand at def nodes; the digest
  refines the global summand. Complementary (`D` + `G`).

For the RD instance, `reader_digest` is **not** monotone: a proper kill (§8) drops a
definition when a later one overwrites it. The earlier "monotone-union / `DELTA_CALL`
monotonicity" framing was an artifact of the may-def model and is discarded (§ Removed).
Other instances (mod-count `≤`, thread mode) *are* monotone; monotonicity is an
instance property, not a kernel requirement.

## 7. Running example — writer re-keying in action

```
main:  G := 0;   (d1)      f();   -- call node 4
       G := 1;   (d3, kills d1)   f()    -- call node 7
```

**Current (writers keyed by context).**
```
Inr(GOther) = SZero ⊔ SPos = SNonNeg     -- both writes, one slot, joined at publication
read at node 4:  ... ⊔ Inr(GOther) = SNonNeg
read at node 7:  ... ⊔ Inr(GOther) = SNonNeg
```

**New (writers keyed by def-site, reader by RD).**
```
Inr(d1) = SZero        Inr(d3) = SPos        -- separate slots, no join at write time
δ(node 4) = RD(G, node 4) = {d1}     ⇒  read = Inr(d1) = SZero
δ(node 7) = RD(G, node 7) = {d3}     ⇒  read = Inr(d3) = SPos     (d3 killed d1)
```

**Both reads exact, contexts unchanged.** Node 4 and node 7 are *distinct program
points* in the single `main` activation, so a flow-sensitive `δ(pp)` separates them
under one call-only context. No context refinement, no `cstep`. This is precisely what
makes `ENTER_MONO` provable: the caller observation of `G` is now exact at each call
node, and the routing to `f`'s context (already exact — `fctx_route_call4 = GZero`,
`fctx_route_call8 = GPos`) becomes sound.

(f's *internal* read `GH := G` is one pp reached from both call sites; under monovariant
it still carries `RD = {d1,d3}`. Its precision comes from the *routed* context — which
becomes usable once `ENTER_MONO` holds — not from `δ(pp)`. RD-digest fixes the
distinct-pp caller reads; routed context handles the shared-pp callee read. They
compose.)

## 8. Interprocedural reaching definitions

A per-point `δ` must be computed with proper kill/gen, and calls must be treated as
possible definitions of the globals the callee writes. Naive *intra*-procedural RD is
unsound.

**Definitions.**
- **gen(n)** — the definitions created at node `n` (an assignment `G := e` gens its own
  def-site).
- **kill(n)** — for a must-overwrite `G := e`, all other defs of `G` (same variable) are
  killed.
- `RD(out, n) = gen(n) ∪ (RD(in, n) \ kill(n))`; `RD(in, n) = ⋃ RD(out, p)` over
  predecessors `p`. Standard flow-sensitive dataflow.

**Procedure summaries.** For each procedure `f` and global `G`:
- `may_write(f, G)` — some path through `f` (incl. its callees) writes `G`.
- `must_write(f, G)` — every path through `f` writes `G`.
- `exit_defs(f, G)` — the def-sites of `G` live at `f`'s exit.

**Call gen/kill (interprocedural).** At a call `f()` at node `n`, for each global `G`:
- `must_write(f, G)`  → **kill** the caller's incoming defs of `G`, **gen**
  `exit_defs(f, G)`.
- `may_write(f, G)` (not must) → **gen** `exit_defs(f, G)` **without kill** (union —
  soundness under conditional callee writes).
- neither → pass through unchanged.

**Return propagation.** The callee's `exit_defs` for each written global flow to the
call's return site, so caller reads after the call see the callee's writes.

**Counterexample — why interprocedural is required.**
```
main:  G := 0;   (d1)      f();      GH := G     -- read here
f:     G := 1    (d2)
```
- *Naive intra RD:* ignores `f`, so `RD(G, GH:=G) = {d1}` → reads `SZero`. **Unsound**:
  the concrete value is `1` because `f` overwrote `G` [validated:
  `A_naive_misses_callee_write`, `A_naive_CMP_SOUND_fails`].
- *Interprocedural RD:* `f` `must_write`s `G`, so the call kills `d1` and gens `d2`;
  `RD(G, GH:=G) = {d2}` → reads `SPos`. **Sound** (exact) [validated:
  `A_CMP_SOUND_incl`, `A_callee_write_seen`].

## 9. Obligations — kernel (once) vs instance (per analysis)

Split by the interface (§6). Everything under **A** is proved **once** over
`digest_global_read` and reused by every instance; **B** is what a new analysis
supplies. The `obs_digest` COMB split, its `CMP_SOUND` reduction, and the RD-instance
inclusions are **[validated]** (REPL-local this session, `digest_reader_split_sketch.thy`);
nothing committed.

### A. Kernel — proved once over the interface

- **A3. `obs_digest` replacement.**
  - `obs_digest` generalizes `side_env_cmp` (degenerate instance `writer_key=ctx`,
    `reader_digest v ctx=ctx`, `compatible=gcmp`). — **mechanical** [validated:
    `obs_digest_collapse`].
  - `glob_env_cmp` mono/singleton/le reusable. — **[proven]** (filter arg free).
  - COMB split (`combine_read_obs_digest`, `combine_case_obs_digest_sound`,
    `combine_read_obs_digest_le`). — **[validated]**, one extra local-case premise (note).
- **A4. `ENTER_MONO` over `obs_digest`.** With an exact per-point `reader_digest` the
  enter observation is exact, so `entdg s` is compatible with the routed callee context.
  — **genuine new proof** (the point; unprovable under `side_env_cmp`).
- **A5. `CMP_SOUND` over `obs_digest`.** The COMB bound `combine_read_obs_le` splits
  pointwise on the variable class and reduces to three per-instance side conditions
  [proven: `combine_read_obs_le`]:
  - *global var* — `CMP_SOUND`: `obs_digest σ (ex, rt cl ctx (σ(Inl(cl,ctx)))) x ≤
    obs_digest σ (v,ctx) x` (Goblint read soundness), discharged per instance by B2;
  - *local var* — `LOCAL_POST` (caller local flows to return local), plus a discharge
    of the global summand at the local variable. **Two routes** [both proven]:
    1. `READER_INCL`: `{g. compatible (reader_digest cl ctx) g} ⊆ {g. compatible
       (reader_digest v ctx) g}` (caller-node reader ⊆ return-node reader), via
       `combine_read_obs_le` / `glob_env_cmp_filter_mono`. The `ctx` version gets this
       for free (filter is `ctx`-only, so `cl` and `v` share the summand). **But this
       route fails for proper kill-RD**: a callee must-write drops the caller's def at
       the return, so `reach cl ⊄ reach v`.
    2. `⊥-on-locals` (`inr_slot_locals_bot`): each global slot is `⊥` on local
       variables, so the filtered global read is `⊥` there (`glob_env_cmp_local_bot`)
       and the local case reduces to `LOCAL_POST` alone — **the reader is left
       unconstrained**. This is the kill-RD-compatible route, via
       `combine_read_obs_le_bot` → `..._final_bot` → `obs_digest_collect_ctx_sound_bot`.
       It is the one proper reaching definitions use.
- **A6. Collecting-soundness wiring.** Reuse `cfg_collect_ctx` /
  `context_collect_sound`. — **mechanical** [proven layer].

### B. Instance — supplied per analysis (RD is the first)

- **B1. Writer tagging (`writer_key`) + transport.** Reshape the generator write-tagging
  (`map_gtree (λ_. writer_key pp var)`) and its `Exec_Cmp_Bridge` zip-relation
  transport. `finite (UNIV::'g set)` for the finite-key discharge. — **mechanical,
  sizable** (metis/simp-heavy bridge; build-timeout risk).
- **B2. `reader_digest` soundness.** `reader_digest v ctx` accepts every writer key that
  may reach `(v,ctx)`. For the **RD instance**: `reader_digest v ctx` ⊇ all def-sites
  reaching `(v,ctx)` with §8 interprocedural kill/gen — **genuine new proof,
  interprocedural**, the load-bearing per-instance obligation. (For mod-count: reader
  count bounds every reaching writer's count. For thread mode: an `ST` reader excludes
  `MT` writes.) The trace layer (`reaching_compat`, `trace_witness_d`) is already
  interprocedural and sound [proven]; the new content is the static per-point projection.

*Note (local-case premise).* Because `reader_digest` depends on the program point, the
shared-global cancellation of the `side_env_cmp` local case no longer holds; the split
carries `READER_INCL`, a caller→return reader inclusion at local variables. This is
**not** a monotonicity requirement (the discarded framing); the kernel discharges it
generically from the inclusion via `glob_env_cmp_filter_mono` [proven:
`combine_read_obs_le`], and each instance supplies the inclusion from its `reader_digest`
soundness (return node's reader accepts what flows through the call) or the
global-slots-⊤-on-locals invariant. Tracked under B2/A5, not a separate obstacle.

## 10. Comparison

| | Current | New (RD instance) |
| --- | --- | --- |
| global key `'g` | `ctx` | `def_site` (abstract `'g` in general) |
| global slot granularity | one per context | one per definition |
| when writes are joined | **at write time** (publication) | **at read time**, only through `δ` (RD) |
| reader filter | `gcmp ctx` (context only) | `dcmp (δ v ctx)` (reaching defs at the point) |
| flat example read | `SNonNeg` at both calls | `SZero` at 4, `SPos` at 7 |
| contexts | call-only | call-only (unchanged) |
| kill/gen | none (join-all) | proper flow-sensitive + interprocedural |

## 11. Migration sequence

1. **[DONE — `Digest_Global_Read.thy`, batch-green]** Define the `digest_global_read`
   interface (`reader_digest`, `compatible`; `writer_key` is generator-side) and the
   generic `obs_digest`; prove it generalizes `side_env_cmp` (`obs_digest_collapse_shape`).
   `glob_env_cmp` reused unchanged. Purely additive: existing spine untouched. The
   degenerate ctx-reader instance closes the interface's instantiation gap and
   re-derives the existing keyed collecting theorem
   (`obs_digest_recovers_cmp_collect` = `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`,
   `READER_INCL` reflexive) — faithful subsumption, not merely shape-equality.
2. **[DONE — batch-green]** Kernel obligations over the interface: the COMB split
   (`combine_case_obs_sound`), the `CMP_SOUND`/`READER_INCL` reduction
   (`combine_read_obs_le`), the trace backbone (`post_fixpoint_sound_obs_digest`), the
   side-condition final theorem (`post_fixpoint_sound_obs_digest_final`), and the
   context-sliced collecting wrapper (`obs_digest_collect_ctx_sound`: `cfg_collect_ctx
   … ≤ obs_digest`). The routing `rt` stays a parameter, so a `context_domain`
   interpretation instantiates it with `context_domain.route` at the use site. **Not
   done (deferred):** a route-bound restatement inside `context_domain` as sugar —
   `obs_digest` is locale-bound to `digest_global_read`, so binding `rt := route`
   needs a combined `digest_global_read + context_domain` locale; a design decision,
   not a blocker (parameter instantiation already suffices).
3. **Instantiate reaching definitions** (§8): `'g = def_site`, `reader_digest v ctx =
   RD(G, v, ctx)` with interprocedural gen/kill; prove B2 (reader_digest soundness) by
   reusing `trace_witness_d` / `reaching_compat` [proven layer]. Discharge the flat,
   nested, and callee-writes compatibility inclusions. (The gate.)
   - **[SCAFFOLD DONE — kernel-only, I/Q-clean]** `Digest_Global_Read.thy` §"Reaching-
     definitions instance": `datatype def_site` (+ `finite`), `rd_compatible d g = g ∈ d`,
     the reader `rd_obs reach = obs_digest reach rd_compatible`, and
     `reaching_def_collect_sound` — the RD-instance collecting theorem. The abstract
     `READER_INCL` premise is reduced (`rd_reader_incl_iff`) to the reaching-def **return
     inclusion** `reach cl ctx ⊆ reach v ctx`, the sole σ-independent per-instance
     obligation. This isolates the two remaining pieces cleanly:
     - the interprocedural RD dataflow (§8 gen/kill) that establishes `RD_RETURN_INCL` —
       a new dataflow formalization, still to build;
     - `CMP_SOUND`, retained verbatim as a post-solution assumption, dischargeable only
       once the generator keys writers by def-site (step 4, B1).
   - **[KILL-COMPATIBLE VERSION DONE — kernel-only, I/Q-clean]** The `RD_RETURN_INCL`
     premise is *too strong for proper kill-RD* (a callee must-write drops the caller's
     def at the return, so `reach cl ⊄ reach v`). Fixed by discharging the local-case
     obligation from the `inr_slot_locals_bot` invariant instead: new kernel chain
     `glob_env_cmp_local_bot` → `combine_read_obs_le_bot` → `..._final_bot` →
     `obs_digest_collect_ctx_sound_bot`, and the RD instance
     `reaching_def_collect_sound_bot` with **`reach` unconstrained**. Its only
     obligations are `GLOB_BOT` (program-independent solution invariant) and
     `CMP_SOUND` (the B1 residue). So the RD reader no longer needs any dataflow
     inclusion — only the def-site-keyed solution (B1) remains for a complete instance.
   - **[SEMANTIC READER (B2.1) DONE — trace-layer, I/Q-clean]** `reach` is realised
     concretely as `reach_sem rd_of dg cmp g S v ctx = ⋃ (rd_of \` reaching_compat dg
     cmp ctx g S v)` — the union of per-trace live def-sites over the digest-compatible
     reaching traces, the tightest sound reader. `reach_sem_admits` is soundness by
     construction; `reach_sem_return_incl` reduces the may-def inclusion to a
     per-combine trace-extension (`NOKILL`) condition; `reaching_def_collect_sound_sem`
     is the end-to-end collecting theorem with the reader *concretely defined* and only
     `NOKILL` + `CMP_SOUND` left. The per-trace def-site map `rd_of` stays abstract
     (its tagging to concrete CFG assignments is the next B2 slice).
   - **[STRUCTURAL NOKILL (B2.2) DONE — trace-layer, I/Q-clean]**
     `reach_sem_NOKILL_via_combine` discharges `NOKILL` through the real combine trace:
     a caller trace extends to `tau @ tl rho @ [<last tau|last rho>]` reaching `v`
     (`trace_witness_combineI`), whose digest equals `dg tau` (`DG_RETURN`), so a
     compatible caller trace stays compatible at the return. `NOKILL` thereby collapses
     to a local per-combine `rd_of`-preservation fact (the callee run reaching `ex` from
     the caller's last store does not drop the caller's live def-sites) — must-kill
     breaks exactly that inclusion, routing such combines to the `bot` theorem.
   - **[CONCRETE PATH-LEVEL RD (B2.3) DONE — new theory `Reaching_Defs.thy`, I/Q-clean]**
     A def-site is an assignment edge's target `pp`; along a single CFG path
     (`(edge_action × pp)` step list) the last writer wins, so `path_def x d0 es` folds
     the reaching def of `x` (seeded by the incoming `d0`), and `path_rd = set_option ∘
     path_def` is the concrete `pp`-set-valued reader (`'g = pp`). `path_def_no_kill` /
     `path_rd_no_kill_pres`: a callee sub-path not writing `x` preserves the caller's
     reaching def — the concrete discharge of the `CALLEE` preservation. `path_def_gen`
     witnesses last-writer semantics. **Remaining:** the trace↔path bridge tying
     `path_rd` (over paths) to `rd_of` (over the store-trace collecting), then the
     interprocedural summary (`may_write`/`must_write`) selecting no-kill vs `bot`.
   - **[BRIDGE CONTRACT (B2.4) DONE — `Reaching_Defs.thy`, I/Q-clean]**
     `path_realized_callee_pres` transfers `path_rd`'s no-kill to any *path-realized*
     `rd_of` (value on a trace = `path_rd` on a corresponding path);
     `reach_sem_CALLEE_via_path` then produces the exact trace-level `CALLEE` premise of
     `reach_sem_NOKILL_via_combine` from a per-caller-trace *path-realized non-writing
     callee run*. The full may-def RD chain now composes:
     `reaching_def_collect_sound_sem` ← `reach_sem_NOKILL_via_combine` ←
     `reach_sem_CALLEE_via_path` ← `path_rd_no_kill_pres`. **Sole remaining obligation:**
     the `RUN` witness — constructing the path-carrying callee run (a paired
     trace/path witness) from the interprocedural summary — plus `CMP_SOUND` (B1).
   - **[PATH-CARRYING WITNESS (B2.5) DONE — `Reaching_Defs.thy`, I/Q-clean]**
     `tp_witness g S v tr es` pairs a witnessed store trace with a generating CFG path,
     mirroring `trace_witness` and threading the `(edge_action × pp)` path (edges append
     their step; a combine composes `es_c @ es_r`). Sound (`tp_witness_trace`, projects
     to `trace_witness`) and complete (`tp_witness_exists`, every witnessed trace has a
     path — so a path-backed reader is total). `tp_witness_combine_rd_pres` carries the
     interprocedural no-kill entirely at the witness level: a combine composes
     caller⌢callee paths and preserves the caller's reaching def when the callee path
     does not write `x`.
   - **[RUN WIRING (B2.6) DONE — `Reaching_Defs.thy`, I/Q-clean]**
     `reach_paths_sem` is the endpoint-aware union over path witnesses. It keys writer
     sites through `path_def_key` / `path_rd_key` (`pp ⇒ 'g::finite`), so the concrete
     path reader fits the finite-key `rd_obs` interface without pretending raw `pp`
     (`nat`) is finite. `reach_paths_return_incl` discharges the return reader
     inclusion from a path-carrying non-writing callee run, and
     `reaching_def_collect_sound_paths` instantiates the generic RD collecting theorem
     with that reader. **CMP_SOUND now discharged:** `reaching_def_collect_sound_paths_incl`
     routes the path-backed reader through `reaching_def_collect_sound_bot_incl`, replacing
     the abstract-value `CMP_SOUND` premise with `INL_GLOB_BOT` (solution invariant) plus
     `CALLEE_INCL` (`reach_paths_sem ex … ⊆ reach_paths_sem v …`, a pure dataflow fact).
   - **[CALLEE_INCL DISCHARGE (B2.7) DONE — `Reaching_Defs.thy`, batch-green]**
     `reach_paths_CALLEE_incl` discharges `CALLEE_INCL` as the **dual** of
     `reach_paths_return_incl`. Where the return inclusion carries the *caller's* def
     across a *non-writing* (no-kill) callee, this carries the *callee-exit* read to the
     return across a callee that *must-write* `x`. The must-write is essential, not an
     artifact of laziness: `reach_paths_sem` seeds every read at the fixed global `d0`, so
     a non-writing callee leaves `d0` in the callee-exit read while the return read already
     holds the caller's real def — the two disagree unless the callee's own last write
     kills `d0`. That collapse is `path_rd_key_write_absorb` (from the new
     `path_def_key_write_seed_indep`: a *writing* path is seed-independent, the exact dual
     of `path_def_key_no_kill`). **Consequence:** `CALLEE_INCL` is **not** unconditionally
     derivable from the path machinery; it reduces to a per-combine *must-write callee run
     with a matching caller* (a `RUN` premise), the precise dual of the no-kill `RUN` the
     return inclusion consumes. This lands the obligation at the same maturity as the
     caller side — both are interprocedural summary premises, neither weakens
     `reaching_def_collect_sound_paths_incl` (whose `CALLEE_INCL` premise is intact;
     `reach_paths_CALLEE_incl` sits beside it as the discharge route, mirroring how
     `reach_paths_return_incl` sits beside `reaching_def_collect_sound_paths`).
     **Left (interprocedural summary, not read-soundness):** the `RUN` witness itself —
     that every digest-compatible must-writing callee run reaching `ex` extends backward
     to a compatible caller trace reaching `cl` (a reachability/summary fact about the
     concrete CFG, not a kernel or reader obligation).
   - **[RUN DISCHARGE DETERMINED (B2.8) DONE — `Reaching_Defs.thy`, batch-green]**
     *Determination of how the remaining `RUN` obligations discharge generically.* The
     callee-exit `RUN` factors into **two independent layers** with different homes:
     - **Must-write summary (`must_write_to`)** — the syntactic `writes_var x es_r`
       conjunct. A pure CFG-path predicate (*every* path witnessing `ex` writes `x`); it
       names neither the digest, the context, nor the abstract domain. This is the classic
       interprocedural must-write bit, computed once per `(ex, x)` over the callee sub-CFG
       — the **generic, instance-independent** half.
     - **Backward realizability (`REAL`)** — the caller-existence conjunct. **Not** a path
       property: it is the interprocedural contract on the digest/routing triple
       `(dg, cmp, rt)`, the converse of the forward `DG_CALLEE`/`ENTER_MONO` direction the
       collecting theorem already carries. It is discharged **per digest instance**, where
       the calling-context encoding lives; it cannot be a once-and-for-all path lemma.

     `reach_paths_CALLEE_incl_via_mustwrite` machine-checks this decomposition:
     `CALLEE_INCL ⟸ must_write_to ∧ REAL`. The no-kill `RUN` factors dually (a
     *may-not-write* summary plus *forward* realizability, which `DG_CALLEE`/`ENTER_MONO`
     already largely supply). **Conclusion:** the residual is not one obligation but two of
     distinct character — a generic decidable CFG summary (`must_write_to`, dischargeable
     by dataflow on any concrete callee) and a per-digest realizability contract (`REAL`,
     the home of "where the summary fixpoint lives"). Neither is a read-soundness, kernel,
     or reader obligation.
   - **[REAL NAMED + THREADED (B2.9) DONE — `Reaching_Defs.thy`, batch-green]**
     `REAL` is now a **named predicate** `combine_backward_realizable g S dg cmp cl ctx ex
     ctx2`: every digest-compatible callee run reaching `ex` at the routed `ctx2` has a
     compatible caller trace reaching `cl` at `ctx` with matching entry store.
     `reach_paths_CALLEE_incl_via_mustwrite` is restated over it (`CALLEE_INCL ⟸
     must_write_to ∧ combine_backward_realizable`). The contract is proven **consistent** —
     `combine_backward_realizable_vacuous` (empty compatible-callee case); a non-vacuous
     discharge needs a concrete digest whose routed context is reachable only through the
     call. The top-level **`reaching_def_collect_sound_paths_mustwrite`** carries the whole
     decomposition: the path-backed reader's collecting soundness with **no reach obligation
     at all**, `CALLEE_INCL` discharged in-place from per-combine `must_write_to` + `REAL`.
     So **read soundness of the semantic path reader is complete modulo exactly two named
     per-instance facts** — `must_write_to` (decidable CFG summary) and
     `combine_backward_realizable` (per-digest contract). *Concrete witness:* the abstract
     `rd_reach` witness (`rd_collect_sound_witness`) discharges `CALLEE_INCL` directly at the
     abstract-reach level and never ranges over `reach_paths_sem`, so `REAL` does not apply
     to it; exhibiting `REAL` non-vacuously requires a concrete `reach_paths_sem` CFG
     (procedure, combine, `tp_witness` paths) — a construction, not a proof gap.
   - **[B1 scaffold — REMOVED. The site-keyed writer generator, the return-aware
     transport, and the def-site `rd_switching_combine` emitter described in the bullets
     below were proven and batch-green, but never consumed: no witness or example drives
     the solver through them, and the RD family is demonstrated reader-side only against a
     hand-built equation system. Deleted in commits `f455d93` (RD emitter + `cmp_site_ret`)
     and `964ea1a` (`cmp_site` writer family). The following text is retained for
     provenance; the named constants no longer exist in the tree.]**
     `side_cfg_T_eff_cmp_site` / `side_cfg_T_eff_cmp_site_st` are the abstract and
     executable writer-keyed generator shapes: intra-edge `Side` contributions route
     to `site v`, the target program point's writer key, while local reads stay indexed
     by `(pp, ctx)`. This is the concrete generator object `reach_paths_sem` needs.
     `part_post_solution_cmp_site_st_to_abs_eff` transports an executable
     post-solution of that site-keyed generator to its abstract image. The existing
     switching-combine transport has a site-keyed variant,
     `part_post_solution_cmp_site_switching_st_to_abs_eff_unit_transfer`, but it is
     necessarily typed with `site :: pp ⇒ 'c` because `switching_combine_st` itself
     still emits context-keyed `Side` nodes. **Left:** add the RD-keyed combine tree
     variant or otherwise instantiate `CMP_SOUND`.
   - **[B1 scaffold — return-aware site transport present, I/Q-clean]**
     `side_cfg_T_eff_cmp_site_ret` / `side_cfg_T_eff_cmp_site_ret_st` extend the
     site-keyed generator with the equation endpoint passed into `cmb`. This is the
     missing generic hook for combine-side writer routing: an RD instance can now
     build combine trees whose `Side` nodes target the return point's writer key.
     `part_post_solution_cmp_site_ret_st_to_abs_eff` transports executable
     post-solutions for that return-aware generator. **Left:** choose and prove the
     concrete RD switching-combine routing (`QueryG` source key and `Side` target
     keys) so a *solved* generator solution keys writers by def-site.
   - **[CONCRETE CMP_SOUND DISCHARGE DONE — `Exec_Sign_RD_Keyed_Run.thy`, batch-green]**
     The `CMP_SOUND` residue is discharged as a post-solution fact for a concrete
     def-site-keyed witness over `sign`, mirroring `Exec_Sign_Cmp_Keyed_DG_Run` but
     keying globals on `def_site` and reading through `rd_obs`. The witness realises
     §7/§8's flat callee-writes program (call `4`, callee exit `5`, return `6`;
     `G:=0(DS1)` killed, `G:=1(DS3)` gen'd): a hand-exhibited solution `rd_sig`
     (slots `Inr DS1 ↦ SZero`, `Inr DS3 ↦ SPos`; `Inl` locals `SBot`-on-globals) and
     reader `rd_reach` (`4↦{DS1}`, `5/6↦{DS3}`). `CMP_SOUND_inst`, `LOCAL_POST_inst`,
     `GLOB_BOT_inst` discharge the three combine premises of
     `reaching_def_collect_sound_bot` in its exact shape, and
     `rd_collect_sound_witness` plugs them in — closing the RD-instance collecting
     soundness for this witness (the generic `ENTRY`/`EDGE`/digest-law/`ENTER_MONO`
     premises stay carried as the program-structural hypotheses). The precision payoff
     is machine-checked: `read_call4 = SZero`, `read_return6 = SPos`, context-blind
     join `= SNonNeg` (`points_separated`); `return_incl_fails` witnesses the kill
     (`{DS1} ⊄ {DS3}`), so the `bot`-on-locals route is the one used.
   - **[GENERIC `CMP_SOUND` DISCHARGE DONE — `Digest_Global_Read.thy`, I/Q-green]**
     `CMP_SOUND` is no longer a per-solution hand obligation. `rd_obs_cmp_sound_from_incl`
     proves it pointwise at every global from two facts that do *not* mention the solved
     solution: at a global `x` the `Inl` slot summand of `obs_digest` is `bot`
     (`inl_slot_globals_bot`), so the read collapses to the `rd_compatible`-filtered global
     join, and `glob_env_cmp_filter_mono` carries the callee-exit read below the return read
     from the reaching-set inclusion `reach ex (rt cl ctx …) ⊆ reach v ctx`.
     `reaching_def_collect_sound_bot_incl` wraps `reaching_def_collect_sound_bot`, replacing
     its `CMP_SOUND` premise with these two structural/dataflow premises (`INL_GLOB_BOT`,
     `CALLEE_INCL`). Unlike `RD_RETURN_INCL` in `reaching_def_collect_sound`, `CALLEE_INCL`
     needs no monotone (kill-free) reader — it is the exit-to-return inclusion, which the
     re-gen satisfies even when the caller inclusion fails under kill. The concrete witness
     `rd_collect_sound_witness` now routes through this generic theorem: `INL_GLOB_BOT_inst`
     + `CALLEE_INCL_inst` (`rd_reach 5 = {DS3} ⊆ {DS3} = rd_reach 6`, holding despite the
     `4↦{DS1}` kill) discharge the two premises, and the hand `CMP_SOUND_inst` is retired
     from the soundness path (kept only as standalone read-collapse evidence).
   - **[DEF-SITE SWITCHING COMBINE + TRANSPORT DONE — `Exec_Cmp_Bridge.thy`, batch-green]**
     `rd_switching_combine_st` / `rd_switching_combine_abs` are the def-site-keyed
     switching combines: the caller global is read at its own key `QueryG (site cc)`,
     the callee-entry globals published to `Side (site ex)`, the merged result to the
     return's key `Side (site ret)`; the context switch `ec cc ctx caller` stays
     call-only and indexes only the callee local slot, never a global key. `side_rg`
     plus the three `fun_of_st` bridges (`traverse`/`sides`/`dep`) hold, so
     `part_post_solution_rd_switching_st_to_abs_eff` transports an executable
     post-solution of the RD-keyed switching generator
     (`side_cfg_T_eff_cmp_site_ret_st site (rd_switching_combine_st …)`) to its abstract
     image. This is the generator that *emits* def-site-keyed `Side` nodes — the object
     `CMP_SOUND` is a post-solution property of. **Left:** the abstract soundness bound
     (`rd_switching_combine_le`, the `abs_switching_combine_le` analogue) tying a solved
     RD-keyed solution to `CMP_SOUND` at the set-valued `rd_obs` reader — the structural
     gap is that a strategy-tree node reads one key (`QueryG (site cc)`) while the reader
     joins a reaching *set*, so the bound must aggregate the def-site slots the generator
     writes across the callee's own intra edges. **Superseded:** with `CMP_SOUND`
     discharged generically (`rd_obs_cmp_sound_from_incl`, below), this abstract-bound
     route is no longer needed — read soundness reduces to `Inl`-bot + reach inclusion,
     not to matching the tree's single-key write against the set-valued read.
   - **[EXECUTABLE RD ANALYSIS DONE — `Exec_Sign_RD_Keyed_Solve.thy`, batch-green]**
     The example is now analysed *executably* by the verified solver. A def-site-routed
     side-effecting equation system (`rd_eqs`: `G:=0` sides to `Inr DS1`, `f`'s `G:=1`
     to `Inr DS3`) is solved by `TD_side_always_join_Interp_solve`; the code generator
     reads back separated slots (`slot_DS1 = SZero`, `slot_DS3 = SPos`, join-all
     `= SNonNeg`, `rd_slots_strictly_separate`), all `by eval`. The reaching-definition
     read runs on the solved environment: `glob_env_cmp` filtered by `rd_compatible`
     (the executable half of `rd_obs`) recovers `SZero` at reaching set `{DS1}`, `SPos`
     at `{DS3}`, `SNonNeg` at `{DS1,DS3}` (`rd_reads_point_sensitive`) — point-sensitive
     precision under one call-only context, sealed by the solver. Required an
     `instance def_site :: enum` (`Digest_Global_Read.thy`) so the filtered join
     code-generates. Together with `Exec_Sign_RD_Keyed_Run` (soundness) this is the
     executable-and-sound pair for the example, at parity with the ctx
     `Exec_Sign_Cmp_Keyed_DG_Run` precedent.
   - **[SITE EDGE POST-FIXPOINT BOUND DONE — `TD_Side_Eff_Cmp_Gen.thy`, batch-green]**
     `side_cfg_T_eff_cmp_site_edge_le` is the def-site-keyed analogue of
     `side_cfg_T_eff_cmp_edge_le`: at a `part_post_solution` of the site generator, each
     intra edge into `v` publishes to the single slot `Inr (site v)`, so the reassembled
     per-edge transfer read through `pull_gk (λ_. site v) ctx` sits below `σ(Inl(v,ctx)) ⊔
     σ(Inr(site v))`. Proved by mirroring the cmp bound with keyer `(λ_. site v)`; the two
     helpers `sides_fold_le_side_cfg_T_eff_cmp_site` / `side_post_solution_le_global_site`
     are the site instances of their cmp counterparts. This is the algebraic groundwork the
     ENTRY/EDGE discharge would compose on the *writing* edges (where `site v` **is** the
     reaching def).
   - **[ENTRY/EDGE DISCHARGE FOR RD — determined research-grade, not a port]** Discharging
     the collecting theorem's `ENTRY`/`EDGE` (over `rd_obs`) from a solved site solution is
     **not** the mechanical port the single-slot cmp closure was. The obstruction is precise
     and structural: the site edge bound pulls the *target's own* slot `Inr(site v)`, whereas
     `rd_obs` at the *source* admits the reaching **set** `⨆{σ(Inr g) | g ∈ reach u ctx}`. A
     global-*reading* edge (`x := G`) needs the abstract transfer to run over the
     reaching-set-merged state, not a single slot — **set-merged transfer soundness that does
     not exist**. This is the same set-vs-single-key wall the `CMP_SOUND` note above hit, but
     on the *per-edge* transfer, where `rd_obs_cmp_sound_from_incl` does **not** apply (that
     reduction is combine-only). Consequence: even the concrete `rd_collect_sound_witness`
     *carries* ENTRY/EDGE. Closing them is a new soundness layer (the transfer over a
     reaching-set of global slots), not a mirror of an existing proof. The site edge bound
     above is the reusable piece toward it.
   - **[EDGE REDUCED TO A SET-READING-GENERATOR OBLIGATION — `RD_Set_Edge_Backbone.thy`, batch-green]**
     The gamma-level `EDGE` premise of `reaching_def_collect_sound_bot` is now *reduced*,
     not assumed. `rd_obs_edge_from_merged_bound` discharges one concrete edge step from a
     single abstract inequality (`MERGED_EDGE`): the effectful transfer, run on the
     reach-merged read at the source, sits below `rd_obs` at the target. The merge is
     `rd_merge_env` — the unit-global environment whose one `Inr` slot holds
     `⨆{σ(Inr g) | g ∈ reach u ctx}`; `side_env_rd_merge_env` proves reading it at the source
     *is* `rd_obs σ (u,ctx)`, so concrete step soundness comes free from the existing
     `edge_collect_etf_sound` and `gamma_state_mono` carries it across the edge.
     `reaching_def_collect_sound_bot_from_merged` packages it: RD collecting soundness holds
     given the per-edge family `MERGED_EDGE` in place of `EDGE`, reusing the theorem's own
     `GLOB_BOT` for the bot-on-locals side. This does **not** move the wall of the note above
     — it *names* it at the interface. An arbitrary `σ` cannot satisfy `MERGED_EDGE` (that is
     the non-additive-transfer / set-merge obstruction), so the residual is precisely the
     post-fixpoint of a **set-reading generator**: a strategy tree that `QueryG`-folds over
     `reach u ctx` instead of reading one keyed slot. That generator (definition, monotonicity,
     post-fixpoint edge bound) is the genuinely-new, multi-session construction; the backbone
     around it is now proven.
   - **[REDUCTION WIRED INTO THE CONCRETE RD WITNESS — `Exec_Sign_RD_Keyed_Run.thy`, batch-green]**
     The reduction is no longer a standalone brick. `reaching_def_collect_sound_bot_incl_from_merged`
     (`RD_Set_Edge_Backbone.thy`) is the reaching-set-inclusion spine variant: it derives the
     combine-side `CMP_SOUND` from the same two dataflow/structural facts (`INL_GLOB_BOT` +
     `CALLEE_INCL` via `rd_obs_cmp_sound_from_incl`) as `reaching_def_collect_sound_bot_incl`,
     but takes `MERGED_EDGE` on the per-edge side. `rd_collect_sound_witness_merged` is the
     concrete sign RD witness built on it: same proven instance facts (`LOCAL_POST_inst`,
     `GLOB_BOT_inst`, `INL_GLOB_BOT_inst`, `CALLEE_INCL_inst`), but the opaque gamma-level
     `EDGE` hypothesis is **replaced** by `MERGED_EDGE` + `sound_effectful_transfer etf`. So
     the RD example's per-edge obligation is now the checkable algebraic inequality, not a
     black-box step. What is **still open** and honestly stated: `MERGED_EDGE` remains a
     *hypothesis* of the merged witness — discharging it concretely on `rd_sig` needs an `etf`
     whose post-fixpoint `rd_sig` is, i.e. the set-reading generator above. `rd_sig` is
     hand-built for point reads and has no generator, so the merged witness proves the spine
     *consumes* the reduced premise; it does not manufacture the generator.
4. Only once (2)+(3) close: the RD instance's writer tagging (`writer_key pp var`) +
   transport, mirroring `part_post_solution_cmp_st_to_abs_eff`. — the sizable mechanical
   step (B1).
5. Retire `cstep`/`side_cfg_T_eff_cmp_ctxupd_st` to "fallback / non-Goblint
   experiment"; keep the `fctxu` prototype as precision evidence.
6. (Later, no kernel work.) Second instance to exercise genericity — mod-count or
   thread-mode — supplying only its `'g`/`'d`, tagging, and `compatible`/soundness.

## 12. Open questions

- **Interface shape.** Is `writer_key :: pp ⇒ vname ⇒ 'g` the right arity, or does a
  writer need the context / abstract value at the write (`pp ⇒ vname ⇒ 'c ⇒ 'a ⇒ 'g`)?
  RD needs only `pp`; mod-count needs history; locksets need the write-time lockset.
- **Exact choice of finite writer key (RD instance).** `def_site` (assignment id) vs a
  value-digest vs a bounded mod-count — minimal and finite for the sign examples, and
  how it code-generates.
- **Interprocedural RD computation.** Where the summary fixpoint lives — a static
  pre-pass producing `reader_digest`, or folded into the collecting layer.
- **Recursive / mutually recursive procedures.** RD sets over finitely many def-sites
  are a finite powerset lattice → terminates without widening; self-recursive callee
  summaries need their own fixpoint. Confirm finiteness end-to-end. (Other instances,
  e.g. mod-count, are the ones that genuinely need a finite abstraction / widening on
  `'d`.)
- **Interaction with widening.** Digest sets (RD) need no widening; an infinite *value*
  domain (intervals) still does; an infinite *digest* (raw mod-count) needs its own.
  Confirm the three do not entangle.
- **Executable transport.** The `Exec_Cmp_Bridge` write-tagging reshape is the largest
  mechanical surface (metis/simp blow-up risk per the build-timeout policy), and is
  per-instance (parameterized by `writer_key`).

---

## Evidence log (this session; REPL-local / eval; no theory changed)

| program | test | result |
| --- | --- | --- |
| flat `G:=0(d1);f();G:=1(d3);f()` | proper RD at calls 4/7 | `RD={d1}`/`RD={d3}` → `SZero`/`SPos` — **exact**, call-only [analysis; §7] |
| current writers, flat | `Inr GOther` slot | `SNonNeg` (joined at publication) [proven: `fctx_GOther_slot_joins_G`] |
| `cstep` writers, flat | `Inr GZero`/`Inr GPos` | `SZero`/`SPos` — exact, but context moved [proven: `fctxu_*`] |
| nested `main→f→g`, single write | RD at g's read | `{d2}` → `SPos` — **exact** [analysis; §8] |
| callee-writes `f{G:=1}; main{G:=0;f();GH:=G}` | *intra* RD | `{d1}`→`SZero` — **UNSOUND** (concrete `1`) [validated] |
| callee-writes, interprocedural RD | call kills `d1`, gens `d2` | `{d2}`→`SPos` — **sound** [validated: `A_CMP_SOUND_incl`] |
| `obs_digest` COMB split | `combine_read_obs_le`, `combine_case_obs_sound` | closed [proven: `Digest_Global_Read.thy`, batch-green] |
| trace backbone over `obs_digest` | `post_fixpoint_sound_obs_digest` | one-line instantiation of the read-agnostic backbone [proven] |
| side-condition final theorem | `post_fixpoint_sound_obs_digest_final` | reduces `COMB_SEM` to `LOCAL_POST`/`READER_INCL`/`CMP_SOUND` [proven] |
| collecting-layer wrapper | `obs_digest_collect_ctx_sound` | `cfg_collect_ctx … ≤ obs_digest`, keyed analogue of the cmp collecting theorem [proven] |
| degenerate read collapse | `obs_digest_ctx_reader_eq` | ctx-reader instance: `obs_digest (λv ctx. ctx) gcmp = side_env_cmp gcmp` [proven] |
| faithful subsumption | `obs_digest_recovers_cmp_collect` | re-derives `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` (identical statement) from the generic theorem; `READER_INCL` reflexive [proven] |
| RD reader `READER_INCL` reduction | `rd_reader_incl_iff` | `{g. g ∈ reach cl ctx} ⊆ {g. g ∈ reach v ctx}` ⟷ `reach cl ctx ⊆ reach v ctx` [proven] |
| RD-instance collecting soundness (may-def) | `reaching_def_collect_sound` | obligation isolated to `reach cl ctx ⊆ reach v ctx`; **monotone reach only** [proven scaffold] |
| filtered global read is ⊥ on locals | `glob_env_cmp_local_bot` | under `inr_slot_locals_bot`, `glob_env_cmp cmp ctx σ` is ⊥ at local vars, any filter [proven] |
| ⊥-on-locals combine/trace/collecting chain | `combine_read_obs_le_bot`, `..._final_bot`, `obs_digest_collect_ctx_sound_bot` | local case from ⊥-on-locals; reader unconstrained [proven] |
| RD-instance collecting soundness (kill) | `reaching_def_collect_sound_bot` | `reach` **unconstrained**; obligations only `GLOB_BOT` + `CMP_SOUND` — the proper kill-RD version [proven] |
| kill route necessity (witness) | `rd_kill_refutes_return_incl` | concrete `def_site` kill (`DS1`↦`DS3`) refutes `RD_RETURN_INCL`: caller set ⊄ return set, so the two RD routes are not interchangeable [proven] |
| semantic reader, sound by construction (B2.1) | `reach_sem`, `reach_sem_admits` | `reach = ⋃ rd_of` over `reaching_compat` admits every reaching-compatible trace's live def-sites [proven] |
| semantic may-def inclusion | `reach_sem_return_incl` | `RD_RETURN_INCL` for `reach_sem` reduces to per-combine trace extension (`NOKILL`) [proven] |
| end-to-end RD soundness, concrete reader | `reaching_def_collect_sound_sem` | collecting soundness with `reach_sem` baked in; obligations reduce to `NOKILL` + `CMP_SOUND` [proven] |
| structural NOKILL discharge (B2.2) | `reach_sem_NOKILL_via_combine` | via `trace_witness_combineI` + `DG_RETURN`: `NOKILL` collapses to a local per-combine `rd_of`-preservation across the return trace; must-kill breaks it (→ `bot` route) [proven] |
| concrete path-level reaching def (B2.3) | `path_def`, `path_rd` (`Reaching_Defs.thy`) | def-site = assign-edge target `pp`; last writer wins along a path; `'g = pp` [proven] |
| concrete no-kill preservation (B2.3) | `path_def_no_kill`, `path_rd_no_kill_pres` | callee sub-path not writing `x` preserves the caller's reaching def — discharges `CALLEE` preservation concretely [proven] |
| last-writer gen witness (B2.3) | `path_def_gen` | an `EA_Assign x` step gens exactly its own def-site, killing prior defs [proven] |
| path→trace no-kill transfer (B2.4) | `path_realized_callee_pres` | a path-realized `rd_of` inherits `path_rd`'s no-kill across a non-writing callee [proven] |
| trace-level CALLEE from path run (B2.4) | `reach_sem_CALLEE_via_path` | produces `reach_sem_NOKILL_via_combine`'s `CALLEE` from a path-realized non-writing callee run; chain composes to `reaching_def_collect_sound_sem` [proven] |
| path-carrying witness, sound+complete (B2.5) | `tp_witness`, `tp_witness_trace`, `tp_witness_exists` | pairs a store trace with a generating CFG path; projects to `trace_witness`, and every witnessed trace has a path [proven] |
| interprocedural no-kill at witness level (B2.5) | `tp_witness_combine_rd_pres` | a combine composes caller⌢callee paths and preserves the caller's reaching def when the callee path does not write `x` [proven] |
| endpoint-aware path reader (B2.6) | `reach_paths_sem`, `reach_paths_return_incl`, `reaching_def_collect_sound_paths` | union over path witnesses at the read endpoint; finite-key path RD discharges `RD_RETURN_INCL` from the path-carrying RUN premise; leaves `CMP_SOUND` [proven] |
| site-keyed writer generator + transport (B1 scaffold) | ~~`side_cfg_T_eff_cmp_site`, `side_cfg_T_eff_cmp_site_st`, `part_post_solution_cmp_site_st_to_abs_eff`~~ | **REMOVED** — proven but never consumed; superseded by the digest writer (`Digest_Keyed_Writer`). Deleted in commit `964ea1a` |
| site-keyed switching transport (typed caveat) | ~~`part_post_solution_cmp_site_switching_st_to_abs_eff_unit_transfer`~~ | **REMOVED** — orphan capstone, sole consumer of the site-keyed transport; deleted in `964ea1a` |
| return-aware site transport (B1 scaffold) | ~~`side_cfg_T_eff_cmp_site_ret`, `side_cfg_T_eff_cmp_site_ret_st`, `part_post_solution_cmp_site_ret_st_to_abs_eff`~~ | **REMOVED** — "concrete RD combine routing" never landed; deleted in `f455d93` |
| concrete CMP_SOUND discharge, def-site-keyed witness | `CMP_SOUND_inst`, `LOCAL_POST_inst`, `GLOB_BOT_inst`, `rd_collect_sound_witness` (`Exec_Sign_RD_Keyed_Run.thy`) | flat §8 callee-writes program over `sign`: hand-exhibited def-site solution discharges the three combine premises of `reaching_def_collect_sound_bot` in exact shape and plugs them in; `CMP_SOUND` proven for the RD reader, not premised [proven, batch-green] |
| def-site RD precision payoff, machine-checked | `read_call4`, `read_return6`, `points_separated`, `merge_join_all`, `return_incl_fails` | reader separates points under one call-only context (`SZero` at call 4, `SPos` at return 6); context-blind join `= SNonNeg`; caller set `{DS1} ⊄ {DS3}` witnesses the kill [proven] |
| def-site switching combine + transport | ~~`rd_switching_combine_st`/`_abs`, `side_rg_rd_switching_combine_st`, `part_post_solution_rd_switching_st_to_abs_eff`~~ | **REMOVED** — the def-site emitter was proven but had zero live consumers; the RD family is demonstrated reader-side only. Deleted in `f455d93` |
| executable RD solve, def-site slots | `rd_eqs`, `rd_solution`, `slot_DS1`/`slot_DS3`/`slot_join_all`, `rd_slots_strictly_separate` (`Exec_Sign_RD_Keyed_Solve.thy`) | verified `TD_side_always_join_Interp_solve` computes separated def-site slots (`SZero`/`SPos`); join-all `= SNonNeg`; strict separation — all `by eval` [proven, batch-green] |
| executable RD read, point-sensitive | `rd_env`, `read_reach_DS1`/`read_reach_DS3`/`read_join_all`, `rd_reads_point_sensitive`; `instance def_site :: enum` | `glob_env_cmp` filtered by `rd_compatible` on the solved env recovers `SZero` at `{DS1}`, `SPos` at `{DS3}`, `SNonNeg` at `{DS1,DS3}`; point-sensitive under one call-only context, `by eval` [proven, batch-green] |
| `obs_digest` generalizes `side_env_cmp` | `obs_digest_collapse_shape` | degenerate `ctx`/`gcmp` instance [proven] |
| kernel finite-key gate | mod-count on raw `nat` | rejected: `No type arity nat :: finite`; needs a bounded key [proven] |
| generic CMP_SOUND at globals | `rd_obs_cmp_sound_from_incl` | at a global, `obs_digest`'s `Inl` summand is `bot`, so the read is the `rd_compatible`-filtered global join; `glob_env_cmp_filter_mono` carries the callee-exit read below the return read from `reach ex (rt cl ctx …) ⊆ reach v ctx` — no solved solution needed [proven, batch-green] |
| CMP_SOUND-free RD collecting theorem (kill route) | `reaching_def_collect_sound_bot_incl` | `reaching_def_collect_sound_bot` with `CMP_SOUND` replaced by `INL_GLOB_BOT` + `CALLEE_INCL` (exit→return reach inclusion); no monotone reader [proven, batch-green] |
| witness rerouted through generic discharge | `INL_GLOB_BOT_inst`, `CALLEE_INCL_inst`, `rd_collect_sound_witness` (`Exec_Sign_RD_Keyed_Run.thy`) | `rd_reach 5 = {DS3} ⊆ {DS3} = rd_reach 6` holds despite the `4↦{DS1}` kill; hand `CMP_SOUND_inst` retired from the soundness path [proven, batch-green] |
| CMP_SOUND-free semantic path reader | `reaching_def_collect_sound_paths_incl` | path-backed reader through `..._bot_incl`; `CMP_SOUND` → `CALLEE_INCL` over `reach_paths_sem` (pure dataflow) [proven, batch-green] |
| writing path is seed-independent | `path_def_key_write_seed_indep` | `writes_var x es ⟹ path_def_key x a site es = path_def_key x b site es` — last-writer wins, dual of `path_def_key_no_kill` [proven, batch-green] |
| write-absorb across a prepended caller path | `path_rd_key_write_absorb` | `writes_var x es_r ⟹ path_rd_key x d0 site (es_c @ es_r) = path_rd_key x d0 site es_r` — the callee's last write kills the caller contribution [proven, batch-green] |
| CALLEE_INCL discharge (dual of return incl) | `reach_paths_CALLEE_incl` | `reach_paths_sem ex ctx2 ⊆ reach_paths_sem v ctx` from a **must-write** callee run with a matching caller (`RUN`); NOT unconditional — the `d0`-seed makes a non-writing callee leave a stale def, so must-write is required [proven, batch-green] |
| generic must-write summary | `must_write_to` | pure CFG-path predicate (`∀ path to ex. writes_var x`); no digest/context/domain — the instance-independent half of the `RUN` [proven, batch-green] |
| RUN two-layer decomposition | `reach_paths_CALLEE_incl_via_mustwrite` | `CALLEE_INCL ⟸ must_write_to ∧ REAL`; separates the generic decidable CFG summary from the per-digest backward-realizability contract [proven, batch-green] |
| REAL named as a predicate | `combine_backward_realizable` | the per-digest backward-realizability contract (compatible callee run reaching `ex` ⟹ matching compatible caller reaching `cl`); isolates the single remaining per-instance obligation [proven, batch-green] |
| REAL contract is consistent | `combine_backward_realizable_vacuous` | holds vacuously when no compatible callee run reaches `ex` — the contract is satisfiable, not inconsistent [proven, batch-green] |
| semantic reader complete modulo REAL + must_write_to | `reaching_def_collect_sound_paths_mustwrite` | path-backed collecting soundness with **no reach obligation**; `CALLEE_INCL` discharged in-place from per-combine `must_write_to` + `combine_backward_realizable` [proven, batch-green] |
| recursion / mutual recursion | — | not probed [conjectured: finite def-site lattice, no widening] |

## Recommendation

**Pursue**, as the paper-faithful direction, structured as a **generic digest interface
proved once + reaching definitions as the first instance**. Gating obligations:

- **Kernel over the interface (A3–A6)** — the COMB split, `CMP_SOUND` reduction,
  `ENTER_MONO`; analysis-independent, reused by every future digest.
- **Writer re-keying** (per instance, `'g` abstract; `def_site` for RD) — without it the
  reader reads a pre-joined slot and no digest helps.
- **`reader_digest` soundness** (per instance; interprocedural RD with §8 kill/gen for
  the first one) — without it callee-modified globals are unsound (`A_naive_*`).

The paper evidence is decisive: digest-refined compatible global reads with call-only
contexts are the paper's own mechanism (§3, §5), and the paper lists several digests
(mod-counts, thread mode, locksets) — so a generic interface matches it better than
hard-coding `def_site`. The semantic layer is proven in-tree; the `obs_digest` split and
its `CMP_SOUND` reduction are validated REPL-local. `cstep` is demoted to fallback. Do
not start the writer-key generator/transport until the kernel (A) and the RD instance's
`reader_digest` soundness (B2) are sketched over `obs_digest` on the flat, nested, and
callee-writes examples.

---

## Executive summary — what changed vs the previous document

1. **Root cause moved from read to publication.** Old: "the observation read is
   indexed by context alone." New: precision is destroyed **at write time** — all
   writers under one context share `Inr ctx` and join to `SNonNeg` before any read
   (`fctx_GOther_slot_joins_G`). A reader change alone cannot help.
2. **Design is now two-part.** Old: reader-only digest refinement. New: **writer
   re-keying (`'g = ctx ↦ 'g = def_site`) + digest-indexed reader** — both required.
3. **δ is reaching definitions with kill/gen, not a monotone union.** Old: monotone
   may-def union, with `DELTA_CALL` monotonicity billed as the main remaining obstacle.
   New: proper RD, so `RD(G, call#2) = {d3}` (kills `d1`), **not** `{d1,d3}`. The
   monotonicity framing is deleted as an artifact of the wrong δ model.
4. **The flat example does NOT inevitably join.** Old: "monovariant digest inevitably
   loses flat-example precision." New: the two caller reads are at *distinct program
   points*, so flow-sensitive `δ(pp)` separates them exactly under one call-only
   context — deleted the inevitability claim.
5. **Interprocedural RD is a first-class section** (§8): gen, kill, must/may-write
   summaries, return propagation, with the callee-writes counterexample showing why
   intra RD is unsound.
6. **Obligations regrouped** (§9) into **A. kernel (proved once)** vs **B. instance (per
   analysis)**, each tagged mechanical vs genuine new proof, and a **Comparison table**
   (§10) added.
7. **Design is now a generic digest interface, not hard-coded `def_site`** (§6).
   `digest_global_read` fixes `writer_key` / `reader_digest` / `compatible`; the kernel
   is proved once over it; reaching definitions are the **first instance**, with
   mod-counts / thread mode / locksets as further instances — matching the paper's list
   of digests. Monotonicity is now an instance property (RD is non-monotone; mod-count
   `≤` and thread mode are monotone), never a kernel requirement.
