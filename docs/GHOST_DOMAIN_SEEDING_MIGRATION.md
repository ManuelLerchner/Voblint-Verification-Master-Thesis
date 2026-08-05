# Migration — ghost facts as product-domain content (Track C replacement)

Status: **design only, replaces `GHOST_INSTRUMENTATION_MIGRATION.md` as issue
#76's plan.** No theory changed by this document. Written after confirming the
old plan's entire dependency chain and semantic vocabulary are gone from
`src/` (section 1) and after reading the two pieces of infrastructure that
have landed since the old plan was written, #66 (`Routed_Context.thy`,
`DG_Ctx_Activation.thy`) and #83 (declared-globals storage classifier), to
check whether either actually solves ghost seeding (sections 3-4) rather than
assuming it does because it landed recently.

Related docs:

- `GHOST_INSTRUMENTATION_MIGRATION.md` — superseded plan; its goal (trace fact
  -> checkable value -> proven check) is kept, its mechanism (source
  instrumentation, generated ghost identifiers, a "Phase 2" gated on a dead
  Track A) is not.
- `TRACE_LAST_WRITE_MIGRATION.md` — superseded design note for `last_writer`;
  targets a `cfg_collect_trace` layer that no longer exists (section 1).
  Section 5 below restates its goal against the current `valid_ltr` layer.
- `SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md` — #66 (`routed_context`, landed) and
  #83 (declared-globals classifier, landed); this document is written in the
  same milestone/design-gate/acceptance-case shape.
- `docs/PROOF_OVERVIEW.md`, `docs/GLOSSARY.md` — current terminology
  (`valid_ltr`, `ltr_collect`, `activation_collect`, `ltr_gamma`).

---

## 1. Why the old plan needs replacing, not patching

Issue #76's own staleness check (2026-08-02) already found: `last_writer` and
`ghost_validation_payoff`, the constants `GHOST_INSTRUMENTATION_MIGRATION.md`
cites as evidence of a working Phase 2, do not exist anywhere in `src/`
(confirmed again here: `rg -n "last_writer|ghost_validation_payoff" src/`
returns nothing), and the plan's dependency chain (this issue -> trace-context
B3 -> Track A) terminates in issue #75, closed `NOT_PLANNED`.

That check did not go far enough. The semantic layer `GHOST_INSTRUMENTATION_
MIGRATION.md` and `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` build on —
`cfg_collect_trace`, `trace_witness`, `digest_env_sound`, `reaching_compat`,
`cfg_collect_ctx` — is **entirely absent from `src/`**, not merely
unfinished:

```text
rg -n "cfg_collect_trace|trace_witness|digest_env_sound|reaching_compat|cfg_collect_ctx" src/
-> 0 matches
```

This is not drift; it is a deliberate, documented replacement.
`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md` records that the predecessor witness
`trace_witness_act` "is deleted" and that the adopted foundation is
`valid_ltr -> cfg_collect_ctx_act -> Activation_Backbone -> DG_Ctx_Activation`
(current names per `docs/GLOSSARY.md`: `valid_ltr`, `ltr_collect`,
`activation_collect`, `ltr_gamma` — `src/CFG/Collecting/CFG_Local_Trace.thy`,
`LTR_Collect.thy`, `LTR_Abstract.thy`). Every semantic citation in the old
ghost plan (`cfg_collect_trace g S v`, `digest_read_sound`,
`context_analysis_sound`) names a layer that predates this convergence and no
longer exists under those names. `TRACE_CONTEXT_ANALYSIS_MIGRATION.md`'s own
"Track B DONE" status line is a separate open question outside this issue's
scope — flagged here, not resolved here, since #76 is about ghost
instrumentation, not auditing that document.

Conclusion: nothing in the old plan can be patched forward. This document
starts from the current `valid_ltr`/`ltr_collect`/`activation_collect`/
`ltr_gamma`/`dg_ctx_activation` layer and from the real Goblint mechanism
established this session (section 2), not from the old plan's vocabulary.

---

## 2. What "ghost variable" means here (recap, established this session)

Real Goblint's load-bearing ghost mechanism is `src/analyses/c2poAnalysis.ml`
+ `src/cdomains/duplicateVars.ml` + `src/common/util/richVarinfo.ml`, not the
witness-export path (`witnessGhost.ml`). Ghost identity is a typed key
(`DuplicateVars.Var.t = DuplicVar of Varinfo.t | NormalVar of Varinfo.t | ...`,
`duplicateVars.ml:24-28`), mapped to a memoized, collision-proof synthesized
`varinfo` (`richVarinfo.ml:32-58`). At function `enter`, c2po builds
`DuplicVar v = NormalVar v` and folds it into **its own** persistent domain
(`c2poAnalysis.ml:242-246`) — the fact is threaded through the fixpoint as
ordinary domain content from that point on. It never touches the analyzed
program's source or CFG.

The target shape for Voblint is the same: a trace-derived fact, seeded into a
consuming analysis's own abstract domain at call/activation entry, carried
through the fixpoint as ordinary domain content. No source instrumentation,
no generated-string identifiers, no recompiled "instrumented program."

---

## 3. What #66 (`routed_context`) actually gives

Read directly (I/Q): `src/Core/Solver/Context/DG/DG_Ctx_Activation.thy`,
`src/Core/Solver/Context/DG/Routed_Context.thy`.

`dg_ctx_activation`'s `extra` hook (`DG_Ctx_Activation.thy:25-26`) runs at
every program point and can, in principle, publish arbitrary strategy-tree
content — that is the shape of an "entry-time hook." But `routed_context`
(the locale #66 actually landed and interpreted) fixes `extra` to
`routed_extra`, and `routed_extra` only ever publishes:

```isabelle
(* Routed_Context.thy:70-72, inside routed_extra's per-call-edge branch *)
publish_global gk0 (enter_global S fs as entry globals);
publish_seed (seed_key w (route v ctx entry ca))
  (enter_local S fs as entry globals);
```

`entry`/`globals` are read back from the caller's **already-solved** slot
(`entry_state <- read_local (v, ctx)`, line 66); `enter_local`/`enter_global`
are the analysis's own `dgs_enter` field (`DG_Framework.thy:420`,
`dgs_enter :: vname list => aexp list => 'dl => 'dg => 'dg × 'dl`), applied to
that existing caller value. `routed_cmb` (lines 36-47) is the same shape on
return: read caller and callee slots, combine via `S`'s own `dgs_combine`.

So `routed_context`/`dg_ctx_activation` are **generic in `S`** and route
whatever `S`'s `dgs_enter`/`dg_spec_step`/`dgs_combine` compute to the correct
context-indexed key `'c`. There is no point in this locale where content not
derivable from the caller's existing `abs_state` enters the system. This
confirms the task's suspicion directly: `routed_context` solves "which slot
does an existing value land in," not "how does a new fact get created." It is
the wrong layer to hook ghost *seeding*.

It is not, however, irrelevant. `'dl`/`'dg` in `dg_spec` are free type
variables (`DG_Framework.thy:414`) — `S`'s carrier is opaque to
`dg_ctx_activation`/`routed_context`. A ghost-carrying analysis whose own
`dgs_enter` (mirroring c2po's `enter`) seeds the ghost fact rides #66's
routing machinery **for free**, exactly the way `Example_Interval_DG_
CallString.thy` already rides it for plain interval values
(`SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`, M3 status). No change to
`Routed_Context.thy` or `DG_Ctx_Activation.thy` is needed. The seeding itself
is a domain-instance question (section 6), not a routing-locale question.

---

## 4. What #83 (declared-globals classifier) actually gives

`gs :: vname => bool` (`DG_Ctx_Activation.thy:20`, `sound_dg_spec`'s own `gs`
parameter, `DG_Soundness.thy:139`) classifies **existing `vname`-keyed
bindings** as local or global; `declared_global`/`declared_global_vars`
(`VIMP_Notation.thy:58-71`) is the program-declaration-driven instance #83
generalized the framework to accept instead of the retired `is_global` naming
rule. Two facts constrain what this can mean for a ghost fact:

- `vname = string` (`VIMP_Syntax.thy:13`); `'a abs_state = vname => 'a`
  (`Abstract_Domain.thy:29`) — a flat pointwise map, the same key space as
  every ordinary source variable.
- The classifier only ever partitions bindings already living in that flat
  map. It has no opinion on whether introducing a new key into that space is
  safe.

Two ways to give a ghost fact identity, evaluated:

**(a) Reuse the `vname` key space with a reserved-prefix name**, classified by
`gs`. Rejected: this is exactly the "ghost identifiers as generated strings"
pattern the task retires, and `vname = string` gives no static collision
protection — unlike real Goblint's `RichVarinfo`/`DuplicateVars.Var.t`
(`richVarinfo.ml:32-58`, `duplicateVars.ml:24-28`), which is memoized and
collision-proof by construction, not by convention.

**(b) Give the ghost fact its own carrier, product-composed** alongside the
existing domain. Voblint already has this precedent for exactly this reason:
`split_state = 'l abs_state × 'g abs_state` (`Split_State.thy:23`) is "give a
second kind of fact its own component instead of overloading the first
component's key space." Since `dg_spec`'s `'dl`/`'dg` are free type
variables, nothing stops an instance from choosing `'dl = 'a abs_state ×
'ghost_dl`. `Mixed_Sign_Interval.thy:30` (`mixed_si_spec :: (sign abs_state,
ivl abs_state) dg_spec`) is existing, batch-green evidence that `'dl ≠ 'dg`,
hand-written product-shaped instances already work in this framework — not a
generic combinator, but proof the shape is not a category error.

**Resolution for `last_writer` specifically:** the ghost fact needed is "the
last write site of `g`," which is naturally indexed by the **same** `vname`
as `g` itself — no new identifier namespace is needed at all, only a second
`vname`-co-indexed carrier (`'ghost_dl = vname => cfg_node_lattice`, section
6) riding beside the base value. Under this framing #83's classifier is not a
category error forced onto a foreign identity — it is a genuine, useful
instance of the axis #83 generalized: whether the *last-writer-of-`g`* fact is
placed flow-sensitively (D) or side-effected (G) is a real, independently
decidable question, exactly the kind `SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`'s
own unbuilt Phase-2 item A4 anticipated (`fact_key = ValueFact vname |
TaintFact vname`, "the D/G split applies to abstract facts, not source
variables"). Milestone G-M1 (section 8) makes this concrete instead of
speculative.

A ghost fact that is **not** naturally `vname`-co-indexed (a call-string or
entry-state ghost, old plan's Ex4/Ex6) would need a genuine typed-identifier
widening (a sum type over `vname` and a ghost-tag type, threaded through
`store`/`abs_state`) — out of scope here; `last_writer` does not need it.

---

## 5. `last_writer` over the current trace layer

`ltr` (`CFG_Local_Trace.thy:31-34`) is `Root p | Call caller p | Resume
current callee p`, each `p :: (cfg_node * store) list` — **richer** than the
`trace = store list` that `TRACE_LAST_WRITE_MIGRATION.md` assumed as its
baseline (that doc predates the current trace design; its blast-radius
targets, `CFG_Collect_Trace.thy`/`Trace_Analysis_Sound.thy`, no longer exist).
`valid_ltr`'s `intra` rule licenses each step from a concrete edge:

```isabelle
(* CFG_Local_Trace.thy:106-110 *)
t ∈ valid_ltr gs g S
⟹ (sink_node t, a, v) ∈ intra g
⟹ s' ∈ edge_step a (sink_store t)
⟹ extend t (v, s') ∈ valid_ltr gs g S
```

so consecutive `(u, s), (v, s')` pairs in `path t` correspond to a witnessing
`edge_action a` with `(u, a, v) ∈ intra g`. `last_writer` is derivable
**directly from `path t` and `intra g`**, without enriching the trace type —
contrary to `GHOST_INSTRUMENTATION_MIGRATION.md`'s and `TRACE_CONTEXT_
ANALYSIS_MIGRATION.md`'s shared assumption that write-site identity is
gated on action-labelled traces (M3.5 Slice 1).

**Open question, first task of milestone G-M0, not yet checked:** this
derivation needs `intra g` to be edge-action-functional on `(u, v)` pairs — no
two `(u, a1, v)` and `(u, a2, v) ∈ intra g` with `a1 ≠ a2` for compiled CFGs
(`compile_prog`, `VIMP_Proc_to_CFG.thy`). Plausible, since `compile`/
`compile_proc` build fresh node intervals per source statement rather than
merging edges, but unproved as of this document. If it fails, `last_writer`
falls back to the M3.5 action-labelled-trace enrichment the old plan assumed
as a hard prerequisite; if it holds, that enrichment is unnecessary for this
goal.

---

## 6. Design: the ghost fact as a product-domain component

Interface-level shape first, not tied to `last_writer`: a ghost-carrying
`dg_spec` product-composes the base local domain with a second, free-standing
carrier — `'dl = 'a abs_state × 'g_dl` for some ghost-domain type `'g_dl`
supplying its own lattice/order, its own seed/update step parallel to the
base value's `dgs_assign` (so a ghost fact can be created directly from
information a transfer function already has at an edge, not routed from
elsewhere), and participating in the same `dgs_enter`/`dgs_combine_env`
local/global split the base value uses (`restrict_local`/`restrict_global`,
generalized over `gs` per #83's `_for` pattern — #83's landed generalization
is reused here, not re-derived). This interface should not be read as
committing to any one `'g_dl`; `last_writer` below is the initial motivating
instance chosen to validate the shape, not the only ghost fact the interface
is meant to support.

**Motivating instance — `last_writer`:** `'g_dl = vname => cfg_node_opt`, for
some finite lattice `cfg_node_opt` over `cfg_node option` (bot = no write
observed; a set/flat lattice over the finite `cfg_node` type of the fixed
compiled CFG; join on divergent writers, mirroring real Goblint's
silent-drop-on-unrepresentable behaviour, `c2poAnalysis.ml:246`, as "join to
top/unknown" here rather than a hard drop, matching Voblint's total abstract
domains). Its seed step: `dgs_assign x e (d, w) g = (dgs_assign_base x e d g,
w(x := {cfg_node_of a}))` — on an assignment edge, the ghost slot for `x` is
seeded fresh exactly at that edge, computed from the edge's own target node,
not routed from anywhere. This is the Voblint analogue of c2po's `enter`
seeding `DuplicVar v = NormalVar v` into its own domain — except here the
seed point is every assignment edge, not only call entry, because
`last_writer` is an intraprocedural fact first and an interprocedural one
only when the write and the read are in different activations.

---

## 7. Design: one check layer for ordinary and ghost-backed checks

This section exists because it is not automatic that a ghost-augmented
analysis can prove ghost-referencing checks *and* ordinary checks through the
same mechanism — the current building blocks do not obviously support it, and
this needs stating explicitly rather than assumed.

`checks_proven`/`check_condition`/`checks_at` do not exist in `src/` today
(`rg -n "checks_proven|check_condition|checks_at" src/` -> 0 matches) — G-M4
is genuinely unbuilt, so this is a decision to make correctly once, not a
retrofit. The old, superseded plan's formula
(`GHOST_INSTRUMENTATION_MIGRATION.md:183`, `checks_proven env <-> forall
check_pp. forall s in gamma(env check_pp). bval (check_condition v) s`) is
built on `bval :: bexp => store => bool` (`VIMP_Expr.thy:19-25`) and
`gamma_state :: 'a abs_state => store set` (`Abstract_Domain.thy:58`). VIMP's
`bexp`/`aexp` grammar (`Bc | Not | And | Or | Less | Eq` over
`N | V | Plus | Minus | Times`, `VIMP_Syntax.thy:18-33`) has no case that can
name a fact like "the last writer of `g`," and `bval`/`gamma_state` only ever
inspect a single concrete `store` — never a trace. A ghost-referencing check
condition does not merely fall outside this shape's current *coverage*; it is
not an expression `bval` can be applied to at all, since the fact it names
does not live in any one `store`.

**Required generalization, so ordinary and ghost checks are one mechanism:**

- A check condition is a proposition over whatever trace-derived projections
  are in scope at a point — minimally the terminal `store` (this alone
  recovers an ordinary `__goblint_check`-style condition, evaluated the same
  way `bval` would), and, for a ghost-augmented instance, any additional
  projection its `'g_dl` tracks (`last_writer`, from G-M0). One condition
  type, one `checks_proven`/`checks_proven_sound` theorem; an ordinary check
  is the case that happens not to inspect the ghost projection, not a
  different kind of check.
- `checks_proven`/`checks_proven_sound` must be anchored to the trace-indexed
  collecting semantics (`ltr_collect`/`activation_collect` — the current
  semantic foundation per this project's `CLAUDE.md`), not to `gamma_state`.
  This matters beyond expressiveness: a check like "`last_writer(g) == W7`
  implies `g == 1`" is a statement that *one trace's* two projections agree.
  If the base component and the ghost component were each proven sound
  against independently-defined concretizations, that would not license the
  implication even when both marginal soundness facts hold — the standard
  reduced-product pitfall (each conjunct sound in isolation, the conjunction
  not). Section 6's pointwise/simultaneous transfer
  (`dgs_assign x e (d, w) g = (dgs_assign_base x e d g, w(...))`, both
  components updated from the *same* edge/trace step) is what makes the
  needed *joint* soundness free — but only once the anchor is the
  trace-indexed collecting semantics; it is not free against `gamma_state`,
  which was never trace-indexed to begin with.
- G-M4's "side table over `cfg_node`" framing (below) still holds for *where*
  checks live in the CFG. What this section adds is that the check
  *condition type* and *soundness anchor* must be shaped this way from G-M4's
  first version, not bolted on after an ordinary-check-only version ships —
  an ordinary-only version built directly on `bexp`/`bval`/`gamma_state`
  would need its condition type replaced, not extended, to add ghost checks
  later.

---

## 8. Milestones

| # | Deliverable | Depends on | File targets |
| --- | --- | --- | --- |
| G-M0 | `last_writer`/`last_write_collect` over `valid_ltr`/`ltr_collect`, plus the edge-determinism check (section 5) | none | `src/CFG/Collecting/CFG_Local_Trace.thy` or new `LTR_Last_Write.thy` |
| G-M1 | Ghost-augmented `dg_spec` instance (`'dl = 'a abs_state × ghost carrier`), hand-written per section 6, one base domain (Sign first) | G-M0 | new `src/Core/Domain/Ghost_Last_Write_Domain.thy`, new `src/Analysis/Instances/.../Sign_LastWrite_Spec.thy` |
| G-M2 | `routed_context` interpretation for the ghost-augmented instance, reusing an existing `route`/`enterc` (e.g. the Sign CallString instance's) unmodified | G-M1 | new `Example_Sign_Ghost_LastWriter_CallString.thy`, mirroring `Example_Interval_DG_CallString.thy`'s structure |
| G-M3 | `ghost_tracks_last_writer` — the ghost component of a post-solution over-approximates `last_write_collect`, as a corollary of `sound_dg_spec` (G-M1) + `dg_ctx_act_edge`/`routed_context_call`/`routed_context_comb` (existing, reused via G-M2) + `last_write_collect_sound` (G-M0) | G-M0, G-M1, G-M2 | example theory alongside G-M2 |
| G-M4 | Check-point machinery: `checks_at`/`checks_proven`/`checks_proven_sound`, as a side table over `cfg_node` (no `edge_action`/`dg_spec` change); condition type generalized over trace-derived projections (store + optional ghost projections) and anchored to `ltr_collect`/`activation_collect` from the start (section 7) — ordinary checks are the store-only case of the same mechanism, not a separate one | G-M0 (needs `last_writer` as the first non-store projection so the generalization is validated, not vacuous) | new `src/CFG/Collecting/Checks.thy` or similar |
| G-M5 | Payoff examples: intraprocedural branch-writer guard (no context needed) and interprocedural two-caller guard (uses G-M2's `routed_context` interpretation), each exercising an ordinary check and a ghost-backed check through the same `checks_proven_sound` instance | G-M0-G-M4 | new `Example_Ghost_LastWriter_Payoff.thy` |
| G-M6 (named, not designed) | `checks_proven_sound` discharge-automation target (`checks_proven_tac` or similar) — scope only, do not design the tactic | G-M4 | none yet; acceptance test only |

---

## 9. Design gate (resolve before G-M0 starts)

1. **Can `last_writer` be defined purely from `valid_ltr`?** (section 5) —
   the semantic question, kept separate from the proof obligation below.
   Answered provisionally yes: consecutive `(u, s), (v, s')` pairs in
   `path t` correspond to a witnessing `(u, a, v) ∈ intra g`
   (`CFG_Local_Trace.thy:106-110`), so write-site identity should be
   readable directly off `path t` and `intra g` without enriching the trace
   type. Confirm this reading before treating it as settled.
2. **Prove edge-action determinism for `intra g`**, if (1) needs it — no two
   `(u, a1, v)` and `(u, a2, v) ∈ intra g` with `a1 ≠ a2` for compiled CFGs.
   This is the proof obligation (1) reduces to, not a separate question. If
   it fails, `last_writer` falls back to the M3.5 action-labelled-trace
   enrichment the old plan assumed as a hard prerequisite.
3. **Ghost component representation** — the section 6 interface (a
   product-composed, free-standing `'g_dl` carrier with its own seed step)
   vs. reserved-prefix `vname` reuse (section 4(a), rejected) vs. full
   typed-identifier widening (out of scope, only needed for non-`vname`-
   co-indexed ghosts). Confirm the product-interface choice before G-M1;
   `last_writer`'s concrete `'g_dl = vname => cfg_node_opt` instantiates it
   and should not be read back into the interface itself.
4. **Check-point representation** (G-M4) — a side table keyed by existing
   `cfg_node`s (recommended: no `edge_action`/`dg_spec` change, no new
   equation-system content) vs. a new `edge_action` constructor (touches
   every transfer function in the codebase). Confirm the side-table choice
   before G-M4.
5. **Check condition type and soundness anchor** (section 7) — a proposition
   type generalized over trace-derived projections (store + optional ghost
   projections), anchored to `ltr_collect`/`activation_collect`, vs. building
   G-M4 directly on `bexp`/`bval`/`gamma_state` and widening later
   (rejected: that shape cannot name a ghost fact at all, so "widening
   later" means replacing the condition type, not extending it). Confirm
   before G-M4; this is what keeps ordinary and ghost-backed checks one
   mechanism instead of two.

---

## 10. Acceptance / validation cases

1. **Intraprocedural branch-writer** (old Ex1/Ex2 analogue): ghost-augmented
   Sign, no context indexing. Proves, through one `checks_proven_sound`
   instance, both an ordinary check on the branch's own local variable
   (`check(i == 3)`-shaped, store-only projection) and the guarded
   ghost-backed checks (`last_writer(g)==W1 => check(g==1)`,
   `last_writer(g)==W2 => check(g==2)`) that plain Sign cannot — on a
   **computed** post-solution, not a hand-built one. This is the pair that
   demonstrates section 7's point directly: same mechanism, same theorem,
   one check ignores the ghost projection and one doesn't. Needs no #66
   infrastructure at all — the correlation lives in one product slot of one
   flat analysis.
2. **Interprocedural two-caller — the flagship** (old Ex3 analogue): two
   callers write the same global via different call sites; the
   `routed_context`-interpreted ghost domain (G-M2) separates the writers by
   call-string context, so a context-indexed check can prove
   `last_writer(g)==callerA_site => check(g==1)` where a flat (unindexed)
   ghost analysis on the same program cannot. Also carries at least one
   plain, context-independent ordinary check in the same program (e.g. a
   local variable set before the call), proved through the same
   `checks_proven_sound` instance, so the example demonstrates both check
   kinds side by side rather than the ghost-only payoff in isolation. This
   is where #66 earns its keep.
3. **Check machinery alone, store-only**: `checks_proven_sound` proved and
   exercised on a ghost-free program — this is the store-only specialization
   of the *same* general condition type from section 7 (an instance whose
   `'g_dl` is trivial/unit), not a separately-typed simpler check mechanism.
   Derisks G-M4 independently of G-M0-G-M3, same instinct as the old plan's
   I1 stage, still good advice, now scoped precisely.
4. **Placement-by-fact-kind**: a declared global's last-writer ghost slot
   side-effected (G) while its base value stays flow-sensitive (D), or vice
   versa — makes concrete `SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`'s unbuilt
   Phase-2 item A4 (`fact_key = ValueFact vname | TaintFact vname`).
5. **Guard reachability**: for each guarded check in case 1/2, a named lemma
   that the guard's abstract state is not `bot` — kept separate from the
   payoff theorem so vacuity cannot be papered over (replaces old D5).

---

## 11. Non-interference, reframed (replaces old G0)

Ghosts here never touch the concrete program, source, or CFG — the product
carrier only exists in the abstract domain `'dl`, seeded by transfer
functions the analysis already owns. There is no "instrumented program" to
prove behaves like the original one. What remains to check is a composition
fact, not a non-interference theorem: does adding the ghost product component
to `'dl` leave the base component's transfer functions acting exactly as they
did without it? For a pointwise product transfer (`dgs_assign x e (d, w) g =
(dgs_assign_base x e d g, w')`), this is true by construction — the base
component is computed by the unmodified base transfer, independent of `w`.
Scope this as a one-paragraph remark inside G-M1's acceptance, not a separate
milestone or theorem statement.

---

## 12. Out of scope

- General typed ghost-identifier namespace (sum type over `vname` and a
  ghost-tag type) — only needed for a ghost fact that is not naturally
  `vname`-co-indexed (call-string/entry-state ghosts, old Ex4/Ex6). Revisit
  if a second ghost kind needs it.
- A generic "lift any `sound_dg_spec` to carry an extra product component"
  combinator — build the one hand-written instance (G-M1) first; generalize
  only when a second ghost kind needs the same lift (existing project
  convention: `mixed_si_spec` is hand-written too, no combinator exists yet
  for heterogeneous `'dl`/`'dg` either).
- A check condition type generic over an arbitrary number of ghost
  projections — section 7 requires the type to accommodate `last_writer` as
  a second projection alongside `store`; generalize to N projections only
  when a second ghost fact needs it, same instinct as the product-domain
  combinator above.
- Source-text instrumentation, generated-string ghost identifiers, a
  recompiled "instrumented program" artifact, the digest-partitioned Track A
  (#75) approach — all explicitly retired; do not resurrect without a
  concrete argument that the real-Goblint mechanism (section 2) does not
  transfer to VIMP/Voblint.
- Designing `checks_proven_tac` itself (G-M6) — scope and acceptance test
  only.

---

## 13. Verification gate

Batch build green on `Voblint_CFG` (G-M0), the owning domain/analysis session
(G-M1-G-M3), and `Voblint_Examples` (G-M2, G-M5), no `sorry`, after each
milestone. G-M4 gates independently on whatever session `Checks.thy` lands
in. Confirm the design-gate item 1 (edge-action determinism) resolution
before G-M0 is marked done, one way or the other — it changes G-M0's proof
shape, not just its difficulty.
