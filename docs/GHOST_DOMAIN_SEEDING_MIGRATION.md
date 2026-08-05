# Migration — ghost facts as product-domain content (Track C replacement)

Status: **G-M0/G-M1 landed** (`src/CFG/Collecting/LTR_Last_Write.thy`,
`src/Core/Domain/Ghost_Last_Write_Domain.thy`,
`src/Core/Domain/Ghost_Last_Write_Product.thy`,
`src/Analysis/Instances/Sign/Sign_Ghost_LastWrite_DG.thy`, and a hand-built
call/join witness, `src/Examples/CFG/Example_Sign_Ghost_LastWrite_Witness.thy`
— see section 14). Everything else below is design only, replacing
`GHOST_INSTRUMENTATION_MIGRATION.md` as issue #76's plan. Written after
confirming the old plan's entire dependency chain and semantic vocabulary are
gone from `src/` (section 1) and after reading the two pieces of
infrastructure that have landed since the old plan was written, #66
(`Routed_Context.thy`, `DG_Ctx_Activation.thy`) and #83 (declared-globals
storage classifier), to check whether either actually solves ghost seeding
(sections 3-4) rather than assuming it does because it landed recently.

**Scope correction (post-G-M1, section 14):** ordinary `__goblint_assert`
support does not need any of the ghost-tracking machinery below. It is split
out as its own milestone (G-A1, section 8) with no dependency on G-M0-G-M3,
so it is not gated on `last_writer` or on any ghost fact at all. The
generalized, trace-projection-aware check condition type that sections 7 and
9 originally required from G-M4's first version is deferred until a second
concrete ghost fact actually needs it (section 7).

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

## 7. Design: ordinary asserts now, a unified check layer only if needed

**Reversed from this section's original argument** (kept below, marked, for
the record): the original text required the check condition type to be
generalized over trace-derived projections *from G-M4's first version*, so
that an ordinary check and a `last_writer`-referencing check would share one
mechanism from day one. That is premature generalization against a single
concrete ghost fact and is retracted. `__goblint_assert` support does not
need `last_writer`, does not need any ghost carrier, and does not need the
trace-indexed collecting semantics at all — most Goblint-style assertions
(`__goblint_assert(x == 5)`, `__goblint_assert(x > 0)`) are a proposition over
the *current* abstract state, nothing more. Splitting the question in two
first, matching C-2PO's own decoupling of relational-domain precision from
assertion generation:

- **Case A — the assertion depends only on the current abstract state.**
  `__goblint_assert(cond)` at a program point evaluates `cond` against
  whatever `sound_dg_spec` instance is in scope, exactly the way `bval` would
  against a concrete store. No trace, no ghost projection, no product-domain
  dependency. This is G-A1 (section 8) — an independent milestone, buildable
  today against plain Sign or Interval, with no dependency on G-M0-G-M3.
- **Case B — the assertion depends on trace-derived history**
  (`__goblint_assert(last_writer(g) == W7)`). This needs a ghost fact in
  scope, hence a real dependency on this document's G-M0-G-M3 track. Nothing
  in `src/` needs this yet: G-A1 covers ordinary asserts without it, and no
  second ghost-backed check consumer exists to justify designing the general
  condition type against.

**G-A1's shape (Case A only):** `checks_proven`/`check_condition`/`checks_at`
do not exist in `src/` today (`rg -n "checks_proven|check_condition|
checks_at" src/` -> 0 matches). Build them directly on the old, superseded
plan's formula (`GHOST_INSTRUMENTATION_MIGRATION.md:183`, `checks_proven env
<-> forall check_pp. forall s in gamma(env check_pp). bval (check_condition
v) s`), which is already exactly Case A: `bval :: bexp => store => bool`
(`VIMP_Expr.thy:19-25`) against `gamma_state :: 'a abs_state => store set`
(`Abstract_Domain.thy:58`), anchored to whatever collecting semantics the
underlying `sound_dg_spec`/`sound_dg_spec_ltr` instance already proves sound
against (not `ltr_collect`/`activation_collect` — those anchor the
trace-indexed layer this milestone does not need). `checks_at` is a side
table keyed by existing `cfg_node`s, unchanged from the original framing
below.

**Why Case B is deferred, not merely postponed arbitrarily** (the analysis
this section originally used to justify building it early — now the argument
for *why it is hard*, hence not worth doing speculatively): VIMP's
`bexp`/`aexp` grammar (`Bc | Not | And | Or | Less | Eq` over
`N | V | Plus | Minus | Times`, `VIMP_Syntax.thy:18-33`) has no case that can
name a fact like "the last writer of `g`" — a ghost-referencing condition is
not an expression `bval` can be applied to at all, since the fact it names
does not live in any one `store`. A unified condition type would need to be a
proposition over whatever trace-derived projections are in scope (minimally
the terminal `store`, plus a ghost-augmented instance's `'g_dl` projection),
anchored to the trace-indexed collecting semantics
(`ltr_collect`/`activation_collect`) rather than `gamma_state` — a check like
"`last_writer(g) == W7` implies `g == 1`" states that *one trace's* two
projections agree, which two independently-anchored marginal soundness facts
would not license (the standard reduced-product pitfall). Section 6's
pointwise/simultaneous transfer makes the needed *joint* soundness free once
the anchor is trace-indexed — but building that anchor, and the wider
condition type, against zero consumers (`last_writer` would be the only
projection, and G-A1 already covers the store-only case without it) is
exactly the generalization this project's `CLAUDE.md` warns against: a
"missing abstraction" that turns out to be a localized generalization once a
second ghost fact actually exists, not upfront framework design. Revisit this
section only when a second concrete ghost fact needs a check condition that
names it.

---

## 8. Milestones

| # | Deliverable | Depends on | File targets |
| --- | --- | --- | --- |
| **G-A1 (next, independent)** | Ordinary `__goblint_assert` support: `checks_at`/`checks_proven`/`checks_proven_sound`, a store-only condition type (`bexp`/`bval`/`gamma_state`, section 7 Case A), a side table over `cfg_node`, anchored to whatever collecting semantics the underlying `sound_dg_spec`/`sound_dg_spec_ltr` instance already proves sound against | none — works against any existing analysis (plain Sign is enough); **not gated on G-M0-G-M3 or on any ghost fact** | new `src/CFG/Collecting/Checks.thy` or similar |
| G-M0 (**done**) | `last_writer`/`last_write_collect` over `valid_ltr`/`ltr_collect`, plus the edge-determinism check (section 5) | none | `src/CFG/Collecting/LTR_Last_Write.thy` |
| G-M1 (**done**, optional precision/provenance track — not a prerequisite for G-A1) | Ghost-augmented product domain, hand-written per section 6, Sign base. Landed as a direct `sound_dg_hooks`/`sound_dg_hooks_ltr` interpretation, not `dg_spec` as originally scoped: `ghost_step`'s value at an edge depends on the edge's *destination* node, which `dg_spec`'s fixed per-edge transfer signature cannot express but hook trees can (`Sign_Ghost_LastWrite_DG.thy`'s own comment on `sign_ghost_edge_tree`) | G-M0 | `src/Core/Domain/Ghost_Last_Write_Domain.thy`, `src/Core/Domain/Ghost_Last_Write_Product.thy`, `src/Analysis/Instances/Sign/Sign_Ghost_LastWrite_DG.thy` |
| G-M1 witness (**done**) | Hand-built `part_post_solution` over a real `compile_prog` output (branch/join + one procedure call), sorry-free. Demonstrates the product domain propagates ghost facts through calls and joins under hand-built hook trees — see section 14 for exactly what it does and does not show | G-M1 | `src/Examples/CFG/Example_Sign_Ghost_LastWrite_Witness.thy` |
| G-M2 (optional precision/provenance track) | `routed_context` interpretation for the ghost-augmented instance. **Open question, not yet checked:** G-M1 landed on `sound_dg_hooks` rather than `dg_spec`, so "reusing an existing `route`/`enterc` unmodified" needs rechecking against a hook-tree instance before this row can proceed as originally scoped — `routed_context`'s genericity argument (section 3) was made against `dg_spec`'s `S` parameter, not against a raw hook-tree interpretation | G-M1 | new `Example_Sign_Ghost_LastWriter_CallString.thy`, mirroring `Example_Interval_DG_CallString.thy`'s structure |
| G-M3 (optional precision/provenance track) | `ghost_tracks_last_writer` — the ghost component of a post-solution over-approximates `last_write_collect`, as a corollary of `sound_dg_hooks` (G-M1) + the routing discipline G-M2 settles + `last_write_collect_sound` (G-M0) | G-M0, G-M1, G-M2 | example theory alongside G-M2 |
| G-M4 (**deferred**, section 7) | Check condition type generalized over trace-derived projections (store + ghost projections), anchored to `ltr_collect`/`activation_collect`, unifying ordinary and ghost-backed checks under one `checks_proven_sound` | a second concrete ghost fact that needs a check condition naming it — not G-A1, not G-M0-G-M3 alone | extension of G-A1's `Checks.thy`, scope TBD when a second ghost fact exists |
| G-M5 (optional precision/provenance track, needs G-M4) | Payoff examples: intraprocedural branch-writer guard and interprocedural two-caller guard, each exercising an ordinary check and a ghost-backed check through the unified `checks_proven_sound` from G-M4 | G-M0-G-M4 | new `Example_Ghost_LastWriter_Payoff.thy` |
| G-M6 (named, not designed) | `checks_proven_sound` discharge-automation target (`checks_proven_tac` or similar) — scope only, do not design the tactic | G-A1 (store-only case first) | none yet; acceptance test only |

---

## 9. Design gate (resolve before G-M0 starts)

1. **Resolved (G-M0 landed).** Can `last_writer` be defined purely from
   `valid_ltr`? (section 5) — yes: consecutive `(u, s), (v, s')` pairs in
   `path t` correspond to a witnessing `(u, a, v) ∈ intra g`
   (`CFG_Local_Trace.thy:106-110`), so write-site identity is readable
   directly off `path t` and `intra g` without enriching the trace type,
   confirmed by `src/CFG/Collecting/LTR_Last_Write.thy`.
2. **Resolved (G-M0 landed).** Edge-action determinism for `intra g` held for
   compiled CFGs, so `last_writer` did not need the M3.5 action-labelled-trace
   enrichment the old plan assumed as a hard prerequisite.
3. **Resolved (G-M1 landed), with one correction.** Ghost component
   representation: the section 6 interface (a product-composed,
   free-standing `'g_dl` carrier with its own seed step) is confirmed, via
   `Ghost_Last_Write_Product.thy`. Correction: the *hosting* locale is
   `sound_dg_hooks`/`sound_dg_hooks_ltr`, not `sound_dg_spec` as this section
   originally assumed — see the G-M1 row in section 8 and section 14.
4. **Check-point representation** (now G-A1, not G-M4 — see section 7) — a
   side table keyed by existing `cfg_node`s (recommended: no
   `edge_action`/`dg_spec` change, no new equation-system content) vs. a new
   `edge_action` constructor (touches every transfer function in the
   codebase). Confirm the side-table choice before G-A1 starts.
5. **Retracted, see section 7.** This item originally required the check
   condition type to be generalized over trace-derived projections from
   G-M4's first version, rejecting a `bexp`/`bval`/`gamma_state`-only version
   as needing its condition type replaced later. That is backwards for a
   milestone (G-A1) with zero ghost-fact consumers today: build the
   store-only version now: `checks_proven`/`checks_proven_sound` on
   `bexp`/`bval`/`gamma_state`, no trace anchor. Only revisit the
   generalized condition type (G-M4) once a second concrete ghost fact
   actually needs a check condition that names it.

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
- Any trace-projection-aware or ghost-aware check condition type at all
  (G-M4) — section 7 now defers this entirely, not merely to "N projections";
  `__goblint_assert` (G-A1) ships on `bexp`/`bval`/`gamma_state` first, with
  no ghost projection in its condition type. Revisit only when a second
  concrete ghost fact needs a check condition that names it.
- Source-text instrumentation, generated-string ghost identifiers, a
  recompiled "instrumented program" artifact, the digest-partitioned Track A
  (#75) approach — all explicitly retired; do not resurrect without a
  concrete argument that the real-Goblint mechanism (section 2) does not
  transfer to VIMP/Voblint.
- Designing `checks_proven_tac` itself (G-M6) — scope and acceptance test
  only.

---

## 13. Verification gate

Batch build green on `Voblint_CFG` (G-M0, done), the owning domain/analysis
session (G-M1-G-M3; G-M1 and its witness done), and `Voblint_Examples` (G-M2,
G-M5), no `sorry`, after each milestone. G-A1 gates independently on whatever
session `Checks.thy` lands in, and does not require the ghost-track sessions
to be green first (it has no dependency on them). G-M4 gates independently
too, once it exists.

---

## 14. What the G-M1 witness demonstrates (and does not)

`Example_Sign_Ghost_LastWrite_Witness.thy` (sorry-free, batch-green) is a
hand-built `part_post_solution` for a real `compile_prog` output covering a
branch/join and one procedure call. What it establishes:

- **Product-domain ghost facts propagate through calls and joins.** The
  witnessed post-solution shows the ghost (last-writer) component threading
  correctly through an intraprocedural join (`FVal (Some gn4)` /
  `FVal (Some gn6)` on the two branches join to `FTop` at `gn7`) and across a
  real call/return (`ghost_enter_step` resets the callee's fresh locals at
  entry; `combine` preserves the caller's ghost facts across the return),
  under the hand-built `sign_ghost_edge_tree`/`sign_ghost_enter_tree`/
  `sign_ghost_combine_tree` hook trees. `hook_post_solution_collect_sound_ltr`
  is instantiated on this witness, giving base-store (Sign) collecting
  soundness at every covered program point.
- **What it does not show about `routed_context`.** This witness interprets
  `sound_dg_hooks`/`sound_dg_hooks_ltr` directly with hand-built trees — it
  does not go through `sound_dg_spec` or exercise `Routed_Context.thy`'s
  routing at all. Section 3's argument for why `routed_context` *would* carry
  a ghost-augmented instance "for free" was made against `dg_spec`'s generic
  `S` parameter; whether that argument transfers unchanged to a hook-tree
  instance is G-M2's open question (section 8), not something this witness
  settles either way.
- **It does not implement or justify `__goblint_assert`.** No check
  machinery, no condition type, no `checks_proven`-shaped statement appears
  anywhere in this file or in `Sign_Ghost_LastWrite_DG.thy`. `__goblint_assert`
  support is G-A1 (section 7, section 8), fully independent of this witness
  and of the ghost track generally.
- **It does not claim the ghost component tracks `trace_last_writer`
  globally** — that is `ghost_tracks_last_writer` (G-M3, still open,
  optional). This witness proves the product domain satisfies the solver's
  equations for one hand-built assignment, not that a computed post-solution
  would produce the same values (the standard `part_post_solution`-witness
  vs. computed-solver distinction, same as every other `sound_dg_hooks`
  example in this repository).
