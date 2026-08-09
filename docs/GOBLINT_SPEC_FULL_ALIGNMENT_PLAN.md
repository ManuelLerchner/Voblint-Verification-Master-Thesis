# Long-term plan — full Goblint Spec alignment

Status: **LONG-TERM / STRETCH** (research findings 2026-06-17, not started).

**Audit update (2026-07-16).** Gap 7 is partially superseded: semantic
context-indexed unknowns and collecting soundness now exist. The remaining work
is the executable D/G generator, computed context schemes, and context bounding.
See `GOBLINT_ALIGNMENT_REGISTER.md` and `GOBLINT_ALIGNMENT_TRACKS.md` for the
current status and upstream evidence baseline.

The effectful-TF migration (`docs/EFFECTFUL_TF_MIGRATION.md`) closes Gaps 1–2
(named globals, effectful transfer functions). This document records the remaining
structural gaps between our proof and Goblint's full `Spec` / `GlobConstrSys`
interface, and sketches what closing each would require. None of this is required
for the thesis; it is a roadmap for post-thesis extension.

Related: `src/Analysis/Generic/Equations/README.md` §Scope vs. Voblint's actual framework —
deliberately lists these extensions as out of scope for the current thesis axis.

---

## Gap inventory

### Source-language boundary — C memory and CIL front end

**Goblint's input:** C programs represented through CIL, including addresses,
arrays, heap allocation, casts, and aliasing. Its analyses can state transfer
functions over that memory model.

**What we do:** scalar IMP2. `ARRAY_SYNTAX_EXTENSION.md` plans array syntax and
array-read analysis, but does not introduce addresses, pointer aliasing, heap
allocation, or a C/CIL translation theorem.

**Closure path:** complete the array plan first. Before any C front-end work,
write a separate design decision fixing the C/CIL fragment, its memory model,
and the translation-correctness statement. Pointer/alias analysis is a distinct
domain track after that semantics exists.

**Status:** deliberately deferred. This is not a `Spec` gap: it is a source
language boundary below the existing CFG and solver interface.

### Gap 3 — analysis-specific interprocedural combine

**Goblint's `Spec` requires:**

```ocaml
val combine_env    : (D, G, C, V) man -> D.t -> D.t -> D.t
val combine_assign : (D, G, C, V) man -> lval -> exp -> D.t -> D.t -> D.t
```

The first argument is the callee's exit state; the second is the caller's state at
the call site. Each analysis decides how to merge them. `combine_assign` additionally
receives the syntactic call `lval := f(args)` to adjust the return value.

**Audit update (2026-07-27).** This gap is not uniform across the codebase. There
are two distinct call/return combine sites, at different degrees of readiness.

**Already closed, in the context-sensitive DG layer.** `dg_spec`
(`DG_Framework.thy:232`) carries combine as a record field:

```isabelle
dgs_combine :: "vname option => 'dl => 'dl => 'dg => 'dg \<times> 'dl"
```

`sound_dg_spec.combine_sound` (`DG_Soundness.thy:138-142`) is proved generically
over `dgs_combine S` for an arbitrary `dg_spec S` - no analysis-specific
instantiation is assumed at the locale level. The Interval context flagship's
`cmb_ivl` already calls `dgs_combine Spoly dst ...`
(`Example_Interval_DG_Ctx_Flagship.thy:87-88`) rather than inlining a structural
split. Every current instance (`unit_dg_spec`, the Interval flagship, Mixed
Sign/Interval) happens to set `dgs_combine` to the structural split
(`unit_combine_step`, `DG_Framework.thy:270-276`, built from
`combine_collect_abs`), but that is a choice of instance, not a limitation of the
interface. A relational instance needs no `DG_Framework.thy` change - only a new
`dgs_combine` value and a `combine_sound` proof for it. `gammaDG :: 'D => 'G =>
store set` already concretizes the pair jointly, so it does not presuppose a
per-variable-splittable domain.

**Closed (2026-07-28), in the flat/context-insensitive constraint system.**
Comparison against Goblint's actual `master` source (`src/framework/analyses.ml`,
`src/framework/constraints.ml`) showed the real interface is split in two:
`combine_env` merges caller/callee environments (may unify, filter by taint,
raise `Deadcode` - see the Apron `relationAnalysis.apron.ml` evidence below), and
the separate `combine_assign` then writes the return value into the lval, run
*against `combine_env`'s output*. Under this project's function-based
`'a abs_state = vname => 'a` representation, the return-value write
(`combine_assign_abs`, `Constraint_System.thy:401-404`) is already
domain-agnostic - it is a plain `dst := v` update, with no case where a domain
needs to see anything but the value being written. Only the environment-merge
half needed to become analysis-specific.

`domain_transfer` (`Constraint_System.thy:38-43`) gained a
`tf_combine :: 'a abs_state => 'a abs_state => 'a abs_state` field, alongside the
existing `tf_assign`/`tf_assume`/`tf_assume_not`/`tf_enter`. `sound_transfer`
(`Constraint_System.thy:634-650`) gained the matching `tf_sound_combine`
assumption, proving `tf_combine tf` over-approximates the fixed concrete
`combine_states` (`CFG_Def.thy:148-149`) - the one true operational return
semantics, unchanged and not analysis-owned. `tf_combine_collect_abs`
(`Constraint_System.thy`) is the new per-analysis return combine
(`combine_assign_abs dst (se ret_var) (tf_combine tf sc se)`); the fixed
`combine_collect_abs`/`combine_abs` are untouched and remain the default every
non-generic consumer (DG-layer defaults, `TD_Side_CFG.thy`,
`Sign_Named_Global_Eff.thy`, `Exec_St.thy`/`Exec_Bridge.thy`) still uses directly.
`rhs_combine_sources`/`rhs_sources` (`Constraint_System.thy`),
`combine_of_bound` (new, `Constraint_System_Sound.thy`, mirroring
`call_enter_of_bound`), `tf_combine_le_rhs` (renamed from `combine_abs_le_rhs`),
and `LTR_Analysis_Sound.thy`'s COMB obligation (`ltr_post_fixpoint_sound_at`,
`unified_ltr_post_fixpoint_sound`) all route through it.  `sign_tf`/`ivl_tf`
(`Sign_Transfer.thy`, `Interval_Transfer.thy`) set `tf_combine` to the existing
default (`combine_sign`/`combine_abs`), so both instances are behaviorally
unchanged - Sign and Interval do not yet exercise a non-default merge, but any
future analysis with a relational or otherwise non-structural env-merge now can,
without touching the DG layer, the solver, or any existing instance.

**Deferred: the DG layer's `dgs_combine` has the same single-phase shape.**
`dgs_combine` (`DG_Framework.thy:238`) is analysis-*parametrized* (Site A was
already closed in that sense, per the earlier audit above) but is still a single
call, with no `combine_env`/`combine_assign` split - the same architectural gap
just closed at the flat layer. This is not a blocking gap today: no DG instance
needs it, since Sign/Interval/Mixed all use the structural default
(`unit_combine_step`, built from `combine_collect_abs`) and no relational DG
instance exists. Revisit alongside Octagon or any other relational domain
(`AGENTS.md`'s locked-decisions table lists it as a stretch goal); do not conflate
"Site A is analysis-parametrized" with "Site A matches Goblint's phase
structure" - they are independent properties, and only the first has ever held
for Site A.

**Effort:** landed. Touched `Constraint_System.thy`, `Constraint_System_Sound.thy`,
`LTR_Analysis_Sound.thy`, `Sign_Transfer.thy`, `Interval_Transfer.thy`, and one
example (`Example_Proc_Call.thy`, which had manually inlined the old
`combine_collect_abs` shape to verify a post-fixpoint). `Voblint_Analysis`,
`Voblint_Formalization`, and `Voblint_Examples` all batch-build green.

Related: `docs/SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md` G2/M2 - a DG-layer defect in
the same call/return lifecycle, but in context *routing* (which slot entry and
return read/write), not in combine. Routing and combine are separate concerns:
G2/M2 fixes which slot is read; this gap fixes what happens with the two values
once found. Fixing one does not fix the other.

---

### Gap 4 — local and global domains are distinct types (`D.t ≠ G.t`)

**Goblint's `GlobConstrSys`:**

```ocaml
module D : Lattice.S   (* local domain *)
module G : Lattice.S   (* global domain *)
```

Locals and globals can have completely different lattice types. A pointer analysis
might use `D.t = vname -> points_to_set` for locals and `G.t = heap_cell -> value_set`
for globals. The two domains never need to be compared or joined directly.

**Audit update (2026-07-28).** The line above is only true of the older
flat/monovariant track (`Constraint_System.thy`, `TD_Side_CFG.thy`). The D/G
layer already closes this gap.

`dg_state` (`DG_Framework.thy:36`) has two independent type parameters:
`datatype ('l, 'g) dg_state = DG (locals: 'l) (globs: 'g)`, with a
componentwise lattice order (`DG_Framework.thy:38-105`). `dg_spec`
(`DG_Framework.thy:232-238`) types every field over independent `'dl`/`'dg`,
constrained only to `bounded_semilattice_sup_bot` - not to `abs_state` at
all. `sound_dg_spec` (`DG_Soundness.thy:127-147`) fixes
`'D`/`'G :: bounded_semilattice_sup_bot` and `gammaDG :: 'D => 'G => store
set` independently, with no assumption forcing them equal.

This is exercised, not just type-checked: `indep_dg_spec :: 'd::sound_domain
domain_transfer => 'g::sound_domain domain_transfer => ('d abs_state, 'g
abs_state) dg_spec` (`DG_Soundness.thy:727-730`) is instantiated at
`mixed_si_spec :: (sign abs_state, ivl abs_state) dg_spec`
(`Mixed_Sign_Interval.thy:43-44`) - local unknowns tracked by Sign, global
unknowns tracked by Interval, genuinely different lattices, proved sound
(`mixed_si_spec_indep`, `Mixed_Sign_Interval.thy:119-127`) and batch-green.

The vendored `TD_side` solver (`vendor/td-verification/`) does fix one value
type `'d` per `strategy_tree`/state map (`TD_side.thy:16-22`,
`Basics_side.thy:94-97`) - `dg_state` is exactly the "flatten to one type at
the interface boundary" workaround this section's own text names as the
alternative to a vendor rewrite. Already built, already proven.

**What remains open (audit refined 2026-07-28).** `dg_ctx_activation`
(`DG_Ctx_Activation.thy:18-19`, Track 1's context-sensitive/routed locale)
only interprets `sound_dg_spec` at the homogeneous
`('a abs_state, 'a abs_state) dg_spec` - combining real `'D != 'G` with
context-sensitivity is unexercised. The earlier `is_global`-occurrence check
was the wrong signal for this file - the real blocker is `gamma_unit d g =
\<lbrakk>d \<squnion> g\<rbrakk>` (`DG_Soundness.thy`), which requires `d`/`g` to share one type
to type-check `d \<squnion> g` at all. This is not a peripheral dependency: every
non-trivial lemma in `DG_Ctx_Activation.thy` routes through it -
`sg_cov`'s own assumption (`sg (Inl (v,c)) = locals (sigma (Inl (v,c))) \<squnion>
globs (sigma (Inr gk0))`, line 35), `dg_ctx_act_edge`
(lines 168-197), and `dg_ctx_act_comb_covered` (lines 208-241) all build their
soundness chain through `gamma_unit`/`gamma_unit_mono` specifically, not
through the already-heterogeneous `sound_dg_spec.gammaDG`/`gamma_dg`
(`DG_Soundness.thy:106-109`, already independent-typed and already exercised
by `indep_dg_spec`). The locale's own `sg` parameter is typed
`pp \<times> 'c + 'k \<Rightarrow> 'a abs_state` - homogeneous by construction, not just by an
unexercised choice. A heterogeneous version needs a new locale built on
`gamma_dg` (already proven monotone, already sound) with `sg`'s type and
every routing lemma redesigned around it, not a re-instantiation of the
existing one. Also open: `mixed_si_spec`'s `'D`/`'G` are both still
`abs_state`-shaped (pointwise, different value lattices); a structurally
different index set (Goblint's `heap_cell -> value_set` example) needs Gap
5's abstract-state work first.

**Effort:** the type-level gap is closed. Extending it to context-sensitivity
is new locale architecture, not a mechanical generalization - comparable in
size to `DG_Ctx_Activation.thy` itself (245 lines), reusing `gamma_dg`'s
already-proven pieces but redesigning `sg`'s type and every `dg_ctx_act_*`
proof around it. No current instance needs this (the one context-sensitive
instance, the Interval flagship, is itself homogeneous); building it now
would be ahead of an actual requirement. Revisit when a context-sensitive
heterogeneous analysis is actually planned. Retiring the older homogeneous
flat track, if wanted, should reuse `Split_State.thy`'s existing
`('l,'g) split_state` pair type and isomorphism lemmas rather than a new type
from scratch - except `restrict_local_global_join` (`TD_Side_CFG.thy:33-35`),
which cannot be
type-class-generalized and must become pair projection instead.

---

### Gap 5 — `'a abs_state = vname -> 'a` excludes relational domains

**Status: architecture and executability both validated.** `Rel_Order_Domain.thy`
interprets `sound_dg_spec` over `relc`, a non-`abs_state` relational carrier,
with zero DG-framework changes, *and* runs end to end through the real
`dg_gen_of`/vendored-solver pipeline (`Example_Relational_DG_Demo.thy`) on a
compiled IMP2 program, batch-green. Full investigation, option comparison,
and the executable follow-through live in
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md`. This section summarizes
the finding; that document is the source of truth for detail.

**The structural issue, restated precisely.** `'a abs_state = vname -> 'a`
is nonrelational at the *flat equation-system spine*
(`Constraint_System.thy`) — true, and the type-class sketch this section
used to propose closing it there is real, correct engineering. But per this
project's own contract, Sign/Interval/Mixed do not execute through that
spine; they run through `DG_Framework.thy`/`DG_Soundness.thy`. Tracing that
layer directly shows its soundness locale, `sound_dg_spec`, is **already**
a locale over an opaque, arbitrary joint concretization
(`fixes S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec" and gammaDG :: "'D => 'G => store set"`,
`DG_Soundness.thy:127-147`) — no `abs_state`, no pointwise structure
required by the locale itself. What's box-only is every existing
*interpretation* of it (`unit_dg_spec`, `indep_dg_spec`, `mixed_si_spec`
all *choose* `'dl`/`'dg = _ abs_state`), not the framework.

**What closing it actually requires: a new `dg_spec` instance, not a
spine migration.** A relational domain is a new `'dl`/`'dg` type, a
`dgs_assign`/`dgs_assume`/`dgs_assume_not`/`dgs_enter`/`dgs_combine_env`/
`dgs_combine_assign` implementation, and a `gammaDG` discharging
`sound_dg_spec`'s four obligations — zero edits to `Constraint_System.thy`,
`DG_Framework.thy`, `DG_Soundness.thy`, or any existing Sign/Interval/Mixed
proof. The type-class migration this section previously proposed remains a
legitimate refactor of the flat spine on its own merits, but is not a
prerequisite: this project already built and later did not keep a
type-class `abs_state` once (`docs/DOMAIN_TYPECLASS_MIGRATION.md`, status
"DONE," predating the `Domains/` -> `Generic/` restructuring), which is
independent evidence against treating it as required groundwork here.

**Effort, decomposed** (previously a flat 4-6 weeks; the decision doc breaks
this down by what's actually being built):

- A minimal, sound, executable, octagon-*shaped* domain (no closure, no
  Goblint-precision parity): days-to-low-weeks — comparable to a single new
  Sign/Interval-sized instance file, because skipping closure and accepting
  a conservative interprocedural combine (both fine for a first instance)
  removes the two things that make relational domains hard in the
  literature.
- Goblint-parity octagon (real DBM closure, Miné's full transfer-function
  case table): weeks-to-months — matches epic #25's own estimate; "no
  reusable Isabelle prior art... mechanization from scratch" (epic #25's own
  words), the genuinely hard part, unaffected by which architecture option
  is chosen.
- A literal Apron-backed domain: not comparably scoped — requires inventing
  a certifying-oracle trust architecture around an unverified external
  library, a different kind of project.

**Note:** the Octagon track (`docs/RELATIONAL_DOMAIN_PLAN.md`, issue #25)
lists a two-layer split as a blocker; `RELATIONAL_DOMAIN_PLAN.md` is now
marked superseded by the decision doc above for the same reason — its
Approach A also targeted the flat spine.

---

### Gap 6 — termination assumed, not proved

**What Goblint does:** the TD solver applies widening at back-edges (or at every
stabilization point). Widening on a lattice of finite height guarantees ascending
chain termination. Goblint proves this as part of the solver correctness argument.

**What we do:** assume `solve_dom v` (the solver terminates when queried at `v`) and
prove soundness conditional on it. We have `abstract_domain` with a `widen` operator
but no proof that the TD solver, applied to our constraint system with widening,
actually terminates.

**What closing it would require:**

1. Prove that the Sign domain (finite height: `{SBot, SNeg, SZero, SPos, STop}`)
   always terminates without widening — since the lattice is finite, all ascending
   chains stabilise.
2. Prove that the Interval domain, equipped with the standard widening
   (`[-∞,n] widen [-∞,m] = [-∞,∞)` when `m > n`), terminates.
3. Prove that the TD solver applied to a monotone equation system over a
   finite-height lattice with widening terminates — i.e., `∀v. solve_dom T v`.

Step 3 requires a termination proof for the vendored `TD_side` solver itself, which
is a significant undertaking (the vendored repo does not currently include this; it
leaves termination to the user, matching our `solve_dom` assumption).

Alternatively, for finite-height domains: `∀v. solve_dom T v` follows from a
termination witness constructed by transfinite induction on the lattice height — no
widening needed. This is feasible for Sign (height 5) and plausible for finite
abstract domains generally.

**Effort:** 1–2 weeks for Sign (finite-height argument). 3–4 weeks for Interval
(widening termination). Full generality: open research.

---

### Gap 7 — context sensitivity (`C : Printable.S`) (partially closed)

**Goblint's `LVar.t = node × C.t`** — each local unknown is a pair of CFG node and
call-string context. Different call sites of the same procedure get different unknowns
and are analysed with different initial states. This is the main source of
interprocedural precision in Goblint.

**What we do:** semantic context-indexed collection and context-domain contracts
exist; some executable keyed instances also use `(pp, context)`. The remaining
gap is a generic executable D/G generator that computes, routes, and seeds the
callee context at every call, plus computed/bounded context schemes.

**What closing it would require:**

Finish the generic executable route over `pp × 'ctx` and instantiate it with a
computed context scheme. The constraint system type is already available in the
semantic layer:

```isabelle
type_synonym ctx_pp = "pp × 'ctx"
```

The key design question is what `'ctx` is: call-string of bounded depth `k` is the
standard choice. Goblint-style context creation occurs at calls, not by threading
the context through ordinary CFG edges. The executable generator must publish the
callee seed to its selected context and read it at the callee entry.

The soundness statement generalises: at each `(node, ctx)` unknown, the abstract
state over-approximates the concrete stores reachable at `node` via runs consistent
with call-string `ctx`.

**Effort:** the semantic proof infrastructure is landed. The remaining generator
and call-string work is tracked by Route A7 and M1; dynamic bounds are M3b.

---

### Gap 7a — inter-analysis queries (`man.ask` / `man.emit`)

```ocaml
ask  : 'a Queries.t -> 'a Queries.result
emit : Events.t -> unit
```

Goblint analyses can query other active analyses mid-TF (e.g., the taint analysis
querying the value analysis for concrete bounds, or the race-condition analysis
querying the thread analysis). We have a single monolithic analysis with no query
bus.

**Scope judgement:** out of scope. Modelling multi-analysis interaction requires a
whole-system framework beyond a single equation system. The NASA FM 2026 paper
(Tilscher et al.) addresses solver correctness for this setting; our thesis is on
the domain-instance axis of a single analysis.

---

## Priority ordering

For a post-thesis extension:

1. **Gap 6 (termination, Sign case)** — cheapest, closes an honest gap, gives a
   stronger theorem for Sign.
2. ~~**Gap 3 (analysis-specific combine, flat layer only)**~~ — closed
   (2026-07-28): `domain_transfer` carries `tf_combine`, `sound_transfer` carries
   `tf_sound_combine`, and the flat/context-insensitive spine
   (`rhs`/`rhs_sources`/`LTR_Analysis_Sound.thy`) routes through it. The DG
   layer's `dgs_combine` is analysis-parametrized but still single-phase;
   revisit only alongside a relational DG instance (see Gap 3's own section).
3. **Gap 5 (relational domains)** — first instance built and executable
   (2026-07-28, `docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md`): a new
   `dg_spec` instance (`relc`, a deliberately imprecise two-variable
   order-constraint domain) against the already-generic `sound_dg_spec`
   locale, no spine/type-class migration, and it runs through the real
   `dg_gen_of`/vendored-solver pipeline end to end
   (`Example_Relational_DG_Demo.thy`). Goblint-parity octagon remains
   weeks-to-months and is a separate, later decision (aligns with the
   Octagon track, issue #25).
4. ~~**Gap 4 (D.t ≠ G.t)**~~ — mostly closed (2026-07-28): the D/G layer
   (`dg_spec`, `dg_state`) already types locals and globals independently and
   `Mixed_Sign_Interval.thy` exercises it. Remaining: context-sensitive DG
   with `D ≠ G` is unexercised (~1-2 weeks, see Gap 4's own section).
5. **Gap 7 (executable contexts and lifters)** — Route A7/M1/M3b; semantic
   context sensitivity is already available.
6. **Gap 7a (inter-analysis queries)** — out of scope.

---

## Relationship to existing plans

| Plan | Closes |
| --- | --- |
| `EFFECTFUL_TF_MIGRATION.md` | Gaps 1–2 |
| `ARRAY_SYNTAX_EXTENSION.md` | Array-only part of the source-language boundary |
| `NONDET_HAVOC_MIGRATION.md` | Nondeterministic source expressions needed by relational examples |
| `RELATIONAL_DOMAIN_PLAN.md` + issue #25 | Requires Gaps 3 (flat layer) + 5 as prerequisites |
| `SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md` G2/M2 | DG-layer context routing - adjacent to Gap 3, not a substitute for it |
| `OPEN_PROBLEMS.md` P11 + `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` Slice 7 | Per-origin update transport and solver integration |
| `M1_CALLSTRING_CONTEXT_MIGRATION.md` + `M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md` | Computed and dynamically bounded contexts |
| `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` Slice 8 | Multi-analysis product/sum and query bus |
| `INTERVAL_REINTRODUCTION_PLAN.md` | Partial Gap 6 (widening needed for termination) |
| This document | Gaps 3–7 (long-term) |

The thesis statement in `src/Analysis/Generic/Equations/README.md` explicitly scopes these
gaps out. That framing is correct and should be kept. This document exists so the
gaps are named, estimated, and not forgotten.
