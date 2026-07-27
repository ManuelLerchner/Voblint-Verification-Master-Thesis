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

**Still open, in the flat/context-insensitive constraint system.**
`combine_abs_le_rhs` (`Constraint_System_Sound.thy:95-109`) calls
`combine_collect_abs` (`Constraint_System.thy:411-413`) directly, with no record
field or locale parameter to override it. This is the layer
`LTR_Analysis_Sound.thy:86` builds the project's context-insensitive soundness
spine on (`ltr_collect`, per `CLAUDE.md`'s project contract). This is the real
remaining target of Gap 3.

**What closing the flat-layer gap would require:**

Add a `combine :: vname option => 'a abs_state => 'a abs_state => 'a abs_state`
field to `domain_transfer` (or a new record), defaulting to `combine_collect_abs`
so every existing Sign/Interval instance is unchanged. Re-state `rhs`/
`rhs_combine_sources` (`Constraint_System.thy`) and `combine_abs_le_rhs`
(`Constraint_System_Sound.thy`) over the abstract field, and re-prove
`combine_states_sound`/`combine_collect_sound` as the soundness obligation a new
`combine` instance must discharge - structurally parallel to
`sound_dg_spec.combine_sound` above, not a new design. `LTR_Analysis_Sound.thy:86`
and its consumers need the added combine-soundness hypothesis threaded through.

Do not read the DG layer's `dgs_combine` as evidence that this half is done -
it is a separate spine with its own hardwired call.

**Effort:** medium, scoped to `Constraint_System.thy`, `Constraint_System_Sound.thy`,
`LTR_Analysis_Sound.thy`, and domain soundness interpretations that feed the
flat/context-insensitive spine. Substantially less than the original 2-3 week
estimate, since the DG-layer half no longer needs this work.

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

**What we do:** both local unknowns (`σ(Inl v)`) and global unknowns (`σ(Inr g)`)
have type `'a abs_state = vname -> 'a`. Same type, same index set.

**What closing it would require:**

Introduce a type parameter `'g_val` for the global domain, separate from `'a` for
the local domain. The constraint system becomes:

```isabelle
type_synonym ('a, 'g_val) combined_state =
  "(pp + 'g) => ('a abs_state + 'g_val)"
```

or equivalently, two separate maps `σ_local : pp => 'a abs_state` and
`σ_global : 'g => 'g_val`. Strategy trees then have two `Answer` payload types.
The vendored solver would need to be generalised (or the flattening to a single type
done at the interface boundary, as Goblint's `Var2` does).

**Effort:** 3–4 weeks. High foundational cost; touches nearly every theory file.
The current single-type approach is a pragmatic simplification worth keeping for
the thesis.

---

### Gap 5 — `'a abs_state = vname -> 'a` excludes relational domains

**The structural issue:** our abstract state is a point-wise function `vname -> 'a`.
This is a product domain — each variable is tracked independently. Relational domains
(octagons, polyhedra, affine equality) represent joint constraints over the entire
variable set as a single opaque object, not as independent per-variable values.

**What closing it would require:**

Replace `type_synonym 'a abs_state = "vname => 'a"` with an abstract type class:

```isabelle
class abstract_state =
  fixes gamma_state :: "'a => store set"
  fixes join_state :: "'a => 'a => 'a"
  fixes bot_state :: "'a"
  fixes apply_assign :: "vname => aexp => 'a => 'a"
  fixes apply_assume :: "bexp => 'a => 'a"
```

Every downstream lemma that pattern-matches on `σ x` (for some variable `x`) would
need to be re-stated in terms of `gamma_state` only, not on the internal structure
of the state. The collecting semantics side remains concrete (`store = vname -> int`);
the abstract side becomes opaque.

This is a substantial architectural change. `restrict_local`/`restrict_global` also
rely on the product structure; they would be replaced by abstract `project_local` /
`project_global` operations with soundness axioms.

**Effort:** 4–6 weeks. Prerequisite for octagons.

**Note:** the Octagon track (`docs/RELATIONAL_DOMAIN_PLAN.md`, issue #25) already
lists this as a blocker.

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
2. **Gap 3 (analysis-specific combine, flat layer only)** — medium effort,
   prerequisite for relational domain soundness at procedure boundaries in the
   context-insensitive spine. The context-sensitive DG layer already supports
   this through `dgs_combine`.
3. **Gap 5 (abstract state type class)** — high effort, prerequisite for octagons;
   aligns with the Octagon track (issue #25).
4. **Gap 4 (D.t ≠ G.t)** — high effort, low payoff for IMP2 scope; would matter
   for a heap analysis.
5. **Gap 7 (executable contexts and lifters)** — Route A7/M1/M3b; semantic
   context sensitivity is already available.
6. **Gap 7a (inter-analysis queries)** — out of scope.

---

## Relationship to existing plans

| Plan | Closes |
|---|---|
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
