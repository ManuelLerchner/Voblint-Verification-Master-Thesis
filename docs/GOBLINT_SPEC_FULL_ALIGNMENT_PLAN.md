# Long-term plan — full Goblint Spec alignment

Status: **LONG-TERM / STRETCH** (research findings 2026-06-17, not started).

The effectful-TF migration (`docs/EFFECTFUL_TF_MIGRATION.md`) closes Gaps 1–2
(named globals, effectful transfer functions). This document records the remaining
structural gaps between our proof and Goblint's full `Spec` / `GlobConstrSys`
interface, and sketches what closing each would require. None of this is required
for the thesis; it is a roadmap for post-thesis extension.

Related: `src/Analysis/Equations/README.md` §Scope vs. Voblint's actual framework —
deliberately lists these extensions as out of scope for the current thesis axis.

---

## Gap inventory

### Gap 3 — analysis-specific interprocedural combine

**Goblint's `Spec` requires:**

```ocaml
val combine_env    : (D, G, C, V) man -> D.t -> D.t -> D.t
val combine_assign : (D, G, C, V) man -> lval -> exp -> D.t -> D.t -> D.t
```

The first argument is the callee's exit state; the second is the caller's state at
the call site. Each analysis decides how to merge them. `combine_assign` additionally
receives the syntactic call `lval := f(args)` to adjust the return value.

**What we do:** fixed structural combine — `restrict_local` of caller joined with
`restrict_global` of callee. This works for Sign and Interval (per-variable domains
commute with the split) but breaks for relational domains: an octagon relating local
`x` to global `G` cannot be split by variable name without losing the constraint.

**What closing it would require:**

Add `combine_env` and `combine_assign` fields to `effectful_domain_transfer` (or a
new `interprocedural_domain_transfer` record). The `combining` locale in
`Constraint_System_IP_Sound.thy` currently hardwires `restrict_local`/`restrict_global`;
it would need to be parameterised over an abstract `combine` operation with axioms:

```isabelle
locale combining_domain =
  fixes combine :: "'a abs_state => 'a abs_state => 'a abs_state"
  assumes combine_sound:
    "\<forall>s_caller s_callee.
       s_caller \<in> gamma_state local_pre \<Longrightarrow>
       s_callee \<in> gamma_state callee_exit \<Longrightarrow>
       combine_states s_caller s_callee \<in> gamma_state (combine local_pre callee_exit)"
```

The soundness proof for `post_fixpoint_sound_at_ip` would then discharge this
obligation rather than applying the hardwired split lemmas.

**Effort:** 2–3 weeks. Touches `Constraint_System.thy`,
`Constraint_System_IP_Sound.thy`, `Analysis_Sound.thy`, all domain soundness
interpretations, and the interprocedural combine lemmas in `CFG_Collect_IP_Adeq.thy`.

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

### Gap 7 — context sensitivity (`C : Printable.S`)

**Goblint's `LVar.t = node × C.t`** — each local unknown is a pair of CFG node and
call-string context. Different call sites of the same procedure get different unknowns
and are analysed with different initial states. This is the main source of
interprocedural precision in Goblint.

**What we do:** `LVar.t = pp` — bare CFG node. All calls to the same procedure share
one set of local unknowns. The FI global unknown accumulates contributions from all
call sites, limiting precision (see §2 example in `EFFECTFUL_TF_MIGRATION.md`).

**What closing it would require:**

Replace `pp` with `pp × 'ctx` throughout. The constraint system type becomes:

```isabelle
type_synonym ctx_pp = "pp × 'ctx"
```

The `compile_prog` / `compile_com` functions would need a context-threading argument.
The key design question is what `'ctx` is: call-string of bounded depth `k` is the
standard choice. Context creation happens at `EA_Enter` edges; the TF for `EA_Enter`
receives the call-string and extends it.

The soundness statement generalises: at each `(node, ctx)` unknown, the abstract
state over-approximates the concrete stores reachable at `node` via runs consistent
with call-string `ctx`.

**Effort:** 4–6 weeks for the proof infrastructure. The `compile_prog` / CFG layer
is currently context-free; threading `'ctx` through would require pervasive changes.

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
2. **Gap 3 (analysis-specific combine)** — medium effort, prerequisite for
   relational domain soundness at procedure boundaries.
3. **Gap 5 (abstract state type class)** — high effort, prerequisite for octagons;
   aligns with the Octagon track (issue #25).
4. **Gap 4 (D.t ≠ G.t)** — high effort, low payoff for IMP2 scope; would matter
   for a heap analysis.
5. **Gap 7 (context sensitivity)** — very high effort, significant precision gain.
6. **Gap 7a (inter-analysis queries)** — out of scope.

---

## Relationship to existing plans

| Plan | Closes |
|---|---|
| `EFFECTFUL_TF_MIGRATION.md` | Gaps 1–2 |
| `RELATIONAL_DOMAIN_PLAN.md` + issue #25 | Requires Gaps 3 + 5 as prerequisites |
| `INTERVAL_REINTRODUCTION_PLAN.md` | Partial Gap 6 (widening needed for termination) |
| This document | Gaps 3–7 (long-term) |

The thesis statement in `src/Analysis/Equations/README.md` explicitly scopes these
gaps out. That framing is correct and should be kept. This document exists so the
gaps are named, estimated, and not forgotten.
