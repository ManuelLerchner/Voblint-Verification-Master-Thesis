# Investigation: call-string precision comparison architecture

Investigation only, per the freeze on `Call_String_Context.thy`. No code
changed. Question: what is the proof shape for a future
`Call_String_Precision.thy`, and which comparison object (context /
unknown-space / semantic-trace / solver-result) carries the least risk?

## Status

The concrete target this investigation converged on in section 10 is proved:
`project_sigma_part_post_solution` in `Call_String_Solver_Refinement.thy`
projects the computed 2-call-string solution onto the 1-call-string
dependency cone and shows the projection is a `part_post_solution` of the
1-call-string equations, closing the `sides_of_rhs` obligation section 10.4
identified as the load-bearing check.

That proof enumerates its dependency cone by hand, per witness node, rather
than by a general construction. `CALLSTRING_PROJECT_SIGMA_GENERALIZATION_DESIGN.md`
works out what a general construction over arbitrary dependency graphs looks
like, including the cyclic case this investigation's sections did not reach.

## 1. Step 1 (context projection) is already available, checked by hand

The proposed commuting diagram —

```isabelle
k1 <= k2 ==>
cs_project k1 (cs_route k2 u ctx d ca) = cs_route k1 u (cs_project k1 ctx) d ca
```

(`cs_project k ctx == take k ctx`) — decomposes into two facts, both already
landed or one line away:

1. `cs_route_k_mono` (landed): `take k1 (cs_route k2 u ctx d ca) = cs_route k1 u ctx d ca`.
2. An idempotence fact, checked algebraically, not yet landed since
   `Call_String_Context.thy` is frozen:
   `cs_route k u (take k ctx) d ca = cs_route k u ctx d ca`, unconditional in
   `k` (no `k1 <= k2` needed). Proof by cases on `k`: `k = 0` is `[] = []`;
   `k = Suc n` reduces (via `take`'s `Cons` case) to `take n (take (Suc n) ctx)
   = take n ctx`, which is `take_take`'s min-absorption since `n <= Suc n`.

Composing (1) and (2) (used right-to-left) gives the commuting diagram
directly. **Step 1 needs no new proof principle** — it is a two-line
corollary of what already exists, whenever `Call_String_Context.thy` is
unfrozen for it.

## 2. The unknown-space type-mismatch risk is avoidable, not inherent

The task's risk list named "different unknown spaces" (`k=1: pp x node`,
`k=2: pp x node list`) as a blocker. Checked: this is real only if the *old*
`Example_Interval_DG_CallString.thy` (`route_cs`, context type bare
`cfg_node`) is one side of the comparison — which is exactly the file the
extraction task deliberately left untouched (design doc section 8). If a
future k=1 baseline is instead built the same way as the k=2 POC — a new
`interpretation` using `cs_route 1`/`cs_enterc 1` from the shared library —
both sides of the comparison share the identical type `pp * cfg_node list`,
identical `dg_ctx_activation`/`routed_context` shape, and identical domain.
**Prerequisite for any precision work: a `cs_route`-based k=1 companion
instance, not a bridge to the old `route_cs` file.**

**Status: done.** `Example_Interval_DG_CallString_K1.thy` and `_K2.thy`
(`src/Examples/Interval/CallString/`) are exactly this pair — both on the
same `nest_cfg` program, same `dg_ctx_activation`/`routed_context` shape,
same domain, unknown-space types `pp * cfg_node list` on both sides. This
was landed as the empirical precision witness (design doc section 9), not
as a bridge to the old `route_cs` file, and satisfies this prerequisite.

## 3. Historical precedent: the deleted architecture proved this at the trace level, not the solver level

Checked `archive/relational-digest-experiment` (commit `4779e90f`,
`src/CFG/Collecting/CFG_Collect_Trace.thy`) for how the now-deleted digest
architecture handled exactly this comparison:

```isabelle
lemma cfg_collect_ctx_subset_flat:
  "cfg_collect_ctx dg cmp g S v c \<subseteq> alpha_last (cfg_collect_trace g S v)"
  unfolding cfg_collect_ctx_reaching_compat
  by (rule alpha_last_mono[OF reaching_compat_subset])
```

One line, entirely at the trace-collecting level (`cfg_collect_ctx`,
`cfg_collect_trace`) — no solver, no widening, no iteration order. The
"coarser context subsumes finer" argument was a monotonicity fact through an
abstraction map (`alpha_last`) applied to a subset relation on which traces
a compatibility predicate keeps (`reaching_compat_subset`). This is direct
evidence that the "hard part" the task worried about (solver correspondence)
is a property of comparing *solved results* specifically, not an inherent
property of comparing *any* two context granularities.

## 4. The same shape exists on the retained architecture

This session's architecture ( `valid_ltr` / `key` / `activation_collect`,
`LTR_Def.thy`) has the analogous structure, arguably simpler than
the deleted one: `valid_ltr gs g S` is a single trace set that does **not**
depend on `enterc` at all — `enterc` only enters via the `key` projection
`activation_collect` applies on top. Concretely:

- `activation_collect gs enterc seedc g S v ctx` selects traces
  `t \<in> valid_ltr gs g S` with `sink_node t = v` and `key enterc seedc t = ctx`
  (`activation_collect_I`/`_E`, `LTR_Def.thy`).
- The candidate semantic inclusion, for a `cs_enterc`-based k1/k2 pair on the
  *same* program and the *same* `valid_ltr` set (concretely available now as
  `nest_1_dg`/`nest_2_dg` in `Example_Interval_DG_CallString_K1.thy`/`_K2.thy`,
  both over `nest_cfg`):

  ```isabelle
  key (cs_enterc 1) [] t = take 1 (key (cs_enterc 2) [] t)
  ```

  for every `t`, provable by induction on `t`'s constructor (`Root`/`Call`/
  `Resume`, `LTR_Def.thy:82-84`), using `cs_enterc_k_mono` at each
  `Call` step (where `key`'s recursion calls `enterc` on the parent's
  already-computed context — exactly `cs_enterc_k_mono`'s hypothesis shape).
  `Resume`'s case is immediate (`key` is unchanged across a return, per its
  own definition). This is the "projection relation" `cs_route_k_mono`/
  `cs_enterc_k_mono` were built to support (their own doc comment already
  said so).
- That gives directly, with **no solver reasoning**:

  ```isabelle
  activation_collect is_global (cs_enterc 2) [] g S v ctx2
    <= activation_collect is_global (cs_enterc 1) [] g S v (take 1 ctx2)
  ```

  a pure trace-level inclusion, the semantic-layer analogue of
  `cfg_collect_ctx_subset_flat`.

## 5. What this gets you, and what it does not

Combined with the two *already-proven* soundness theorems
(`nest_1_activation_collect_sound` and `nest_2_activation_collect_sound`,
both landed per section 2's prerequisite), the semantic inclusion transports
into a bound on the k=2 activation collection via the k=1 solved result:

```isabelle
activation_collect is_global (cs_enterc 2) [] g S v ctx2
  <= [ivl_ctx_sg_1 (Inl (v, take 1 ctx2))]
```

This is a genuine, solver-independent fact and is cheap to reach once the
section 4 induction lands. **It is not yet the literal precision claim**
(`gamma (sigma_k2 x2) <= gamma (sigma_k1 (project x2))`, the task's "option
C"): that statement compares the two *solved* `ivl_ctx_sg` values directly,
and nothing above relates `ivl_ctx_sg_2` to `ivl_ctx_sg_1` — both are
independently sound upper bounds on the same (now demonstrably related)
semantic sets, not shown comparable to each other. Closing that gap likely
needs an optimality/minimality argument (`least_partial_post_solution`,
already named in `docs/history/M1_CALLSTRING_CONTEXT_MIGRATION.md` section 1 as a
property `TD_side` retains) — genuinely open, not investigated here, and
should not be assumed easy.

## 6. Revised staged recommendation

The task's own A/B/C map onto, in order of what is now known:

| # | Comparison object | Status |
| --- | --- | --- |
| 1 | Context projection (`cs_project`/commuting diagram) | done by hand (section 1), two-line corollary once unfrozen |
| 2 | Trace-set inclusion (`activation_collect` at k2 vs k1) | **done**, landed as `call_string_collecting_mono` (`Call_String_Collecting_Refinement.thy`) |
| 3 | Solved-result comparison (`ivl_ctx_sg_2` vs `ivl_ctx_sg_1`) | genuinely open; investigated (section 8) — not a short corollary of row 2, needs a different route |

Recommended order, revised from "start with a single witness program, not a
general theorem" (still correct) plus this investigation's finding: attempt
row 2 (trace-level inclusion) as the first real proof, since it has a
working precedent to copy the *shape* of (not the code — the deleted
architecture's constructs are gone) and does not require solving row 3's
open optimality question at all. If row 2 alone is judged sufficient
evidence of "the analysis actually gets more precise" for the thesis's
purposes, row 3 may not be needed. If row 3 is required, row 2's inclusion
is very likely a necessary lemma inside it regardless, so it is not wasted
work either way.

## 7. Immediate prerequisite (small, mechanical, not precision work) — done

Before any of the above: build a `cs_route 1`/`cs_enterc 1` companion
instance so both sides of a future comparison share one type and one
library. **Landed**: `Example_Interval_DG_CallString_K1.thy` and `_K2.thy`
(`src/Examples/Interval/CallString/`), both over a nested-call program
(`nest_cfg`, `main -> f -> g` reached through two distinct outer call sites)
rather than the old flat `twice_cfg` — `twice`'s call graph cannot separate
any two contexts at any `k`, so it could not have served this purpose (see
design doc section 9). This was infrastructure in the same sense the k=2
POC was — a mechanical instantiation, not a new abstraction — and its
completion is the prerequisite section 2 named, for both row 2 and row 3
of the table above.

## 8. What relates `activation_collect` to the solved result — investigated

The question: does anything in the DG/solver layer already give a
Galois connection, a best-correct-approximation theorem, or an
optimality/minimality result strong enough to turn row 2's trace-level
inclusion into row 3's solved-result comparison? Checked directly against
the DG soundness layer (`DG_Ctx_Activation.thy`, `DG_Soundness.thy`) and
the vendored solver (`vendor/td-verification/TD_side.thy`,
`src/Analysis/Generic/Solver/Core/TD_Side_Eff_Interface.thy`). Answer: no
Galois connection, no completeness theorem — a repo-wide check for
`complete`/`exact_dg`/`precise_dg`/any equality between `activation_collect`
and a `gamma`-image turned up zero hits. Two facts exist, on two different
axes, and neither alone bridges row 2 to row 3.

**Fact 1 — soundness only, one direction.** Every headline theorem in this
layer (`nest_1_activation_collect_sound`, `nest_2_activation_collect_sound`,
and the generic `activation_collect_sound` they instantiate) states

```text
activation_collect gs enterc seedc g S v c  <=  gamma (locals (sigma (Inl (v,c))))
```

— the collected concrete states are a subset of what the abstract value
denotes. There is no lemma anywhere in `DG_Ctx_Activation.thy` or
`DG_Soundness.thy` stating the reverse inclusion or an equality. This is
expected (`sound_dg_spec` is a soundness locale, not an exactness one), but
it means two independently sound upper bounds — `ivl_ctx_sg_2` and
`ivl_ctx_sg_1` — do not become comparable just because their underlying
concrete sets (row 2) are now known to be comparable. An inclusion between
lower bounds does not transport through two independent upper bounds.

**Fact 2 — optimality, but on a different axis.** `TD_side.thy:3133`'s
`least_partial_post_solution` (exposed at the analysis level as
`td_cfg_side_solver_eff.least_part_post_at_cfg`,
`TD_Side_Eff_Interface.thy`, and already the backend both K1 and K2 run
on) says the solved `sigma` is the *least* among all partial post-solutions
of the *same fixed equation system* `T`:

```text
solve_dom x  ==>  solve x = (st, sigma)  ==>
  ALL sigma_l varsl. part_post_solution T x sigma_l varsl
    --> sigma <= sigma_l /\ st <= varsl
```

This is optimality relative to *other candidate solutions of `T`* — it
says nothing about `activation_collect` or about a *different* equation
system `T'` (e.g. the k=1 system versus the k=2 system). It is the right
tool for row 3, but not through `activation_collect`.

**The route this actually points to: work at the RHS level directly,
skip `activation_collect` for row 3.** Sketch, not verified — this is
the shape a proof would need to take, not a proof:

1. Build a candidate k=1 solution by joining the k2 solution over its
   fiber: `sigma_1' (Inl (v, ctx1)) = Sup { sigma_2 (Inl (v, ctx2))
   | ctx2. ctx2 : dom sigma_2, take k1 ctx2 = ctx1 }`.
2. Show `sigma_1'` satisfies `part_post_solution T1 x0 sigma_1' vars1'`
   for the k1 equation system `T1` — the actual technical content. Needs
   `cs_route_k_mono` again (to match up which k2-contexts fall in which
   k1-fiber) plus a monotonicity/distributivity argument for the RHS
   combinator (`side_cfg_T_eff_keyed_seed_dg`) under the domain join. Not
   attempted here.
3. Invoke `less_than_part_post_solution`/`least_partial_post_solution` on
   the k1 solve to conclude `sigma_1 <= sigma_1'`, i.e.
   `sigma_1 (Inl (v,ctx1)) <= Sup { sigma_2 (Inl (v,ctx2)) | take k1 ctx2 = ctx1 }`
   — the actual row-3 inequality, obtained without ever mentioning
   `activation_collect`.

**Difficulty:** moderate, not open-ended — the only unbounded-risk step is
(2), a single `part_post_solution` obligation. Everything it depends on
(`least_partial_post_solution`'s availability at this solver
instantiation, `cs_route_k_mono`) is already landed and already exercised
by K1/K2. Row 2's `call_string_collecting_mono` is not a required
ingredient for this route and should not be forced into it — it stands as
an independent, already-complete semantic result regardless of whether
row 3 is pursued.

## 9. Isolating the equation systems (investigated, before any proof attempt)

Per the plan: define the projection explicitly and check its algebraic
shape before touching the transfer/combine rules. Read the actual RHS
constructors directly (`side_cfg_T_eff_keyed_seed_dg`,
`DG_Constraint_Trees.thy:393`; `routed_cmb`/`routed_extra`, `Routed_Context.thy`)
rather than guessing their shape.

### 9.1 The unknown spaces are not quite the same type

`nest_1_eqs :: (pp * cfg_node list, gk_1, (ivl st, ivl st) dg_state) eqsT`,
`nest_2_eqs :: (pp * cfg_node list, gk_2, (ivl st, ivl st) dg_state) eqsT`
(`Example_Interval_DG_CallString_K1.thy`/`_K2.thy`). The **local** unknown
type `'x = pp * cfg_node list` is identical for both — `call_string` is
unbounded as a *type*, `k` only bounds *values* (design doc section 3), so
no coercion is needed there. The **global** key type differs:
`gk_1 = Global1 | Seed1 pp (cfg_node list)` vs. `gk_2 = Global2 | Seed2 pp
(cfg_node list)` — different datatypes, same payload shape. A single
uniform `project_sigma` cannot be typed as one function; it needs an
explicit case split between `Inl` (shared type, direct fiber join) and
`Inr` (different types per constructor, one mapping per constructor).

### 9.2 What the RHS actually reads, read off the definitions directly

`side_cfg_T_eff_keyed_seed_dg`'s RHS at `(v, c)` (`DG_Constraint_Trees.thy:406`)
is `side_rhs_fold_dg` over three pieces:

- `intra`: for each CFG predecessor `(u, a)` of `v` (from `pred_sel g v`,
  purely structural, **identical for T1 and T2** — same `nest_cfg`, same
  `intra_predecessor_list`), a term reading `(u, c)` — **the same context
  `c`**, never routed. Intra edges never change context, by construction.
- `comb` (`routed_cmb`): for each return site, reads the caller's own state
  at `(cc, c)` (same `c` again), computes `ctx' = route cc c (locals ...)
  ca`, then reads the callee's exit at `(ex, ctx')`.
- `extra` (`routed_extra`): at a `FunctionEntry`, reads the published seed
  `(seed_key v c)`; for each outgoing call, publishes into
  `seed_key w (route v c entry ca)`.

Every context-changing step funnels through exactly one call to `route`
(`cs_route k`), always as `cs_route k (call site) (current context) ...`.
Every context-*preserving* step (`intra`, and the caller-side reads inside
`comb`/`extra`) uses the unchanged incoming `c`.

### 9.3 `cs_route_k_mono` is exactly the fact this needs, and it is already landed

For the projection-join idea to line up, a context `c2` in `c1`'s fiber
(`take k1 c2 = c1`) must put `route`'s *output* in the fiber of `route`'s
output at `c1` too — otherwise joining over the fiber at the parent
context would not line up with joining over the fiber at the child
context. That is precisely

```text
take k1 (cs_route k2 u c2 d ca) = cs_route k1 u (take k1 c2) d ca = cs_route k1 u c1 d ca
```

— `cs_route_k_mono`, proved and landed already (`Call_String_Context.thy`,
used for row 2). Every context-changing RHS site (`comb`'s `ctx'`,
`extra`'s seed-publish target) routes through `cs_route k` exactly once,
so this one lemma covers all of them. Every context-preserving site
(`intra`, and every "read my own context" step inside `comb`/`extra`)
needs no routing lemma at all — `c` is untouched, so membership in the
fiber is inherited directly.

### 9.4 `project_sigma`, defined explicitly

Contexts reached by the solver are finite (`vars2 = fst nest_2_sol`), so
the fiber join is a finite `Finite_Set.fold`, matching this project's
existing join convention (no infinite `Sup` needed):

```text
project_sigma k1 sigma2 vars2 (Inl (v, c1)) =
  Finite_Set.fold (\<squnion>) bot
    { sigma2 (Inl (v, c2)) | c2. (v, c2) \<in> vars2 \<and> take k1 c2 = c1 }

project_sigma k1 sigma2 vars2 (Inr Global1) = sigma2 (Inr Global2)

project_sigma k1 sigma2 vars2 (Inr (Seed1 v c1)) =
  Finite_Set.fold (\<squnion>) bot
    { sigma2 (Inr (Seed2 v c2)) | c2. take k1 c2 = c1 }
```

(`Global1`/`Global2`, `Seed1`/`Seed2` are the only constructors of
`gk_1`/`gk_2`, so this is a complete case split, not a partial function.)

### 9.5 The three requested algebraic properties

- **Idempotence**, restated precisely (the literal `project_sigma k1 k1
  sigma = sigma` is false in general — a fiber can have more than one
  element even at `k1 = k1`): if every context in `vars2` already has
  `length c2 <= k1`, each fiber is the singleton `{c1}` (since `take k1 c2
  = c2` for already-short `c2`, by plain `List.take` on short lists), so
  the fold collapses to `sigma2 (Inl (v, c1))` directly. A one-line
  corollary of `take`'s behavior on lists no longer than `k1`, not new
  machinery.
- **Monotonicity in `sigma2`**: `sigma2 <= sigma2'` (pointwise) implies
  `project_sigma k1 sigma2 vars2 <= project_sigma k1 sigma2' vars2` —
  monotonicity of a finite fold of `\<squnion>` over a fixed index set in the
  folded function, a standard `Finite_Set.fold`/`SUP_mono`-shaped fact.
- **Fiber-join distributivity**: `project_sigma k1 (sigma2 with an
  additional join) = project_sigma k1 sigma2` joined the same way — holds
  by construction (a join of a join over the same index set collapses),
  not a separate proof; this is the property that makes the fold
  well-defined against `Finite_Set.fold`'s own commutativity/associativity
  requirement in the first place, not an extra fact layered on top.

None of these three touch `combine_local`/`enter_local`/`dg_spec_step` —
exactly the separation the plan asked for.

### 9.6 What is left before attacking the transfer equations

> **Landed (2026-07-31, issue #45).** `side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen`,
> `_mono_sides_gen`, `_mono_deps_gen` (`DG_Constraint_Trees.thy`) discharge the three
> `TD_side_mono` preconditions for an arbitrary `side_cfg_T_eff_keyed_seed_dg`
> instance from a per-tree contract on the `pred_sel`/`cmb`/`extra` hooks —
> mirroring `td_cfg_side_solver_eff_gen` (`TD_Side_Eff_Pipeline.thy`), the same
> reduction already landed for the flat generator. `side_rhs_fold_dg_mono`,
> `_sides_mono`, `_static_deps` (also `DG_Constraint_Trees.thy`) are the underlying
> fold lemmas, proved by structural induction over the tree list via
> `seqcomp_mono`/`static_deps_seqcomp` (`Strategy_Tree_Monad.thy`) — no new
> proof technique beyond what the flat generator's own pipeline used.
> `side_cfg_T_eff_keyed_seed_dg_threefold_mono` bundles the three into
> `TD_Side_Eff_Pipeline.thy`'s `threefold_mono`. I/Q clean, no `sorry`, batch
> green on `Voblint_Examples`. What remains is Step 3: instantiate this pipeline at
> `nest_2_eqs`'s actual `route`/`cmb`/`extra` (`routed_cmb`/`routed_extra` via
> `cs_route`, `Example_Interval_DG_CallString_K2.thy`) and discharge the nine
> primitive obligations concretely — not yet attempted.
>
> `threefold_mono` is a precondition, not a precision result: it makes the
> TD solver's ordering reasoning available for a `side_cfg_T_eff_keyed_seed_dg`
> instance, but proves nothing about any computed answer, and no analysis
> gets more precise by this lemma landing. The chain to an actual k=2-vs-k=1
> precision theorem still needs `least_partial_post_solution` (upgrading the
> existing `part_post_solution` guarantee once `threefold_mono` is
> instantiated at `nest_2_eqs`) and a `TD_side` precision theorem built on
> top of that — both still open.

The one thing not yet located: where `is_mono_eq`/`mono_sides`/`mono_deps`
(`td_cfg_side_solver_eff`'s three assumptions, `TD_Side_Eff_Interface.thy`)
get discharged for a `side_cfg_T_eff_keyed_seed_dg`-generated system.
Searched `src/Analysis` directly — no hits outside the locale's own
`assumes` clauses, so the proof lives in whatever K1/K2 actually call
(`TD_side_warrowing_apinis_Interp_solve`, via `Exec_DG_Bridge.thy`/
`Solver_Menu.thy`, neither opened yet). This matters because the
`part_post_solution` obligation in section 6's step 2 needs exactly the
same kind of fact this generic mono proof already needs — monotonicity of
`eq T x` in whatever it reads from `sigma` — just applied across two
systems (`T1` against a lifted `sigma2`) instead of within one. Likely
already available in substance, not confirmed. This is the next concrete
lookup, still before writing any part-post-solution proof.

**Net effect of this section on the outlook:** more encouraging than
section 8's "moderate, bounded risk" already suggested. Every RHS site
that changes context funnels through one `cs_route k` call, and
`cs_route_k_mono` — already landed, already used for row 2 — covers all
of them uniformly. The genuinely new work is `project_sigma`'s definition
(now written down, section 9.4) and confirming the cross-system
monotonicity step (section 9.6), not a from-scratch argument about the
transfer functions themselves.

## 10. The smallest concrete case, traced and checked

Per the suggestion to try one representative equation rather than read
more infrastructure first: picked the actual merge point —
`FunctionEntry g` at `k=1` context `[Statement 2]`, fed from two `k=2`
contexts, `[Statement 2, Statement 5]` (the `f(3)` branch) and
`[Statement 2, Statement 6]` (the `f(10)` branch) — and traced its RHS
down to the base solver constructors instead of guessing.

### 10.1 The local (`eq`) obligation is a plain monotone fold

`side_acc_dg` (`DG_Constraint_Trees.thy:357`), which `eq_side_cfg_T_eff_keyed_seed_dg`
reduces every `eq` to, is exactly `acc \<squnion> locals (traverse_rhs t tau)` folded
over the `intra @ comb @ extra` subtree list, starting from `acc0`. No
hidden structure — the `eq` obligation is a join of independently-evaluated
per-site contributions, which is exactly the shape the monotonicity
argument (section 9.5) needs.

### 10.2 `FunctionEntry` nodes read a seed and nothing else

`FunctionEntry` nodes have no CFG predecessors and are never a return
target, so their `intra`/`comb` lists are empty; their only RHS content is
`routed_extra`'s seed-read clause. `FunctionEntry g`'s own `eq` obligation
is therefore closer to a definitional readback than a proof burden — the
real content is in what gets *published* to that seed, from elsewhere.

### 10.3 `publish_seed` is `Side`, and `sides_of_rhs` already joins same-key publishers

`publish_seed key x = depend_on key x ... = Side key x ...`
(`Strategy_Tree_Combinators.thy:69`), and the base evaluator
(`Basics_side.thy:295`) is `sides_of_rhs (Side y d t) sigma = (let m =
sides_of_rhs t sigma in m(Inr y := m (Inr y) \<squnion> d))` — a single `Side`
node joins its own contribution into whatever else already targets that
key. `publish_seed`'s *local* answer is always `bot` (confirmed by its
definition: `depend_on key (DG bot x) (answer (DG bot bot))`) — it
contributes nothing to `eq`, only to `sides_of_rhs`.

**The consequence that actually matters:** `Statement 2` is not one
unknown under `k=1` — `f`'s own context already separates at `k=1` (single
call site each from `main`), so `(Statement 2, [Statement 5])` and
`(Statement 2, [Statement 6])` are two *different* unknowns, each
independently publishing into the identical key `Inr (Seed1 (FunctionEntry
g) [Statement 2])` (both route to `take 1 [Statement 2, ...] = [Statement
2]`). `part_post_solution`'s own `ALL u : vars. ... sides_of_rhs (T u)
sigma <= sigma` quantifies over *every* unknown separately against the
*same* shared `sigma` — so the join across the fiber is not something a
single equation needs to construct by hand; it falls out of two
independent per-unknown constraints being satisfied against one shared
target, which is exactly what `project_sigma`'s `Inr`-`Seed` case (the
join in section 9.4) is built to provide as that shared target.

### 10.4 Concrete check, on the already-solved values

Not the algebraic proof — a decisive empirical gate on it, run via `value`
against `nest_1_sol`/`nest_2_sol` (both already solved and verified):

```text
snd nest_1_sol (Inr (Seed1 (FunctionEntry ''g'') [Statement 2]))
  ...  p in [3, +inf]

snd nest_2_sol (Inr (Seed2 (FunctionEntry ''g'') [Statement 2, Statement 5]))
  ...  p in [3, 3]

snd nest_2_sol (Inr (Seed2 (FunctionEntry ''g'') [Statement 2, Statement 6]))
  ...  p in [10, 10]
```

`[3,3] \<squnion> [10,10] = [3,10]`, and `[3,10] \<subseteq> [3,+inf]` — the k=1 solved
seed already dominates the join of the two k=2 branches, at exactly the
node where the whole projection argument is most load-bearing. This is
the same fact the rendered DOT output (design doc section 9) showed
visually; checking it directly against the raw solved values closes the
loop between the two.

**Status:** empirical, not algebraic — this checks the *conclusion* at one
instance, not the general `part_post_solution` proof. But it is the
highest-leverage single check available: had it failed, the whole
projection-join direction would be wrong regardless of how the algebra
worked out. It didn't fail. Combined with 10.1-10.3's structural tracing
(the fold shape, and `part_post_solution`'s own quantifier doing the
fiber-join), the actual next proof attempt has a fully concrete target:
show, for `u = (Statement 2, [Statement 5])` and `u = (Statement 2,
[Statement 6])` individually, that `sides_of_rhs (nest_1_eqs u)
project_sigma <= project_sigma` at the shared key — two instances of the
same argument, using `cs_route_k_mono` to confirm each routes into the
fiber `project_sigma`'s join already covers.
