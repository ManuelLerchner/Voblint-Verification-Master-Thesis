# Generalizing `project_sigma`: design

Design only. No `.thy` file was read, edited, or created through host tools;
`Call_String_Solver_Refinement.thy` was read through I/Q and is untouched.

Everything below is checked against the repository. Where a claim is not
checked, it says so.

---

## 0. What the witness actually is, read off the file

`project_sigma` (`Call_String_Solver_Refinement.thy:72-97`) is a valuation
`pp x cfg_node list + gk_1 => (ivl st, ivl st) dg_state` built by an
if-chain over 16 concrete unknowns. Three kinds of case:

| Kind | Nodes in the witness | Definition |
| --- | --- | --- |
| passthrough | 8 unknowns (`Statement 2`/`5`, `FunctionEntry f`/`main`, ...) | `snd nest_2_sol (Inl (v, ctx1))` |
| fiber join | `Statement 0`, `FunctionResult ''g''`, `FunctionEntry ''g''` at `[Statement 2]`; `Seed1 (FunctionEntry ''g'') [Statement 2]` | `sigma2 (.., [S2,S5]) \<squnion> sigma2 (.., [S2,S6])` |
| recomputed | `Statement 3`, `FunctionResult ''f''` (both contexts), `Statement 6`, `Statement 7`, `FunctionResult ''main''` | `statement3_val`, `result_f_val`, `statement6_val`, `statement7_val`, `result_main_val` (lines 46-70) |

Two structural facts drive the whole generalization:

1. **Passthrough and fiber join are the same construction.** A passthrough is
   a fiber join over a singleton fiber. The witness only splits them because
   `cs_route`'s fibers were enumerated by hand. There is one operation here,
   not two.

2. **The recomputed cases are definitionally `eq`.** `statement3_val ctx1`
   is literally `eq nest_1_eqs (Statement 3, ctx1) project_sigma` with the
   dependency values substituted --- compare `eq_statement3_closed_form`
   (line 436) with `statement3_val_def` (line 46): same term. That is why
   `project_sigma_eq_statement3` (line 445) closes with `by auto` after
   unfolding both sides. The recomputed cases are a **hand-unrolled partial
   fixpoint of `nest_1_eqs`**, unrolled because `definition` cannot recurse
   (the file's own header text, lines 21-24, says exactly this).

So `project_sigma` is: *fiber join everywhere, then re-run the k=1 right-hand
sides forward until the effect of the join stops propagating*. The
enumeration is the unrolling, not the idea.

**Why the join alone is not enough.** With `pi` = pure fiber join, the `eq`
obligation at a node reading a merged unknown is
`f (\<Squnion>i d_i) \<le> \<Squnion>i f (d_i)`: the transfer function would have to be a join
morphism. `combine_local`/`dg_spec_step` over `ivl st` are monotone, not
completely additive, so this fails in general. Section 9.4 of
`docs/CALLSTRING_PRECISION_INVESTIGATION.md` proposed the pure join and did
not see this; the witness is the counterexample-in-practice. Any
generalization must keep the recomputation, in some form.

**A second, less visible gap.** `pi(sigma2) \<le> project_sigma` is *not* proved
in the file, and does not follow from the construction: `sigma2` may sit
strictly above its own right-hand side (warrowing at k=2), so a recomputed
downstream value built from `sigma2`'s inputs need not dominate `sigma2`'s
own value at that node. Without that domination the theorem says only "here
is *a* sound k=1 post-solution", not "here is the k=2 result projected down".
The general design should make the domination structural (section 3.2).

---

## 1. Item 1: what object the dependency closure is

**Not a node set.** A node set loses the two things the witness needs: the
recomputed values, and the fact that recomputation must reach a state where
re-evaluating changes nothing. The dependency *relation* is also not enough:
for `cs_route`-based systems `dep` happens to be independent of `sigma`
(`cs_route k u ctx d ca = take k (u # ctx)` ignores `d`, so `dep_L_statement3`
collapses under `cs_route_k1`), so the node set and the relation are both
statically computable --- and still insufficient, because the values are the
content.

**The object is a valuation together with a pre-fixpoint property.** Define,
for an equation system `T`, a finite unknown set `W` and a valuation `sigma`,
the one-step operator

```text
Phi T W sigma = (\<lambda>y. case y of
    Inl u \<Rightarrow> (if u \<in> W then eq T u sigma else \<bottom>)
  | Inr g \<Rightarrow> \<Squnion>{ sides_of_rhs (T u) sigma (Inr g) | u \<in> W })
```

Then `part_post_solution T x sigma W` is exactly
`x \<in> W \<and> dep-closed W sigma \<and> Phi T W sigma \<le> sigma`
--- the three bullets of the vendored abbreviation (`Basics_side.thy:337`)
repackaged as one inequality. The closure object is therefore

```text
(W, sigma)  with  W dep-closed,  pi(sigma2) \<le> sigma,  Phi T1 W sigma \<le> sigma
```

carrying affected nodes (`W`), the relation (through dep-closure), the
projected values (`pi(sigma2) \<le> sigma`), and the recomputation
(`Phi T1 W sigma \<le> sigma`) in one statement.

**Cast: least fixed point, realized by the existing solver.** Mathematically
the canonical such object is `lfp (\<lambda>sigma. pi(sigma2) \<squnion> Phi T1 W sigma)`,
monotone when `is_mono_eq`/`mono_sides` hold. Isabelle's `lfp` is **not
available** here: the payload class is `bounded_semilattice_sup_bot`, not
`complete_lattice`, and `ivl st` has infinite ascending chains, so even
Kleene iteration needs widening. Demanding a complete lattice would be a
false abstraction in the sense of the AGENTS.md audit (item 3) --- it would
exclude the interval instance this repo runs on.

Rejected alternatives, explicitly:

- *Recursive definition (`fun`/`primrec` over the cone)*: impossible for
  cyclic dependency graphs, and the file already documents why (`definition`
  cannot recurse); this is the current shape, not a generalization.
- *Graph fold*: presumes an acyclic traversal order; re-derives the witness.
- *Node-set closure*: drops values and recomputation, as above.

Conclusion: **least fixed point in spirit, computed by the vendored TD
solver, not by new fixpoint machinery.** See item 2.

---

## 2. Item 2: acyclic vs cyclic --- the crux

### 2.1 DAG case: well-founded recursion, not a topological order

For an acyclic cone the right device is `wfrec` over the dependency relation
restricted to the affected set, with `wf` as an explicit hypothesis --- not a
topological sort. `wf` handles diamonds and multiple callers with no extra
work (no order to choose, no merge rule to state), and it comes with the
matching proof principle:

```text
definition proj_wf sigma2 W2 rho R u =
  (if u \<in> affected R  then eq T1 u (proj_wf ...)   -- wfrec unfolding
                       else pi rho W2 sigma2 (Inl u))
```

Connecting theorem: by `wf_induct` on `R`, at every affected `u` the
recursion equation gives `eq T1 u sigma = sigma (Inl u)` --- the `eq`
obligation holds by reflexivity, exactly as `project_sigma_eq_statement3`
does today --- and at every unaffected `u` it reduces to a *frontier lemma*:
the fiber join satisfies `eq T1 u (pi sigma2) \<le> pi sigma2 (Inl u)` when `u`
reads no merged unknown. The frontier lemma is where `sigma2`'s own
`part_post_solution` and `cs_route_k_mono` are consumed.

This is a genuine generalization of the witness (it eliminates the
enumeration and the per-node closed forms), and it is *still not the answer*,
because:

### 2.2 Cyclic case: the topological answer is structurally unavailable

`f` calling `f`, directly or through a cycle in the call graph, makes
`FunctionResult f` at context `c` depend on `Statement k` at `c` which
depends on `FunctionResult f` at `cs_route k ...` --- and under k-limiting
those two contexts can be *equal*, which is the entire point of bounding the
call string. Recursion is not an edge case for this construction; it is the
case k-limiting exists for. Also, ordinary loops inside a procedure already
make `intra` dependency cycles at a single context, so cyclicity is not even
exotic here (the `nest_cfg` witness is loop-free, which is why the hand
unrolling terminated at all).

Evaluated options:

**(a) restrict to acyclic cones, hypothesis `wf R`.** Rejected as the
primary architecture. It excludes recursion and loops, i.e. it excludes the
motivating case for bounded call strings. Keep `wf` only as an *optional*
characterization corollary (section 2.3), never as the interface.

**(b) inner fixpoint computation.** Rejected. Needs a complete lattice or
ACC on the payload; `ivl st` has neither. Building one means re-deriving
widening/narrowing and a termination argument that
`vendor/td-verification` already contains. That is a second fixpoint
mechanism next to the verified one --- the failure mode AGENTS.md's
"generalize in place" rule names.

**(c) reuse the verified TD solver on a *seeded* equation system.**
**Chosen.** Cycles are what a demand-driven fixpoint solver is for. Instead
of computing the closure, build the equation system whose solutions *are* the
closure, and hand it to the solver already in the repository:

```text
seed_rhs T1 s gseeds x0 x =
   (a tree that evaluates T1 x, joins the constant s (Inl x) into its Answer,
    and, at x = x0, additionally Side-publishes s (Inr g) for each g in gseeds)
```

with `s = pi rho W2 sigma2` the fiber join. Then run
`TD_side_warrowing_apinis_Interp_solve (seed_rhs ...) x0` --- the same call
`nest_1_sol` already makes (`Example_Interval_DG_CallString_K1.thy:100`).

Why this is not a workaround:

- Termination, widening, dependency tracking, and side-effect handling are
  already verified for this solver; nothing is re-invented.
- Cyclic dependency cones cost exactly zero extra proof.
- `pi(sigma2) \<le> sigma` becomes **structural**, not an extra obligation: the
  seeded right-hand side contains `pi` as a disjunct, so any post-solution of
  the seeded system dominates `pi` at every unknown in `W` (and at every
  seeded global key). This closes the gap noted in section 0.
- It is executable end to end: `pi` is a finite fold over `fst nest_2_sol`,
  so the seeded system code-generates and the termination side condition is
  an `eval`.

Proof obligations of (c), each small and local:

1. `eq_seed_rhs`: `eq (seed_rhs T s gs x0) u sigma = eq T u sigma \<squnion> s (Inl u)`.
   One line from `traverse_seqcomp` (`Strategy_Tree_Monad.thy:23`).
2. `sides_seed_rhs`: `sides_of_rhs (seed_rhs T s gs x0 u) sigma
   = sides_of_rhs (T u) sigma \<squnion> (seeded globals, only at u = x0)`.
   One line from `sides_of_rhs_seqcomp` (`Strategy_Tree_Monad.thy:32`) plus
   `sides_of_rhs`'s own `Side` case.
3. `dep_seed_rhs`: `dep (seed_rhs T s gs x0) sigma u = dep T sigma u`
   (an `Answer` and a `Side` add no dependencies). One line from
   `dep_aux_seqcomp` (`Strategy_Tree_Monad.thy:27`).
4. `mono_seed_rhs`: the seeded system inherits `is_mono_eq`, `mono_sides`,
   `mono_deps` --- `seqcomp_mono` (`Strategy_Tree_Monad.thy:64`) and
   `static_deps_seqcomp` (line 113) are already there. Needed only if a
   leastness-carrying solver is used; the warrowing route does not need it.
5. `post_solution_of_seeded` (the transfer step, the only real content):
   from `part_post_solution (seed_rhs T1 pi gs x0) x0 sigma W` conclude
   `part_post_solution T1 x0 sigma W \<and> pi \<le> sigma` --- immediate from
   1-3, since `eq T1 u sigma \<le> eq(seeded) u sigma \<le> sigma (Inl u)` and
   `pi (Inl u) \<le> eq(seeded) u sigma \<le> sigma (Inl u)`.
6. Termination, per instance: `..._solve_c (seed_rhs ...) x0 \<noteq> None`, by
   `eval`, exactly as `nest_1_terminates`
   (`Example_Interval_DG_CallString_K1.thy:103`). Not provable in general and
   must stay a hypothesis --- honest, and matching how K1/K2 already work.
7. Per instance, if the theorem is to be stated over `fst nest_1_sol` rather
   than the seeded solve's own stable set: `fst (seeded solve) = fst nest_1_sol`,
   by `eval`. Expected to hold because seeding changes no dependency
   (obligation 3), but it is an `eval`, not a theorem.

**(d) something else --- the dual, and it is worth knowing about.**
See section 4.3: pulling the *coarse* solution *up* to the fine system is a
strictly cheaper theorem, needs no joins, no cone, no monotonicity, and no
cyclicity argument at all. It answers a different (and arguably the more
interesting) question, so it complements rather than replaces (c).

### 2.3 What survives of the acyclic story

`wf`-based recursion stays useful as an *optional characterization*: when the
affected cone is well-founded, the seeded solve's result and the `wfrec`
closed form agree (or at least the closed form is a post-solution of the
seeded system, hence an upper bound target). This is what lets the current
hand-written `project_sigma` be recognized as an instance rather than
deleted. Nothing in the main line depends on it. Do not build it first.

---

## 3. Item 3: the general theorem shape

Abstraction boundary, in four layers, each independently reusable:

```text
  seed unknowns          dependency closure       projection             correspondence
  -------------          ------------------       ----------             --------------
  rho : X2+G2 -> X1+G1    dep-closed W1           pi = fiber join        part_post_solution T1
  (context projection)    (from the solver)       + seeded re-solve      + pi <= sigma1
```

### 3.1 New definitions

| Name | Type / statement | Notes |
| --- | --- | --- |
| `locale ctx_projection` | fixes `rhoL :: 'x \<Rightarrow> 'x`, `rhoG :: 'g2 \<Rightarrow> 'g1`; abbreviates `rho = map_sum rhoL rhoG` | pure data, no domain, no solver, mirrors `Call_String_Context.thy`'s style |
| `cs_proj` | `cs_proj k1 (v, c) = (v, take k1 c)`; `cs_proj_gk k1 Global2 = Global1`, `cs_proj_gk k1 (Seed2 v c) = Seed1 v (take k1 c)` | the call-string instance of `rho`, for any `k1 \<le> k2` |
| `fiber_join` (`pi`) | `fiber_join rho W2 sigma2 y1 = \<Squnion> { sigma2 y2 | y2 \<in> W2', rho y2 = y1 }` as a `Finite_Set.fold` over the finite index set | generalizes section 9.4 of the investigation doc by replacing `take k1` with `rho` |
| `seed_rhs` | `seed_rhs T s gseeds x0 :: ('x,'g,'d) eqsT`, see 2.2(c) | built from `seqcomp_tree` + `Answer` + `Side`; no new solver notion |
| `affected` (optional) | `affected rho W2 = { u \<in> W1 . fiber of u is not a singleton }` closed under `trans_dep_L` | only needed for the `wf` characterization and for diagnostics |

### 3.2 Theorems to aim for

**T1 --- criterion form (the repackaging; the frozen witness instantiates this).**

```text
theorem projected_part_post_solution:
  fixes   T1 sigma1 W1
  assumes closed:  "\<forall>u \<in> W1. dep_L T1 sigma1 u \<subseteq> W1"
      and rhs_le:  "\<forall>u \<in> W1. eq T1 u sigma1 \<le> sigma1 (Inl u)"
      and side_le: "\<forall>u \<in> W1. sides_of_rhs (T1 u) sigma1 \<le> sigma1"
      and start:   "x0 \<in> W1"
  shows "part_post_solution T1 x0 sigma1 W1"
```

Trivial to prove; its value is that its three hypotheses are *exactly*
`project_sigma_dep_L_all`, `project_sigma_eq_all`, `project_sigma_sides_all`
(lines 1608, 1674, 1687). It is the seam the witness plugs into.

**T2 --- constructor form (the general construction; where cycles are handled).**

```text
theorem seeded_projection_part_post_solution:
  assumes pp2:  "part_post_solution T2 x2 sigma2 W2"
      and proj: "rhoL x2 = x1"
      and term: "solve_c (seed_rhs T1 (fiber_join rho W2 sigma2) gseeds x1) x1 \<noteq> None"
  defines "sol \<equiv> solve (seed_rhs T1 (fiber_join rho W2 sigma2) gseeds x1) x1"
  shows "part_post_solution T1 x1 (snd sol) (fst sol)"
    and "fiber_join rho W2 sigma2 \<le> snd sol"
```

The second conclusion is the one the current theorem lacks: it is what makes
`snd sol` *the projection of* `sigma2` rather than an arbitrary sound k=1
result. `pp2` is used only to make `fiber_join` meaningful (it is not needed
for the inequality itself); keep it in the statement so instances cannot
forget it, or drop it and state the soundness corollary separately --- decide
when writing, not now.

**T3 --- soundness corollary (what a reader wants).** Compose T2 with the
existing DG endpoint (`nest_1_pp_abs` / `activation_collect_sound` route,
`Example_Interval_DG_CallString_K1.thy:293`) to get: every k=2 activation's
collected states are contained in `gamma` of the projected value at the
k=1 activation `take k1 c2`. This is the statement that pairs with
`call_string_collecting_mono` (`Call_String_Collecting_Refinement.thy`) on
the semantic side.

**T4 (optional) --- `wf` characterization.** As in 2.3. Skip unless a
human-readable closed form is wanted for the thesis text.

### 3.3 How the current theorem becomes an instance

`project_sigma_part_post_solution` today =
`T1 := nest_1_eqs`, `sigma1 := project_sigma`, `W1 := fst nest_1_sol`,
`x0 := (cfg_exit nest_cfg, [])`. Under T1 (criterion form) the proof becomes

```text
lemma project_sigma_part_post_solution:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, []) project_sigma (fst nest_1_sol)"
  by (rule projected_part_post_solution)
     (use project_sigma_dep_L_all project_sigma_eq_all project_sigma_sides_all
          statement_..._covered_1 in \<open>...\<close>)
```

i.e. the last lemma changes, nothing above it does. Under T2, a *second*,
independent lemma appears --- `nest_1_proj_sol` defined as the seeded solve,
with `part_post_solution` free --- and the hand-written `project_sigma` is
kept as the readable regression witness. The two coexist; the k=2 -> k=1
instantiation of `rho` is `cs_proj 1`, and `cs_route_k_mono`
(`Call_String_Context.thy`) is the only call-string-specific fact either
needs.

---

## 4. Item 4: alignment with Goblint, and k=n -> k-1

### 4.1 What the repository says about Goblint's shape

- Goblint solves over `(node, context)` unknowns and keeps flow-insensitive
  globals in a separate `V.t -> G.t` store
  (`docs/ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md:7-19`, citing
  `constraints.ml`'s `FromSpec`, `type lv = MyCFG.node * S.C.t`). The
  formalization's `('x = pp * cfg_node list, 'g = gk_1)` split mirrors that,
  and `seed_rhs` respects it: local seeding via `Answer`, global seeding via
  `Side`, never mixed.
- Context changes only at calls (`ROUTE_A7...:31-43`, `120-127`), which is
  why every context-changing site in the generator funnels through exactly
  one `route` call (`docs/CALLSTRING_PRECISION_INVESTIGATION.md:274-291`,
  confirmed against `DG_Framework.thy:406`). This is what makes a single
  `rho`-commutation lemma sufficient for the whole system.
- Goblint bounds contexts with *lifters over the constraint system*
  (Context Gas, Loopfree Callstring; named as such in
  `ROUTE_A7...:26-28`). A lifter changes the system and the system is
  re-solved. **Goblint has no post-hoc projection of a finer solution onto a
  coarser one.** Not verified against the OCaml source in this session ---
  no Goblint checkout is present in this repo --- so treat the lifter claim
  as repo-documented, not source-verified; the `constraints.ml` claims above
  are the project's own vetted citations.

Consequence for this design: approach (c) --- *build a system, hand it to the
solver* --- is the one that matches how the analyzer really produces results.
A hand-built topological closed form has no counterpart anywhere in Goblint.
Seeding a solver with an initial valuation is also not exotic there: side
effects and start values are first-class in the side-effecting constraint
system model (Apinis/Seidl/Vojdani, cited in
`docs/GOBLINT_DG_INTERFACE_VALIDATION.md:138`).

Where the analogy is weakest: Goblint would answer the k -> k-1 question by
*re-running* with the coarser lifter, not by projecting at all. The projection
theorem is a formalization-side artifact --- it is how you relate two runs
after the fact. That is a legitimate thing to prove, but it should not be
presented as modeling a Goblint pass.

### 4.2 k=n -> k-1, and composition

Everything in section 3 is parameterized by `rho`, never by `k`. The
call-string instance needs, for any `k1 \<le> k2`:

- `cs_route_k_mono` (landed): `take k1 (cs_route k2 u ctx d ca) = cs_route k1 u ctx d ca`;
- `cs_route k u (take k ctx) d ca = cs_route k u ctx d ca` (one line, checked
  by hand in `docs/CALLSTRING_PRECISION_INVESTIGATION.md:21-27`, unlanded
  because `Call_String_Context.thy` is frozen).

Both are `k`-generic, so k=2 -> k=1 is not special. Composition
(`take k1 \<circ> take k2 = take k1` for `k1 \<le> k2`) means `rho` composes, so
k=3 -> k=2 -> k=1 chains for free provided the general theorem is stated over
`rho` and not over `take 1`. **Do not let `k` appear anywhere in T1/T2.**

### 4.3 The dual theorem, which is cheaper and cycle-free

Worth stating because a reviewer will ask, and because it may be the better
route to the actual precision claim. Instead of pushing `sigma2` *down*,
pull `sigma1` *up*: define `iota sigma1 = sigma1 \<circ> rho` and prove

```text
theorem pullback_part_post_solution:
  assumes "part_post_solution T1 x1 sigma1 W1"
  shows   "part_post_solution T2 x2 (sigma1 \<circ> rho) (rho -` W1)"
```

Checked by hand against the generator (`DG_Framework.thy:406`,
`Routed_Context.thy`): at a fine unknown `(v,c2)`, every intra read is at
`(u,c2)` whose `rho`-image is the unknown `T1` reads; every `comb`/`extra`
context computation is `cs_route k2 cc c2 d ca` whose `take k1` is
`cs_route k1 cc c1 d ca` by `cs_route_k_mono`, with the *same* `d` because
the pullback assigns the fine unknown exactly the coarse value; and the
transfer functions (`Spoly`, `combine_local`, `dg_spec_step`) are identical
on both sides. So `eq T2 u2 (sigma1 \<circ> rho) = eq T1 (rhoL u2) sigma1`
**definitionally** --- no monotonicity, no distributivity, no fiber joins, no
dependency cone, and cycles are irrelevant because the argument is per-node
and unconditional. Side effects survive fine-key collapse because
`sides_of_rhs`'s `Side` case joins same-key publications
(`Basics_side.thy:295`), and the coarse tree publishes the join of exactly
those terms into the collapsed key.

The catch: to turn this into `sigma2 \<le> sigma1 \<circ> rho` (the literal precision
claim, "k=2 is at least as precise as k=1 fiberwise") you need **leastness of
the k=2 solve**, and that is currently unavailable: `least_partial_post_solution`
lives in `TD_side_mono = TD_side_opt True T` (`TD_side.thy:4277, 5284`), while
`TD_side_upd_rule` --- the interface every menu solver including
`TD_side_warrowing_apinis_Interp_solve` goes through --- interprets
`TD_side_opt False T` (`TD_side_upd_rule.thy:26`). K1/K2 therefore get
`part_post_solution` only (`Solver_Menu.thy:40`,
`Example_Interval_DG_CallString_K2.thy:150`). Closing that would mean
interpreting `TD_side_mono` at `nest_2_eqs`, which needs the threefold
monotonicity for the keyed-seed DG generator (per
`docs/CALLSTRING_PRECISION_INVESTIGATION.md:358-372`, never located for this
generator) and a solver run without widening --- plausible on the loop-free
`nest_cfg`, unproven. Flagged, not assumed.

---

## 5. Item 5: deliverable summary

### 5.1 New definitions (names + intended statements)

1. `ctx_projection` (locale): `rhoL`, `rhoG`, `rho = map_sum rhoL rhoG`.
2. `cs_proj k1`, `cs_proj_gk k1`: the call-string instance; obligations
   discharged by `cs_route_k_mono` + take-idempotence.
3. `fiber_join rho W2 sigma2`: finite `Finite_Set.fold` of `\<squnion>` over the
   `rho`-fiber; `[simp]`-worthy singleton-fiber collapse lemma.
4. `seed_rhs T s gseeds x0`: `T` with `s`'s local value joined into each
   answer and `s`'s global values `Side`-published at `x0`.
5. Characterization lemmas `eq_seed_rhs`, `sides_seed_rhs`, `dep_seed_rhs`,
   `mono_seed_rhs` (obligations 1-4 of section 2.2).
6. Optional: `affected`, `proj_wf` (only for the `wf` characterization).

### 5.2 Theorems

- `projected_part_post_solution` (T1, criterion form).
- `seeded_projection_part_post_solution` (T2, constructor form) + its
  `fiber_join \<le> sigma` conclusion.
- `projected_activation_collect_sound` (T3, corollary through the existing
  DG endpoint).
- `pullback_part_post_solution` (the dual, section 4.3) --- recommend proving
  this *first*: it is smaller, it is `k`-generic, it needs no new machinery,
  and it is the honest route to a precision statement.

### 5.3 Assumptions and hypotheses

- `part_post_solution T2 x2 sigma2 W2` (already available: `nest_2_pp_st`).
- Executable termination of the seeded solve, per instance, by `eval`.
- Finiteness of `W2` and of the seeded global key list (both hold: solver
  stable sets are finite; keys come from `W2`'s image).
- `rho`-commutation of `route` (`cs_route_k_mono` + take-idempotence).
- For the dual: leastness at k=2, currently **not** available (section 4.3).
- Not assumed anywhere: complete lattice, ACC, join-morphic transfer
  functions, acyclic dependency cone.

### 5.4 Known limitations

1. **T2 does not prove that k=2 is more precise than k=1.** The seeded system
   dominates `T1`, so its solution is *above* the plain k=1 least solution.
   T2 says "the k=2 result collapses to a sound k=1 result"; it cannot say
   "k=1 loses precision". That claim needs section 4.3's dual plus leastness.
   Do not oversell T2.
2. The seeded-solve construction yields no readable closed form. If the
   thesis wants to *display* the widened downstream values, keep the current
   witness (or T4) for that purpose.
3. `fst (seeded solve) = fst nest_1_sol` is an `eval` per instance, not a
   theorem.
4. Termination of the seeded solve is a hypothesis. Unavoidable.
5. `Call_String_Context.thy` is frozen; the take-idempotence lemma must
   either be unfrozen there or kept local, as
   `Call_String_Collecting_Refinement.thy` already does for
   `cs_enterc_take_stable`.

### 5.5 Migration path

Stage 0 (no risk): add T1 in a new theory (suggested
`src/Analysis/Generic/Solver/Context/DG/Context_Refinement.thy`, next to
`Call_String_Collecting_Refinement.thy`) and rewrite only the final lemma of
`Call_String_Solver_Refinement.thy` to `by (rule projected_part_post_solution) ...`.
The 1600 lines above it are untouched and keep working --- their three `_all`
lemmas are literally T1's hypotheses. The witness becomes the acyclic /
k=2 -> k=1 specialization by instantiation, which is what "the special case
falls out by instantiation" requires.

Stage 1: `fiber_join` + `seed_rhs` + the four characterization lemmas +
`post_solution_of_seeded`. All small, all in the new theory, no dependence on
the witness.

Stage 2: T2, and a new `nest_1_proj_sol` in a *separate* example theory
(not in the frozen file) defined as the seeded solve, with its `eval`
termination lemma. This demonstrates the general path end to end on the same
program and is the artifact a second program (diamond, recursion) would reuse
unchanged.

Stage 3: the dual, `pullback_part_post_solution`, generic over `rho`.

Stage 4 (optional): T4 `wf` characterization, only if a closed form is wanted.

Nothing in stages 1-4 requires editing `Call_String_Solver_Refinement.thy`
beyond stage 0's one-lemma rewrite, and stage 0 is itself optional --- the
existing proof remains valid as written.

---

## 6. Where this design could be wrong

- If a future instance's `route` reads the abstract value (Goblint's `context`
  callback genuinely does --- it filters the callee store), `dep` stops being
  static and `mono_deps` becomes load-bearing. The design survives (the
  solver handles value-dependent dependencies), but the `wf` characterization
  and any "the cone is statically computable" claim do not. `cs_route`'s
  data-independence is a property of *this* context, not of contexts.
- T2's value hinges on the `fiber_join \<le> sigma` conclusion being the
  interesting half. If the intended headline is instead "k=2 beats k=1",
  section 4.3's route is the one to build, and T2 is supporting material.
- The claim that the recomputed cases are definitionally `eq` was checked on
  `Statement 3` only (lines 436/46 line up exactly). The other four closed
  forms look identical in shape but were not each unfolded against their
  `eq ..._closed_form` lemma.
