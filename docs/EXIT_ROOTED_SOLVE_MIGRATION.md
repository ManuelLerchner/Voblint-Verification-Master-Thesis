# Migration — exit-rooted single solve (Goblint-aligned), and interval widening (#39)

Status: **design + core lemma proved; instantiations pending.** This doc records
the decision, the proved pieces (drop-in Isar), the remaining steps, and one
newly-found prerequisite. Supersedes the per-pp widen-interface sketch.

## Why

Two problems, one root cause and one fix.

1. **#39 — interval headline carries a false hypothesis.** `goblint_interval_sound`
   (`src/Goblint_Formalization.thy:120`) assumes, per program point,
   `TD_plain.solve_dom (make_rhs_tree … ivl_tf (⊔) bot …) v`. For intervals this
   is **not just unproven, it is false**: the interval lattice has infinite
   ascending chains, so the plain join solver never stabilises. Termination needs
   the **widening** solver (`TD.TD_plain_widen`).

2. **Per-pp solving is inelegant.** The plain pipeline solves *once per program
   point* (`td_analyse … v = lookup_bot (solve … v) v`). That is an artifact of
   our **pull-based** constraint encoding, not a necessity.

### The encoding, and what Goblint/the paper actually do

Our `make_rhs_tree` builds the forward equation `[v] ⊒ ⟦s⟧(get[u])` for each edge
`(u,s,v)` — the unknown for the **end** point `v` reads its **predecessor** `u`
(`Query` targets = `predecessor_list g v`; see `docs/OPEN_PROBLEMS.md` §P2). So the
demand-driven solver, queried at `x`, explores the **backward cone of `x`** (nodes
that can reach `x`).

This is *exactly* the Apinis–Seidl–Vojdani *Side-Effecting Constraint Systems*
construction (§2, eq. 0):

```
[s_main] ⊒ d0                         -- entry seeded with the initial state
[v]      ⊒ ⟦s⟧♯ (get [u])    for all (u,s,v) ∈ E_main
```

and the paper queries the **return node** `r_main`, relying on an explicit CFG
well-formedness condition (§2):

> "every program point `v`, even when semantically unreachable, can be formally
> (ignoring edge-label semantics) reached from `s_g`, and likewise, `r_g` can be
> formally reached from `v`."

So: query the exit once; the backward cone covers the whole program **because**
every node formally reaches the exit (the always-emitted `EA_AssumeNot b` exit
edge of `compile (WHILE …)` provides this even for `while(true)` — the node after
the loop is *formally* reachable and gets `⊥`). **Widening is orthogonal**: it
makes the fixpoint iteration over that (cyclic, finite) dependency graph
terminate; it does not change which unknowns are reached.

### Decision

Replace the per-pp `∀v. solve_dom v` with a **single solve rooted at `cfg_exit`**,
plus the two CFG well-formedness conditions the paper assumes:

- `entry_reachable`: `∀v. ∃es. cfg_path (to_cfg c) (cfg_entry …) es v`
  (already a standing assumption on the per-pp point-map theorems).
- `exit_reachable`: `∀v. ∃es. cfg_path (to_cfg c) v es (cfg_exit …)` **(new)**.

For sign this is one plain solve; for interval it is one **widening** solve, which
makes the `solve_dom` hypothesis satisfiable — closing #39.

## What is proved (drop-in ready)

All three check in I/R against `Interval_Soundness` + `TD_Widen_Interface`.

### 1. The solver-agnostic exit-rooted soundness theorem (the core)

Belongs in `context sound_transfer` (e.g. a new `TD_Exit_Soundness.thy` or appended
to `TD_Soundness.thy`). Generic over any `sigma` that is a post-solution on
`reach T sigma (cfg_exit …)` — so **both** the plain and widening solvers
instantiate it.

```isabelle
theorem post_solution_exit_collect_sound_at:
  fixes c :: com and s0 :: "'a abs_state" and v0 :: pp and es
    and T :: "pp \<Rightarrow> (pp, 'a abs_state) strategy_tree"
    and sigma :: "(pp, 'a abs_state) map"
  assumes Tmk: "\<And>w. T w = make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0 w"
  assumes S_sub: "S \<le> gamma_state s0"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  assumes exit_reach: "\<And>v. v \<in> reach T sigma (cfg_exit (to_cfg c))"
  assumes post: "\<And>v. v \<in> reach T sigma (cfg_exit (to_cfg c)) \<Longrightarrow> (eq T) v sigma \<le> mlup sigma v"
  shows "cfg_collect (to_cfg c) S v0 \<le> gamma_state (lookup_bot sigma v0)"
proof -
  have cfi: "comp_fun_idem ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    by (rule join_state_comp_fun_idem)
  have js: "\<And>x y :: 'a abs_state. x \<squnion> y = y \<squnion> x" by (rule sup.commute)
  have rhs_le_all: "\<And>v. rhs (to_cfg c) tf (\<squnion>) bot s0 (\<lambda>w. lookup_bot sigma w) v \<le> lookup_bot sigma v"
  proof -
    fix v
    have le: "(eq T) v sigma \<le> mlup sigma v" by (rule post[OF exit_reach])
    show "rhs (to_cfg c) tf (\<squnion>) bot s0 (\<lambda>w. lookup_bot sigma w) v \<le> lookup_bot sigma v"
      by (rule eq_le_mlup_imp_rhs_le[OF Tmk fin_cfg cfi js le])
  qed
  have entry_le: "s0 \<le> lookup_bot sigma (cfg_entry (to_cfg c))"
  proof -
    have "s0 \<le> rhs (to_cfg c) tf (\<squnion>) bot s0 (\<lambda>w. lookup_bot sigma w) (cfg_entry (to_cfg c))"
      by (rule s0_le_rhs_entry[OF fin_cfg])
    thus ?thesis using rhs_le_all order_trans by blast
  qed
  have step_le: "\<And>u a w es'. cfg_path (to_cfg c) u ((a, w) # es') v0
                  \<Longrightarrow> apply_tf tf a (lookup_bot sigma u) \<le> lookup_bot sigma w"
  proof -
    fix u a w es'
    assume p: "cfg_path (to_cfg c) u ((a, w) # es') v0"
    have ed: "(u, a, w) \<in> edges (to_cfg c)" by (rule cfg_path_ConsD_edge[OF p])
    have "apply_tf tf a (lookup_bot sigma u)
            \<le> rhs (to_cfg c) tf (\<squnion>) bot s0 (\<lambda>w. lookup_bot sigma w) w"
      by (rule apply_tf_le_rhs[OF fin_cfg ed])
    thus "apply_tf tf a (lookup_bot sigma u) \<le> lookup_bot sigma w"
      using rhs_le_all order_trans by blast
  qed
  show ?thesis
    by (rule post_fixpoint_sound_at[OF fin_cfg rhs_le_all step_le S_sub entry_le])
qed
```

Note `post_fixpoint_sound_at` only needs `rhs_le` at `v0`, `step_le` on edges, and
`entry_le` — each reduces to "`rhs_le` at node `n`", which `exit_reach` discharges
(every `n ∈ reach(cfg_exit)`).

### 2. Interval widening discharges the `TD_plain_widen` obligations

Belongs near the interval domain (mentions `widen_ivl`). The locale assumptions of
`TD.TD_plain_widen` are `widening_ge: a ⊔ b ≤ a ∇ b` and
`widening_bounded: b ≤ a ⟹ a ∇ b = a`, lifted pointwise via `widen_abs`.

```isabelle
lemma widen_abs_ivl_ge: "(s1::vname \<Rightarrow> ivl) \<squnion> s2 \<le> widen_abs widen_ivl s1 s2"
  by (rule widen_abs_ge[OF sup_le_widen_ivl])

lemma widen_abs_ivl_bounded: "(s2::vname \<Rightarrow> ivl) \<le> s1 \<Longrightarrow> widen_abs widen_ivl s1 s2 = s1"
  by (rule ext) (auto simp: widen_abs_def le_fun_def intro: widen_ivl_id)
```

(`sup_le_widen_ivl`, `widen_ivl_id` already exist in `Interval_Domain.thy`.)

## What remains

### Prerequisite P0 — register `fun :: bounded_lattice_bot` (newly found)

`TD_plain_widen` fixes `'d :: bounded_lattice_bot`. For the interval instance,
`'d = vname \<Rightarrow> ivl`. The proposition `OFCLASS(vname \<Rightarrow> ivl,
bounded_lattice_bot_class)` is **provable** (`by intro_classes` — `ivl` is a
lattice with bot), **but the arity is not registered**, so type inference for
`TD_plain_widen.solve (make_rhs_tree … ivl_tf …)` fails with
`No type arity ivl :: bounded_lattice`: lacking a `fun :: bounded_lattice_bot`
arity, Isabelle falls back to HOL's `fun :: (type, bounded_lattice) bounded_lattice`,
which needs a `top` on `ivl` (there is none).

**Fix:** register, alongside the existing `fun :: bounded_semilattice_sup_bot`
instance in `src/Domains/Abstract_Domain.thy`:

```isabelle
instance "fun" :: (type, bounded_lattice_bot) bounded_lattice_bot ..
```

**Risk to verify:** HOL already ships `fun :: (type, bounded_lattice) bounded_lattice`.
Adding the `bounded_lattice_bot` arity may be rejected as a non-coregular /
overlapping arity (a full `bounded_lattice` codomain would match both). If so, the
fallback is a dedicated interval-state type (type copy of `vname \<Rightarrow> ivl`
with the needed instances) — heavier, isolates the widen path. Try the one-liner
first.

This blocks **only** the interval/widen instantiation. The generic theorem and the
sign/plain instantiation below are unblocked.

### Step 1 — `exit_reachable` lemma — DONE (intraprocedural)

Proved by induction over `compile` in `src/CFG/Collecting/CFG_Exit_Reachable.thy`:
every node of `to_cfg c` edge-reaches `cfg_exit`.

```isabelle
theorem to_cfg_node_reach_exit:        (* frag_node v ==> exists path v -> exit *)
corollary to_cfg_entry_reach_exit:     (* cfg_entry reaches cfg_exit *)
corollary to_cfg_edge_target_reach_exit: (* every edge target reaches cfg_exit *)
```

The core lemma `compile_frag_node_reach_exit` threads each compile fragment's nodes
to its exit (`WHILE` via the unconditional `EA_AssumeNot` edge), lifting sub-paths
with `cfg_path_mono_edges` and composing with `cfg_path_append`. Convert path-form
to the `reach` form the core theorem wants with `cfg_path_node_in_reach`.

**Interprocedural case — trio collapsed to one hypothesis (DONE).**
`Sign_IP_Soundness.ip_sign_analysis_sound` previously carried three verbose
`reach`-from-`cfg_exit` obligations (`edge_reach`, `combine_reach`, `entry_reach`).
These are now a single well-formedness hypothesis `node_reach_exit` — "every
formally-reachable source node (entry, every edge target, every combine/return
target) lies in the demand-driven cone queried at the exit" — exactly the paper's
condition. The former trio is derived from it internally; `Example_Proc_Global`
discharges the single obligation via `proc_global_node_reach`.

**`node_reach_exit` cannot be discharged — it is a *necessary* hypothesis
(refutable), not an unproven lemma.** `compile_prog` (`IMP2_Proc_to_CFG.thy`) builds
`mk_ip_cfg main_en main_ex (E_proc \<union> E_main) (C_proc \<union> C_main)`, where
`compile_procs_list` merely unions every procedure's edges/combines into the graph.
A procedure connects forward to the rest *only* via a combine `(call, ex_p, ret)`
emitted at a `PCall` site. So a procedure in `ps` that is never called has body
nodes that are edge-targets (hence in `node_reach_exit`'s premise) yet have no
edge-or-combine path to `cfg_exit`.

Concrete refutation: `pi p = Some PSKIP`, `ps = [p]`, `main = PSKIP`. The body edge
`(en_p, EA_Nop, ex_p)` lands in `E_proc`; nothing calls `p`, so no combine
references `ex_p`; `cfg_exit` is main's exit. Then `ex_p` is an edge-target (premise
holds) but `ex_p \<notin> reach(cfg_exit)` (conclusion fails). Hence `node_reach_exit`
is *false* for ill-formed (dead-procedure) `compile_prog` and is genuinely
necessary — this is precisely the CFG well-formedness condition the paper assumes
("every program point, even when semantically unreachable, can be formally reached
from `s_g`, and `r_g` can be reached from `v`") rather than proves.

The only routes to elimination are (a) restrict to programs with no dead procedures
(an *extra* hypothesis — no net reduction), or (b) refactor the generic
`TD_IP_Soundness.ip_sign_analysis_sound` so its `reach` obligations range only over
the backward cone of `cfg_exit` (cone-edges/combines), not all edges/combines — then
the dead-procedure nodes fall outside scope and the residual is auto-dischargeable
by a cone-restricted induction. (b) is the real follow-up; until then the single
`node_reach_exit` is the minimal, necessary well-formedness hypothesis.

### Step 2 — sign exit-rooted (plain), unblocked

Instantiate `post_solution_exit_collect_sound_at` with
`sigma = TD_plain_Interp_solve cfg_T (cfg_exit …)`; discharge `post` from
`td_plain_part_solution_at` / `part_solutionD`; `exit_reach` from Step 1. Yields a
single-solve sign soundness; the per-pp `∀v. solve_dom v` collapses to one
`solve_dom (cfg_exit)`.

### Step 3 — interval exit-rooted (widen), needs P0

Inside the proof, interpret
`TD_plain_widen "make_rhs_tree (to_cfg c) ivl_tf (⊔) bot s0" "widen_abs widen_ivl"`
(discharging the two obligations via §2 lemmas); take
`sigma = solve (cfg_exit …)`; `post` from `partial_correctness[OF dom refl]`
(`part_post_solution σ (reach T σ x) ≡ ∀x∈…. eq T x σ ≤ mlup σ x`); `exit_reach`
from Step 1. Apply `ivl_sound_tf.post_solution_exit_collect_sound_at`.

### Step 4 — restate the headline

```isabelle
theorem goblint_interval_sound_widen:
  assumes runs: "runs_to c s t"
  assumes exit_reachable: "\<And>v. v \<in> reach (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot (ac_init …))
                                     (\<dots>solve\<dots> (cfg_exit (to_cfg c))) (cfg_exit (to_cfg c))"
  assumes td_solve_dom: "TD_plain_widen.solve_dom (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot (ac_init …))
                                                  (widen_abs widen_ivl) (cfg_exit (to_cfg c))"
  shows "t \<in> ivl_domain.gamma_state (\<dots> (cfg_exit (to_cfg c)))"
```

The `td_solve_dom` here is over the **widening** solver — satisfiable for
intervals, unlike the plain-join one it replaces.

### Step 5 — (optional) migrate sign + tidy

Decide whether to also move `goblint_sign_sound` / the pipeline point-map theorems
onto the exit-rooted shape (one solve) or keep the per-pp versions. The generic
theorem supports both; the per-pp ones can stay as corollaries.

## Sequencing

```
P0 (fun arity)  ─┐
Step 1 (exit_reachable) ─┼─► Step 3 (interval widen) ─► Step 4 (headline)  = #39 closed
                 └─► Step 2 (sign plain, unblocked now)
Step 5 optional, last.
```

## Provenance

- Constraint construction + start/return reachability: Apinis, Seidl, Vojdani,
  *Side-Effecting Constraint Systems*, §2 (eq. 0). https://goblint.in.tum.de/assets/papers/side.pdf
- Pull-direction of our encoding: `docs/OPEN_PROBLEMS.md` §P2 finding.
- `compile (WHILE …)` exit edge: `src/CFG/IMP2_to_CFG.thy`.
