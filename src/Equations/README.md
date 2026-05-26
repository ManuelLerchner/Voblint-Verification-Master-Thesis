# Equation systems

**Main contribution:** Turn a CFG plus abstract domain into a constraint system
(`rhs :: pp => (pp => abs_state) => abs_state`, `domain_transfer` record), and prove
that any post-fixpoint soundly over-approximates collecting semantics `cfg_collect`.

**Theories**

| File | Role |
| --- | --- |
| `Constraint_System.thy` | `domain_transfer`, `apply_tf`, `rhs`, `is_post_fixpoint`, `rhs_mono` |
| `Constraint_System_Sound.thy` | `collect_pp_abstract_sound`, `post_fixpoint_sound`, `exit_sound` |

**Key concepts:** One equation per program point (join over predecessor edges).
`is_post_fixpoint g tf join bot s0 env` means `∀v. rhs g tf join bot s0 env v ≤ env v`
(env is a post-fixpoint of the one-step operator). `post_fixpoint_sound` is per-pp
inclusion in `gamma_state`; `exit_sound` is the exit-projected corollary.

**Imports:** `Constraint_System` → `CFG_Def`, `Abstract_Domain`.
`Constraint_System_Sound` → `Constraint_System`, `CFG_Runs_To_Bridge` (not a separate
`CFG_Collecting` theory).

**Downstream:** `Solver/TD_CFG_Core.thy` — `make_rhs_tree`; `Solver/TD_Interface.thy` —
`td_analyse`, `td_analyse_post_fixpoint` (TD session `TD_plain`).

## Scope vs. Goblint's actual framework

The constraint system above models a **single-domain, single-procedure,
side-effect-free** equation system over a CFG — matching the AFP
`Top_Down_Solver` (Stade, Tilscher, Seidl, CAV 2024) it sits on. The
framework Goblint actually uses is **mixed flow-sensitive** (Seidl, Vojdani,
Erhard, Schwarz, *Mixed Flow-Sensitive Static Analysis: Engineering
Modularity*, FM 2026 tutorial, LNCS 15557, open access) — a tuple
`(L, G, D^X, C)` of locals, globals, per-unknown domains, and side-effecting
constraints. The OCaml realisation is `GlobConstrSys` /
`DemandGlobConstrSys` in `src/constraint/constrSys.ml` of the
`goblint/analyzer` repo. **None of the following structural extensions is
currently modelled here**:

1. Locals / globals split (polymorphic-variant `[\`L | \`G]` unknowns)
2. Side-effects (`set y d` callback alongside `get`)
3. Per-unknown distinct domains `D_{[x]}` (`Lift2(G)(D)` variant lattice)
4. Context refinement `[u, c]` (Goblint: `LVar = MyCFG.node × C.t`)
5. Digests (trace abstractions; reduced cardinal power refinement)
6. Update rules (per-origin widening; `EqConstrSys.postmortem` —
   Stemmler et al. PLDI 2025, arXiv:2504.06026)
7. `demand` callback (force evaluation without read)
8. `Queries` system for inter-analysis communication
9. `sync` events (`Normal | Join | JoinCall | Return`)
10. Multi-analysis `Var2` sum on globals + product on locals
11. Context-set tracking on globals (`G = GVarG (G) (C)` — Goblint-specific
    bookkeeping)

This is intentional, not a bug. The thesis is positioned on the
**pipeline / domain-instance axis** (IMP AST → CFG → eqsys → TD → sound
pointwise result, with sign + interval domain instances), not the solver
axis. The directly adjacent published work on the latter is
**Tilscher, Graß, Schwarz, Seidl, *Verifying a Solver for Mixed
Flow-Sensitive Analyses*, NASA FM 2026** — supervisor Graß is co-author
and the two strands should be complementary. See the KB page
`~/git/goblint-formalization-kb/wiki/concepts/goblint-isabelle-gap.md`
for the gap table and the meeting-4 prep page for the coordination
questions.
