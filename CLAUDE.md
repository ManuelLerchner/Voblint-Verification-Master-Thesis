# Goblint Formalization — Project Orientation

Master's thesis at TUM: prove the **complete Goblint static analysis pipeline** in Isabelle/HOL.
Supervisors: Alexandra Graß, Michael Schwarz.

## Goal

Verify the pipeline:
**IMP2 AST → CFG → equation system → TD solver → sound annotated result**.

The AFP `Top_Down_Solver` (Stade et al., CAV 2024) is already verified — the gap is:
1. IMP2 syntax + operational semantics + collecting semantics
2. IMP2 → CFG translation + correctness
3. CFG → equation system + soundness (post-fixpoint overapproximates collecting sem.)
4. Abstract domain instances (sign, interval; octagon stretch)
5. Mapping solver output back to annotated program

## Key decisions (locked)

| | |
|---|---|
| Proof assistant | Isabelle/HOL |
| Source language | **IMP2** (custom; richer than IMP: adds Minus, Times, Or, Eq) |
| Intermediate repr. | **CFG** (program points = nat; edges labeled with edge_action) |
| Solver | AFP `Top_Down_Solver` (install from AFP; stub in Solver/TD_Interface.thy) |
| Solver interface | `rhs :: pp => (pp => abs_state) => abs_state` (monotone) |
| Domains tier 1 | Sign (finite lattice, no widening) |
| Domains tier 2 | Interval (widening required) |
| Domains tier 3 | Octagon (stretch goal) |

## Source structure

```
ROOT                                  ← Isabelle session config (HOL-IMP parent)
src/
  Goblint_Formalization.thy           ← top-level imports + smoke test
  Scratch.thy                         ← scratch pad (Knaster-Tarski, Cantor)
  IMP2/
    IMP2_Syntax.thy                   ← aexp, bexp, com datatypes
    IMP2_Semantics.thy                ← aval, bval, big_step
    IMP2_Collecting.thy               ← collecting semantics (concrete gold standard)
  CFG/
    CFG_Def.thy                       ← pp, edge_action, cfg record
    IMP2_to_CFG.thy                   ← compile :: com => nat => (nat*pp*pp*edges)
    CFG_Collecting.thy                ← CFG collecting sem + bridge to IMP2
  Domains/
    Abstract_Domain.thy               ← abstract_domain locale + gamma_state
    Sign_Domain.thy                   ← sign instantiation + transfer functions
    Interval_Domain.thy               ← interval instantiation (widening)
  Equations/
    Constraint_System.thy             ← rhs function from CFG + domain_transfer
    Constraint_System_Sound.thy       ← post-fixpoint soundness theorem
  Solver/
    TD_Interface.thy                  ← AFP TD solver stub + td_analyse
    TD_Soundness.thy                  ← combined solver soundness
  Pipeline/
    Pipeline.thy                      ← full pipeline + Sign/Interval theorems
    Result_Mapping.thy                ← annotated program (acom) + annotation sound.
```

## AFP solver connection (key insight)

The thesis contribution divides into:

| Part | Who proves it | Where |
|---|---|---|
| `make_rhs` is monotone | **us** | `TD_Interface.make_rhs_mono` |
| Solver output is a post-fixpoint | **AFP** TD_plain.partial_correctness | `td_solve_post_fixpoint` axiom (stub) |
| Post-fixpoint overapproximates collecting sem. | **us** | `Constraint_System_Sound.post_fixpoint_sound` |

`td_analyse_post_fixpoint` is a **real proof** (not sorry) — it chains `make_rhs_mono` into `td_solve_post_fixpoint` directly. When AFP is installed, replace the `axiomatization` in `TD_Interface.thy` with an `interpretation` of `TD_plain`.

## Key design decisions (locked + rationale)

| Decision | Rationale |
|---|---|
| `abs_join_set` uses `Finite_Set.fold join_abs bot_abs S` | Hilbert choice (`SOME x. x:S`) ignores `join_abs` and is not monotone — fold is the correct implementation |
| `finite (cfg_edges g)` in `cfg_wf` | Required for fold to be meaningful; proved via `compile_finite` / `to_cfg_finite` |
| `abstract_domain` locale requires `join_comm` + `join_assoc` | Needed to derive `comp_fun_commute join_op` → fold is order-independent |
| `abstract_domain` locale fixes `'a::ord` | Allows `<=` on abstract values inside locale context |
| `sign :: ord`, `ivl :: ord` instances | Required for `abs_state = vname => 'a` to have `<=` (pointwise order) |
| `make_rhs_mono` takes `finite` + `comp_fun_commute` as hypotheses | Both hold in practice; `to_cfg_finite` is proved; `comp_fun_commute join_state` follows from locale axioms |

## Proof status

| Lemma | Status | Difficulty | Notes |
|---|---|---|---|
| `td_analyse_post_fixpoint` | **proved** | trivial | follows from `make_rhs_mono` + AFP axiom |
| `join_sign_comm`, `join_sign_assoc` | **proved** | easy | case splits on datatype |
| `big_step_determ` | sorry | easy | induction on big_step |
| `collect_SKIP/Assign/Seq/If` | sorry | easy | unfold + big_step cases |
| `compile_fresh`, `compile_finite`, `compile_entry_ne_exit` | sorry | medium | induction on `compile` |
| `collect_While` | sorry | medium-hard | lfp + big_step |
| `collect_pp_mono` | sorry | medium | monotonicity of lfp argument |
| `sign_le` lattice laws, `gamma_sign_mono` | sorry | easy | case splits |
| `aval_sign_sound`, `assign_sign_sound` | sorry | easy | induction on aexp |
| `make_rhs_mono` | sorry | medium | fold monotonicity; depends on `tf` being monotone |
| `post_fixpoint_sound` | sorry | hard | requires CFG path inductive def + bridge |
| **`cfg_collect_exit_eq_collect`** | sorry | **very hard** | hardest: WHILE loop + back-edges; needs `cfg_path` inductive predicate |

Fill in roughly in order: easy → medium → hard.

## Critical TODO before `post_fixpoint_sound`

Define a `cfg_path` inductive predicate in `CFG_Collecting.thy`:
```
inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool"
```
Without this, `cfg_collect_exit_eq_collect` has no proof structure.

## Open questions (need supervisor sign-off)

- CFG intermediate: keep, or go direct AST → equation system?
- Result mapping: ACom annotation (current approach) vs. point-map soundness predicate?
- IMP2 vs. IMP: keep IMP2 or fall back to bare IMP if CFG bridge is too hard?
- AFP TD_warrow_mono (total correctness via widening): needed for Interval?
- Scope: prove Sign end-to-end first; defer Interval/widening to stretch goal?

## Isabelle MCP daemon

```bash
./setup.sh        # sparse-clones AutoCorrode I/R into ir-repo/ (once)
./start-ir.sh     # start daemon on http://localhost:9148/mcp, token: isabelle-local
```
Restart Claude Code after `./start-ir.sh`.

## Knowledge base

Research notes, supervisor meetings, concept articles: `~/goblint-formalization-kb/`.
