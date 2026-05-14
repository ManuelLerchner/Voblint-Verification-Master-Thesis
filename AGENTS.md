# Goblint Formalization — Project Orientation

Master's thesis at TUM: prove the **complete Goblint static analysis pipeline** in Isabelle/HOL.
Supervisors: Alexandra Graß, Michael Schwarz.

## Latest meeting

Research notes + supervisor meetings live in the KB: `~/goblint-formalization-kb/wiki/meetings/`.
Run `ls ~/goblint-formalization-kb/wiki/meetings/ | sort | tail -1` to find the most recent note.

**Meeting 2 reframe (2026-04-20)**: thesis goal expanded from "formalize domains" to **prove the complete analysis pipeline end-to-end**. Domain instances become *demonstrations* of the pipeline, not the main artifact.

## Goal

Verify the pipeline:
**IMP AST → (CFG?) → equation system → TD solver → sound result mapped back to program**.

The AFP `Top_Down_Solver` (Stade et al., CAV 2024) is already verified — the gap is:
1. IMP syntax + operational semantics + collecting semantics
2. (CFG intermediate — decision open, see below)
3. AST/CFG → equation system + soundness (post-fixpoint overapproximates collecting sem.)
4. Abstract domain instances (sign, interval; octagon stretch)
5. Mapping solver output back to annotated program

## Key decisions (locked)

| | |
|---|---|
| Proof assistant | Isabelle/HOL |
| Source language | **IMP primary** (bare HOL-IMP); IMP2 only if supervisors request |
| Solver | AFP `Top_Down_Solver` (install from AFP; stub in Solver/TD_Interface.thy) |
| Solver interface | `rhs :: pp => (pp => abs_state) => abs_state` (monotone) |
| Domains tier 1 | Sign (finite lattice, no widening) — confirm locale instantiates |
| Domains tier 2 | Interval (widening required) |
| Domains tier 3 | Octagon (stretch goal; aligns with Schwarz SAS 2023) |

## Open decisions (need supervisor sign-off)

| | |
|---|---|
| CFG intermediate | AST → eqsys directly, or AST → CFG → eqsys? |
| Result mapping | Annotated commands (`acom`) vs. point-map soundness predicate? |
| Pipeline bridge | Single pipeline-level Galois connection vs. chain of per-stage soundness lemmas? |
| IMP vs IMP2 | Keep bare IMP or use IMP2 if CFG bridge requires it? |
| Scope | Prove Sign end-to-end first; defer Interval/widening to stretch goal? |

> **Note**: current `src/` code uses IMP2 + CFG (pre-reframe). These files remain valid as a prototype; the above decisions govern the *thesis artifact*.

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
    CFG_Path.thy                      ← cfg_path inductive predicate + lemma library (see §CFG Path Infrastructure)
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
| `big_step_determ` | **proved** | easy | HOL-IMP-style `blast+` after `inductive_cases` |
| `collect_SKIP/Assign/Seq/If` | **proved** | easy | unfold + big_step / `fastforce` |
| `compile_fresh`, `compile_finite`, `compile_entry_ne_exit` | sorry | medium | induction on `compile` |
| `collect_While` | sorry | medium-hard | lfp + big_step |
| `collect_pp_mono` | **proved** | medium | monotonicity of `collect_pp` in `rho` (`CFG_Collecting.thy`) |
| `sign_le` lattice laws, `gamma_sign_mono` | sorry | easy | case splits |
| `aval_sign_sound`, `assign_sign_sound` | sorry | easy | induction on aexp |
| `make_rhs_mono` | sorry | medium | fold monotonicity; depends on `tf` being monotone |
| `post_fixpoint_sound` | sorry | hard | requires CFG path inductive def + bridge |
| **`cfg_collect_exit_eq_collect`** | sorry | **very hard** | hardest: WHILE loop + back-edges; needs `cfg_path` inductive predicate |

Fill in roughly in order: easy → medium → hard.

## CFG Path Infrastructure

**File:** `src/CFG/CFG_Path.thy` (imports `CFG_Def`, imported by `CFG_Collecting`)

**Pattern source:** FormalSSA (Ullrich/Lohner) — see KB article:
`~/goblint-formalization-kb/wiki/concepts/isabelle-proof-engineering.md`

The file provides three layers:

### 1. Core inductive predicate
```isabelle
inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool"
  (* records edge actions along the path — needed for transfer-fn composition *)
```

### 2. Reachability abbreviation + notation
```isabelle
abbreviation cfg_reaches :: "cfg => pp => pp => bool" ("_ \<turnstile> _ \<rightarrow>* _")
```

### 3. Lemma library (attribute discipline from FormalSSA Pattern 2)
| Lemma | Attribute | Purpose |
|---|---|---|
| `cfg_reaches_refl` | `[intro, simp]` | `g |- v ->* v` |
| `cfg_reaches_step` | `[intro]` | edge → extend reachability |
| `cfg_reaches_trans` | `[intro]` | chain paths |
| `cfg_path_cases` | `[consumes 1, case_names empty step]` | named case split |
| `cfg_path_induct` | `[consumes 1, case_names empty step]` | structured induction |
| `cfg_entry_reachable` | `[intro, simp]` | entry always reachable |

### 4. Transfer function composition
```isabelle
fun path_collect :: "(edge_action * pp) list => state set => state set"
```
Composes `edge_collect` along a path — the bridge between `cfg_path` and `post_fixpoint_sound`.

**Why `(edge_action * pp)` not just `pp list`**: unlike FormalSSA (which needs only node
topology for SSA), our soundness proofs need to know *which action* was taken on each step
to compose transfer functions.

## Isabelle MCP daemon

```bash
./setup.sh        # sparse-clones AutoCorrode I/R into ir-repo/ (once)
./start-ir.sh     # start daemon on http://localhost:9148/mcp, token: isabelle-local
```
Restart Claude Code after `./start-ir.sh`.

**Agent tips (Sledgehammer, MCP, Isar traps):** see **`docs/ISABELLE_AGENT_NOTES.md`** in this repository.

## Knowledge base

Research notes, supervisor meetings, concept articles: `~/goblint-formalization-kb/`.

**Novelty / related work (relevant vs already covered, what rests on the CFG bridge):**  
`~/goblint-formalization-kb/wiki/research/novelty-not-covered-positioning.md`

---

## Agent workflow (Claude Code, MCP, Isabelle)

*Merged from `.claude/CLAUDE.md` — this file is the single source of truth; root `CLAUDE.md` and `.claude/*.md` symlink here for Cursor / Claude / other agents.*

### Session start

1. Read **`AGENTS.md`** (this file) — project goal, locked decisions, folder layout; skim **`docs/ISABELLE_AGENT_NOTES.md`** for Isabelle/MCP/Sledgehammer workflow
2. Check which theories exist: `ls src/`
3. Batch-check compilation: `isabelle build -d <afp> -D . Goblint_Formalization` (see `ROOT` for AFP path)
4. Optionally connect MCP for interactive proof work (see below)

### Two modes: batch build vs. interactive MCP

#### Batch build (checking the whole session)

```bash
isabelle build -d <path-to-AFP>/Top_Down_Solver -D . Goblint_Formalization
```

(Adjust Isabelle binary path for your install, e.g. `~/Isabelle2025-2/bin/isabelle`.)

Requires `options [quick_and_dirty]` in `ROOT` to allow `sorry`.

#### Isabelle MCP (interactive)

```bash
./start-ir.sh   # starts daemon on HOL session (see script for session name)
```

**Limitation:** if the daemon uses `--session HOL` only, loading project theories may require loading imports manually or switching the daemon session to `Goblint_Formalization` after a successful full build.

**Workflow:** run `isabelle build` first → start daemon → `load_theory` for dependencies → `step` / `sledgehammer` on subgoals.

Load tool schemas before first MCP use (example):

```
ToolSearch("select:mcp__isabelle-ir__connect")
ToolSearch("select:mcp__isabelle-ir__init,mcp__isabelle-ir__step,mcp__isabelle-ir__state,mcp__isabelle-ir__back")
ToolSearch("select:mcp__isabelle-ir__sledgehammer,mcp__isabelle-ir__find_theorems,mcp__isabelle-ir__load_theory")
```

### ASCII symbols — mandatory (when writing Isabelle in chat)

| Write | Meaning |
|---|---|
| `:` | ∈ (NOT `::`) |
| `~:` | ∉ |
| `=>` | ⇒ (metalogic arrow in chat; in theories use `\<Longrightarrow>` / `==>` as appropriate) |
| `-->` | ⟶ |
| `~` | ¬ |
| `&` / `\|` | ∧ / ∨ |
| `!`/`ALL` | ∀ |
| `?`/`EX` | ∃ |
| `::` | type annotation only |

### Proof pitfalls

- **Simp loops**: never put `hy: f y = {x. P (f x)}` in simp set — use `subst hy` once then `simp add: mem_Collect_eq`.
- **monoD**: use `monoD[OF mono h]` not `using mono by (rule monoD)`.
- **Named assumptions**: `assume surj: "surj f"`, not `from "surj f"`.
- **Biconditional**: use `=` not `<->` in Isar propositions.
- **Multi-line strings in MCP**: write all Isar on **one line** per `step` call when the MCP API rejects newlines.

### Isabelle type / syntax pitfalls (project-specific)

**Inside quoted strings `"..."` — NOT comments:** `(* ... *)` inside type strings is parsed as HOL.

**`fun` patterns:** numeral literals cannot be patterns; avoid `inv` as a pattern name (clash with `Hilbert_Choice.inv`).

**Bounded quantifiers:** `ALL j >= n.` is invalid — use `ALL j. n <= j --> ...`.

**Free variables in axioms:** names like `rhs` may clash with imported constants — rename (e.g. `rhsfn`).

**Sorts:** `abs_state = vname => 'a` needs `'a::ord` where pointwise `<=` is used; align with `abstract_domain` locale.

**`instantiation`:** must follow the `datatype` / `typedecl` it instantiates.

**Imports:** theories using `to_cfg`, `domain_transfer`, locales — keep import closure consistent (see `IMP2_to_CFG`, `Constraint_System`, interpretations in domain theories).

### HOL-IMP / IMP2 semantics

- Import HOL-IMP material with `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`, etc.
- Session parent in `ROOT`: `= "HOL-IMP" +` (not bare `HOL +`).
- **Big-step:** this repo uses HOL-IMP-style infix **`(c,s) \<Rightarrow> t`** in `IMP2_Semantics.thy` (same term as `big_step (c,s) t`).
- **Execution proofs:** for schematic final states, often `apply (rule exI)` (or `exI`) before `Assign` / `Seq` intros.
- **`rule Assign`:** needs schematic target state in some setups; use `exI` first when unification fails on concrete stores.
- **AFP `IMP2` (Lammich):** not the same as this repo’s minimal **IMP2** frontend — disambiguate in prose (see KB [[concepts/imp-language]] / [[concepts/imp2]]).
- **`schematic_lemma`:** not always available in MCP step commands — use `lemma` + `exI` pattern.
- **`sorry` in batch build:** needs `quick_and_dirty` in `ROOT`.

### Abstract domain architecture (reminder)

- `abstract_domain` locale: `join_comm`, `join_assoc` → `comp_fun_commute` for folds
- `td_analyse_post_fixpoint`: real proof from `make_rhs_mono` + AFP post-fixpoint
- AFP install: replace `axiomatization` stub in `TD_Interface.thy` with `interpretation TD_plain ...` when ready

### Development loop

1. Draft lemma with `sorry` to check the statement type-checks
2. `sledgehammer` on subgoals (time-bounded); see **`docs/ISABELLE_AGENT_NOTES.md`** for MCP + tactic choice
3. Fill proofs; structured Isar when automation fails
4. Commit when a top-level lemma closes

### Commit style

`feat(proof): <what was proved>` — e.g. `feat(proof): soundness of sign addition`
