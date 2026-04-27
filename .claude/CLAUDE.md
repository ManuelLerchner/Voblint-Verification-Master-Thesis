# Goblint Formalization — LLM Instructions

## Session start

1. Read `CLAUDE.md` — project goal, locked decisions, folder layout
2. `mcp__isabelle-ir__connect(token="isabelle-local")` — connect to daemon
3. Check which theories exist: `ls src/`

## Isabelle MCP workflow

Load tool schemas before first use (deferred loading):
```
ToolSearch("select:mcp__isabelle-ir__connect")
ToolSearch("select:mcp__isabelle-ir__init,mcp__isabelle-ir__step,mcp__isabelle-ir__state,mcp__isabelle-ir__back")
ToolSearch("select:mcp__isabelle-ir__sledgehammer,mcp__isabelle-ir__find_theorems,mcp__isabelle-ir__load_theory")
```

Then connect, init a REPL, and step through proofs.

## ASCII symbols — mandatory

| Write | Meaning |
|---|---|
| `:` | ∈ (NOT `::`) |
| `~:` | ∉ |
| `=>` | ⇒ |
| `-->` | ⟶ |
| `~` | ¬ |
| `&` / `\|` | ∧ / ∨ |
| `!`/`ALL` | ∀ |
| `?`/`EX` | ∃ |
| `::` | type annotation only |

## Proof pitfalls

- **Simp loops**: never put `hy: f y = {x. P (f x)}` in simp set — use `subst hy` once then `simp add: mem_Collect_eq`.
- **monoD**: use `monoD[OF mono h]` not `using mono by (rule monoD)`.
- **Named assumptions**: `assume surj: "surj f"`, not `from "surj f"`.
- **Biconditional**: use `=` not `<->` in Isar propositions.
- **Multi-line strings in MCP**: write all Isar on ONE LINE per `step` call — multi-line breaks in `isar_text` cause parse errors.

## Isabelle type / syntax pitfalls (discovered in this project)

**Inside quoted strings `"..."` — NOT comments:**
- `(* ... *)` inside `"cfg => 'a (* comment *) => bool"` is parsed as HOL, not stripped — `*` becomes the product type operator → parse error. Remove all inline comments from type annotation strings.

**`fun` pattern restrictions:**
- Numeral literals (`0`, `1`) cannot appear in `fun` patterns — "Non-constructor pattern". Use a variable `n` + `if n = 0 then...` instead.
- `inv` as a pattern variable name clashes with `Hilbert_Choice.inv :: ('a => 'b) => 'b => 'a` — Isabelle resolves it as the constant, not a fresh variable. Rename to `invs` or `invariant`.
- Bounded quantifier `ALL j >= n.` is invalid HOL syntax → "Inner syntax error". Write `ALL j. n <= j -->` instead.

**Free variables in axioms clash with imported constants:**
- In `axiomatization where "... rhs v ..."`, if `rhs` is imported, it's resolved as the constant. Rename to `rhsfn` or similar.

**Sort constraints propagate:**
- If a definition uses `<=` on `'a abs_state = vname => 'a`, Isabelle needs `'a::ord`. Add `'a::ord` explicitly in the type annotation of `definition` or `record` if Isabelle complains.
- `abstract_domain` locale fixes `'a::ord` — any use of `abstract_domain.*` outside the locale context requires the concrete type to have an `ord` instance.
- `record ('a::ord) foo = ...` syntax for sort-constrained record type params.

**`instantiation` ordering:**
- `instantiation T :: ord begin...end` MUST come AFTER `datatype T = ...`. Placing it before causes "Undefined type name: T".

**`assumes/shows` vs inline `-->`:**
- For lemmas with nested quantifiers inside an implication (`ALL i. P i --> EX n. ALL j. Q j`), use `assumes "ALL i. P i" shows "EX n. ALL j. Q j"` to avoid parser ambiguity.

**Imports:**
- `to_cfg` is defined in `IMP2_to_CFG` — any theory using it must import `IMP2_to_CFG` (directly or transitively via `CFG_Collecting`).
- `domain_transfer` is in `Constraint_System` — `Sign_Domain` and `Interval_Domain` must import it.
- `sign_domain.*` locale names only available after `interpretation sign_domain: abstract_domain ...` — ensure interpretation appears before any lemma that uses `sign_domain.gamma_state` etc.

## HOL-IMP specifics

- **Import**: `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`, etc. Load with `load_theory "HOL-IMP.Com"` in REPL.
- **Session ROOT**: use `= "HOL-IMP" +` not `= HOL +`. Add `options [quick_and_dirty]` to allow `sorry` in batch `isabelle build`.
- **Big-step notation**: `big_step (c, s) t` not `(c, s) => t` — `=>` is the type arrow, which conflicts.
- **Execution proofs**: for `big_step (c, s) ?t` with schematic final state, use `apply (rule exI)` first to make `?t` fresh, then apply `Seq`/`Assign`/etc.
- **Correctness proofs**: state `big_step (c, s) t ==> property t` and prove with `auto elim!: big_step.cases`.
- **`rule Assign`** only works when the target state is SCHEMATIC — it cannot unify against concrete state expressions (like `s(''x'' := 5)`) because `aval` is unevaluated. Use `exI` first.
- **IMP2 (AFP)**: not installed. Not needed — `HOL-IMP.Abs_Int*` already has the abstract interpretation framework for the thesis.
- **`schematic_lemma`**: not available as a step command. Use `lemma` + `rule exI` instead.
- **`isabelle build` with sorry**: requires `options [quick_and_dirty]` in ROOT. Without it, `sorry` causes build failure even if type-checking passes.

## Abstract domain architecture (project-specific)

- `abstract_domain` locale: fixed `'a::ord`, `bot`, `join_op`, `widen`; assumes `join_comm` + `join_assoc` (needed for `comp_fun_commute`)
- `abs_join_set join_abs bot S = Finite_Set.fold join_abs bot S` — requires `comp_fun_commute join_abs` + `finite S` for correct behaviour
- `rhs_mono` / `make_rhs_mono`: take `finite (cfg_edges g)` + `comp_fun_commute join_abs` as explicit hypotheses
- `td_analyse_post_fixpoint` is a **real proof** (not sorry): `make_rhs_mono` + `td_solve_post_fixpoint` → done
- When installing AFP: replace `axiomatization td_solve` in `TD_Interface.thy` with `interpretation TD_plain "make_rhs g tf ..."` using `make_rhs_mono`

## Development loop

1. Draft lemma with `sorry` to check statement type-checks
2. `sledgehammer` on each subgoal (≤15s)
3. Fill in successful proofs; use structured Isar for failures
4. Commit once a top-level lemma closes

## Commit style

`feat(proof): <what was proved>` — e.g., `feat(proof): soundness of sign addition`
