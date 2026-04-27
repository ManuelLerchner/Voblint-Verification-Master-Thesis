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

## HOL-IMP specifics

- **Import**: `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`, etc. Load with `load_theory "HOL-IMP.Com"` in REPL.
- **Session ROOT**: use `= "HOL-IMP" +` not `= HOL +`.
- **Big-step notation**: `big_step (c, s) t` not `(c, s) => t` — `=>` is the type arrow, which conflicts.
- **Execution proofs**: for `big_step (c, s) ?t` with schematic final state, use `apply (rule exI)` first to make `?t` fresh, then apply `Seq`/`Assign`/etc.
- **Correctness proofs**: state `big_step (c, s) t ==> property t` and prove with `auto elim!: big_step.cases`.
- **`rule Assign`** only works when the target state is SCHEMATIC — it cannot unify against concrete state expressions (like `s(''x'' := 5)`) because `aval` is unevaluated. Use `exI` first.
- **IMP2 (AFP)**: not installed. Not needed — `HOL-IMP.Abs_Int*` already has the abstract interpretation framework for the thesis.
- **`schematic_lemma`**: not available as a step command. Use `lemma` + `rule exI` instead.

## Development loop

1. Draft lemma with `sorry` to check statement type-checks
2. `sledgehammer` on each subgoal (≤15s)
3. Fill in successful proofs; use structured Isar for failures
4. Commit once a top-level lemma closes

## Commit style

`feat(proof): <what was proved>` — e.g., `feat(proof): soundness of sign addition`
