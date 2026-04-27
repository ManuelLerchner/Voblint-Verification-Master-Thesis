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

## Development loop

1. Draft lemma with `sorry` to check statement type-checks
2. `sledgehammer` on each subgoal (≤15s)
3. Fill in successful proofs; use structured Isar for failures
4. Commit once a top-level lemma closes

## Commit style

`feat(proof): <what was proved>` — e.g., `feat(proof): soundness of sign addition`
