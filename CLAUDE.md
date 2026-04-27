# Goblint Formalization — Project Orientation

Master's thesis at TUM: prove the **complete Goblint static analysis pipeline** in Isabelle/HOL.
Supervisors: Alexandra Graß, Michael Schwarz.

## Goal

Verify the pipeline: **IMP AST → equation system → TD solver → sound result**.

The AFP `Top_Down_Solver` (Stade et al., CAV 2024) is already verified — the gap is:
1. IMP syntax + operational semantics
2. AST → equation system construction (via CFG or direct)
3. Abstract domain instances (sign, parity; relational as stretch)
4. Mapping solver output back to program annotations

## Key decisions (locked)

| | |
|---|---|
| Proof assistant | Isabelle/HOL |
| Solver | AFP `Top_Down_Solver` |
| Interface | `strategy_tree`-based RHS + TD locale hierarchy |
| Language | IMP primary |
| Domains | Sign/parity first; octagon as stretch goal |

## Source structure

```
ROOT                    ← Isabelle session config
src/
  Goblint_Formalization.thy   ← top-level imports
  IMP/                        ← language definition (to be created)
  Analysis/                   ← abstract interpretation machinery (to be created)
  Domains/                    ← abstract domain instances (to be created)
```

## Isabelle MCP

The I/R daemon lives in `~/goblint-formalization-kb/isabelle-mcp/`.
Start it from there: `./isabelle-mcp/start-ir.sh`

It then listens on `http://localhost:9148/mcp` — the `.mcp.json` here connects to it.
Restart Claude Code after starting the daemon so it picks up the MCP server.

## Knowledge base

Research notes, supervisor meetings, concept articles: `~/goblint-formalization-kb/`.
