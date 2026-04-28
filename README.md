# Goblint Formalization

Machine-checked Isabelle/HOL formalization of the Goblint static-analysis pipeline:

`IMP2 program -> CFG -> equation system -> AFP Top_Down_Solver -> sound abstract result`

This repository is the code/proof artifact for the thesis work on connecting domain-level abstract interpretation proofs to the verified AFP top-down solver.

## What This Repository Contains

- `src/IMP2/`: IMP2 syntax and semantics
- `src/CFG/`: CFG model, compiler from IMP2 to CFG, and CFG collecting semantics
- `src/Equations/`: Constraint/equation-system construction and soundness layer
- `src/Solver/`: AFP solver bridge (`Top_Down_Solver`) and solver soundness composition
- `src/Pipeline/`: End-to-end pipeline theorems and result mapping
- `docs/`: Project documentation (`IMPLEMENTATION_GUIDE.md`, `PROOF_OVERVIEW.md`)

## Existing Verified Dependencies

- Isabelle session parent: `HOL-IMP`
- AFP session dependency: `Top_Down_Solver`

The repository now uses AFP's strategy-tree interface directly for solver integration.

## Knowledge Base Submodule

The thesis/research wiki is included as a git submodule:

- `goblint-formalization-kb/`
- remote: [ManuelLerchner/goblint-formalization-kb](https://github.com/ManuelLerchner/goblint-formalization-kb)

Clone with submodules:

```bash
git clone --recurse-submodules https://github.com/ManuelLerchner/goblint-formalization.git
```

If already cloned:

```bash
git submodule update --init --recursive
```

## Build

From repository root:

```bash
isabelle build -D .
```

## Isabelle MCP / IR helper

Use the existing scripts:

```bash
./setup.sh
./start-ir.sh
```

## Suggested Reading Order

1. `docs/PROOF_OVERVIEW.md` (theorem chain, key types, key lemmas)
2. `docs/IMPLEMENTATION_GUIDE.md` (phase plan and dependency order)
3. `src/Goblint_Formalization.thy` (top-level imports/session entry)
