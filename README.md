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

Prerequisites: **Isabelle/HOL** (e.g. install from [isabelle.in.tum.de](https://isabelle.in.tum.de/)) and a checkout of the Archive of Formal Proofs session **Top_Down_Solver** (or point `-d` at your local AFP tree that contains it).

From the **repository root** (the directory that contains `ROOT`):

```bash
isabelle build -o quick_and_dirty \
  -d /path/to/afp-entries/Top_Down_Solver \
  -d . \
  -b Goblint_Formalization
```

Example if Isabelle lives in your home directory and the AFP entry is next to this knowledge base:

```bash
cd /path/to/goblint-formalization
"$HOME/Isabelle2025-2/bin/isabelle" build -o quick_and_dirty \
  -d "$HOME/goblint-formalization-kb/raw/repos/afp-entries/Top_Down_Solver" \
  -d . \
  -b Goblint_Formalization
```

- **`-d` (first)**: session root for **Top_Down_Solver** (must contain a `ROOT` with that session).
- **`-d` (second)**: this repository (must contain the top-level `ROOT` for `Goblint_Formalization`). Use **`.`** only if your shell is already in that directory; otherwise pass the absolute path to the repo.
- **`-o quick_and_dirty`**: matches the session option in `ROOT` and allows `sorry` while proofs are in progress.

The main session is **`Goblint_Formalization`**. The vendor session **TD** (for `TD_Total.thy` / warrowing track) is **not** in the default session list; it needs an extra AFP dependency (**Root_Balanced_Tree**). See the comment in `ROOT` for how to re-enable it.

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
