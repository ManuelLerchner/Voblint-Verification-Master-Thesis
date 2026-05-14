# Goblint Formalization

Machine-checked Isabelle/HOL formalization of the Goblint static-analysis pipeline:

`IMP program -> CFG -> equation system -> TD solver (vendor/td-verification) -> sound abstract result`

This repository is the code/proof artifact for the master's thesis on formalizing the complete Goblint static-analysis pipeline in Isabelle/HOL.

## What This Repository Contains

- `src/IMP2/`: IMP syntax and semantics (`store` = `vname => int`)
- `src/CFG/`: CFG model, compiler from IMP to CFG, and CFG collecting semantics
- `src/Equations/`: Constraint/equation-system construction and soundness layer
- `src/Solver/`: TD solver bridge (`vendor/td-verification`) and solver soundness composition
- `src/Pipeline/`: End-to-end pipeline theorems and result mapping
- `docs/`: Project documentation

## Verified Dependencies

| Dependency | Source | Role |
|---|---|---|
| `HOL-IMP` | Isabelle distribution | session parent; IMP syntax/semantics base |
| `TD` (TD_plain, Basics, …) | `vendor/td-verification` submodule | verified top-down solver |
| `Root_Balanced_Tree` | AFP | transitive dep of TD session |

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

### Prerequisites

- **Isabelle/HOL** — download from [isabelle.in.tum.de](https://isabelle.in.tum.de/)
- **AFP** — the Archive of Formal Proofs (needed for `Root_Balanced_Tree`, a transitive dependency of the TD solver). Clone or download from [isa-afp.org](https://www.isa-afp.org/download/).
- **Submodules** — populate after cloning (see above); `vendor/td-verification` provides the `TD` solver session.

### Exact build command

From the **repository root** (the directory containing `ROOT`):

```bash
isabelle build \
  -d ~/afp/thys \
  -d vendor/td-verification \
  -D . \
  Goblint_Formalization
```

Substitute `~/afp/thys` with the path to your AFP checkout's `thys/` directory.

The `quick_and_dirty` option is already set in `ROOT` (allows `sorry` during proof development).

### Isabelle/jEdit

`isabelle jedit` does **not** accept `isabelle build`’s `-D DIR` (for jEdit, `-D` is only for JVM properties like `-Dfoo=bar`). Use **`-d`** for each session root that supplies a `ROOT`.

From the repository root:

```bash
isabelle jedit \
  -d ~/afp/thys \
  -d vendor/td-verification \
  -d .
```

Adjust `~/afp/thys` to your AFP `thys/` directory. The final `-d .` registers this repo’s `ROOT` (same role as `build`’s `-D .` for the project session). Then open a theory from `src/` (for example `Goblint_Formalization.thy`) and pick the `Goblint_Formalization` logic session in jEdit if prompted.

### Session dependencies

| `-d` path | Provides session | Used for |
|---|---|---|
| `~/afp/thys` | `Root_Balanced_Tree` | transitive dep of TD solver |
| `vendor/td-verification` | `TD` | top-down solver (`TD_plain`, `strategy_tree`, …) |
| `.` (`build`’s `-D .`, or `jedit`’s `-d .`) | `Goblint_Formalization` | this project |

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
