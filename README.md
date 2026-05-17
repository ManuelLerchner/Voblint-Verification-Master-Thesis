Goblint Formalization
=====================

Abstract
--------
Machine-checked Isabelle/HOL formalization of *abstract interpretation* for a
small imperative language. We model IMP, compile it into a control-flow graph,
derive a constraint system over an abstract domain (Sign, Interval, ...), and
solve it with the verified top-down solver of stilscher/td-verification. The
end-to-end theorem connects the concrete collecting semantics of an IMP program
to the abstract result returned by the solver, giving a soundness statement for
the full analysis pipeline -- a formal counterpart to the Goblint static
analyzer.

```
IMP program -> CFG -> abstract eq. system -> TD solver -> sound abstract result
```

This repository is the code/proof artifact for the master's thesis on
formalizing the Goblint static-analysis pipeline in Isabelle/HOL.


Requirements
------------

- A running version of [Isabelle](https://isabelle.in.tum.de/) (Isabelle2025 or
  newer) with `isabelle` in your `$PATH`.
- The [Archive of Formal Proofs](https://www.isa-afp.org/) checked out locally;
  the build needs the `thys/` directory (transitive dependency
  `Root_Balanced_Tree`).
- GNU `make`, `git`, and standard POSIX tools.


Build instructions
------------------

Set `AFP` to your AFP `thys/` directory (default `~/afp/thys`) and use the
provided `Makefile` targets:

- `make vendor`: clones [stilscher/td-verification](https://github.com/stilscher/td-verification)
  into `vendor/td-verification`, checks out the pinned upstream commit, and
  applies `vendor/td-verification.patch` (Isabelle2025 compatibility — uses
  `Set.remove_eq` in place of `remove_def`, see the patch for details).

- `make build` (default): runs the Isabelle formalization, depends on `vendor`.
  Equivalent to:
  ```
  isabelle build -d $(AFP) -d vendor/td-verification -D . Goblint_Formalization
  ```

- `make jedit`: launches Isabelle/jEdit with the correct session roots
  pre-loaded.

- `make clean-vendor`: removes `vendor/td-verification/` (re-fetched on next
  `make vendor`).

- `make clean`: removes vendored sources and the built session heap.

Example:
```
make AFP=/path/to/afp/thys build
```

The `quick_and_dirty` option is set in `ROOT`, so `sorry` placeholders are
permitted during proof development.


Repository layout
-----------------

```
.
├── src/
│   ├── IMP2/             IMP syntax and big-step semantics
│   ├── CFG/              CFG definition, IMP-to-CFG compiler, CFG collecting
│   ├── Equations/        constraint system + soundness layer
│   ├── Solver/           bridge to the verified top-down solver
│   ├── Domains/          abstract domains (Sign, Interval, ...)
│   ├── Pipeline/         end-to-end pipeline theorems and result mapping
│   ├── Examples/         concrete instantiations and worked examples
│   └── Goblint_Formalization.thy   top-level session entry
├── vendor/
│   ├── td-verification/             fetched by `make vendor` (gitignored)
│   └── td-verification.patch        local fixes to the vendored TD solver
├── docs/                 design notes, proof phases, agent notes
├── Makefile              build entry points (vendor, build, jedit, clean)
└── ROOT                  Isabelle session definition
```


Verified dependencies
---------------------

| Dependency                       | Source                                                  | Role                                      |
| -------------------------------- | ------------------------------------------------------- | ----------------------------------------- |
| `HOL-IMP`                        | Isabelle distribution                                   | session parent; IMP syntax/semantics base |
| `TD` (`TD_plain`, `Basics`, ...) | vendored from `stilscher/td-verification` + local patch | verified top-down solver                  |
| `Root_Balanced_Tree`             | AFP                                                     | transitive dep of TD session              |


Vendoring the TD solver
-----------------------

The top-down solver lives upstream at
[stilscher/td-verification](https://github.com/stilscher/td-verification).
A small local change is needed for Isabelle2025 compatibility, kept as a
plain `git`-format patch in `vendor/td-verification.patch`. The Makefile
clones the pinned upstream commit and applies the patch on demand. This avoids
maintaining a long-lived submodule fork-pin: the diff is reviewable in this
repository and the vendored tree is never tracked.


Knowledge-base submodule
------------------------

The thesis/research wiki is included as a git submodule:

- `goblint-formalization-kb/` -- [ManuelLerchner/goblint-formalization-kb](https://github.com/ManuelLerchner/goblint-formalization-kb)

Clone with submodules:
```
git clone --recurse-submodules https://github.com/ManuelLerchner/goblint-formalization.git
```
If already cloned:
```
git submodule update --init --recursive
```


Agent / MCP helpers
-------------------

Sledgehammer tips, `metis` pitfalls, induction gotchas, and the MCP tool
list are documented in `docs/ISABELLE_AGENT_NOTES.md`. Bootstrap scripts:

```
./setup.sh
./start-ir.sh
```


Suggested reading order
-----------------------

1. `docs/ISABELLE_AGENT_NOTES.md` -- MCP + Sledgehammer workflow, proof traps.
2. `docs/PROOF_OVERVIEW.md` -- theorem chain, key types, key lemmas.
3. `docs/IMPLEMENTATION_GUIDE.md` -- phase plan and dependency order.
4. `src/Goblint_Formalization.thy` -- top-level imports / session entry.
