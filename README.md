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
│   ├── Pipeline/         end-to-end pipeline theorems
│   ├── Examples/         concrete instantiations and worked examples
│   └── Goblint_Formalization.thy   top-level session entry
├── vendor/
│   ├── td-verification/             fetched by `make vendor` (gitignored)
│   └── td-verification.patch        local fixes to the vendored TD solver
├── docs/                 proof overview, phases, walkthroughs
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

Documentation
-------------

| Document | Contents |
| -------- | -------- |
| `docs/PIPELINE_AT_A_GLANCE.md` | What changed when sign pipeline closed (diagram + stack) |
| `docs/PROOF_OVERVIEW.md` | Theorem chain, key types and lemmas |
| `docs/PROOF_PHASES.md` | Proof status, sorry inventory, remaining work |
| `docs/PIPELINE_WALKTHROUGH.md` | Stage-by-stage walkthrough with examples |
| `docs/PROOF_SIMPLIFICATION.md` | CFG_Collecting refactor playbook (optional maintenance) |
| `docs/html/` | HTML renderings of the walkthroughs (may lag `.md`) |

Agent / MCP workflow notes: `docs/ISABELLE_AGENT_NOTES.md`. Bootstrap: `./setup.sh`, `./start-ir.sh`.

Agent-assisted development (Isabelle/Q)
---------------------------------------

Proof development in this repository also experiments with
[Isabelle/Q](https://github.com/awslabs/AutoCorrode/tree/main/iq) (I/Q), an MCP
server for Isabelle/jEdit that lets coding agents edit theories, query proof
states, run Sledgehammer, and explore tactics interactively. The setup follows
the autoformalization workflow described by Kevin Kappelmann et al. in
[*Just Type It in Isabelle! AI Agents Drafting, Mechanizing, and Generalizing
from Human Hints*](https://arxiv.org/abs/2604.15713) (arXiv:2604.15713, 2026);
see their §6.1 for the Isabelle/Q technical setup and `AGENTS.md` here for
project-specific conventions.

| Script | Role |
| ------ | ---- |
| `./setup-iq.sh` | Build and install the I/Q jEdit plugin (vendored under `ir-repo/iq/`) |
| `./start-iq.sh` | Launch Isabelle/jEdit with I/Q listening on port 8765 |
| `./setup.sh` / `./start-ir.sh` | Headless [Isabelle/R](https://github.com/awslabs/AutoCorrode/tree/main/ir) MCP when jEdit is not running |
