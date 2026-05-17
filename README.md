Goblint Formalization
=====================

Abstract
--------

We formalize the Goblint analysis pipeline from IMP through CFG compilation and
a constraint system to the verified top-down solver of
[stilscher/td-verification](https://github.com/stilscher/td-verification), and
prove that **any abstract domain** satisfying our locale and transfer obligations
yields a solver result that soundly over-approximates concrete collecting
semantics; sign analysis is a fully discharged instance.

### Pipeline (overview)

Solid arrows: compilation and analysis steps. Dotted arrows: proved soundness links.

```mermaid
flowchart LR
  IMP["IMP"]
  CFG["CFG"]
  EQ["eq. system"]
  TD["TD solver"]
  OUT["γ ∘ env"]

  IMP -->|compile| CFG
  CFG -->|make RHS| EQ
  EQ -->|td_analyse| TD
  TD --> OUT

  IMP -.->|big-step sound| CFG
  CFG -.->|post-fixpoint sound| OUT
```

| Link            | Lemma / idea                                                                         |
| --------------- | ------------------------------------------------------------------------------------ |
| IMP ↔ CFG       | `cfg_collect_exit_eq_collect` — AST collecting = CFG collecting at exit              |
| CFG → abstract  | `post_fixpoint_sound` — post-fixpoint of `rhs` over-approximates `cfg_collect`       |
| eq. system → TD | `td_analyse_post_fixpoint` — vendored solver returns a post-fixpoint                 |
| End-to-end      | `pipeline_sound` / `pipeline_invariant_sound` (generic); `goblint_sign_sound` (sign) |

Where abstract interpretation is in the proof
-------------------------------------------

The equation system is not validated by a separate “code generator correctness”
theorem. We **define** `rhs` as the abstract analogue of CFG collecting, then
prove that **every post-fixpoint** over-approximates concrete reachability.

|                      | Concrete (collecting)                    | Abstract interpretation                                          |
| -------------------- | ---------------------------------------- | ---------------------------------------------------------------- |
| One edge             | `edge_collect a` on store sets           | `apply_tf tf a` on `abs_state`                                   |
| One program point    | `collect_pp` — join of predecessor edges | `rhs` — join of `apply_tf` images                                |
| Global               | `cfg_collect` (least fixpoint)           | `env` with `is_post_fixpoint`                                    |
| Link                 | (definition)                             | `edge_collect (γ σ) ⊆ γ (apply_tf … σ)` — **transfer soundness** |
| Main soundness lemma |                                          | `post_fixpoint_sound`: `cfg_collect ⊆ γ ∘ env`                   |

So **abstract interpretation is the `rhs` / `γ` / `join` / `apply_tf` layer**.
`make_rhs` / `make_rhs_tree` spell out the equations; `td_analyse` (TD solver)
returns an `env` that satisfies them; `post_fixpoint_sound` shows that solution
is sound w.r.t. `cfg_collect`. IMP enters via `collect` and
`cfg_collect_exit_eq_collect`.

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

| Document                       | Contents                                                |
| ------------------------------ | ------------------------------------------------------- |
| `docs/PIPELINE_AT_A_GLANCE.md` | Thesis goal, AI vs collecting, status, theorem stack    |
| `docs/HOL_IMP_COMPARISON.md`   | vs HOL-IMP `Abs_*`: workflow, domain theory tradeoffs   |
| `docs/PROOF_OVERVIEW.md`       | Theorem chain, key types and lemmas                     |
| `docs/PROOF_PHASES.md`         | Proof status, sorry inventory, remaining work           |
| `docs/PIPELINE_WALKTHROUGH.md` | Stage-by-stage walkthrough with examples                |
| `docs/PROOF_SIMPLIFICATION.md` | CFG_Collecting refactor playbook (optional maintenance) |
| `docs/html/`                   | HTML renderings of the walkthroughs (may lag `.md`)     |

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

| Script                         | Role                                                                                                     |
| ------------------------------ | -------------------------------------------------------------------------------------------------------- |
| `./setup-iq.sh`                | Build and install the I/Q jEdit plugin (vendored under `ir-repo/iq/`)                                    |
| `./start-iq.sh`                | Launch Isabelle/jEdit with I/Q listening on port 8765                                                    |
| `./setup.sh` / `./start-ir.sh` | Headless [Isabelle/R](https://github.com/awslabs/AutoCorrode/tree/main/ir) MCP when jEdit is not running |
