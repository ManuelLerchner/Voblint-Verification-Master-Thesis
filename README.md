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

Solid arrows: compilation and analysis steps. Dotted arrows: proved soundness
bridges. Dashed red arrows: bridges still missing (open problems; see
`docs/OPEN_PROBLEMS.md`).

```mermaid
flowchart LR
  BS["big_step"]
  COL["collect"]
  CC["cfg_collect"]
  PFP["env (post-fixpoint)"]
  TD["TD solver output"]
  TERM["TD terminates"]
  IVL["interval domain"]

  BS -->|B1| COL
  COL -->|B2| CC
  CC -->|B3| PFP
  PFP -->|B4| TD

  CC -.->|"B5: cfg_in_reach (P2)"| TD
  PFP -.->|"B6: comp_fun_idem (P3)"| TD
  TD -.->|"B7: TD_plain.solve_dom (P1, gated on P5)"| TERM
  IVL -.->|"B8: widening termination (P6/P7)"| TERM

  linkStyle 4,5,6,7 stroke:#c62828,stroke-dasharray: 4 3
```

| Bridge | Lemma / obligation                                            | Status              |
| ------ | ------------------------------------------------------------- | ------------------- |
| B1     | `big_step ⇒ collect` (definition of `collect`)                | **done**            |
| B2     | `cfg_collect_exit_eq_collect` — AST collecting = CFG at exit  | **done**            |
| B3     | `post_fixpoint_sound` — post-fixpoint over-approximates       | **done**            |
| B4     | `td_analyse_post_fixpoint` — TD output is a post-fixpoint     | **done**            |
| B5     | `cfg_in_reach (to_cfg c)` — CFG shape ⇒ solver reach-set      | **missing** (P2)    |
| B6     | `sound_domain ⇒ comp_fun_idem join_state`                     | **missing** (P3)    |
| B7     | `TD_plain.solve_dom` on compiled CFG — termination            | **missing** (P1/P5) |
| B8     | `widen_ivl` axioms + wf widening chains                       | **missing** (P6/P7) |

End-to-end theorems: `pipeline_sound` / `pipeline_invariant_sound` (generic,
chains B1–B4, carries B5/B6/B7 as assumptions); `goblint_sign_sound` (sign
instance). For the open bridges see `docs/OPEN_PROBLEMS.md`.

Where abstract interpretation is in the proof
-------------------------------------------

The equation system is not validated by a separate “code generator correctness”
theorem. We **define** `rhs` as the abstract analogue of CFG collecting, then
prove that **every post-fixpoint** over-approximates concrete reachability.

|                      | Concrete (collecting)                  | Abstract interpretation                                        |
| -------------------- | -------------------------------------- | -------------------------------------------------------------- |
| One edge             | `edge_collect a` on store sets         | `apply_tf tf a` on `abs_state`                                 |
| One program point    | `collect_pp` join of predecessor edges | `rhs` join of `apply_tf` images                                |
| Global               | `cfg_collect` (least fixpoint)         | `env` with `is_post_fixpoint`                                  |
| Link                 | (definition)                           | `edge_collect (γ σ) ⊆ γ (apply_tf … σ)` **transfer soundness** |
| Main soundness lemma |                                        | `post_fixpoint_sound`: `cfg_collect ⊆ γ ∘ env`                 |

So **abstract interpretation is the `rhs` / `γ` / `join` / `apply_tf` layer**.
`make_rhs` / `make_rhs_tree` spell out the equations; `td_analyse` (TD solver)
returns an `env` that satisfies them; `post_fixpoint_sound` shows that solution
is sound w.r.t. `cfg_collect`. IMP enters via `collect` and
`cfg_collect_exit_eq_collect`.

Adding a new abstract domain
----------------------------

To plug a new analysis into the pipeline, a user supplies an abstract value
type and a transfer bundle, then discharges a handful of obligations. The
parametric `pipeline_sound` does the rest. Sign (`src/Domains/Sign_Domain.thy`)
is the worked reference.

```mermaid
flowchart TD
  subgraph U ["User supplies"]
    T["abstract value type 'a"]
    G["gamma :: 'a => int set"]
    TF["transfer bundle:<br/>tf_assign / tf_assume / tf_assume_not"]
    INIT["initial abstract state ac_init"]
  end

  subgraph I ["Instance work (per domain)"]
    LAT["instantiation:<br/>'a :: bounded_semilattice_sup_bot<br/>(gives bot, sup, ord)"]
    SD["interpretation sound_domain gamma<br/>obligations: gamma_bot, gamma_mono"]
    DTS["lemma domain_transfer_sound:<br/>each tf preserves gamma"]
    AC["definition my_analysis_config:<br/>bundles gamma, join, bot, tf, init"]
    INITg["lemma: s ∈ gamma_state (ac_init my_cfg)"]
  end

  subgraph F ["Framework provides (proved once)"]
    PS["pipeline_sound[OF ...]<br/>--&gt; concrete ⊆ gamma . env"]
  end

  T --> LAT --> SD
  G --> SD
  TF --> DTS
  G --> DTS
  T --> AC
  G --> AC
  TF --> AC
  INIT --> AC
  INIT --> INITg
  G --> INITg
  SD --> PS
  DTS --> PS
  AC --> PS
  INITg --> PS

  style U fill:#e3f2fd
  style I fill:#fff3e0
  style F fill:#e8f5e9
```

Concretely, the user writes:

| Step | What                                                                                       | Reference (sign)                                              |
| ---- | ------------------------------------------------------------------------------------------ | ------------------------------------------------------------- |
| 1    | Declare abstract value type and its lattice instance                                       | `Sign_Domain.thy` — `datatype sign`, `instantiation` blocks   |
| 2    | Define `gamma_<dom>` and prove `gamma_bot`, `gamma_mono`                                   | `Sign_Domain.thy:54` (`gamma_sign_mono`)                      |
| 3    | `interpretation <dom>_domain: sound_domain gamma_<dom>` (or `abstract_domain` with widen)  | `Sign_Domain.thy:229`                                         |
| 4    | Define `tf_assign`, `tf_assume`, `tf_assume_not` and prove `domain_transfer_sound`          | `assign_sign_sound`, `assume_sign_sound`                      |
| 5    | Bundle as `analysis_config`                                                                | `Pipeline.thy:87` (`sign_analysis_config`)                    |
| 6    | Show `s \<in> gamma_state (ac_init my_cfg)` for the initial store                          | `Pipeline.thy:103` (`sign_analysis_init_in_gamma_stub`)       |
| 7    | Apply `pipeline_sound[OF ...]`                                                             | `Goblint_Formalization.thy:80` (`goblint_sign_sound`)         |

The pipeline still carries three TD-side assumptions (`comp_fun_idem`,
`solve_dom`, `cfg_in_reach`) the user must currently discharge. These are
open problems P1-P3 in `docs/OPEN_PROBLEMS.md`; bridges B5/B6 would lift
them off the user.

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
  applies `vendor/td-verification.patch` (Isabelle2025 compatibility uses
  `Set.remove_eq` in place of `remove_def`, see the patch for details).

- `make build` (default): runs the Isabelle formalization, depends on `vendor`.
  Equivalent to:

  ```
  isabelle build -d $(AFP) -d vendor/td-verification -D . Goblint_Formalization
  ```

- `make jedit`: launches Isabelle/jEdit with the correct session roots
  pre-loaded.

- `make html`: builds Isabelle browser info (`-o browser_info`) and copies it to
  `docs/html/index.html` for offline browsing (gitignored; same mechanism as the
  [Isabelle library HTML pages](https://stackoverflow.com/questions/17833567/how-to-generate-html-version-of-isabelle-theory)).
  CI deploys `docs/html/` to GitHub Pages on push to `main`. Handwritten layer
  walkthroughs live under `docs/walkthrough/` (repo only, not on the site).

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
├── docs/                 proof overview, phases; walkthroughs + generated HTML
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
| `docs/OPEN_PROBLEMS.md`        | Bridges B1-B8, problem catalogue, handoff notes         |
| `docs/HOL_IMP_COMPARISON.md`   | vs HOL-IMP `Abs_*`: workflow, domain theory tradeoffs   |
| `docs/PROOF_OVERVIEW.md`       | Theorem chain, key types and lemmas                     |
| `docs/PROOF_PHASES.md`         | Proof status, sorry inventory, remaining work           |
| `docs/walkthrough/`            | Per-layer HTML walkthroughs (`index.html` hub; not on GitHub Pages) |
| `docs/html/`                   | Isabelle browser info (`make html`; gitignored; GitHub Pages on `main`) |

Agent / MCP workflow notes: `docs/ISABELLE_AGENT_NOTES.md`. Bootstrap: `./scripts/setup.sh`, `./scripts/start-ir.sh`.

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

| Script                                  | Role                                                                                                     |
| --------------------------------------- | -------------------------------------------------------------------------------------------------------- |
| `./scripts/setup.sh`                    | One-shot bootstrap: submodules, venv, I/Q jEdit plugin (skip with `--no-iq`)                             |
| `./scripts/start-iq.sh`                 | Launch Isabelle/jEdit with I/Q listening on port 8765                                                    |
| `./scripts/start-ir.sh`                 | Headless [Isabelle/R](https://github.com/awslabs/AutoCorrode/tree/main/ir) MCP on port 9148              |
| `./scripts/start-both.sh`               | Start I/R in background + I/Q in foreground; Ctrl+C tears down both                                      |
