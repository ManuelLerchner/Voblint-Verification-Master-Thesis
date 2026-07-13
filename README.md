Voblint
=======

> **Towards a Verified Goblint-style Analysis Pipeline in Isabelle/HOL**
> Master's thesis. Manuel Lerchner, TUM Informatics 2, supervised by Alexandra Graß.

## Abstract

We formalize an end-to-end soundness proof for a Goblint-style abstract
interpreter. An IMP2 program (with procedures, scopes, calls) is compiled to a
control-flow graph; the graph induces a constraint system; the verified
side-effecting top-down solver of
[stilscher/td-verification](https://github.com/stilscher/td-verification)
computes a post-fixpoint; and **any abstract domain** satisfying our locale and
transfer obligations yields a result that soundly over-approximates the
interprocedural collecting semantics **at every program point**. Sign analysis
is the worked instance.

## The soundness statement

The current reusable end-to-end theorem in the repo is the locale bridge:

```isabelle
theorem source_reaches_side_analyse_eff:
  assumes run: "psteps Pi (main, s, []) src'"
      and se:  "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom:
        "\<And>v. cfg_reaches g (cfg_entry g) v \<Longrightarrow>
         side_cfg_solve_dom_eff g etf bot s0 gseed v"
  shows "\<exists>v t stk.
    concrete_program_match Pi ps main src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
```

The concrete theory then instantiates that bridge as:

```isabelle
theorem concrete_source_reaches_side_analyse_eff:
  assumes wf:  "wf_compile_input Pi ps main"
      and run: "psteps Pi (main, s, []) src'"
      and se:  "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff (compile_prog Pi ps main) etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom:
        "\<And>v. cfg_reaches (compile_prog Pi ps main)
               (cfg_entry (compile_prog Pi ps main)) v \<Longrightarrow>
         side_cfg_solve_dom_eff (compile_prog Pi ps main) etf bot s0 gseed v"
  shows "\<exists>v t stk.
    concrete_program_match Pi ps main src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
```

This is the strongest verified statement that connects the IMP2 source layer to
the abstract result. It says:

1. The source execution `psteps Pi (main, s, []) src'` is a real IMP2 run.
2. The compiled CFG is the graph the solver runs on.
3. The analysis result contains the concrete state `t` at the matched CFG point `v`.

The assumptions mean:

**IMP2 source assumptions**

| Assumption | What it says | Why it is needed |
| --- | --- | --- |
| `wf` | The procedure table, entry procedure list, and main command are well-formed source input. | The compiler bridge and the source-to-CFG simulation only make sense for source programs in the expected shape. |
| `run` | The IMP2 source program reaches `src'` from the initial state. | This is the concrete witness that the theorem transports into the analysis result. |
| `init` | The concrete initial source store is covered by the abstract initial state. | The abstract analysis must start from a state that includes the concrete input. |

**CFG / compiler assumptions**

| Assumption | What it says | Why it is needed |
| --- | --- | --- |
| `tfm` | The effectful CFG generator is monotone in the solver sense. | The TD-side solver interface requires this to produce a valid post-solution. |
| `cone` | The transfer obeys the dependency/cone discipline. | This is what lets the pruning and side-effect machinery stay sound. |

**Solver / transfer assumptions**

| Assumption | What it says | Why it is needed |
| --- | --- | --- |
| `se` | The effectful transfer is sound. | The solver soundness theorem needs each abstract transfer step to over-approximate the concrete effect. |
| `dom` | Every CFG point reachable from the entry satisfies the solver domain precondition. | This is the local precondition needed to read the solver result back as an abstract state at each point. |

The theorem is proved through the CFG collecting semantics:

- `source_reaches_cfg_collect` turns the IMP2 run into a matched CFG point and a concrete store in `cfg_collect`.
- `side_analyse_eff_collect_sound_at_pruned` turns that collecting fact into an abstract inclusion at the same CFG point.
- `IMP2_Bridge.thy` provides the source/CFG simulation that connects the two.

The trace semantics still matters, but only as an intermediate layer for the
collecting proof, not as an equality. What the repo proves is the projection
lemma:

$$
\alpha_{\mathrm{last}}\bigl(\mathrm{cfg}_{\mathrm{collect\_trace}}\ g\ S\ v\bigr)
\subseteq
\mathrm{cfg}_{\mathrm{collect}}\ g\ S\ v
$$

That trace layer is needed for the per-global reaching-read theorem
`reaching_global_read_sound`. For the main source-to-analysis theorem above,
`cfg_collect` is where the solver soundness result lands.

The shipped examples already expose concrete IMP2 witnesses for the flagship
showcase and the recursive `rdiv` program, so the source layer is visible in the
example suite as well.

## Pipeline

```
IMP2 (+ Proc + Globals) → CFG (+ IP Collecting) → Equations → Solver (TD side) → Pipeline → Examples
                    Domains ────────────────────────────────┘
```

Four Isabelle sessions, built in order:
`Voblint_IMP2` → `Voblint_CFG` → `Voblint_Analysis` → `Voblint_Formalization`.

## Architecture

Voblint is **one generic soundness core with several specializations**, not a set
of competing analyses. Every soundness endpoint descends from a single theorem —
a TD-side post-fixpoint over CFG collecting semantics over-approximates that
semantics at every program point — and the context-sensitive analyses form *one
layered tower* culminating in the recursive `twfr` witness flagship.

### Core shape

- IMP2 source semantics and the backward bridge live in `Voblint_IMP2`.
- CFG construction and collecting semantics live in `Voblint_CFG`.
- Equation systems, solver wiring, and domain instances live in `Voblint_Analysis`.
- The end-to-end theorems and examples live in `Voblint_Formalization`.

The genericity is carried by a type-class + locale hierarchy:
`abstract_domain` extends `sound_domain`; `sound_transfer` and
`sound_effectful_transfer` carry transfer soundness; the solver side uses the
`*_rhs_generator` and `TD_Side_*` locale stack. Sign and Interval are concrete
interpretations of that stack.

**Canonical end-to-end chain** — each step reuses the soundness of the one below:

`cfg_collect_trace` → `Constraint_System_Sound` → `TD_Side_Eff_Soundness` →
`TD_Side_Eff_Ctx_Sound` → `TD_Side_Eff_Cmp_Sound` → `Clean_RRead_Sound` →
`Seeded_Clean_Ctx_Collect` → `Seeded_Activation_Sound` →
`Activation_Witness_From` → `Example_Rdiv_Twfr_Sound`.

Five theorems close the loop end-to-end: the base flow-sensitive theorem,
context-indexed soundness, keyed/combine soundness, seeded activation soundness,
and the recursive `twfr` witness theorem. The digest spine
`context_collect_sound` runs in parallel.

| Role | Meaning | Representative |
| --- | --- | --- |
| Canonical spine | proved end-to-end soundness | `source_reaches_side_analyse_eff`, `rdiv_witness_G_over_approximated` |
| Required support | inside a flagship's dependency cone | context tower, return rehydration |
| Regression / counterexample | intentional negative or precision fact | `clean_transfer_unsound` |
| Precision comparison | `eval`-only sharper-than witness | bare `Exec_*_Ctx_Run` |
| Design evidence | motivates a design; proves no soundness | `Example_Interval_Recursion_Digest` |

## Semantic foundation

The concrete spec is the interprocedural trace collecting semantics
(`cfg_collect_trace`). It records ordered runs, which is what history-sensitive
globals need. The state-level collecting semantics (`cfg_collect`) is the
projection target, not an equality:
`alpha_last_cfg_collect_trace_le`.

Big-step is only a reference semantics. `IMP2_Bridge.thy` shows every
terminating AFP IMP2 big-step run is reproduced by our small-step
(`pstep`, `IMP2_Proc.thy`). The two views are complementary: the analyzer
certifies every program point, while big-step / VCG pins the exact terminating
result at exit.

## Headline result

`source_reaches_side_analyse_eff`
(`src/Formalization/Pipeline/Compiler_Correctness_Prototype.thy`): for a real
IMP2 run, the compiled CFG, and a sound solver instance, the abstract result
contains the matched concrete state at some CFG point. Sign instantiation:
`demo_source_to_sign_analysis` / `rdiv_source_to_interval_analysis` in the
example suite.

`TD_Side_Eff_Soundness.side_analyse_eff_collect_sound_exit_pruned`
(`src/Analysis/Generic/Solver/Core/TD_Side_Eff_Soundness.thy`) is the solver
endpoint at CFG exit. Sign instance: `side_sign_analysis_sound`
(`src/Analysis/Instances/Sign/Sign_Side_Soundness.thy`).

Globals shared across the program are tracked flow-insensitively through the
solver's side-effect mechanism. In `Trace_Analysis_Sound.thy`:
`reaching_global_read_sound` - any global's value over any reaching trace lies in
`gamma`; `digest_read_sound` - digest-indexed reads are sound;
`flat_env_is_digest_sound` - the flat (flow-insensitive) env is the degenerate
sound digest. `Example_Trace_Digest_Precision.thy` then witnesses
(`digest_beats_flat`) that a digest-indexed read is strictly tighter than the
flat read on a concrete program.

Soundness is *not* validated by a separate code-generator theorem. We **define**
the equation system as the abstract analogue of CFG collecting, then prove every
post-fixpoint over-approximates concrete reachability:

| | Concrete (collecting) | Abstract |
| --- | --- | --- |
| One edge | `edges_collect` on store sets | `apply_tf tf` on `abs_state` |
| One point | join of predecessor edges | constraint `rhs` join |
| Global | `cfg_collect_trace` | `env` with `is_post_fixpoint` |
| Link | (definition) | transfer soundness: `gamma` commutes with each `tf` |

## Adding a domain

Supply an abstract value type, a `gamma`, and a transfer bundle
(`tf_assign` / `tf_assume` / `tf_assume_not`); discharge a handful of
obligations; the parametric pipeline does the rest. Sign
(`src/Analysis/Instances/Sign/Sign_Domain.thy`) is the reference.

| Step | What | Reference (sign) |
| --- | --- | --- |
| 1 | value type + lattice instance (`bot`, `sup`, `ord`) | `datatype sign`, `instantiation` |
| 2 | define `gamma`, prove `gamma_bot` / `gamma_mono` | `gamma_sign_mono` |
| 3 | `interpretation` of the `abstract_domain` locale | `sign_domain` |
| 4 | define transfer fns, prove they preserve `gamma` | `assign_sign_sound`, `assume_sign_sound` |
| 5 | apply the IP pipeline soundness theorem | `side_sign_analysis_sound` |

## Requirements

- [Isabelle](https://isabelle.in.tum.de/) 2025 or newer, with `isabelle` in `$PATH`.
- A local [AFP](https://www.isa-afp.org/) checkout (`thys/`): transitive deps
  `Root_Balanced_Tree`, `Dijkstra_Shortest_Path`.
- GNU `make`, `git`, POSIX tools.

## Build

Set `AFP` to your AFP `thys/` directory (default `~/afp/thys`):

```
make AFP=/path/to/afp/thys build
```

| Target | Role |
| --- | --- |
| `make vendor` | init `vendor/td-verification` submodule + apply Isabelle2025 patch |
| `make build` (default) | build session `Voblint_Formalization` (depends on `vendor`) |
| `make jedit` | launch Isabelle/jEdit with session roots pre-loaded |
| `make html` | browser info → `docs/html/` (CI deploys to GitHub Pages on `main`) |
| `make clean` / `clean-vendor` | remove built heaps / vendored sources |

The checked source tree is sorry-free; `ROOT` files do not enable
`quick_and_dirty`. See `src/README.md` for the per-layer map.

## Layout

```
src/
  IMP2/          syntax, procedures, globals/locals, small-step
  CFG/           CFG, IP compilation, paths; Collecting/ - IP collecting semantics
  Analysis/      Generic/ (Domain/ Equations/ Solver/) Instances/ (Voblint_Analysis session)
  Formalization/ Pipeline/ Examples/ (Voblint_Formalization session)
vendor/
  td-verification/         verified TD solver (submodule, AFP session TD)
  td-verification.patch    local Isabelle2025 compatibility patch
  autocorrode/             I/Q + I/R MCP servers (via ./scripts/setup.sh)
docs/          proof overview, phases, roadmap, walkthroughs, generated HTML
```

The analysis rides on the **side-effecting** solver (`TD.TD_side`) only; the
plain top-down solver was retired. The intra-procedural (classical) spine moved
to the sibling repo `voblint-formalization-classical`.

## Verified dependencies

| Dependency | Source | Role |
| --- | --- | --- |
| `HOL-IMP` | Isabelle distribution | session parent; IMP base |
| `TD` (`TD_side`, `Basics`, …) | vendored `stilscher/td-verification` + patch | verified top-down solver |
| `Dijkstra_Shortest_Path` | AFP | CFG graph type |
| `Root_Balanced_Tree` | AFP | transitive dep of TD |

## Vendoring the TD solver

Upstream: [stilscher/td-verification](https://github.com/stilscher/td-verification).
Vendored as a submodule via the private fork
[`ManuelLerchner/td-verification`](https://github.com/ManuelLerchner/td-verification)
(CI + local access). GitHub Actions cannot clone the fork with the default
`GITHUB_TOKEN`; add a classic PAT with `repo` scope as repository secret
`SUBMODULES_TOKEN`, or make the fork public. A small Isabelle2025 compatibility
change lives in `vendor/td-verification.patch`; `make vendor` applies it
(idempotent).

## Agent-assisted development

Proof development experiments with
[Isabelle/Q](https://github.com/awslabs/AutoCorrode/tree/main/iq) (I/Q), an MCP
server for Isabelle/jEdit that lets coding agents edit theories, query proof
states, run Sledgehammer, and explore tactics. Following the autoformalization
workflow of Kappelmann et al.,
[*Just Type It in Isabelle!*](https://arxiv.org/abs/2604.15713) (arXiv:2604.15713,
2026), §6.1. See `AGENTS.md` and `docs/ISABELLE_AGENT_NOTES.md`.

| Script | Role |
| --- | --- |
| `./scripts/setup.sh` | one-shot bootstrap: submodules, venv, I/Q plugin (`--no-iq` to skip) |
| `./scripts/start-iq.sh` | Isabelle/jEdit + I/Q on port 8765 |
| `./scripts/start-ir.sh` | headless Isabelle/R MCP on port 9148 |
| `./scripts/start-both.sh` | I/R background + I/Q foreground; Ctrl+C tears down both |

`start-ir.sh` registers `vendor/td-verification` as an Isabelle component via
`isabelle components -u`. This persistent, idempotent registration lets the
I/R `ML_process` resolve the parent session `TD`; the I/R launcher accepts only
one explicit session directory. Remove the registration, if needed, with:

```bash
isabelle components -x "$(pwd)/vendor/td-verification"
```
