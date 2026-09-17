# Thesis blueprint

> **Frozen 2026-09-17.** Planning is complete; drafting has begun with
> Chapter 4. Do not add further sections. Amend only when drafting reveals a
> concrete contradiction with the theories, and record the contradiction rather
> than expanding the plan around it.

A structure proposal grounded in the current formalization, not in the
knowledge base and not in the earlier outlines. Every claim below was checked
against `src/` on 2026-09-17. Where the knowledge base disagrees, the
repository wins and the discrepancy is recorded in §2.6.

Scope of this document: what the thesis should contain and in what order. No
thesis prose is written here.

---

## 1. Executive thesis story

A test runs a program on some inputs and watches what happens. A static analyzer
computes with descriptions of values instead — "an integer between 0 and 5" —
each kept large enough to cover every value a real run could produce, so that a
description satisfying a check settles it for every run at once. That is the
trade the field is built on: coverage of all executions, bought with precision.

It has a catch, and the catch is the thesis. An analyzer is itself a large
program, and a bug in a static analyzer can invalidate the guarantees it reports
about the programs it analyzes: it answers that a check holds where real runs
violate it, and nothing downstream looks again. Static analyzers are trusted to
show that programs do not divide by zero, do not race, do not overflow, and
nothing about the analyzer itself is proved. In the Goblint ecosystem one piece now is: the top-down
solver, verified in Isabelle/HOL by Stade, Tilscher and Seidl and extended to
side-effecting constraint systems by Tilscher, Graß and Seidl. A verified
solver computes a correct post-solution of the equation system it is handed.
It says nothing about whether that equation system describes the program.

Everything between the source program and the solver's input is where the
semantic content of a static analyzer lives — the control-flow graph, the
transfer functions, the interprocedural call protocol, the choice of calling
context, the split between flow-sensitive local facts and flow-insensitive
shared facts. Everything between the solver's output and the report is where
its usefulness lives — the result table, the check verdicts, the dead-code
markers. Voblint closes that ring. It is a machine-checked Isabelle/HOL
development that compiles a small imperative language to a procedure-aware
CFG, generates a side-effecting equation system in the shape Goblint's `Spec`
interface prescribes, runs the vendored verified solver on it, publishes a
result table, and proves that every execution of the source program is
over-approximated by that table and that every definite verdict in it holds.

The statement is about the analyzer that ships. `run_voblint` is one Isabelle
constant; `export_code` emits it as OCaml; the command-line tool and the
browser playground call the emitted function; and
`run_voblint_certified_source_sound` is a theorem about that same constant. No
idealized model sits between the theorem and the program people run.

Three design decisions give the thesis its technical spine, and each is worth
a chapter.

**The concrete semantics is activation-local.** A run is not modelled as a set
of reachable states but as a family of *activation-local traces*: one trace is
one procedure activation together with its structural caller chain, and a
return composes a completed callee back into the caller it was spawned from.
This adapts the thread-modular local-trace semantics of Schwarz and Erhard
from threads to procedure activations. The payoff is that calling context
becomes a *projection of the concrete object* rather than an extra parameter
whose soundness must be postulated: `trace_context` reads a context off a
trace, and `activation_collect` is the collecting semantics indexed by it.

**Soundness is one contract, stated once, over an arbitrary graph.** An
analysis claims "at node `v`, in context `c`, only these stores occur".
`ltr_coverage` says what such a claim must satisfy to be believed: five local
obligations — `INIT`, `INTRA`, `CALL`, `RETURN`, `TOTAL` — and
`activation_collect_sound` proves that satisfying them bounds every valid
trace. No domain, no solver, no equation system appears in that theorem. The
whole rest of the development exists to construct a claim that discharges
those five obligations, and to compute it.

**Domain, context policy and solver discipline are orthogonal.** A domain
supplies a `dg_spec` — the Isabelle counterpart of Goblint's `Spec`: one
manager-native transfer per edge action, plus `enter`, `combine_env` and
`combine_assign` — and proves one soundness contract about it. A context
policy supplies a routing function and its relation. A solver discipline is an
argument. The generic assembly (`routed_dg_analysis`, `unit_dg_analysis`) is
proved once, and every combination inherits it: five domains, four global
update rules, three context policies, call strings at every bound. The
registrations that instantiate this are generated from a manifest, not written
by hand.

What the thesis must be equally clear about is the boundary. The result is
partial correctness: solver termination is a per-program premise, discharged
by evaluation for concrete programs and proved for none in general. The source
language is scalar — no arrays, pointers, heap, or C. The lexer, the parser,
Isabelle's code generator, the OCaml toolchain and every renderer sit outside
the proof. Nothing is claimed about precision or completeness, and `REFUTED`
is not a verified counterexample. The trust boundary is not an appendix
concession; it is a chapter, because knowing exactly what a verified analyzer
does *not* establish is most of what makes the verified part meaningful.

The thesis therefore has a double audience and must serve both. To a static
analysis reader it says: here is Goblint's interprocedural architecture, given
a concrete semantics and a soundness proof, with every deliberate
simplification recorded. To a verification reader it says: here is how a
non-trivial analyzer decomposes so that its proof stays modular — where
locales carry the reusable obligations, where type classes carry the domain
algebra, where a quotient type separates what the solver computes on from what
soundness is stated over, and where an external verified component can be
consumed through a single certificate.

---

## 2. Current formalization architecture

### 2.1 Numbers

| Layer | Directory | Lines | Theories |
| --- | --- | ---: | ---: |
| Source language | `src/Program_Model/VIMP` | 1 507 | 8 |
| CFG + collecting semantics | `src/Program_Model/CFG` | 2 023 | 8 |
| Compiler + simulation | `src/Program_Model/Compile` | 5 813 | 10 |
| Abstract domains (generic) | `src/Abstract_Interpreter/Domain` | 2 733 | 8 |
| Solver interface | `src/Abstract_Interpreter/Solver` | 1 259 | 7 |
| D/G framework | `src/Abstract_Interpreter/Framework` | 8 471 | 26 |
| Executable carrier | `src/Abstract_Interpreter/Exec` | 2 413 | 11 |
| Shared analysis layer | `src/Analyses/Shared` | 4 841 | 15 |
| Sign | `src/Analyses/Sign` | 1 964 | 10 |
| Interval | `src/Analyses/Interval` | 3 107 | 14 |
| Parity | `src/Analyses/Parity` | 1 187 | 8 |
| Congruence | `src/Analyses/Congruence` | 3 405 | 12 |
| Int (reduced product) | `src/Analyses/Int` | 5 324 | 12 |
| Relational witness | `src/Analyses/Relational` | 576 | 1 |
| CLI + codegen | `src/Executable_Surface` | 2 250 | 8 |
| Examples and regressions | `src/Examples` | 14 382 | 65 |
| **Total `src/`** | | **61 255** | **223** |
| Vendored TD solver | `vendor/td-verification` | 31 322 | 26 |
| Handwritten OCaml | `cli/` | 3 675 | — |
| Generated OCaml | `codegen/generated/ml` | 9 400 | — |

No `sorry` and no `oops` in `src/`; none in the vendored solver theories
either. 283 `.vimp` regression fixtures across 25 groups, partitioned into
`precision/` (197), `known-imprecision/` (48) and `soundness/` (9).

### 2.2 Session graph

Twenty-eight sessions, one per directory carrying a `ROOT`.

```text
Voblint_VIMP ─┬─> Voblint_CFG ─┬─> Voblint_Compile ──────────┐
              │                │                             v
              │                └─> Voblint_Framework ─> Voblint_Exec ─> Voblint_Routing
              └─> Voblint_Domain ──^                                          │
TD ──> Voblint_Solver ──────────────^                                         v
                                                                     Voblint_Result
                                                                              │
                                                                              v
                                                                  Voblint_Nonrelational
                                                                              │
             ┌────────────────┬───────────────┬──────────────┬────────────────┘
             v                v               v              v
      Analysis_Sign   Analysis_Interval  Analysis_Parity  Analysis_Congruence
             └────────────────┴───────────────┴──────────────┴──> Analysis_Int
                                                                        │
Voblint_Exec ──> Voblint_Analysis_Relational                            v
                                                                  Voblint_CLI ──> Voblint_Codegen
                                                                        │
                                                                        v
                                                              Voblint_Examples_*
```

Two session boundaries are load-bearing arguments, not packaging:

- `Voblint_CFG` never mentions the compiler. Every D/G soundness endpoint is
  therefore stated for an *arbitrary* CFG, and the session boundary is what
  keeps that true.
- `Voblint_Analysis_Relational` is parented on `Voblint_Exec`, *below* the
  `Routing → Result → Nonrelational` chain. The pointwise reuse locales are
  unreachable from it. That makes `Rel_Order_Domain`'s claim — a
  non-`abs_state` carrier discharges the framework contract unchanged —
  structural rather than a matter of which imports happen to be written.

### 2.3 What each layer owns

**`Voblint_VIMP`.** `com` with calls, explicit returns, and the runtime-only
`Restore`/`Unwind` commands; small-step `pstep` over `(command, store, frame
stack)`; `wf_source_program` as the admissibility contract; the locals/globals
classifier `gs :: vname => bool` with `enter_state` and `combine_env`;
`special_call` as a closed enumeration standing in for Goblint's library-function
table; and a `parse_translation`-based concrete syntax generated from
`manifests/vimp-grammar.yaml`.

**`Voblint_CFG`.** `cfg` as two disjoint relations — `intra` labelled by an
`edge_action`, and a four-place `calls` relation carrying call action, callee
entry and continuation. Nodes are `Statement n`, `FunctionEntry p`,
`FunctionResult p`. `cstep` executes an arbitrary graph. `CFG_Transfer` gives
the three concrete transfers: `edge_collect`, `call_enter`, `combine_collect`.
`Collecting/` holds the semantic heart: `ltr`, `valid_ltr`, `ltr_collect`,
`trace_context`, `call_context_rel`, `activation_collect`, and the
`ltr_coverage` locale with `activation_collect_sound` and
`ltr_collect_eq_Union_activation_collect`.

**`Voblint_Compile`.** `compile_prog` as a continuation-passing compiler;
`wf_compile_input` and its executable form; graph well-formedness
(`compile_prog_wf`, `compile_prog_finite`, `compile_prog_calls_source_unique`);
`control_at` (where a partly executed command sits in the graph); `csim` and
the forward simulation `csim_step`/`csim_star`; procedure ownership; live
nodes; and the one theory that needs both halves, `Source_To_Trace`, which
turns a source run into a `valid_ltr` witness.

**`Voblint_Domain`.** The `sound_domain` type class (carrier, order,
concretization, no `alpha`); the reachability lift `'a lifted` mirroring
Goblint's `Lattice.LiftConf`; pointwise `'a abs_state = vname => 'a` with
`gamma_state` and `is_empty_state`; the `backward_domain` locale for guard
narrowing (`afilter`, `bfilter`, `branch_lifted`); and the numeric-query
interface (`less`, `eq`) the check layer consumes.

**`Voblint_Solver`.** The vendored solver's strategy-tree language
(`Answer | QueryL | QueryG | Side`) with a typed continuation-passing frontend
(`strategy_program`), the right-hand-side fold, per-key side buffering, the
`part_post_solution` vocabulary, the bridge `part_post_solution_of_solve_c`,
and `globals_rule` as a value so one interpretation covers all four update
rules.

**`Voblint_Framework`.** The D/G analysis framework, domain-free and
compiler-free. `dg_state` (opaque `D`/`G`), the manager (`man_local`,
`man_global`, `man_sideg`), `dg_spec` with one field per Goblint `Spec` method,
`sound_dg_spec_core` as the soundness contract, the keyed equation generator
`routed_node_rhs` (and its buffered production variant), `Activation_Backbone`
(the `ltr_coverage` obligations in global shape), `DG_Ctx_Activation` (EDGE and
COMB discharged from a post-solution), `Routed_Context` (CALL and COMB
discharged once for any routing policy), the check layers, and the result table.

**`Voblint_Exec`.** The gap between what soundness talks about and what the
solver computes on. `resolved_st_q` is a quotient type over
(local default, global default, override list); `fun_of_resolved_st_q_for gs`
reads it back as an `abs_state`; every executable operation carries a commute
theorem against its abstract counterpart; `Exec_St_Reachability` gives a finite
dead-state test proved equivalent to the infinite one.

**`src/Analyses/Shared/`.** Three chained sessions. `Voblint_Routing` builds
the compiled equation system and the two concrete context policies
(`Call_String_Routed_Context`, `Entry_State_Routed_Context`) plus the
finite-context-space arguments. `Voblint_Result` is the publication surface:
`Analysis_Surface`, `Routed_DG_Analysis` (construction half
`routed_dg_pipeline`, correctness half `routed_dg_analysis`),
`Routed_Live_Keys` (coverage derived from termination), `Unit_DG_Analysis`
(the context-insensitive endpoints), `Source_Activation_Sound`.
`Voblint_Nonrelational` is what a pointwise domain reuses — the shared
expression-soundness induction, special-call dispatch, the generic transfer
locale `nonrelational_transfer`, the primitive bundle `numeric_ops`, and the
executable backward filter.

**`src/Analyses/<Domain>/`.** Each domain supplies a lattice, arithmetic,
optionally backward inversion, special calls, numeric queries, the transfer
registration (one `interpretation` of `nonrelational_transfer`), an executable
mirror with its commute lemmas, the initial-state fact, a check classifier, and
a *generated* `<Domain>_Analyses.thy` registering it at all three context
policies with the update rule left as a parameter.

**`src/Executable_Surface/`.** `Analysis_Config` (three closed datatypes),
`Analysis_Run` (`run_voblint`), the soundness theories, and the single
`export_code` declaration.

### 2.4 The configuration space

`run_voblint :: analysis_domain => globals_rule => context_mode => imp_prog =>
String.literal analysis_answer`.

- `analysis_domain` — `Sign_Analysis`, `Interval_Analysis`, `Int_Analysis`,
  `Parity_Analysis`, `Congruence_Analysis`.
- `globals_rule` — always-join, per-origin, Apinis warrowing,
  warrowing-per-origin. All four are vendored rules under one
  `TD_side_rule_Interp` interpretation.
- `context_mode` — `Ctx_None`, `Ctx_EntryState`, `Ctx_CallString k` for any `k`
  (including `0`).

Every combination is answered, and every combination carries the source-level
theorem. A malformed program answers `Malformed_Program` before any
configuration is consulted.

### 2.5 Goblint correspondence, as the repository records it

`docs/GOBLINT_ALIGNMENT_REGISTER.md` is a source-checked register of every
deliberate difference. The rows the thesis must carry are:

| Aligned | Deliberately different | Absent |
| --- | --- | --- |
| `Spec` method-per-construct shape (`dgs_*`) | source language (scalar VIMP vs C/CIL) | `sync` |
| manager `local`/`global`/`sideg` | callee-entry unknown is a *global* proxy (`Activation_Seed`), because the vendored solver has no `sidel` | `startstate`/`exitstate`/`morphstate` |
| context selected from the post-`enter` callee state | context selector is a *relation* on the concrete side (several contexts per call) | query channel for transfers |
| local unknown `(node, context)` | `__voblint_check` is a first-class edge kind, not `special` | multi-analysis manager |
| `combine_env` then `combine_assign` as two fields | mathematical `int`, no `ikind`/wraparound | `Group`-shaped findings (so no data race is expressible) |
| `enter` returns a list of alternatives | `int_dom` components are mandatory, not optional | global read digest filter (single-threaded scope) |

Two claims the register makes that the thesis must repeat verbatim: the
`Activation_Seed` encoding reproduces the same collecting dependency but **no
operational equivalence to Goblint's fixpoint is claimed**, and widening lands
one hop later than in Goblint by construction. And: the shipped whole-state
specifications leave `dgs_combine_env` the identity, so the `combine_env` /
`combine_assign` split is nominal at the instances even though the interface
carries it.

### 2.6 Knowledge-base audit

`git/goblint-formalization-kb` last moved 2026-08-11; the formalization has
moved substantially since. Classification of the material that matters:

| KB material | Verdict | Note |
| --- | --- | --- |
| `wiki/research/thesis-structure.md` (485 lines) | **Obsolete in specifics, useful in shape** | Every headline theorem it names is gone: `mixed_flow_analysis_sound`, `trace_analysis_sound`, `cfg_collect_trace`, `sound_effectful_transfer`, `digest_beats_flat`, `reaching_global_read_sound`, `obs_digest`. Its math/engineering interleave and its per-section "Goal / Relevance / Literature" template are worth keeping. |
| `docs/THESIS_SCOPE_MEMO.md` | **Partly outdated; its refresh section is accurate** | The 2026-08-04 refresh correctly flags that the June recommendation rests on deleted evidence. Its "Scope A vs B" framing is superseded: the relational carrier and the reduced product both landed. |
| `wiki/research/thesis-contribution-reassessment.md` | **Still live as a question, stale in its answer sketch** | Its candidate pipeline narrative cites `sound_dg_hooks` and the placement analyses; both were deleted 2026-09-02. Its four-question framework is unanswered and should be answered by §5 of this document plus a supervisor conversation. |
| `wiki/research/novelty-not-covered-positioning.md` | **Directionally right, evidentially stale** | The "decoupled pipeline" framing survives. Its concrete lemma names do not. |
| `wiki/concepts/*` (170 notes) | **Useful background, not thesis material** | Literature notes and terminology. Good raw material for Ch. 2 and Ch. 13; must not be cited as a source. |
| `wiki/summaries/*` (170 notes) | **Useful reading aids** | Paper summaries. Treat as notes, verify against primary sources before citing. |
| `wiki/research/architecture-decisions.md` (AD ledger) | **Historical record** | AD-41…AD-50. Valuable for a "design history" appendix if one is wanted; every AD after AD-44 must be re-checked against the tree. |
| `wiki/research/sign-callstring-precision-witness.md` | **Accurate** | The k=1 vs k=2 witness still exists as `sign_k2_strictly_more_precise_than_k1_at_g`. |

Specific deletions the KB still presents as delivered: the digest/trace-read
spine (AD-44, 2026-07-18), the AFP IMP2 bridge and `backward_sim`
(2026-07-20), `Retain_Analysis`, `sound_dg_hooks` and the placement analyses
(2026-09-02). None of them exists in `src/`. Any thesis sentence inherited from
the KB must be re-derived from a theory.

One structural lesson from the KB worth keeping: it repeatedly recorded a
*capability* as a contribution and then deleted the capability. The thesis
should claim what the endpoint theorems establish, not what the framework can
in principle express.

---

## 3. Soundness / proof spine

Read bottom-up: each layer consumes the one below and adds exactly one thing.

```text
L0  SOURCE EXECUTION
    pstep / psteps / pcompletes                    VIMP_Proc
    wf_source_program, cinit_stores                VIMP_Proc, VIMP_Globals
             │  wf_compile_inputD
             v
L1  COMPILATION AND SIMULATION
    compile_prog                                   VIMP_Proc_to_CFG
    compile_prog_wf / _finite / _calls_source_unique   Compile_Wellformed
    control_at, csim                               Residual_Location, Simulation_Relation
    csim_step, csim_star                           Simulation_Preservation
             │  source_run_has_ltr
             v
L2  CONCRETE INTERPROCEDURAL SEMANTICS
    ltr, valid_ltr (Root / intra / call / ret)     LTR_Def
    ltr_collect, ltr_collect_I / _E                LTR_Collect
    trace_context, call_context_rel,
    call_context_total_on, activation_collect      LTR_Activation_Context
             │
             v
L3  THE SOUNDNESS CONTRACT  ← the pivot of the thesis
    locale ltr_coverage: INIT, INTRA, CALL, RETURN, TOTAL
    valid_ltr_covered_at                           LTR_Abstract
    ltr_collect_semantic_postfix                   LTR_Abstract
    ltr_collect_eq_Union_activation_collect        LTR_Abstract
    activation_collect_sound  (global shape)       Activation_Backbone
             │  "construct a cover that discharges the five obligations"
             v
L4  WHAT AN ANALYSIS SUPPLIES
    dg_spec (Spec analogue), man_local/global/sideg    DG_Spec, DG_Manager
    sound_dg_spec_core: gammaDG_mono, step_sound,
                        combine_sound                  DG_Spec_Sound
    sound_transfer_for → local_state_dg_spec_for_core_sound   DG_Local_State_Spec
    nonrelational_transfer (one interpretation per domain)    Nonrelational_Transfer
             │
             v
L5  EQUATIONS
    routed_node_rhs / routed_node_rhs_buffered     DG_Keyed_Generator
    routed_call_tree, routed_entry_seed_tree       Routed_Call_Trees
    compiled_routed_eqs_for                        Compiled_Routed_Equations
             │
             v
L6  FROM A POST-SOLUTION TO A COVER
    dg_ctx_activation_base  ⊢ EDGE, COMB           DG_Ctx_Activation
    routed_context_base_hetero ⊢ CALL, COMB,
      activation_collect_dg_sound                  Routed_Context
    route_unit, activation_collect_unit_eq_ltr_collect   Routed_Context_Unit
    cs_route / cs_context  (call strings)          Call_String_Context,
                                                   Call_String_Routed_Context
    formals_route_lifted_gen  (entry state)        Entry_State_Routed_Context
             │
             v
L7  SOLVER
    strategy_tree, part_post_solution              vendor Basics_side
    TD_side_upd_rule: solve / solve_c,
      term_equivalence, solve_code_equation [code],
      partial_post_solution                        vendor TD_side_upd_rule
    part_post_solution_of_solve_c                  TD_Solver_Bridge
    globals_rule (four vendored update rules)      Globals_Rule
             │
             v
L8  EXECUTABLE ↔ MATHEMATICAL
    resolved_st_q (quotient), fun_of_resolved_st_q_for   Exec_St_Base, Exec_St_Transfer
    generic_tf_st_for_commute, branch_st_commute        Numeric_Ops, Exec_Backward
    routed_dg_domain_exec, Routed_Exec_Refinement       Exec/Refinement/
    readback_result_value, canonicalize_lift            Exec_Result_Readback
             │
             v
L9  PUBLICATION
    analysis_result, lookup_context, wf_analysis_result  Analysis_Result
    dg_analysis_adapter                                  DG_Analysis_Adapter
    routed_dg_pipeline / routed_dg_analysis              Routed_DG_Analysis
    live_keys, live_keys_cover                           Routed_Live_Keys
    unit_dg_analysis: source_sound, completed_run_sound,
                      result_node_sound                  Unit_DG_Analysis
    source_activation_sound,
    source_sound_from_collecting_cap                     Source_Activation_Sound
             │
             v
L10 CHECKS
    check_result (flat 3-valued), contextual_verdict = check_result lifted
    classify_checks_verdicts, checks_proven         Check_Result,
                                                    Contextual_Check_Report, Checks
             │
             v
L11 THE ANALYZER
    run_voblint                                     Analysis_Run
    sound_table, sound_table_of_activation,
      sound_table.source_sound                      Analysis_Run_Sound,
                                                    Analysis_Run_Ctx_Sound
    run_voblint_certified_source_sound   ← headline Analysis_Certified
    run_voblint_check_sound
    run_voblint_dead_check_unreached
    run_voblint_check_sites
    run_voblint_arithmetic_safe
             │
             v
L12 NON-VACUITY AND EXPORT
    certificate_demo_full_certificate               Example_End_To_End_Certificate
    export_code ... module_name Generated           Voblint_Codegen
```

### 3.1 The headline, in full

```isabelle
theorem run_voblint_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 ∈ cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
  shows "∃v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               ∧ s ∈ ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               ∧ analysis_result_covers D rule ctx p v s
               ∧ checks_sound_at res v s"
```

Four things about this statement deserve a paragraph each in the thesis.

*The node is existential.* A source configuration does not determine a CFG
node — `x := 1` in `main` and in an unused procedure match structurally. `csim`
records the structural match; `ltr_collect` picks the reachable witness.

*The context is existential too.* Under entry-state routing one store may be
admitted at several contexts; under call strings at exactly one. A statement
over *every* solved context would be false.

*Coverage is not a premise.* `live_keys_cover` derives it from termination
plus well-formedness, by reading what the generated equations actually query.

*Well-formedness is not a premise either.* A malformed program answers
`Malformed_Program`, and the `ans` assumption supplies the contract.

### 3.2 What is trusted

| Proved | Trusted |
| --- | --- |
| VIMP execution from a constructed `imp_prog` | lexer and parser (`cli/frontend/`, generated from `manifests/vimp-grammar.yaml`) |
| compilation and forward simulation | Isabelle's code generator |
| equation generation and the computed post-solution | the OCaml compiler, runtime, Zarith, `wasm_of_ocaml` |
| the vendored solver's `part_post_solution` | solver termination for an arbitrary program |
| the result table, check verdicts, arithmetic diagnostics | source positions, rendered graphs, state strings, the playground |
| | precision and completeness |

The one seam between Voblint and the vendored solver is
`part_post_solution` — a two-part certificate (the local answer bounds the
right-hand side; every side contribution bounds its target key; dependencies
stay inside the covered set). `activation_collect_dg_sound` consumes it and
never asks how it was produced, which is what makes the collecting-soundness
argument solver-independent.

---

## 4. Literature map

Organized by what each source *supplies* to the thesis, not by topic.

### 4.1 Abstract interpretation: the framework

| Source | Supplies | Relevance | Thesis home |
| --- | --- | --- | --- |
| Cousot & Cousot, POPL 1977 | the framework itself; lattices, Galois connections, fixpoint approximation | the vocabulary every chapter uses | Ch. 2 |
| Cousot & Cousot, POPL 1979, *Systematic design* | systematic construction of abstract domains; products | justifies the `sound_domain`/`gamma`-only presentation; background for `int_dom` | Ch. 2, Ch. 10 |
| Cousot, TCS 2002, *Constructive design of a hierarchy of semantics* | trace semantics as the base of the hierarchy; reachable states as its abstraction | the licence for building on traces rather than reachable states | Ch. 4 |
| Cousot & Cousot, PLILP 1992, *Comparing the Galois connection and widening/narrowing approaches* | widening/narrowing without a best abstraction | why `alpha` is never mechanized here | Ch. 2, Ch. 5 |
| Miné, FnTPL 2017 tutorial | a modern, readable presentation of numeric domains and widening | the reference a reader without an AI background should be pointed at | Ch. 2 |
| Rival & Yi, *Introduction to Static Analysis* (MIT 2020) | textbook treatment; domain design recipe | secondary background reference | Ch. 2 |

### 4.2 Constraint-based analysis and solvers

| Source | Supplies | Relevance | Thesis home |
| --- | --- | --- | --- |
| Apinis, Seidl, Vojdani, APLAS 2012, *Side-effecting constraint systems* | the side-effecting constraint system; write-as-side-effect, read-as-join | the equation-system shape Voblint generates | Ch. 2, Ch. 7 |
| Apinis, PhD 2014 | mixed flow-sensitivity; the `(L, G, D, C)` tuple | the locals/globals split the D/G framework realizes | Ch. 2, Ch. 6 |
| Seidl & Vogler, MSCS 2021, *Three improvements to the top-down solver* | TD3, demand-driven solving, dependency tracking | what the vendored solver implements | Ch. 8 |
| Stade, Tilscher, Seidl, CAV 2024, *The top-down solver verified* | machine-checked partial correctness of TD; AFP `Top_Down_Solver` | the prior verified component; marks where reuse begins | Ch. 8, Ch. 13 |
| Tilscher, Graß, Seidl, NFM 2026, *Verifying a solver for mixed flow-sensitive analyses* | the verified side-effecting solver `TD_side`, strategy trees, update rules, `part_post_solution` | **the vendored artifact**; the single interface Voblint consumes | Ch. 8, Ch. 13 |
| Graß, MSc 2024, *Towards the verification of top-down solvers* | warrowing; the widening/narrowing-in-one-operator discipline | why `widening`/`narrowing` appear as type classes with only the bracket laws | Ch. 5, Ch. 8 |
| Hofmann, Karbyshev, Seidl, 2010, *Verifying a local generic solver in Coq* | the earlier mechanized local solver | the first point on the verified-solver line | Ch. 13 |
| La Spina et al., 2025, WTO-based dataflow solvers in Coq | an alternative verified fixpoint engine | comparison point for "verified solver, unverified pipeline" | Ch. 13 |

### 4.2a Syntax-directed versus constraint-based analysis

An axis the rest of this map leaves implicit, and the one that separates Voblint
from most mechanized abstract interpretation. A *syntax-directed* analyzer
recurses over the statement tree, interpreting each construct and iterating
loops in place; a *constraint-based* one turns the program into unknowns and
equations and hands them to a solver that knows nothing about programs.

| | syntax-directed | constraint-based |
| --- | --- | --- |
| shape | `asem(stmt)` recurses; a loop is a local post-fixpoint | one unknown per (point, context); one equation per unknown |
| who iterates | the interpreter, structurally | a separate solver, by demand and dependency |
| interprocedural calls | inlining, summaries, or a second mechanism | a call is just more equations |
| flow-insensitive facts | need a side channel | side effects into global unknowns |
| verification consequence | soundness proved by induction on syntax | soundness proved once against a *solver-independent* certificate |
| examples | Nipkow's `Abs_Int`; Franceschino et al.; Verasco's iterator | Goblint; Voblint; the TD line |

The consequence is the one Chapter 2 should state and Chapter 13 should
develop: a syntax-directed proof is an induction whose cases *are* the language
constructs, which makes it compact and ties it to the language; a
constraint-based proof has to say separately what the equations mean, which
costs a whole layer (`ltr_coverage`, Ch. 4) and buys a solver that can be
replaced without touching the semantics (C4). Neither is better; they fail
differently. Voblint is constraint-based because Goblint is.

**Where this belongs.** Ch. 2.4 states the distinction and says which side this
thesis is on. Ch. 13.1 develops it as the main comparison: Verasco, Nipkow's
`Abs_Int_ITP2012` and Franceschino et al. are all syntax-directed and all
verified; the contrast is architectural, not a matter of rigour. A short
comparison table there — verification environment, research emphasis, language,
procedures, context sensitivity, how the fixpoint is computed, domains,
termination, artifact, proof style — carries it better than prose.

**One warning for Ch. 12.** Franceschino et al. report 487 lines of code to 39
lines of manual proof and make proof-effort reduction an evaluation criterion,
while cautioning that such comparisons are limited because the languages and
scopes differ. §2.1's effort table must be read the same way: report proof
effort by layer, do not turn a proof-to-code ratio into a quality metric, and do
not compare across projects without stating the scope difference. A
constraint-based development with an interprocedural contract layer will lose
that ratio to a syntax-directed interval analyzer, and losing it means nothing.

### 4.3 Interprocedural and context-sensitive analysis

| Source | Supplies | Relevance | Thesis home |
| --- | --- | --- | --- |
| Sharir & Pnueli 1981 | call strings and the functional approach | names the two classical context abstractions; `Ctx_CallString k` is the bounded call-string one | Ch. 7 |
| Knoop & Steffen 1992 | interprocedural coincidence; the call/return matching discipline | background for why `calls` carries its continuation | Ch. 3, Ch. 7 |
| Sotin & Jeannet, ESOP 2011 | precise interprocedural analysis with stack-allocated data | closest classical relative of the activation-local view | Ch. 4, Ch. 13 |
| Erhard, Schinabeck, Schwarz, Seidl, *Context gas and friends* | on-the-fly context bounding | the named reference for the open context-bounding problem | Ch. 14 |
| Rival & Mauborgne, TOPLAS 2007, *Trace partitioning* | partitioning a semantics by control history | the sequential precedent for context-indexed collecting; must be compared to `trace_context` when claiming novelty | Ch. 4, Ch. 13 |

### 4.4 Goblint and local traces

| Source | Supplies | Relevance | Thesis home |
| --- | --- | --- | --- |
| Goblint `analyzer` source (`analyses.ml`, `constraints.ml`) | the `Spec` interface; `FromSpec`'s call path | the interface `dg_spec` models; **cite the pinned commit** as `docs/GOBLINT_ALIGNMENT_REGISTER.md` does | Ch. 6, Ch. 13 |
| Vojdani, PhD 2010; Vojdani et al., FM 2016 | Goblint's architecture and race analysis | the analyzer the thesis is modelled on | Ch. 1, Ch. 13 |
| Schwarz et al., SAS 2021, *Improving thread-modular abstract interpretation* | local traces; the thread-modular local perspective | the semantics Voblint adapts | Ch. 4 |
| Schwarz et al., ESOP 2023, *Clustered relational thread-modular AI with local traces* | relational local-trace analyses | positions the relational stretch goal | Ch. 13 |
| Schwarz & Erhard, VMCAI 2026 (arXiv:2511.11055), *Data race detection by digest-driven AI* | the current formulation of local-trace semantics and digests | **the direct source of the `ltr` design**; `LTR_Def`'s header cites it | Ch. 4, Ch. 13 |
| Seidl et al., FM 2026, *Mixed flow-sensitive static analysis: engineering modularity* | the engineering account of Goblint's modularity | the architecture claim's upstream statement; per-origin widening examples in `tests/regression/19-paper-examples/` | Ch. 6, Ch. 12 |

### 4.5 Verified analyzers and mechanized abstract interpretation

| Source | Supplies | Relevance | Thesis home |
| --- | --- | --- | --- |
| Jourdan, Laporte, Blazy, Leroy, Pichardie, POPL 2015, *A formally-verified C static analyzer* (Verasco) | the reference point: a full verified analyzer in Coq, extracted, over CompCert C | **the closest comparable artifact**; the contrast is structural iterator + monolithic proof vs constraint system + borrowed solver | Ch. 1, Ch. 13 |
| Jourdan, PhD 2016 | Verasco in depth; domain combination and communication | detailed comparison for the reduced product and for interprocedural handling | Ch. 10, Ch. 13 |
| Blazy, Laporte, Maroneze, Pichardie, NFM 2013, *Formal verification of a C value analysis* | the earlier value analysis | precursor to Verasco | Ch. 13 |
| Leroy, CACM 2009 (CompCert) | the verified-compiler methodology; forward simulation | the proof technique `csim_step`/`csim_star` instantiates | Ch. 3, Ch. 13 |
| Cachera & Pichardie, ITP 2010, *A certified denotational abstract interpreter* | certified AI in Coq, extraction | methodological comparison | Ch. 13 |
| Nipkow, ITP 2012, *Abstract interpretation of annotated commands*; AFP `Abs_Int_ITP2012` | the Isabelle reference formalization; `Abs_State`, widening, `Abs_Int1` | **the Isabelle baseline**; `Exec_St_Base` explicitly argues against its single-default `Abs_State` | Ch. 2, Ch. 5, Ch. 13 |
| Nipkow & Klein, *Concrete Semantics* (2014) | IMP, small-step semantics, Ch. 13 abstract interpretation | the background a reader is assumed to have or can get | Ch. 2, Ch. 3 |
| Michelland et al., 2024, monadic abstract interpreters in Coq | a monadic structuring of AI proofs | alternative proof architecture; compare to the locale layering | Ch. 13 |
| Keidel & Erdweg, 2018/2019, *Sound and reusable components for abstract interpretation* | compositional soundness by decomposition | the methodological justification for per-stage soundness instead of one Galois connection | Ch. 6, Ch. 13 |
| Franceschino, Pichardie, Talpin, SAS 2021, *Verified functional programming of an abstract interpreter* | a verified analyzer in F\* with refinement types and SMT automation; concretization-based `adom` interface (γ, lattice ops, widening, termination); syntax-directed `asemstmt` over a small IMP; **a hosted browser version**; 487 lines of code to 39 lines of manual proof | **three roles.** The closest methodological *contrast*: same problem, very different verification architecture (§4.7 below). The γ-only precedent for Ch. 2.2. And the counterexample that stops any "first verified analyzer in a browser" claim (C11) | Ch. 2.2, Ch. 11.5, **Ch. 13.1** |
| Lammich & Wimmer, AFP `IMP2` | a verified IMP with procedures and a VCG | **not used**: the bridge to it was removed. Cite only if the thesis discusses the choice of reference semantics | Ch. 3 (design decision), Ch. 14 |

### 4.6 Isabelle mechanisms

| Source | Supplies | Thesis home |
| --- | --- | --- |
| Ballarin, *Locales — a module system for mathematical theories* (JAR 2014) | locales, interpretation, sublocale | Ch. 2 |
| Haftmann & Nipkow, *Code generation from Isabelle/HOL theories* | the code generator and its trust story | Ch. 11 |
| Huffman & Kunčar, *Lifting and Transfer* | quotient types; `resolved_st_q` | Ch. 8 |
| Haftmann & Wenzel, *Constructive type classes in Isabelle* | type classes; `sound_domain`, `widening` | Ch. 2, Ch. 5 |

---

## 5. Candidate contributions

Each entry: the claim as it could be defended, the repository evidence, what
must be compared, and a confidence verdict. Confidence is about *defensibility
as stated*, not about the quality of the work.

### C1 — End-to-end soundness for the analyzer that ships

**Claim.** For every configuration the tool offers — five abstract domains,
four global update rules, three context policies, call strings at every
bound — every finite execution of an accepted source program is
over-approximated by the result table the analyzer returns, and every definite
verdict in that table holds for that execution. The theorem is about the same
constant that is exported to OCaml and called by the CLI and the browser
playground.

**Evidence.** `run_voblint_certified_source_sound`, `run_voblint_check_sound`,
`run_voblint_dead_check_unreached`, `run_voblint_arithmetic_safe`
(`Analysis_Certified.thy`); the configuration coverage argument in
`docs/THEOREM_MAP.md`; `certificate_demo_full_certificate`
(`Example_End_To_End_Certificate.thy`) discharging every premise by evaluation
for one program; the single `export_code` in `Voblint_Codegen.thy`.

**Must compare.** Verasco (Coq, C, extracted, verified against CompCert C
semantics) — the honest comparison is that Verasco covers a vastly larger
language and Voblint covers a verified *pipeline around a borrowed solver*
with a context-sensitive interprocedural architecture Verasco does not have.
Also: Blazy et al.'s value analysis, and the AFP `Abs_Int_ITP2012` line, which
is intraprocedural and not executable in this sense.

**Confidence.** **High**, provided the language scope and the termination
premise are stated in the same breath. The premise `config_terminates` is the
one thing a careless reading could miss.

### C2 — A concrete semantics for calling context

**Claim.** Calling context is given a semantics rather than postulated. A
`call_context_rel` says which contexts may describe one concrete call
transition; `trace_context` threads it along a concrete trace; and
`activation_collect` is the collecting semantics indexed by it. The relational
form is essential, because Goblint's `enter` returns a list of alternatives
and each routes separately, so one concrete call may be admitted at several
contexts — buckets are a cover, not a partition. The conditional totality
condition `call_context_total_on` is exactly what makes the buckets exhaust
the context-insensitive collection
(`ltr_collect_eq_Union_activation_collect`).

**Evidence.** `LTR_Activation_Context.thy`, `LTR_Abstract.thy`,
`Activation_Backbone.thy`; the multi-alternative regression
`Example_Sign_DG_Overlapping_Enter.thy`; both policy instances
(`Call_String_Routed_Context`, `Entry_State_Routed_Context`) discharging the
same obligations.

**Must compare.** Rival & Mauborgne's trace partitioning (the closest concept:
partition the semantics by control history) and Sharir–Pnueli call strings.
The distinguishing points to check in the literature are (a) the *relational*
admissibility rather than a partition function, and (b) that the totality
condition is derived and used to recover the unindexed collection.

**Confidence.** **Medium–high.** The engineering is clearly there and the
statement is clean. Before claiming priority, do a focused search for
mechanized call-string or context-sensitivity soundness proofs; this document
found none, but absence of evidence after one pass is not evidence of absence.

### C3 — Local-trace semantics adapted to procedure activations

**Claim.** The thread-modular local-trace semantics of Schwarz et al. is
adapted from threads to procedure activations and mechanized: one `ltr` is one
activation plus its structural caller chain; a return recovers its caller
through `caller_of` rather than by an independent choice; recursion needs no
duplicated nodes because there is one `FunctionResult` per procedure and the
continuation comes from the `calls` edge.

**Evidence.** `LTR_Def.thy` (datatype, four `valid_ltr` clauses, `caller_of`,
`extend`), `LTR_Collect.thy`; `Source_To_Trace.thy` connecting an actual source
run to a trace; `Procedure_Ownership.thy`'s activation-locality theorem.

**Must compare.** Schwarz et al. SAS 2021 / ESOP 2023 / VMCAI 2026 (the source
of the idea, not mechanized in a prover and about concurrency); Sotin &
Jeannet; classical stack-based interprocedural semantics.

**Confidence.** **Medium.** Frame it as "the first mechanization of a
local-trace-style semantics, specialized to activations, and the first use of
one as the soundness target of a verified analyzer" — not as a new semantics.
The adaptation is real but derivative, and the header of `LTR_Def.thy` already
says so.

### C4 — Solver consumption through a single certificate

**Claim.** The whole soundness argument depends on the external verified
solver only through `part_post_solution`. `activation_collect_dg_sound` proves
collecting soundness from *any* valuation satisfying that certificate, without
asking how it was computed; `part_post_solution_of_solve_c` is the only bridge
from an executable solve. Consequently all four vendored update rules are
covered by one interpretation, and swapping the solver would not touch the
semantic layer.

**Evidence.** `TD_Solver_Bridge.thy`, `Globals_Rule.thy`, `Routed_Context.thy`,
and the fact that the domain registrations discharge their post-solution
obligation with the vendored `TD_side_rule_Interp.partial_post_solution`
directly.

**Must compare.** Verasco's monolithic iterator; La Spina's Coq WTO solvers
(verified engine, no pipeline); the AFP `Top_Down_Solver` entry standing alone.

**Confidence.** **High.** This is a structural property of the development and
is easy to demonstrate in one diagram.

### C5 — Orthogonality of domain, context policy and solver discipline

**Claim.** A domain proves its facts without mentioning a context, a routing
function, a seed key, or a solver. A context policy proves its facts without
mentioning a domain. Their composition is proved once. 60 configurations
inherit one theorem, and each domain's registrations are *generated* from
`manifests/analyses.yaml` rather than written.

**Evidence.** `Sign_Sound.thy` / `Interval_Sound.thy` / `Parity_Sound.thy` /
`Congruence_Sound.thy` / `Int_Sound.thy` (each explicitly says it mentions no
context and no solver); `routed_dg_analysis`, `unit_dg_analysis`,
`Routed_Analysis_Sound.thy`, `Routed_Exec_Refinement.thy`; the generated
`<Domain>_Analyses.thy` files and their drift check.

**Must compare.** Goblint's own `Spec`/`Spec2Spec` modularity (the thing being
modelled); Keidel & Erdweg's reusable components; Verasco's domain interfaces.

**Confidence.** **High**, with one caveat to state: the split is proved for
the analyses that exist, and the register records that every instance uses the
whole-state specification with an inert global channel and pins
`static_resolve`. The interface is wider than any instance exercises.

### C6 — A verified reduced product with controlled reduction

**Claim.** `int_dom` is a machine-checked reduced product of Sign, Interval,
Parity and Congruence, with reduction exposed as an explicit policy
(`Refine_Never` / `Refine_Once` / `Refine_Fixpoint`), each proved reductive and
concretization-preserving, and with a proved asymmetry: only the
non-fixpoint modes are monotone. The development additionally records a
*negative* result — narrowing cannot be composed with reduction without
violating the solver's `narrow_ge` law, because reduction may push a result
strictly below the narrowing argument.

**Evidence.** `Int_Domain.thy`, `Int_Refinement.thy` (1 430 lines),
`Int_Refinement_Control.thy` (`refine_reductive`, `refine_nonfixpoint_mono`),
`Int_Warrowing.thy` (the argument against refining narrowing),
`Int_Backward.thy`; the CLI-visible witness
`tests/regression/16-composite-domain/precision/01-refinement_beats_components.vimp`.

**Must compare.** Cousot & Cousot 1979 (reduced product, reduced cardinal
power); Goblint's `IntDomTupleImpl` and `ana.int.refinement`; Verasco's domain
communication. Note the register's finding that two reduction edges Goblint has
are missing here, and that `DefExc` is provably not addable under this
project's `bounded_semilattice_sup_bot` discipline.

**Confidence.** **Medium.** "A verified reduced product" is not new in kind.
The defensible sharpening is the *mode control with its proved reductiveness,
the monotonicity asymmetry, and the narrowing impossibility argument* — those
are specific and checkable.

### C7 — The executable/abstract refinement

**Claim.** Soundness is stated over `'a abs_state = vname => 'a`, a function on
an infinite domain. The solver runs on `resolved_st_q`, a quotient of
(local default, global default, override list). Every operation carries a
commute theorem through `fun_of_resolved_st_q_for gs`, and the finite
dead-state test is proved equivalent to the infinite one. The two defaults are
forced, not chosen: C-style zero-initialization of globals needs a non-`top`
default for globals and `top` for locals, and the ownership split needs `bot`
on the discarded side.

**Evidence.** `Exec_St_Base.thy` (with an explicit argument against Nipkow's
single-default `Abs_State`), `Exec_St_Transfer.thy`, `Exec_St_Reachability.thy`,
`Exec_Backward.thy`, `Numeric_Ops.thy` (`generic_tf_st_for_commute`).

**Must compare.** Nipkow's `Abs_State`/`Abs_Int1` refinement in
`Abs_Int_ITP2012` — this is the direct antecedent and the theory header already
argues against it.

**Confidence.** **Medium.** Present as an engineering contribution with a
crisp justification, not as a research result. Its value in the thesis is
pedagogical: it is the cleanest example of how a verification-friendly
specification and an executable implementation are kept apart and reconciled.

### C8 — Machine-checked precision witnesses

**Claim.** Precision differences are stated as machine-checked strict
inequalities on computed values, not as anecdotes. `k = 2` call strings are
strictly more precise than `k = 1` at one program point of one program;
warrowing-per-origin keeps a bound that warrowing-after-join loses; the product
domain proves a check three of its four components leave `UNKNOWN`.

**Evidence.** `sign_k2_strictly_more_precise_than_k1_at_g`
(`Example_Sign_DG_CallString_K2.thy`),
`Example_Per_Origin_Widening_Precision.thy`,
`Example_Int_*`, the `16-composite-domain` and `19-paper-examples` fixtures.

**Must compare.** Nothing directly — this is methodology, not a result. But
the scoping must be explicit: these are forcing witnesses for specific
programs, not theorems that one policy dominates another.

**Confidence.** **High as scoped**, and it would be **indefensible** if stated
generally. The Sign choice is itself principled and worth explaining: Sign is
finite, so the plain-join rule computes an exact least post-solution and the
witness sits inside the vendored optimality theorem's own envelope, where an
Interval-plus-warrowing witness would not.

### C9 — The framework is not secretly non-relational

**Claim.** `Rel_Order_Domain` runs a carrier that is not a
variable-indexed map — a set of known pairwise orderings — through the
*unmodified* framework, and the session graph makes the claim structural: its
session is parented below the pointwise reuse chain, so those locales are
unreachable, not merely unimported.

**Evidence.** `src/Analyses/Relational/Rel_Order_Domain.thy` (576 lines),
`src/Analyses/Relational/ROOT`, `Example_Relational_DG_Demo.thy`.

**Must compare.** Schwarz et al.'s clustered relational thread-modular
analyses; Miné's octagons (as the analysis this is *not*).

**Confidence.** **High as a structural claim**, and the theory itself says
"the purpose of this file is not a useful analysis". Say the same in the
thesis. Claiming a relational *analysis* would be false.

### C10 — An explicitly mapped trust boundary

**Claim.** The development states, in a checked form, exactly what is proved
and what is not: which constants are exported, which consumers call them
(checked by `codegen-api-check`), which handwritten OCaml sits outside, and
which properties are deliberately unproved.

**Evidence.** `docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md`,
`scripts/check_codegen_modules.py`, `scripts/check_generated_api.py`,
`scripts/retired_identifiers.txt`, `scripts/check_thesis_refs.py`, and the
`thm_oracles` audit the thesis tooling can render.

**Confidence.** **High**, but this is an *engineering achievement*, not a
research contribution. Put it in the evaluation chapter, and use the
`thm_oracles` output as machine-checked evidence that the endpoint theorems
rest on no oracle — most comparable theses assert that in prose.

### C11 — An interactive executable artifact

**Claim.** The verified analyzer is exported to OCaml, compiled to WebAssembly,
and exposed as a browser-local artifact that runs the generated core itself
rather than a reimplementation of it. The interface varies every dimension the
soundness theorem quantifies over — five domains, four global update rules,
three context policies with a call-string depth — and shows the solved result at
the granularity the theorems talk about: per-point abstract states, per-context
CFG nodes, entry seeds as solver globals, check verdicts, arithmetic
diagnostics, and the raw typed input and output of the generated core. The
unverified parser and presentation layer are named as such in the same page.

**Evidence.** `run_voblint` and the single `export_code`
(`Voblint_Codegen.thy`); `pixi run browser-build`; `pages/playground.html`'s
controls (`analysis-select`, `globals-select`, `context-select`,
`context-depth`) and panels (`state-inspector`, `analysis-graph`,
`solver-globals`, `raw-input`/`raw-output`, `value-hints-toggle`) — all verified
present; the regression corpus loadable through the examples dialog; the
site-figure fixtures pinning the values the explainer quotes.

**Must compare.** **Franceschino, Pichardie and Talpin's verified abstract
interpreter in F\*** ships a hosted browser version
(<https://w95psp.github.io/verified-abstract-interpreter>) — confirmed. Verasco
extracts to OCaml and ships a command-line analyzer. So a browser-hosted
verified analyzer is **not new** and the thesis must not say it is.

**Confidence.** **High as an engineering and reproducibility contribution;
novelty deliberately not claimed.** What is distinctive is narrower and factual:
the *amount of verified internals exposed interactively* — the configuration
space the theorem ranges over, and the solved contextual CFG, entry seeds and
raw core result beside the source annotations. A stronger claim about that
combination needs a targeted artifact comparison that has not been done.

**Type:** engineering / reproducibility. **Thesis home:** Ch. 11.4–11.5, Ch. 12.

**Why it earns space.** Most verified-analyzer work ends at a proof development
and perhaps an extracted binary. Here a reader who knows static analysis but not
Isabelle can vary a configuration and inspect what the proved core computes.
That is worth two pages and an honest label, not a novelty claim.

### Explicitly *not* contributions

State these plainly so a reader does not have to guess: the top-down solver
(vendored, verified elsewhere); the side-effecting constraint system (Apinis et
al.); local traces (Schwarz et al.); the D/G architecture (Goblint); widening
and narrowing; the reduced-product idea. The CLI, the browser playground, the
grammar pipeline and the 283-fixture regression suite are engineering that
makes the work usable and checkable, not results.

---

## 6. Alternative thesis structures

### Option A — Framework first, instances later

Build the general theory top-down: order theory, abstract interpretation, the
generic D/G framework and its soundness contract, then instantiate with
domains and contexts, then run it.

*For.* Matches the dependency order of the formalization almost exactly. Each
chapter is self-contained. The genericity claim is visible from the start.

*Against.* The reader spends three chapters on interfaces before seeing an
analysis do anything. `dg_spec` has ten fields with five type parameters; it is
unreadable before one knows what fills them. The concrete semantics — the
thesis's most interesting idea — arrives as infrastructure rather than as a
result.

### Option B — One analysis end to end, then generalize

Start with Sign on a five-line program: abstract values, a CFG, transfer
functions, a fixpoint. Then add procedures, then contexts, then the other
domains, then the framework as the thing all of them turned out to share.

*For.* Every concept arrives when it is needed. A reader is never asked to hold
an unfilled interface in their head. The generalization reads as earned.

*Against.* The soundness argument gets told twice — once informally for the
special case and once properly — and the second telling is the real one, so the
first is scaffolding the reader must discard. Worse, the special case is
*monovariant*, and the development's actual design makes monovariant analysis
an instance of the routed one (`unit_dg_analysis` interprets
`routed_dg_analysis`). Presenting the special case as primary inverts the
formalization's own architecture and creates a chapter-long correction later.

### Option C — Pipeline order: semantics, then analyzer, then soundness

Follow the arrows: source language, CFG, collecting semantics, domains,
equations, solver, result. Prove soundness at the end.

*For.* Natural narrative order. Mirrors the pipeline diagram a reader will
carry through the thesis.

*Against.* Soundness arriving last means the reader has no criterion while
reading the analyzer chapters. Every design decision in the framework exists to
make one of five obligations dischargeable, and a reader who does not yet know
the obligations cannot see why. It also misrepresents the development: the
soundness contract is defined in `Voblint_CFG`, below everything, not at the end.

### Option D (recommended) — Contract-centred

Pipeline order for the *concrete* side, then the soundness contract as the
pivot, then the analyzer as "how to build and compute something that discharges
it".

Source language → CFG and compilation → activation-local traces → **the five
obligations and what they buy** → domains → the analysis interface → equations
and contexts → solving and the executable carrier → results and the source-level
theorem → instances → code generation → evaluation.

*For.* It matches the formalization's own layering, including the two
load-bearing session boundaries. It puts the thesis's best idea early, where it
organizes everything after it. It gives the reader a criterion — "does this
discharge `CALL`?" — from chapter 4 onward. And it makes the final chapters
short, because by then every endpoint is an instantiation of something already
proved.

*Against.* Chapter 4 is abstract and arrives before the reader has seen a
domain. This is real and must be paid for with a worked example: the five
obligations should be illustrated on a hand-written cover for the running
program before any framework appears.

**Recommendation: Option D**, with Option B's running example threaded through
it and Option A's genericity introduced exactly where a proof needs it.

### 6.1 Against the expected ordering

A natural prior ordering for this project is:

```text
semantics → AI interface → interprocedural constraint system
  → context/routing → solver → soundness composition
  → executable analyzer → concrete analyses
```

The recommendation agrees with six of its eight steps. Two deviations are
deliberate and both are forced by the theories rather than by taste.

**Deviation 1: the soundness contract moves from seventh place to fourth.**
The reason is that the contract is what gives the later machinery its purpose.
`Routed_Context` exists to discharge `CALL` and `RETURN` once for any routing
policy; `DG_Ctx_Activation` exists to discharge `EDGE` and `COMB` from a
post-solution; the whole equation generator exists to build a `cover` that
satisfies five obligations. A reader who has not met those obligations has no
way to see why any of it is shaped as it is, and the chapters read as a tour of
machinery. Met early, each later chapter has a question it answers.

Import order is corroboration, not the argument. It happens that `ltr_coverage`
sits in `Voblint_CFG.LTR_Abstract`, a session with no domain, no solver, no
framework and no compiler — which is evidence that the contract really is
independent of everything that discharges it, and that stating it first is
possible. But repository topology is a fact about a build graph, and exposition
order has to be justified by what a reader needs. Were the contract buried in
the framework session for some accident of packaging, it would still belong in
Chapter 4.

The cost is that the reader meets an abstract contract before a concrete
domain. §4.9's hand-built cover for the running program pays it.

**Deviation 2: soundness is not composed at one place, and should not be drawn
that way.** It is discharged in five named steps, each in a different session:

| Step | Discharges | Where |
| --- | --- | --- |
| `ltr_coverage` / `activation_collect_sound` | the contract itself | `Voblint_CFG`, `Voblint_Framework.Activation_Backbone` |
| `dg_ctx_activation_base` | EDGE, COMB, from a post-solution | `Voblint_Framework.DG_Ctx_Activation` |
| `routed_context_base_hetero` | CALL, COMB, for any routing policy | `Voblint_Framework.Routed_Context` |
| `routed_dg_analysis` / `unit_dg_analysis` | the published table and the source bridge | `Voblint_Result` |
| `sound_table` / `run_voblint_certified_source_sound` | the configuration-level statement | `Voblint_CLI` |

Chapter 9 therefore *assembles* rather than *proves*, and should say so. Each
of the four chapters before it ends by discharging its own obligation; the
thesis's climax is that nothing is left, not that a long proof finally runs.

The remaining six steps keep the expected order, with one refinement: abstract
domains (Ch. 5) come after traces and before the analysis interface, because
`sound_dg_spec_core` needs a concretization `gammaDG` in its statement, so
`sound_domain` and `gamma_state` must already exist.

---

## 7. Recommended thesis structure

Five parts, fourteen chapters. Rough weight is given as a share of the body;
use it to allocate pages, not as a rule.

```text
Abstract
Acknowledgements

PART I — THE PROBLEM
1 Introduction                                                    [6%]
  1.1 Tests observe some executions; static analysis describes all of them
  1.2 Analyzers are programs, and an analyzer bug is worse than most
  1.3 The Goblint ecosystem: a verified solver, an unverified pipeline
  1.4 What this thesis builds, in one figure
  1.5 Contributions
  1.6 What is deliberately out of scope
  1.7 Outline

2 Foundations                                                     [8%]
  2.1 Lattices, monotonicity, fixpoints (Knaster–Tarski, Kleene)
  2.2 Abstract interpretation: concretization, soundness, and why no alpha
  2.3 Widening and narrowing; warrowing as one operator
  2.4 Constraint systems over program points; side effects
  2.5 Isabelle/HOL for this thesis: type classes, locales, inductive
      definitions, quotient types, code equations
  2.6 Notation used throughout

PART II — WHAT MUST BE OVER-APPROXIMATED
3 VIMP and its control-flow graph                                 [10%]
  3.1 Syntax and expressions: integers only, C-style truthiness
  3.2 Procedures, activations, and the small-step semantics
  3.3 Locals and globals as a classifier; enter_state and combine_env
  3.4 Which programs are admitted (wf_source_program) and why
  3.5 The procedure-aware CFG: two relations, three node kinds
  3.6 Compilation as continuation passing
  3.7 Forward simulation: csim and what it does not determine
  3.8 Structural certificates: ownership, liveness, call-source uniqueness

4 Activation-local traces and the soundness contract               [12%]
  4.1 Why not reachable states: context must be a projection of the concrete
  4.2 Local traces, from threads to activations
  4.3 valid_ltr: four clauses, one per graph phenomenon
  4.4 ltr_collect: the set an analysis must over-approximate
  4.5 Contexts as an admissibility relation; trace_context
  4.6 activation_collect and why buckets cover rather than partition
  4.7 THE CONTRACT: INIT, INTRA, CALL, RETURN, TOTAL
  4.8 What the contract buys: activation_collect_sound, and the union theorem
  4.9 A worked cover for the running program, by hand
  4.10 From a source run to a trace (Source_To_Trace)

PART III — THE ANALYZER
5 Abstract domains                                                 [8%]
  5.1 The sound_domain class: what a domain is, minimally
  5.2 Pointwise abstract states; when a state denotes nothing
  5.3 The reachability lift: dead code as an explicit tag
  5.4 Backward filtering: guards that narrow (backward_domain)
  5.5 Numeric queries, and what a check needs from a domain

6 What an analysis supplies                                        [10%]
  6.1 Goblint's Spec, in one page
  6.2 D and G: separating flow-sensitive from shared facts
  6.3 The manager: capabilities, not keys
  6.4 dg_spec, field by field
  6.5 sound_dg_spec_core: the contract, stated over compiled trees
  6.6 The whole-state shortcut: eight operations and one interpretation
  6.7 The ownership-split lifter as a Spec2Spec functor
  6.8 What the interface deliberately does not have (sync, query, startstate)

7 Equations, contexts, and routing                                 [12%]
  7.1 From a graph to a strategy tree
  7.2 Keyed unknowns: one program point, several contexts
  7.3 The call protocol: enter, seed, exit read, combine
  7.4 Why the callee entry is a global proxy, and what that costs
  7.5 Routing policies: monovariant, call strings, entry state
  7.6 Discharging CALL and RETURN once (routed_context_base_hetero)
  7.7 Side buffering: why one right-hand side must not name a key twice
  7.8 Context spaces: which policies can be finite

8 Solving                                                          [8%]
  8.1 The vendored solver: strategy trees, demand, dependencies
  8.2 part_post_solution: the one certificate that crosses the boundary
  8.3 Four update rules as one parameter
  8.4 The executable carrier: a quotient with two defaults
  8.5 Commutation: running the real thing, reasoning about the other one
  8.6 Deciding deadness finitely

9 Results, checks, and the source-level theorem                    [10%]
  9.1 The published table: coverage is not reachability
  9.2 Live keys: coverage derived from termination
  9.3 Three-valued verdicts, and why Dead is a fourth thing
  9.4 Arithmetic diagnostics
  9.5 Assembling one analysis: routed_dg_analysis
  9.6 The monovariant case as an instance, not a special case
  9.7 run_voblint and its soundness theorem
  9.8 Reading the theorem: the two existentials and the one premise

PART IV — INSTANCES AND PRACTICE
10 Five domains and a relational witness                           [8%]
  10.1 What a domain must supply, as a checklist
  10.2 Sign: a finite lattice and an exact solve
  10.3 Interval: infinite height, widening, narrowing
  10.4 Parity, and a domain with no backward filter
  10.5 Congruence: Chinese remainder as an exact meet
  10.6 int_dom: a reduced product with an explicit reduction policy
  10.7 Why narrowing cannot refine (a negative result)
  10.8 Rel_Order_Domain: a carrier that is not a map

11 From formalization to executable analyzer                       [8%]
  11.1 Executable Isabelle definitions: what makes a definition run
  11.2 Code generation, one module, and the public run_voblint interface
  11.3 The OCaml and browser boundary
  11.4 An interactive analyzer artifact
  11.5 What the playground demonstrates, and what it cannot
  11.6 What remains outside the trusted boundary

12 Evaluation                                                      [8%]
  12.1 Three kinds of evidence, and what each can support
       (machine-checked | executable | explorable)
  12.2 Proof effort: where the lines are
  12.3 The regression suite: precision, soundness, known-imprecision
  12.4 Precision witnesses: contexts, update rules, the product
  12.5 Known imprecision, with mechanisms named
  12.6 A real unsoundness, replayed: goblint/analyzer #1161
  12.7 Runtime behaviour and its limits
  12.8 Goblint alignment: an audited difference table

PART V — ASSESSMENT
13 Related work                                                    [8%]
  13.1 Verified analyzers: Verasco and the CompCert line
  13.2 Mechanized abstract interpretation in Isabelle
  13.3 Verified fixpoint solvers
  13.4 Goblint, local traces, and thread-modular analysis
  13.5 Context sensitivity and trace partitioning
  13.6 Where Voblint sits

14 Conclusion                                                      [6%]
  14.1 What was established
  14.2 Limitations, honestly enumerated
  14.3 Future work: termination, context bounding, relational domains,
       richer source language, multi-analysis composition
  14.4 Closing

Appendices
  A  Isabelle theory map and session graph
  B  Notation reference, mapped to Isabelle names
  C  The five obligations, per policy instance
  D  The Goblint alignment register (condensed)
  E  Regression corpus index
```

### 7.1 Per-chapter design notes

**Ch. 1.** The pipeline figure belongs on the second page, with the trust
boundary already drawn on it — this is already the plan in
`content/01-introduction.typ`. State the headline theorem informally in §1.3
and precisely in §1.4, then never restate it until Ch. 9. *Omit* all Isabelle
syntax.

**Ch. 2.** The hardest chapter to keep short. Rule: include a concept only if a
later chapter's *statement* depends on it. Galois connections get one page,
ending with "only `gamma` is mechanized here, because soundness never needs
`alpha` and no optimality is claimed". Widening gets a figure. Isabelle
mechanisms get exactly what the later chapters use, with a forward pointer each
time — locales because the soundness obligations are locale assumptions; type
classes because `sound_domain` is one; quotient types because the executable
state is one; code equations because the export depends on them. *Defer*
strategy trees to Ch. 8.

**Ch. 3.** Prerequisite: Ch. 2.1–2.2. The compiler is 5 813 lines and cannot be
presented in full. Present `compile` as a continuation-passing function with
one worked fragment (the `while` loop), state `csim` with its three
constructors and the picture of nested `Restore` wrappers against the frame
stack, state `csim_step` and `csim_star`, and push the residual-edge machinery
(`control_at`, `Residual_Edges`) to a two-paragraph proof sketch. *Omit*
`Live_Nodes` here; it is needed only in Ch. 9 for `live_keys`, so introduce it
there.

**Ch. 4.** The pivot. Prerequisite: Ch. 3. Build in this order: the design law
("the concrete semantics must carry at least the distinctions the analysis
claims"), then `ltr`, then `valid_ltr`'s four clauses side by side with
`cstep`'s three rules, then `ltr_collect`. Contexts come second, as a *separate*
layer: relation, `trace_context`, `activation_collect`, cover-not-partition.
Then the five obligations, each with the one sentence saying what goes wrong
without it — `RETURN` is the load-bearing one (a return may only compose a
callee whose context came from the caller it is resuming) and `TOTAL` is what
makes buckets meaningful rather than merely safe. Close with §4.9's hand-built
cover, which is the only place in the thesis a reader sees the obligations
discharged without machinery.

**Ch. 5.** Short. Prerequisite: Ch. 2.1–2.3. The lift deserves a figure
(`Bot` vs `Lifted bot` are different, and the reason is the whole point).
*Omit* the refined backward locale (`backward_domain_refined`) and the
numeric-query derivation details; state the interface and one soundness lemma.

**Ch. 6.** Prerequisite: Ch. 2.4, Ch. 5. Open with Goblint's `Spec` signature
verbatim, then the correspondence table. `dg_spec`'s record is worth showing in
full — ten fields is readable, and the `#` notation makes the correspondence
visual. `sound_dg_spec_core` is worth showing; its statement over compiled
trees rather than a reconstructed pair is a design point. *Omit* `DG_Manager`'s
five type parameters from the main text; put the parameter table in Appendix B.

**Ch. 7.** The heaviest chapter. Prerequisite: Ch. 4, Ch. 6. The call protocol
needs a sequence figure: caller value → `enter` alternatives → `route` picks a
context → `Side` publishes the seed → callee entry reads it back → callee exit
read at the same context → `combine_env` then `combine_assign`. Side buffering
needs its own subsection because the failure it prevents (non-convergence under
a per-origin rule) is a genuine, reproduced bug with a regression. *Defer* the
generator's ten parameters to a table; show `routed_node_rhs`'s shape, not its
definition.

**Ch. 8.** Prerequisite: Ch. 2.4, Ch. 7. Present the solver as a black box with
one interface. Show the `strategy_tree` datatype (four constructors) and
`part_post_solution` (three conjuncts) — both are small and both are the
boundary. The executable carrier gets the "why two defaults" argument in full,
because it is the clearest instance of a verification-driven representation
choice. *Omit* the vendored solver's internals entirely; cite the NFM paper.

**Ch. 9.** Prerequisite: everything. This chapter is mostly assembly, and its
job is to be precise about the statement rather than to introduce ideas. The
one genuinely new idea here is `live_keys`: the solved key set is not closed,
and closing it is derived from termination rather than assumed. The four
existential/premise subtleties in §9.8 are what a careful examiner will probe.

**Ch. 10.** Prerequisite: Ch. 5, Ch. 6. Use the checklist in §10.1 as the
chapter's skeleton and fill it five times, in decreasing detail: Sign in full,
Interval in full for widening, Parity as the "what if a domain has no backward
filter" case, Congruence for the exact meet, `int_dom` for reduction. §10.7's
negative result deserves a full page. §10.8 is one page.

**Ch. 11.** Concrete, and larger than the first draft of this plan allowed.
§11.1–11.3 are the export story; the module-cycle argument (why `module_name
Generated` is forced) is worth two paragraphs because it is a real constraint a
reader would otherwise assume was laziness. §11.4–11.5 are the artifact (C11),
and 2–4 pages is the right size: describe what the interface exposes, show one
screenshot of a configuration being varied, and state plainly that the browser
runs the generated core rather than a reimplementation. §11.5 must also say what
the artifact *cannot* show. It cannot exhibit the proof. And on a run that never
finishes it must be precise: nontermination of the generated analysis is
permitted by the theorem, since termination is a premise (`config_terminates`)
rather than a proved property, so observing it does not contradict soundness —
but an individual hang could still have an implementation cause, in the exported
code, the toolchain or the browser, and the artifact cannot tell the two apart. §11.6 is the
trust boundary, drawn once and referred back to from Ch. 12 and Ch. 14.

**Ch. 12.** Prerequisite: all. Structure it as questions with answers, not as a
data dump: How much proof per line of analyzer? Which regression categories
exist and why the three-way split matters? Which precision claims are
machine-checked and which are measured? What does the alignment register say is
different? Include the `thm_oracles` audit (`[]`, generated).

§12.1 is new and sets up the rest. Three kinds of evidence, in decreasing
strength, and the chapter should say which each later claim rests on:

| Kind | What it can establish | Instances |
| --- | --- | --- |
| machine-checked | a theorem, for every input the statement ranges over | the five endpoints; `sign_k2_strictly_more_precise_than_k1_at_g`; `certificate_demo_full_certificate`; `thm_oracles = []` |
| executable | that *this* program, at *this* configuration, answers *this* | the 283-fixture corpus; the `by eval` witnesses; the site-figure fixtures |
| explorable | that a reader can check the above without Isabelle | the playground (C11) |

§12.6 is the chapter's strongest section and should be written early — see
§14.2. It is a real upstream unsoundness in the same domain, replayed as a
fixture, where the verified domain answers correctly. It is also the section
most easily overclaimed; §14.2 states the exact boundary.

**Ch. 13.** Prerequisite: Ch. 1, 4, 6, 8. Organize by *what each related system
verified*, not chronologically. The Verasco comparison needs its own table:
language, proof assistant, iterator vs constraint system, interprocedural
treatment, context sensitivity, extraction, proof size.

**Ch. 14.** Keep limitations concrete and enumerated, mapped to the register
rows and `docs/NON_GOALS.md`. Future work should name the *next* thing, with
its known obstacle: context bounding (key closure under routing is unproved),
termination (a finite key space does not make a solve terminate), relational
domains (the carrier is already opaque; the missing piece is a useful one),
arrays (needs explicit semantics, not inherited), multi-analysis composition
(needs a query channel that does not exist).

---

## 8. Isabelle-to-thesis mapping

Maintain this table in `thesis/shared/` and check it with `thesis-refs`. Format:
thesis section → theories → central definitions → central theorems.

| Thesis | Theories | Definitions | Theorems |
| --- | --- | --- | --- |
| 3.1–3.2 | `Voblint_VIMP.VIMP_Syntax`, `VIMP_Expr`, `VIMP_Proc` | `exp`, `aval`, `com`, `proc_decl`, `frame`, `pstep`, `psteps`, `pcompletes` | `pstep` inversion rules |
| 3.3 | `Voblint_VIMP.VIMP_Globals` | `cinit_stores`, `enter_state`, `combine_env`, `enter_frame` | — |
| 3.4 | `Voblint_VIMP.VIMP_Proc`, `Voblint_Compile.Compile_Invariants` | `source_com`, `wf_source_com`, `value_providing`, `wf_source_program`, `wf_compile_input`, `wf_program_compile_input_exec` | `wf_source_programD`, `wf_compile_inputD` |
| 3.5 | `Voblint_CFG.CFG_Def`, `CFG_Transfer`, `CFG_Exec` | `cfg_node`, `edge_action`, `call_action`, `intra`, `calls`, `wf_cfg`, `edge_step`, `edge_collect`, `call_enter`, `combine_collect`, `cstep` | `cfg_nodes_finite` |
| 3.6 | `Voblint_Compile.VIMP_Proc_to_CFG` | `compile`, `compile_proc`, `compile_prog`, `prog_cfg` | — |
| 3.7 | `Voblint_Compile.Simulation_Relation`, `Simulation_Preservation`, `Residual_Location` | `csim`, `control_at`, `procs_embedded` | `csim_step`, `csim_star`, `procs_embedded_compile_prog` |
| 3.8 | `Voblint_Compile.Compile_Wellformed`, `Procedure_Ownership`, `Live_Nodes` | `frag_stmts`, `prog_live` | `compile_prog_wf`, `compile_prog_finite`, `compile_prog_calls_source_unique`, `valid_ltr_entry_result_eq`, `prog_live_reaches` |
| 4.2–4.4 | `Voblint_CFG.LTR_Def`, `LTR_Collect` | `ltr`, `path`, `sink_node`, `sink_store`, `caller_of`, `extend`, `valid_ltr`, `ltr_collect` | `ltr_collect_I`, `ltr_collect_E` |
| 4.5–4.6 | `Voblint_CFG.LTR_Activation_Context` | `call_context_rel`, `call_context_rel_of_fun`, `admits_call_context`, `trace_context`, `call_context_total_on`, `activation_collect`, `startcontext` | `activation_collect_I`, `activation_collect_E`, `activation_collect_of_fun` |
| 4.7–4.8 | `Voblint_CFG.LTR_Abstract`, `Voblint_Framework.Activation_Backbone` | locale `ltr_coverage`, `trace_covered` | `valid_ltr_covered_at`, `ltr_collect_semantic_postfix`, `ltr_collect_eq_Union_activation_collect`, `activation_collect_sound` |
| 4.10 | `Voblint_Compile.Source_To_Trace` | `stack_repr` | `source_run_has_ltr`, `source_reaches_ltr_collect` |
| 5.1–5.3 | `Voblint_Domain.Abstract_Domain`, `Nonrelational_State`, `Reachability_Lift`, `Nonrelational_Reachability` | class `sound_domain`, class `executable_domain`, `abs_state`, `gamma_state`, `is_empty_state`, `'a lifted`, `normalize_lift`, `canonicalize_lift` | `gamma_stateD` |
| 5.4–5.5 | `Voblint_Domain.Backward_Domain`, `Abstract_Numeric_Queries`, `Backward_Numeric_Queries` | locale `backward_domain`, `afilter`, `bfilter`, `branch_lifted`, locale `abstract_numeric_queries`, `less`, `eq` | `branch_sound`, `bfilter_sound`, `branch_le_bfilter` |
| 6.2–6.4 | `Voblint_Framework.DG_State`, `DG_Manager`, `DG_Spec` | `dg_state`, `man`, `man_local`, `man_global`, `man_sideg`, `mk_dg_man`, `dg_spec` (ten fields), `analysis_event` | — |
| 6.5–6.6 | `Voblint_Framework.DG_Spec_Sound`, `DG_Local_State_Spec`, `Transfer_Algebra` | locale `sound_dg_spec_core`, `sound_local_dg_spec`, `sound_transfer_for`, `local_state_dg_spec_for`, `_lifted`, `combine_collect_abs` | `local_state_dg_spec_for_core_sound`, `combine_sound_tree` |
| 6.7 | `Voblint_Framework.DG_Ownership_Split_Spec`, `State_Restriction` | `ownership_split_lift`, `gamma_ownership_split`, `restrict_local`, `restrict_global` | `gamma_ownership_split_combine_env` |
| 7.1–7.2 | `Voblint_Solver.Strategy_Tree_Program`, `Voblint_Framework.DG_Constraint_Trees`, `DG_Keyed_Generator`, `CFG_Enumeration` | `strategy_program`, `sp_compile_with`, `side_rhs_fold_dg`, `routed_node_rhs`, `routed_node_rhs_buffered`, `cfg_intra_list`, `call_site_list` | `routed_node_rhs_buffered_correspondence` |
| 7.3–7.4 | `Voblint_Framework.Routed_Call_Trees` | `routed_gk` (`Analysis_Global`, `Activation_Seed`), `routed_call_tree`, `routed_callee_call_tree`, `routed_entry_seed_tree`, `resolve`, `static_resolve` | — |
| 7.5–7.6 | `Voblint_Framework.Routed_Context`, `Routed_Context_Unit`, `Call_String_Context`, `Voblint_Routing.Call_String_Routed_Context`, `Entry_State_Routed_Context` | locale `routed_context_base_hetero`, `route`, `route_unit`, `enterc_unit`, `cs_route`, `cs_context`, `formals_route_lifted_gen`, `routed_entry_cover` | `activation_collect_dg_sound`, `activation_collect_unit_eq_ltr_collect`, `cs_route_context_agree`, `cs_route_length` |
| 7.7 | `Voblint_Solver.Strategy_Tree_Side_Buffering` | `buffer_sides` | — |
| 7.8 | `Voblint_Routing.Context_Space_Finite` | — | `compiled_call_strings_finite`, `compiled_call_string_vars_finite` |
| 8.1–8.3 | vendor `Basics_side`, `TD_side_upd_rule`; `Voblint_Solver.TD_Solver_Bridge`, `Globals_Rule`, `Strategy_Tree_Post_Solution` | `strategy_tree`, `eqsT`, `part_post_solution`, `least_part_post_solution`, `globals_rule`, locale `TD_side_upd_rule` | `partial_post_solution`, `term_equivalence`, `solve_code_equation`, `part_post_solution_of_solve_c` |
| 8.4–8.6 | `Voblint_Exec.Exec_St_Base`, `Exec_St_Algebra`, `Exec_St_Transfer`, `Exec_St_Reachability`, `Exec_DG_State` | `resolved_st`, `resolved_st_q` (quotient), `location`, `location_of`, `fun_of_resolved_st_q_for`, `resolved_st_is_bot`, `canonical_location`, `exec_dg_st`, `fun_of_dg_st_for` | `resolved_st_q_is_bot_for_iff`, `generic_tf_st_for_commute`, `branch_st_commute` |
| 9.1–9.2 | `Voblint_Framework.Analysis_Result`, `Voblint_Result.Routed_Live_Keys` | `analysis_result`, `result_keys`, `lookup_context`, `wf_analysis_result`, `live_keys` | `live_keys_cover`, `routed_dg_analysis.fun_route_activation_collect_sound_of_terminates` |
| 9.3–9.4 | `Voblint_Framework.Check_Result`, `Checks`, `Abstract_Checks`, `Check_Report`, `Contextual_Check_Report`; `Voblint_CLI.Arithmetic_Diagnostics` | `check_result`, `contextual_verdict`, `checks_proven`, `classify_checks_verdicts`, `arithmetic_diagnostics` | `abstract_checks_proven_sound` |
| 9.5–9.6 | `Voblint_Result.Routed_DG_Analysis`, `Unit_DG_Analysis`, `Analysis_Surface`, `Source_Activation_Sound`; `Voblint_Framework.DG_Analysis_Adapter` | locale `routed_dg_pipeline`, locale `routed_dg_analysis`, locale `unit_dg_analysis`, locale `analysis_surface`, `state_at`, `report` | `entry_state_activation_collect_sound`, `fun_route_activation_collect_sound`, `entry_state_has_context`, `gamma_reader_eq_lookup`, `source_activation_sound`, `source_sound_from_collecting_cap`, `unit_dg_analysis.source_sound`, `result_node_sound` |
| 9.7–9.8 | `Voblint_CLI.Analysis_Config`, `Analysis_Run`, `Analysis_Run_Sound`, `Analysis_Run_Ctx_Sound`, `Analysis_Certified` | `analysis_domain`, `globals_rule`, `context_mode`, `run_voblint`, `analysis_result_covers`, `config_terminates`, locale `sound_table` | `run_voblint_certified_source_sound`, `run_voblint_check_sound`, `run_voblint_check_sites`, `run_voblint_dead_check_unreached`, `run_voblint_arithmetic_safe`, `sound_table_of_activation`, `sound_table.source_sound` |
| 10.1 | `Voblint_Nonrelational.Nonrelational_Transfer`, `Numeric_Ops`, `Special_Ops`, `Abstract_Arithmetic` | locale `nonrelational_transfer`, `numeric_ops`, `generic_tf_abs`, locale `expression_domain_sound` | `tf_abs_eq_generic`, `aval_dom_sound` |
| 10.2 | `Voblint_Analysis_Sign.*` | `sign`, `plus_sign`, `sign_lt`, `sign_ops`, `sign_conf_spec`, `sign_classify_check` | `sign_tf_st_for_commute`, `sign_rule.source_sound` |
| 10.3 | `Voblint_Analysis_Interval.*` | `eint`, `ivl`, `ivl_widen`, `ivl_narrow`, `aval_ivl`, `branch_ivl` | `interval_rule.source_sound` |
| 10.4 | `Voblint_Analysis_Parity.*` | `parity`, `parity_min`, `parity_max`, `branch_parity` | `parity_tf_st_for_commute` |
| 10.5 | `Voblint_Analysis_Congruence.*` | `congruence`, `congruence_le_rep`, `intersect_congruence`, `inv_plus_congruence` | `congruence_lt_sound` |
| 10.6–10.7 | `Voblint_Analysis_Int.*` | `int_dom`, `refine_mode`, `refine_round`, `refine_fix`, `int_tf_st_*_for` | `refine_reductive`, `refine_nonfixpoint_mono`, `int_is_sound_transfer_for` |
| 10.8 | `Voblint_Analysis_Relational.Rel_Order_Domain` | `relc`, `rel_order_spec`, `gamma_relc` | `sound_dg_spec_core` instance |
| 11.1–11.2 | `Voblint_Codegen.Voblint_Codegen` | the export root list | — |
| 12.3 | `Voblint_Examples_Sign.Example_Sign_DG_CallString_K1/K2`, `Voblint_Examples_Tooling.Example_Per_Origin_Widening_Precision`, `Voblint_Examples_CLI.*` | — | `sign_k2_strictly_more_precise_than_k1_at_g` |
| 12.x | `Voblint_Examples.Example_End_To_End_Certificate` | `certificate_demo_prog` | `certificate_demo_full_certificate` |

---

## 9. Figures and running examples

### 9.1 Running-example strategy

Do not force one program to carry everything. Use one **spine program**
through Parts II and III, and three **single-purpose programs** where the spine
cannot show the effect.

**The spine program** (proposed; combines the existing `contexts.vimp` and
`while-loop.vimp` figures):

```c
fun bump(n) {
  return n + 1;
}

fun main() {
  a = bump(5);
  b = bump(4);
  x = 0;
  while (x < 10) {
    x = x + 1;
  }
  __voblint_check(a == 6);
  __voblint_check(0 < x);
}
```

It exercises assignment, a guard, a loop, two call sites of one procedure,
return flow, two checks, and a precision difference under contexts. Its CFG is
about a dozen nodes — drawable on one page. It is the only program the reader
needs to hold in mind.

Where each chapter uses it:

| Chapter | Use |
| --- | --- |
| 1 | the analyzer's output on it, with the trust boundary drawn |
| 3 | its AST, one `pstep` sequence, its compiled CFG with node numbers |
| 4 | one `ltr` for the second `bump` activation, drawn as a tree; the hand-built cover in §4.9 |
| 6 | what `assign#`, `branch#`, `enter#`, `combine_assign#` do at three of its edges |
| 7 | its full equation system at `Ctx_None`, then the two `bump` contexts under `Ctx_CallString 1` |
| 8 | the solver's iteration at the loop head, with and without widening |
| 9 | its result table and check column |
| 10 | the same table under all five domains |
| 12 | its runtime across configurations |

**Single-purpose programs:**

| Program | Shows | Where |
| --- | --- | --- |
| `int-refinement.vimp` (`if (y+1==3) check(y==2)`) | the reduced product proving what three components cannot | 10.6 |
| `division-possible.vimp` (nondeterministic divisor) | arithmetic diagnostics and the soundness category | 9.4, 12.2 |
| `certificate_demo_prog` (`bump(1)`, `bump(41)`, `Int` + `Ctx_CallString 1`) | every premise discharged by evaluation | 12.x |
| the Sign k=1/k=2 nesting program | the strict precision inequality | 12.3 |

**Action item.** The spine program does not yet exist as a figure source. Add
it to `docs/readme-figures/`, as a `tests/regression/` fixture, and to
`thesis/shared/claims.toml`, so every figure built from its output is
re-checked by `pixi run thesis-claims`.

### 9.2 Figure inventory

Prefer generated over drawn wherever the infrastructure already exists
(`thesis/README.md` lists the generators).

**Structural figures (hand-drawn, in `fletcher`/`diagraph`):**

1. **The pipeline with its trust boundary** (Ch. 1, repeated as a chapter
   opener in Parts II–IV with the current stage highlighted). The single most
   important figure in the thesis.
2. **The session graph** (Ch. 1 or Appendix A), generated by
   `isabelle build -g`.
3. **`cstep`'s three rules beside `valid_ltr`'s four clauses** (Ch. 4) — the
   correspondence is the chapter's core and reads far better as a table of
   rule shapes than as prose.
4. **An `ltr` as a tree** (Ch. 4): `Resume (Call (Root …) …) …` with the
   caller chain drawn, for the second `bump` activation.
5. **The five obligations as a commuting diagram** (Ch. 4): concrete step on
   one axis, `cover` membership on the other. `commute` handles this.
6. **The call protocol sequence** (Ch. 7): caller value → `enter` → `route` →
   `Side` seed → entry read-back → exit read → `combine_env` →
   `combine_assign`, with the Goblint name beside each Voblint name.
7. **The two representations and their morphism** (Ch. 8): `abs_state` on the
   left, `resolved_st_q` on the right, `fun_of_resolved_st_q_for gs` between,
   and one commuting square for a transfer.
8. **The locale hierarchy** (Ch. 6 or Appendix A), generated by
   `tools/locale_graph.ML`.
9. **The `sound_domain` / `widening` class hierarchy** (Ch. 5), generated by
   `class_deps`.
10. **`thm_deps` for `run_voblint_certified_source_sound`** (Ch. 9 or 12) —
    what the headline actually rests on, machine-generated.

**Content figures (generated from the analyzer):**

1. The spine program's CFG (`--graph-snapshot` / playground GraphViz).
2. Its solved graph under `Ctx_None` and `Ctx_CallString 1`, side by side —
    one box per `(procedure, context)`.
3. Its result table and check column, quoted through `claims.toml`.
4. The interval lattice and the widening/narrowing iteration at the loop head
    (an iteration plot; `lib/figures.typ` already has the vocabulary).
5. The Sign seven-element lattice and the Parity four-element lattice
    (Hasse diagrams).
6. The `int_dom` refinement round on `int-refinement.vimp`: four component
    values before and after.
7. The k=1 vs k=2 call-string comparison as two solved graphs.

**Tables:**

1. Goblint `Spec` ↔ `dg_spec` field correspondence (Ch. 6).
2. The Goblint alignment register, condensed (Ch. 12 and Appendix D).
3. Proof effort by layer (Ch. 12) — the table in §2.1 above.
4. Verasco / Abs_Int_ITP2012 / Top_Down_Solver / Voblint comparison (Ch. 13).
5. Regression corpus by category and outcome class (Ch. 12).

---

## 10. Open research questions and uncertainties

Things this document cannot settle from the repository or from one literature
pass. Each needs a decision or a check before the corresponding chapter is
written.

**U1 — The title, and with it the framing.** `thesis/thesis.typ` says
*"Voblint: Towards a Verified Goblint-style Analysis Pipeline in
Isabelle/HOL"*. The repository's own GitHub description says *"A Generic,
Executable, and Machine-Checked Framework for Interprocedural Abstract
Interpretation in Isabelle/HOL"*. These are different theses: the first is a
pipeline-soundness thesis with Goblint as the reference architecture; the
second is a framework-genericity thesis. The recommended structure supports
both, but Ch. 1 and Ch. 14 differ substantially. *Decide with the supervisors
before writing Ch. 1.* The word "Towards" is also a scope hedge that the
current endpoint theorems may no longer need.

**U2 — Priority of the relational context semantics (C2).** One literature
pass found no mechanized soundness proof for call-string or entry-state
context selection stated over a concrete trace semantics. That is not enough to
claim priority. Check specifically: Coq/Isabelle formalizations of
interprocedural dataflow; any mechanization of trace partitioning;
Verasco's treatment of function calls; the IFDS/IDE mechanization literature.

**U3 — Whether the four-question framework was ever answered.** The KB's
`thesis-contribution-reassessment.md` poses four questions explicitly reserved
for the author and supervisors, and records that they were unanswered as of
2026-08-04. §5 of this document is a candidate answer to questions (1) and (2).
Questions (3) and (4) — which open issues strengthen the contributions, and
what would be defended in a presentation — remain open.

**U4 — How prominently to foreground `config_terminates`.** It is the one
analyzer-side premise, and it is discharged per program by evaluation. Options:
state it in the abstract (maximally honest, slightly deflating), state it in
§1.3 and Ch. 9 only, or give it its own short section in Ch. 9 with the
`live_keys_cover` result that shows how much *else* follows from it.
Recommendation: the third, and mention it in the abstract in one clause.

**U5 — Artifact reproducibility.** The vendored solver is pinned to a *private*
fork of `stilscher/td-verification` and CI needs a token. A thesis that claims
a reproducible artifact must either get that fork made public or state the
dependency explicitly. This is a real blocker for an artifact-evaluation claim
and should be raised now, not in November.

**U6 — Whether to discuss the removed AFP IMP2 bridge.** Soundness is stated
against VIMP's own semantics only. A reader may ask why the reference semantics
is bespoke. The bridge to AFP `IMP2` existed and was removed. Options: say
nothing; state the design decision in Ch. 3 with the reasoning; or state it in
Ch. 14 as future work. Recommendation: one honest paragraph in Ch. 3.4, because
"why should I believe your semantics" is the first question a verification
examiner asks.

**U7 — How much of the compiler chapter survives the page budget.** 5 813
lines, and it contributes exactly two facts to the spine (`csim_star` and
`source_run_has_ltr`) plus the structural certificates. It is defensible to
compress Ch. 3.6–3.8 heavily. Decide once a page count exists.

**U8 — Evaluation content.** §12.5 ("runtime behaviour") is currently
speculative: no systematic performance measurement exists in the repository.
Either build one (the CLI and the fixture corpus make it cheap) or drop the
section. A verified analyzer's performance is a fair question and an empty
answer is worse than an acknowledged limitation.

**U9 — Whether `int_dom` counts as a "reduced product".** The term has a
precise meaning (the quotient of the product by the reduction operator). What
exists is a product carrier with an explicit, optionally-iterated reduction
step. Check the terminology against Cousot & Cousot 1979 before using the
phrase in the abstract; "a product domain with controlled reduction" may be the
accurate name.

**U10 — The `Activation_Seed` deviation's rhetorical weight.** The register is
explicit that no operational equivalence to Goblint's fixpoint is claimed, and
that widening lands one hop later. This is the largest architectural deviation
and it is invisible in the soundness theorem. Decide where it is stated: Ch. 7.4
(recommended, at the point the encoding is introduced) and again in Ch. 12.7.

**U12 — What may be said about the artifact beyond "it exists".** C11 is
labelled an engineering contribution with novelty not claimed, because
Franceschino et al.'s F\* interpreter already ships a browser version. The
narrower claim — the *amount of verified internals exposed interactively*, and
that the configuration space on offer is the one the theorem quantifies over —
may well be distinctive, but it rests on one artifact comparison that has not
been done. Before Chapter 11.5 says anything stronger than "here is what it
shows", compare against: the F\* interpreter's hosted version, Verasco's
released artifact, any Goblint web front end, and the AFP entries' own demos.
Until then the chapter describes and does not rank.

**U13 — How much of the explainer's prose may be reused verbatim.** §14 treats
`pages/index.html` as a prototype of the thesis's explanations, and some
sentences are good enough to keep. Both are the author's own writing, so this is
text recycling rather than plagiarism, and TUM's citation guide treats it as its
own category: previously published material should be made visible as such and
the original cited, and reused figures and tables identified and sourced. The
working rule that follows, and which does not block writing:

- *expository order and ideas* — reuse freely, rewritten for the thesis register;
- *exact prose* — do not copy;
- *web figures used as-is or adapted* — mark as adapted from the project
  explainer, which is already public;
- *technical content* — ground in the theories and the primary literature; the
  site is never the authority for a technical claim.

Worth one question to the supervisors in case the chair has its own convention.

**U11 — Whether a precision claim can be made at all beyond witnesses.** The
repository has strict-order witnesses for specific programs and no general
precision theorem. Confirm that no general claim is intended, and make the
scoping language uniform across Ch. 12 and the abstract.

---

## 11. Proposed writing order

Final chapter order is not writing order. Write the load-bearing and stable
material first; write the material that depends on choices last.

**Phase 1 — the spine (weeks 1–3).**

1. **Ch. 4** (traces and the contract). Hardest, most original, most stable,
   and it fixes the vocabulary everything else uses. Writing it first also
   forces the notation decisions in `lib/math.typ` that every later chapter
   inherits.
2. **Ch. 9** (results and the source-level theorem). Write the endpoint second,
   even though it depends on unwritten chapters. Stating precisely what is
   proved is what keeps Chapters 5–8 honest, and every forward reference it
   needs becomes a checklist item.
3. **The spine program and its figures.** Add the fixture, regenerate the
   figures, wire `claims.toml`. Everything after this can quote checked output.

**Phase 2 — the concrete side (weeks 3–5).**

1. **Ch. 3** (VIMP and the CFG). Mostly descriptive; low risk. Decide the
   compression level for 3.6–3.8 here (U7).

**Phase 3 — the analyzer (weeks 5–9).**

1. **Ch. 6** (what an analysis supplies). Needs the Goblint correspondence
   table, which already exists in `Framework/README.md` and the register.
2. **Ch. 7** (equations, contexts, routing). The heaviest chapter; budget
   accordingly. The call-protocol figure is the gating artifact.
3. **Ch. 8** (solving and the executable carrier).
4. **Ch. 5** (domains). Deliberately after 6–7: only then is it clear which
   parts of the domain interface are load-bearing and which are detail.

**Phase 4 — instances and practice (weeks 9–11).**

*Write §12.6 first within this phase.* It is the chapter's strongest section,
the evidence already exists as a fixture, and its boundary is the easiest thing
in the thesis to overclaim — §14.2 states the exact wording. Writing it early
also settles how Chapter 1's motivation lands, since the two share the same
example.

1. **Ch. 10** (five domains). Largely mechanical once Ch. 5–7 exist.
2. **Ch. 11** (code generation and the trust boundary). Short; the material is
    already written in `VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md`.
3. **Ch. 12** (evaluation). Requires U8 resolved first.

**Phase 5 — framing (weeks 11–13).**

1. **Ch. 2** (foundations). Write it *late*, deliberately. Background written
    first always over-covers; background written after Chapters 3–10 contains
    exactly what those chapters used, and nothing else. Extract it by walking
    the drafted chapters and listing every concept used without definition.
2. **Ch. 13** (related work). Requires U2 resolved.
3. **Ch. 1** and **Ch. 14** and the **abstract**, in that order, last.
    Requires U1 and U3 resolved.
4. **Appendices**, generated where possible.

**Continuous.** Keep `shared/facts.toml`, `shared/snippets.toml` and
`shared/claims.toml` growing with each chapter rather than in a final pass;
`pixi run thesis-check` is what stops the text from outliving the formalization,
and it only helps if the entries exist.

**Two early risks worth retiring now.** U5 (the private solver fork) needs a
conversation with its author and has a long lead time. U1 (the title and
framing) gates Ch. 1, Ch. 14 and the abstract — three of the four things an
examiner reads first.

---

## 12. Visualization audit and figure supply

The figure situation is much better than a blank thesis suggests, and it has
one specific liability. Both are worth stating precisely, because they change
what the figure work actually *is*: curation and extraction, not authoring.

### 12.1 What already exists

**A. The Typst figure vocabulary — `thesis/lib/figures.typ` (30 primitives).**

| Primitive | Draws |
| --- | --- |
| `stage`, `flow`, `badge`, `proved-badge`/`trusted-badge`/`unproved-badge` | pipeline stages coloured by proof status |
| `ppoint`, `entry-node`, `result-node`, `intra-edge`, `call-edge` | CFG nodes and the two edge kinds |
| `unk`, `global-unk`, `dep-edge`, `side-edge`, `withdrawn-edge` | solver states as graphs, with stability colouring |
| `locale-node`, `instance-node`, `import-edge`, `sublocale-edge`, `interp-edge` | locale hierarchies with three distinguished edge kinds |
| `hasse` | lattice diagrams |
| `rhsbox` | boxed transfer-function definitions |
| `iteration-plot` | fixpoint iteration against `f x`, with widening and narrowing |
| `simulation` | commuting simulation squares |
| `annotation-grid` | program point × variable abstract-state tables |
| `algorithm` | pseudocode listings |
| `subfigures`, `chapter-numbering` | layout |

Backed by `lib/theme.typ` (a semantic palette: `proved`, `trusted`, `unproved`,
`stable`, `unstable`, `called`, `sign`, `ivl`, `mut`, …), `lib/math.typ`
(81 notation macros, already aligned to `docs/GLOSSARY.md`), and `lib/code.typ`
(Isabelle/VIMP/OCaml listings, ASCII-symbol decoding, entity references that
link to the rendered theory HTML).

**B. `content/03-gallery.typ` — 823 lines, 14 sections, one worked instance of
every figure kind.** It already covers: the pipeline with its trust boundary,
source/CFG/AST triptych, a Graphviz CFG laid out inline, transfer-function
right-hand sides, `valid_ltr` as four inference rules, Hasse diagrams plus a
Galois square, a widening/narrowing plot, solver-state Euler regions and graph,
a solver computation trace table, the `TD_side` algorithm, a locale hierarchy,
an instantiation matrix, a module graph, a verbatim theory snippet, a
`thm_oracles` table, a fixpoint-iteration plot, two simulation squares, an
annotation grid, an Isabelle symbol table, the two stack views
(standard vs activation-local), a Goblint/Voblint interface comparison, an
annotated analyzer output, a checked CLI-output listing, an evaluation bar
chart, and a size table.

**C. The generators the build already wires** (`thesis/README.md`): `diagraph`
renders Graphviz inline with no build step; `tools/locale_graph.ML` emits the
locale hierarchy from `Locale.pretty_locale_deps`; `class_deps` emits the type
class hierarchy; `thm_deps` emits what a theorem rests on; `thm_oracles` emits
the oracle audit; `isabelle build -g` emits the session graph;
`tools/claims.py` re-runs the CLI behind every output-quoting figure and fails
on a diff.

**D. `pages/` — the explainer, and this is the find.** `pages/index.html` is
3 800 lines with ~50 figure modules under `pages/figures/`. It is a complete
visual exposition of this thesis, already written, with headings that map
almost one-to-one onto the proposed chapters. **Every figure is inline SVG plus
CSS — 39 `<svg>` blocks and zero `<canvas>`.** They are vector, extractable,
and renderable by Typst's `image()` directly.

| Explainer figure | Section heading | Thesis home |
| --- | --- | --- |
| `gamma` | What an abstract value stands for | 2.2, 5.1 |
| `particles`, `runs` | Many runs in, one region per node out | 4.4 |
| `metro` | Five domains, five kinds of description | 10.1 |
| `reduce` | Four domains, one value: reduction | 10.6 |
| `source-morph`, `cfg` | Watch the compiler take a program apart | 3.6 |
| `eqs` | From a graph to equations to values | 7.1 |
| `trees` | What an equation is made of: strategy trees | 7.1, 8.1 |
| `loop` | Loops: widening and narrowing | 5.3, 8 |
| `call` | The life of a call | 7.3 |
| `context` | Context sensitivity: how many copies of a procedure | 7.5 |
| `cost` | The price of precision | 12.3 |
| `solver`, `td` | Globals: how contributions combine / update rules | 7.3, 8.3 |
| `recursion-spiral` | A call that never stops calling | 7.8, 14.3 |
| `trust`, `iceberg` | Where the proof starts and stops | 1.3, 11.4 |
| `timeline` | What a run is: source, graph, trace | 3.2, 4.3 |
| `chain`, `strata` | The proof chain: each set inside the next | 4, 9, 12 |
| `bridge` (“Take a pillar away”) | five facts hold the chain up; remove one and an honest-looking answer becomes a lie | **12.6** |
| `theorems` | The flagship theorems | 9.7 |
| `build` | From Isabelle to your browser tab | 11.1 |
| `align` | Voblint and Goblint, side by side | 12.7 |
| `island` | A small island in a large language | 14.2 |
| `zoom` | Zoom into one PROVED | 9.3, 12 |
| `bug`, `run`, `runs`, `graph`, `editor`, `guide` | supporting UI and worked-run figures | as needed |

(The full module list is `align bridge bug build call chain context cost editor
eqs gamma graph guide iceberg island loop metro particles recursion-spiral
reduce run runs solver source-morph strata td theorems timeline trees trust
zoom` — 31 modules. “What the theorems don't promise” is prose in the `limits`
*section*, not a figure module.)

`bridge` deserves special note: it is exactly the figure §12.6 needs
(*what does the formalization establish that testing would not*), and it is the
hardest figure in the thesis to invent from scratch. It already exists.

**E. Captured playground runs.** `docs/images/` holds six composed screenshots
and `scripts/capture_readme_figures.mjs` regenerates them: it serves `pages/`
and the wasm build itself, drives Chrome through Playwright, and tiles editor,
inspector and graph into one image. Every figure is a real run of the real
analyzer, reachable through the `#code=` link printed beneath it.

### 12.2 The liability: figure payloads are unchecked, and several are wrong

`pixi run thesis-refs` passes — 36 references resolve. It passes because the
gallery's figure *content* bypasses it. Identifiers inside a figure are written
as raw literals (`` `Constraint_System` ``) or hand-typed Isabelle blocks
(`isa(...)`), neither of which the checker can see. Only `isathm`/`isaconst`/
`isalocale`/`isatype`/`isasession` calls are resolved.

Verified defects in the current gallery, all in figure payloads:

| Figure | Defect | Reality |
| --- | --- | --- |
| `fig:modules` | six theory names that do not exist: `Constraint_System`, `DG_Framework`, `Ivl_Exec`, `Analyse_Dispatch`, `State_Report_GraphViz`; caption cites `code_identifier` | zero occurrences in `src/`; the export uses one `module_name Generated` block and no `code_identifier` at all |
| `fig:pipeline` | edge labelled `dg_gen_of` | zero occurrences; the generator is `routed_node_rhs` / `compiled_routed_eqs_for` |
| `fig:correspondence` | shows `locale dg_spec = fixes tf, route, read, publish` | `dg_spec` is a **record** with ten fields; `route` is a parameter of `routed_context_base_hetero`, not of `dg_spec`; reads/publishes go through `man_global`/`man_sideg` |
| `tab:instantiation` | Congruence marked ✗ for `dg_spec` / `sound_dg_spec_core`, captioned “not selectable on its own” | **false**: `Congruence_Analysis` is one of the five `analysis_domain` constructors and `Congruence_Analyses.thy` registers it at all three context policies |
| `fig:cfg-source`, `fig:ast` | `proc fac(n) { … }` | VIMP's keyword is `fun` (`manifests/vimp-grammar.yaml`, `keywords: fun: FUN`) |
| `fig:validltr` | constructors `Called`, `Resumed` | `Call`, `Resume`; the step rule appends through `extend` |
| `tab:oracles` | a `sorry` column with ✓ marks, reading as “has a sorry”; `source_sound` attributed to `Voblint_CLI` | no `sorry` anywhere in `src/`; `source_sound` is `unit_dg_analysis.source_sound` in `Voblint_Result` |
| `tab:size` | 105 theories / 56 800 lines (caption admits placeholders) | 223 theories / 61 255 lines (§2.1) |
| `fig:eval` | invented bar values | no such measurement exists yet (U8) |

None of this matters while the gallery is a gallery — the chapter is marked
for deletion before submission. It matters the moment a figure is copied into a
real chapter, which is exactly what the gallery invites. **Treat every gallery
payload as a placeholder, not as content.**

### 12.3 Figure inventory, after extraction and generator runs

> **Amended 2026-09-17, during drafting.** The "ready now" table below was
> written on the assumption that an extracted web figure could be a thesis
> figure. That assumption is wrong and the assessment above it over-valued the
> extraction. A figure drawn for a web page is persuasive, simplifies
> deliberately and is composed for a screen; a thesis figure is none of those.
> Eleven of the thirteen extracted figures were **composition references**, not
> content, and are no longer generated. Two remain — `strata` and `iceberg` —
> because they carry *measured data* (61,255 lines, 223 theories, 2,947 lemmas,
> 1,380 definitions, the session layering) that would otherwise be re-derived by
> hand and drift. Everything else the thesis needs is drawn in Typst, from the
> theories and the analyzer. Read the table as a list of *sources to draw from*,
> not as figures that ship.
>
> Evidence the assumption was wrong, beyond taste: three of thirteen needed
> per-figure intervention to render at all (a dropped state class, an unsupported
> `:not()` selector, a palette that turned five figures monochrome), and each was
> found only by rendering and looking. That is maintenance on artwork that was
> always going to be replaced.

Superseding the speculative gap list: this is what exists on disk now.

#### Ready now

Regenerate with `pixi run thesis-figures-write`; `pixi run thesis-figures`
fails on drift. All thirteen render in Typst and in `rsvg-convert`, in thesis
colours, with no linked assets.

| Figure | Output | Chapter | Source | Identifiers checked |
| --- | --- | --- | --- | --- |
| call protocol, six stages, Goblint names alongside | `svg/call-protocol.svg` | 7.3 | extracted | n/a (labels are prose) |
| equations read off the graph | `svg/equations-from-graph.svg` | 7.1 | extracted | n/a |
| the compiler taking a program apart | `svg/source-to-graph.svg` | 3.6 | extracted | n/a |
| a compiled procedure-aware CFG | `svg/run-cfg.svg` | 3.5 | extracted | n/a |
| where the proof starts and stops | `svg/trust-boundary.svg` | 1.3, 11.4 | extracted | n/a |
| Isabelle to binary and browser | `svg/export-lane.svg` | 11.1 | extracted | n/a |
| generated code above, proof below | `svg/iceberg.svg` | 11.4, 12.1 | extracted | n/a |
| **five facts hold the chain up** | `svg/proof-bridge.svg` | **12.6** | extracted | n/a |
| sessions as a metro map | `svg/sessions.svg` | 2.5, app. A | extracted | n/a |
| the formalization in cross-section | `svg/strata.svg` | 12.1 | extracted | n/a |
| VIMP as a small island in C | `svg/scope.svg` | 14.2 | extracted | n/a |
| the price of precision (nodes) | `svg/cost-nodes.svg` | 12.3 | extracted | n/a |
| the price of precision (checks) | `svg/cost-contexts.svg` | 12.3 | extracted | n/a |
| session graph, Pure to `Analysis_Certified` | `session_graph.png` | 2.5, app. A | generated (Isabelle presentation) | yes, by construction |
| locale hierarchy of the D/G spine | `dot/locale_deps.dot` | 6 | generated (`locale_graph.ML`) | yes, by construction |
| what the headline rests on | `thm_deps`, filtered | 9 | generated | yes, by construction |

#### Needs adaptation

| Figure | What is wrong | Work |
| --- | --- | --- |
| class hierarchy (`class_deps`) | the ML query returns the *transitive* supers, so 33 classes yield ~50 edges and an unreadable graph | transitive reduction, and a fragment filter down to `sound_domain`, `executable_domain`, `warrowing`, `widening`, `narrowing`, `bounded_warrowing`, `bounded_semilattice_sup_bot` |
| locale graph | four nodes come out isolated (`sound_domain`, `ltr_coverage`, `nonrelational_transfer`, `analysis_surface`) because they are reached by interpretation rather than inheritance | widen the fragment list, or draw interpretations as a second edge kind — `lib/figures.typ` already distinguishes three |
| `cost-nodes` / `cost-contexts` | the bar values are the explainer's, not measured here | re-derive from the regression runner (U8) and keep the extracted figure as the layout |
| `strata` | eleven session colours collapse to a depth ramp, which is right for print but drops the identity the web version carries | add a legend, or label each stratum |
| `iceberg`, `export-lane` | vendor logos dropped (Typst cannot nest an SVG) | fine as is; the shapes still read |

#### Actually missing

Nothing else has a source. These four must be drawn:

| Figure | Chapter | Payload comes from |
| --- | --- | --- |
| `cstep`'s three rules beside `valid_ltr`'s four clauses | 4.3 | `CFG_Exec.thy`, `LTR_Def.thy`; `curryst` |
| one `ltr` as a tree, with the `caller_of` chain | 4.2 | the running program; `syntree` or `fletcher` |
| the five obligations as commuting squares | 4.7 | `ltr_coverage` in `LTR_Abstract.thy`; `simulation` generalizes |
| `abs_state` ↔ `resolved_st_q` and one commuting transfer | 8.5 | `Exec_St_Transfer.thy`; `simulation` + `annotation-grid` |

Three further figures the explainer has and the thesis cannot lift, with the
reason recorded in the manifest: `gamma`, `strategy-tree` and `timeline-of-runs`
are empty `<svg>` shells filled by JavaScript; `contexts` and
`program-and-values` have markup but draw their nodes at run time, so a static
copy renders edges and labels with nothing at the vertices. Capture those with
`scripts/capture_readme_figures.mjs`, which already drives Chrome, or redraw
them. `gamma` and the strategy tree are better drawn natively anyway.

### 12.4 Recommended figure pipeline

Four channels, in decreasing order of trustworthiness. **Every figure in the
thesis should sit in one of them; a figure that sits in none is a figure that
will silently go stale.**

1. **Generated from a built session.** Locale graph, class graph, `thm_deps`,
   `thm_oracles`, session graph, theorem statements (`stmt`/`proved`),
   declaration snippets (`thy`). Already wired; mostly unused. *Action: run
   each one once and commit the output, so the figures start honest.*

2. **Generated from the analyzer.** CFGs, solved graphs, result tables,
   annotated sources, CLI listings — through `claims.toml` (checked by
   `pixi run thesis-claims`) and `--graph-snapshot`. *Action: add the spine
   program as a fixture and a figure source first; everything else follows.*

3. **Extracted from the explainer.** The ~39 inline SVGs. *Action: write
   `thesis/tools/explainer_svg.py` — a small extractor that pulls a named
   `<svg>` out of `pages/index.html` into
   `thesis/shared/generated/svg/<name>.svg`, records the source element id, and
   fails when the id disappears.* This gives the thesis its hardest figures
   (`bridge`, `strata`, `chain`, `iceberg`, `context`, `reduce`, `recursion-spiral`)
   for the cost of one script, keeps the web and print versions from diverging,
   and inherits the existing Biome lint on `pages/`.
   Two caveats, both checked. Interactive figures need one frame chosen, which
   is a content decision, not a technical one. And the palettes do **not**
   match: `lib/theme.typ` names colours by proof status (`proved`, `trusted`,
   `unproved`) and by domain (`sign`, `ivl`, `par`, `cong`), while `pages/`
   names them by UI role (`--primary`, `--success`, `--danger`, `--caution`,
   `--accent`). An extractor must therefore carry a fixed CSS-variable → Typst
   colour map and rewrite `fill`/`stroke` on the way out; otherwise the thesis
   inherits web colours that carry no proof-status meaning and lose it in
   greyscale. Build that map once, in the extractor, not per figure.

4. **Hand-drawn in `fletcher`/`cetz`/`curryst`.** Only for figures with no
   generable source: the pipeline diagram, the five obligations, the `ltr` tree,
   the rule correspondence, the executable/abstract square. *Rule for these:
   every identifier goes through `isathm`/`isaconst`/`isatype`/`isalocale`, so
   `thesis-refs` sees it.* That single discipline would have caught six of the
   nine defects in §12.2.

### 12.5 Two concrete tooling gaps worth closing early

**Extend `thesis-refs` to figure payloads.** Today a raw `` `Foo` `` inside a
diagram is invisible to it. Either lint for backtick-raw identifiers inside
`figure(...)` blocks and require an `isa*` wrapper, or accept that figures are
unchecked and mark them as such. The first is cheap and closes the whole class.

**Wire the counting script.** `tab:size` and `fig:eval` are the only two
figures whose captions already admit to being placeholders. Both are one script
away from being real, and both appear in the evaluation chapter an examiner
will read closely.

### 12.6 One warning

The explainer is persuasive, animated, and written for a general reader. A
thesis figure has a different job: it must be precise, static, and legible in
greyscale at print size. Do not import the explainer's *rhetoric* along with
its SVGs. Where a web figure simplifies — and several do, deliberately — the
thesis must either restore the detail or say in the caption what was dropped.
The `Activation_Seed` proxy (§10, U10) is the obvious case: any call-protocol
figure that draws the callee entry as an ordinary local unknown is drawing
Goblint, not Voblint.

---

## 13. Generator findings

Four generators the blueprint listed as wired-but-unused were run. Three work
and one claim was wrong.

**`isabelle build -g` does not emit a session graph.** In Isabelle2025-2 `-g`
selects a session *group*; `thesis/README.md` says otherwise and is wrong. The
session graph comes from the presentation build (`isabelle build -P`), which
`pixi run pages-site-build` already runs — `build/github-pages/Voblint/<session>/session_graph.pdf`
exists for all 28 sessions. `Voblint_CLI`'s is the useful one: Pure down to
`Analysis_Certified`, 28 nodes, readable at 62% width, no filtering needed.
Copied to `thesis/shared/generated/session_graph.png` and now used in place of
the hand-drawn module graph it contradicted.

**`thm_deps` on the headline is the best of the four.** 29 direct
dependencies, of which 24 are Pure/HOL plumbing and `arity_type_*` instances.
Filtered, the headline rests on exactly five project facts:

```text
run_voblint_certified_source_sound
  ├─ Compile_Invariants.wf_program_compile_input_exec_sound
  ├─ Compile_Invariants.prog_cfg_def
  ├─ Source_Activation_Sound.source_reaches_ltr_collect
  ├─ Analysis_Certified.run_voblint_AnalysedE
  └─ Analysis_Certified.run_voblint_sound_at
```

That is §3.1's reading of the theorem, confirmed by the machine rather than by
reading the proof: the executable well-formedness check, the compiled graph,
the source-to-collecting bridge, the answer eliminator, and the per-node
soundness. Useful, needs the Pure/HOL filter, belongs in Chapter 9.

**The caption must say what this is.** `Thm_Deps.thm_deps` returns the facts the
theorem's proof cites *directly*. It is a one-level view, not the proof: each of
those five rests on hundreds more, and the filtering removes a large transitive
structure rather than showing it to be absent. The figure's claim is "these are
the five facts the endpoint is assembled from", which is exactly what Chapter 9
needs, and it is not "the proof consists of five facts". Drawing two levels
would make the point without inviting the misreading, and is worth trying.

**`thm_oracles` gives the claim `tab:oracles` currently transcribes by hand.**
`Thm_Deps.all_oracles [@{thm run_voblint_certified_source_sound}]` returns
`[]`. Machine-checked evidence that the headline rests on no oracle and no
admitted subgoal, and one line to regenerate.

**`locale_graph.ML` works and confirms the spine.** Filtered to the framework
fragments it yields 17 nodes and 10 edges, and the edges are the proof spine:

```text
sound_dg_spec_core -> dg_ctx_activation_base -> routed_context_base_hetero
  -> dg_analysis_adapter -> routed_analysis_sound
routed_dg_pipeline -> routed_dg_analysis -> unit_dg_analysis
```

Two things this settles. §3's layering L4 → L6 → L9 is the real inheritance
chain, not an exposition convenience. And `unit_dg_analysis` really is below
`routed_dg_analysis`, which is the machine-checked form of "monovariant
analysis is an instance, not a special case" — the claim §6.1 uses to reject
the example-first structure.

**`class_deps` needs work before it is a figure.** `Sorts.super_classes`
returns the transitive closure, so 33 classes produce roughly 50 edges. The
content is right — `bounded_warrowing` sits on
`bounded_semilattice_sup_bot` + `widening` + `narrowing`, which is exactly what
the solver demands of a domain — but it needs transitive reduction first.

### Nothing here contradicts the recommended structure

The generated graphs agree with §3 and §7 everywhere they overlap. One small
correction to §2.2: `Deriving` feeds `Voblint_VIMP`, and `HOL-Computational_Algebra`
is an ancestor of `TD`, neither of which the hand-drawn session graph showed.

---

## 14. Web explainer → thesis content map

`pages/index.html` is not a marketing page. It is 3 800 lines of technically
precise exposition covering, in order, most of what Chapters 1–14 have to say,
and its quantitative claims are already regression-checked: the 59 fixtures in
`tests/regression/24-site-figures/` exist so that a change in the analyzer
cannot leave a figure on the site silently wrong. Treating it as a source of
figures only, as §12 did, undersells it.

The prose was checked against the current theories while building this map. It
is accurate — it names `pstep`, `cstep`, `valid_ltr`, `csim_step`,
`source_run_has_ltr`, `part_post_solution_of_solve_c`, `gamma_reader_eq_lookup`
and the five headline theorems correctly, and its statements of them match
`Analysis_Certified.thy`. Where a section simplifies it says so.

Format: web section → core idea → thesis destination → what to reuse → what to
re-verify.

### 14.1 The map

**`abstract-interpretation` — "What is abstract interpretation?"**
→ *A test runs a program on some inputs and watches what happens; abstract
interpretation computes with descriptions large enough to include every value a
real run could produce.*
→ **Ch. 1.1, Ch. 2.2, Ch. 9.3.**
→ **Reuse the prose almost directly** for the opening motivation, and the
DEAD/UNKNOWN distinction verbatim in spirit: *"DEAD says the analysis proved
unreachability, not merely that the point is unreachable."* That sentence
settles a distinction Chapter 9 has to make anyway and that `contextual_verdict`
encodes as a fourth value outside `check_result`.
→ Re-verify: the worked program's node numbering against a current compile.

**`values` — abstract values, five domains, reduction**
→ *What one abstract value stands for, and what four of them together say that
none says alone.*
→ **Ch. 5.1, Ch. 10.1, Ch. 10.6.**
→ **Reuse the concept**: the step-through of a reduction round is the right way
to present `refine_round` before any algebra. The figure is JS-built and must be
redrawn as a sequence (four component values, before and after each pass, to a
fixed point).
→ Re-verify: the component values against `Int_Refinement_Control.thy`.

**`solver` — graph → equations → values; the compiler walk; widening; strategy trees**
→ *One unknown per node, one term per incoming edge; a solver finds a value for
every unknown; below that, each right-hand side is a tree of reads and writes.*
→ **Ch. 3.6, Ch. 7.1, Ch. 8.1–8.2, Ch. 5.3.**
→ **Reuse the mental model and its order.** Chapter 7 is the heaviest chapter in
the plan and the one most likely to read as machinery; the site's progression —
graph, then equations, then the solver as a black box, then the tree one level
down — is the sequence that makes `routed_node_rhs` land. Its
`compile_proc` excerpt is already the real clause.
→ Re-verify: the excerpt against `VIMP_Proc_to_CFG.thy`; the post-solution
wording against `part_post_solution`.

**`settings` — the life of a call; contexts; the price of precision; globals rules**
→ *An analysis does not hard-code what a call does. It supplies `enter`, a
context policy, and `combine`; the framework wires them the same way for every
domain, and each wire carries its own soundness obligation.*
→ **Ch. 7.3, Ch. 7.5, Ch. 8.3, Ch. 12.3.**
→ **Reuse the framing, and reuse it hard.** That sentence is the thesis's own
claim C5 in one line. The call lifecycle presented as *one call stepped through*
rather than as eight definitions is what §7's figure list already asks for, and
`svg/call-protocol.svg` is the extracted figure. The "price of precision" node
counts are measured by the analyzer on the site and pinned by fixtures, so they
can be quoted.
→ Re-verify: nothing in the prose; the counts are already under test.

**`verified` — "What does 'verified' mean?" and the replayed Goblint bug**
→ *Analyzers are programs and programs have bugs; an analyzer bug reports PROVED
for a check real runs violate and nobody looks again.*
→ **Ch. 1.1, Ch. 12.6.**
→ **Reuse directly, and make this §12.6's centrepiece.** See §14.2.

**`semantics` — "What a run is: source, graph, trace"**
→ *Every theorem is about what a program really does, so "what it does" needs a
definition first. Voblint gives three, one per layer.*
→ **Ch. 3.2, Ch. 4.3.**
→ **Reuse the concept, and prefer it to the plan's current order.** §7 currently
introduces `pstep` in 3.2, `cstep` in 3.5 and `valid_ltr` in 4.3, three chapters
apart. The site introduces all three *together*, as three answers to one
question, and then says the proofs connect them one step at a time. That is
better, and it is what §9.2's missing figure (`cstep`'s rules beside
`valid_ltr`'s clauses) was reaching for. Recommendation: keep the definitions
where they are, but open §3.2 with the three-way statement so the reader knows
two more are coming.
→ Re-verify: nothing; `csim_step` and `source_run_has_ltr` are stated correctly.

**`chain` — "The proof chain: each set inside the next"**
→ *Soundness is a chain of set inclusions: the stores real runs have, the stores
the graph's traces reach, those traces split by context, what the solver's answer
concretizes to. Each link is its own theorem.*
→ **Ch. 4, Ch. 9.**
→ **Reuse the figure and the framing.** This is §3's proof spine stated for a
reader, and the nested-sets presentation is better than a layer diagram for
showing that precision is lost at every link and a store never is.
→ Re-verify: the link names against §3; `gamma_reader_eq_lookup` and
`part_post_solution_of_solve_c` are correct as cited.

**`theorems` — the five flagship theorems, with a zoom into one PROVED**
→ *Five theorems about `run_voblint`, the function the analyzer in your browser
calls.*
→ **Ch. 9.7–9.8.**
→ **Reuse the per-theorem "what it assumes / what it proves" split.** The site
states each theorem in prose beside its Isabelle statement, which is exactly the
presentation §7 asks for in 9.8. It also has `run_voblint_arithmetic_intra_safe`,
a corollary the blueprint's §3 spine omitted — verified present at
`Analysis_Certified.thy:290`.
→ Re-verify: nothing; statements match.

**`pipeline` — "From Isabelle to your browser tab"**
→ *The analyzer you run in the browser is not a reimplementation. Isabelle
exports the proved definitions as OCaml, the OCaml is compiled to WebAssembly,
and a background worker calls it.*
→ **Ch. 11.2–11.4.**
→ **Reuse almost verbatim**, with the verified/untrusted split made explicit.

**`goblint` — "Voblint and Goblint, side by side"**
→ *Voblint follows Goblint's architecture and simplifies wherever a proof would
have to model all of C.*
→ **Ch. 6.1, Ch. 12.7, Ch. 13.4.**
→ **Reuse the comparison structure**; the claim discipline is already the
register's ("a simplified, machine-checked semantic model … and not the exact
implementation").
→ Re-verify: every row against `docs/GOBLINT_ALIGNMENT_REGISTER.md`, which is
authoritative.

**`limits` — what Voblint cannot do**
→ *A proof is only as wide as its statement.*
→ **Ch. 1.5, Ch. 14.2.**
→ **Reuse directly.** Six of its points are the thesis's own limitations
verbatim: termination assumed, no completeness, REFUTED is not a counterexample,
the parser and toolchain trusted, the compiler proved in one direction only, and
no theorem about Goblint's OCaml.

**`further-reading`** → **Ch. 13.** Reuse the grouping; it is already organised
by the same areas as §4's literature map.

### 14.2 The replayed Goblint bug is the best evidence in the project

The `verified` section replays **goblint/analyzer #1161**: Goblint's congruence
domain read `c % 2` as the constant `1` for every `c` it knew to be odd, sign
included. In C, `%` truncates toward zero, so for `c ∈ {−5, −7}` every run gives
`−1`. Goblint therefore reported a check that every run violates as succeeding,
and the check every run satisfies as failing — *both verdicts backwards*.

This is checked here, not asserted. `tests/regression/24-site-figures/precision/04-goblint_1161_congruence_mod.vimp`
is Goblint's own regression test for the fix (`37-congruence/14-negative.c`)
transliterated into VIMP, and the `int` product answers `REFUTED` then `PROVED`
— confirmed by running it.

Why this matters for the thesis: §12.6 asks *what does the formalization
establish that testing would not*, and this is the most concrete answer the
project has. The contrast to draw is between two kinds of guarantee, not
between two kinds of engineering:

> A regression test catches one incorrect result on one program. A soundness
> proof discharges an obligation for every program the theorem's statement
> ranges over.

The honest claim is narrow and worth stating precisely:

> A real unsoundness in the same abstract domain, in a mature analyzer, of
> exactly the shape a soundness obligation rules out. Voblint's congruence
> domain cannot have this bug, because `congruence_arith`'s operations are
> proved against `gamma`, and an operation returning `1` where a concretized
> value is `−1` cannot discharge that obligation.

What must *not* be claimed: that Voblint would have found the bug (it analyzes a
different language and was written after the fix), that testing could not have
found it (Goblint's own test suite did, eventually), or anything about Goblint's
implementation. The claim is about where the obligation sits — in a proof
obligation discharged once, rather than in a test someone has to think to write.

### 14.3 What the site does *not* give the thesis

Three things, worth naming so nobody looks for them.

- **No formal content the theories lack.** Everything it says is downstream of
  `src/`. It is an exposition asset, not a source.
- **No related work.** `further-reading` is a reading list, not a comparison.
  Chapter 13 is unwritten either way.
- **No evaluation numbers beyond the figure fixtures.** The node counts and
  verdicts are pinned; there is no performance measurement anywhere (U8 stands).

### 14.4 Working rule

The site is a *prototype of the thesis's explanations*, and prototypes are kept
for what they got right, not copied wholesale. Two cautions, both from §12.6's
warning:

- The site is written for a general reader and simplifies deliberately. Chapter
  7 cannot draw the callee entry as an ordinary local unknown, however well that
  reads: it is a global proxy (`Activation_Seed`), and the register records that
  no operational equivalence to Goblint's fixpoint is claimed.
- Site prose is prose, not a checked artifact. Only its *numbers* are pinned, by
  the site-figure fixtures. Every identifier a sentence carries into the thesis
  goes through `isathm`/`isaconst`/`isatype`/`isalocale` so `thesis-refs` sees
  it — which is exactly how the gallery's five dead theory names were caught.

---

## 15. Definitional adequacy: what the theorems rest on

> **Added 2026-09-17, during drafting.** The frozen plan covered the *trust
> boundary* — which code is outside the proof — and not *definitional
> adequacy*, which is whether the definitions are the ones we mean. They are
> different questions and the second is the one a formalization cannot answer
> about itself. This section is a temporary plan; it will be replaced by written
> chapter text.

### 15.1 Three questions that are routinely conflated

| Question | Answered by | Where in the thesis |
| --- | --- | --- |
| Which code is not proved? | enumeration | Ch. 11.6 (trust boundary) |
| What does the theorem assume? | reading the statement | Ch. 9.8 (premises) |
| **Are the definitions the ones we mean?** | **argument and review only** | **missing — this section** |

The third cannot be discharged by a proof, because every proof is stated over
the definitions in question. It is settled by making the definitions small,
stating where they diverge from the thing being modelled, exhibiting
non-vacuity, and telling a reviewer where to look.

### 15.2 Where VIMP differs from C

Verified against `VIMP_Expr.thy` and `VIMP_Globals.thy`.

| | VIMP | C |
| --- | --- | --- |
| integers | mathematical, unbounded | `ikind`-sized; wraps or is undefined |
| `a / 0` | **defined as `0`** (`c_div`) | undefined behaviour |
| `a % 0` | **defined as `a`** (`c_mod`) | undefined behaviour |
| `/` rounding | truncates toward zero | the same, since C99 |
| `&&`, `\|\|` | both operands evaluated | short-circuits |
| uninitialised locals | an arbitrary integer | undefined behaviour |
| globals at entry | zero (`cinit_stores`) | zero |
| `main` | may not `return` explicitly | may |

Three of these need a sentence of consequence rather than a table row.

**Division is the sharpest.** VIMP *defines* what C leaves undefined, so a
`PROVED` verdict on a program that divides by zero is a true statement about
VIMP and says nothing whatever about the C program with the same text. The
arithmetic diagnostic exists to mitigate this, but it is a separate claim with
its own theorem (`run_voblint_arithmetic_safe`), not part of the check verdict.
This belongs in Chapter 1, not only in Chapter 3.

**Short-circuiting diverges in the report, not the semantics.** Because VIMP
expressions are total and pure, evaluating both operands of `&&` yields the same
*value* as short-circuiting; there is no semantic difference. But the arithmetic
diagnostic traverses both operands, so `x != 0 && 10 / x > 1` draws a divisor
warning where a C reader expects the guard to protect it.

**Arbitrary locals are more general than C, hence sound-safe.** C leaves an
uninitialised local undefined; VIMP admits any integer. The analyzer must
therefore handle a strictly larger set of initial states than C requires, which
can only cost precision.

### 15.3 What a reviewer must check, in order of what a mistake would cost

1. **`pstep` *is* the definition of VIMP.** Since the AFP IMP2 bridge was
   removed (2026-07-20), no external reference semantics cross-checks it.
   Everything rests on this and it should be stated outright rather than
   discovered. See §15.4.
2. **`valid_ltr`'s four rules against `cstep`'s three.** Does the trace
   semantics admit exactly the graph's runs? Too few and soundness is vacuous
   where it matters; too many and it is unprovable. Ch. 4's two figures exist to
   make this checkable side by side.
3. **The five `ltr_coverage` obligations.** They are proved *sufficient*. The
   reviewer's question is whether any one is *vacuous* for the shipped
   instances — particularly `TOTAL`, which is conditional on the claim itself.
4. **`config_terminates`.** The one analyzer-side premise, discharged per
   program by evaluation and proved for none.
5. **Non-vacuity.** Is a conclusion true because a set is empty? Not
   hypothetical here: the project has a recorded case where a conclusion was
   provably empty for seeded runs, and `Example_End_To_End_Certificate` exists
   precisely to witness that the headline is not.
6. **`checks_sound_at`.** Does `PROVED` mean what a report reader takes it to
   mean, and is it clear that `REFUTED` is not a verified counterexample?
7. **`wf_source_program`.** Every theorem assumes it. What does accepting fewer
   programs buy, and does it exclude anything interesting?
8. **`csim` is structural and not functional**, so the source-level theorems are
   existential in their node. Is that existential doing hidden work?
9. **`gammaDG` ignores its global argument** in `dg_analysis_adapter`, which is
   what makes the published table readable from the local unknown alone. A
   documented restriction that no current instance violates.

### 15.4 Should the AFP IMP2 bridge come back?

Investigated 2026-09-17 against `~/afp/thys/IMP2` and
`docs/history/AFP_IMP2_REUSE_DECISION.md`. **Recommendation: no, not as the
semantic anchor. Possibly yes as one validation artifact in Ch. 12.**

*What the old bridge was.* The June decision adopted a one-way embedding
`to_imp2` plus a backward simulation, so that soundness could be restated
against IMP2's big-step semantics. It was built, then deleted on 2026-07-20 in
an undocumented commit. The decision document still reads as adopted.

*What IMP2 actually provides.* `val = int => pval`, so every variable is an
array and a scalar is index 0. `PCall pname` takes **no arguments and returns
no value**; parameters travel by naming convention. `SCOPE c` saves the caller's
locals into the command (`c ;; Assign_Locals s`) and runs with fresh ones —
structurally the same trick as VIMP's `Restore`, which is encouraging.
`is_local` is a syntactic classifier on names, close in spirit to VIMP's `gs`.
Operators are reflected as opaque HOL functions, which is why the embedding must
stay one-way. Both a big-step and a small-step semantics exist.

*Three arguments against re-anchoring.*

- **It would cover strictly fewer executions than the current theorem.**
  `run_voblint_certified_source_sound` quantifies over *any finite prefix* of a
  run, terminating or not. IMP2's big-step relates only complete terminating
  runs, so anchoring through it weakens the reachable-state claim rather than
  strengthening it. Bridging to `small_steps` instead avoids that, but the thing
  that makes IMP2 *recognised* is its VCG, and the VCG is big-step.
- **The nondeterministic fragment is not expressible.** IMP2's `small_step` is a
  function; its semantics is deterministic. VIMP's `__voblint_nondet_int()`
  makes `pstep` genuinely nondeterministic, and **63 of the 283 regression
  fixtures use it, 7 of them in `soundness/`** — the category that exists to
  show `UNKNOWN` is the only sound answer. An IMP2 anchor would exclude exactly
  the cases that demonstrate the analyzer is not overclaiming.
- **It trades one adequacy question for two.** Today a reviewer must believe
  `pstep`. With a bridge they must believe the translation *and* the backward
  simulation — and translating VIMP's `Call dst p args` into IMP2's
  parameterless `PCall` plus a naming convention is exactly the kind of encoding
  where a mistake hides. The net adequacy gain is not obvious, and the cost is
  larger than in June: VIMP has since gained explicit `return`, `Restore` and
  `Unwind`, the `gs` classifier threaded throughout, first-class checks, and
  special calls. The deleted bridge was 456 lines against a simpler language.

*What is worth doing instead, in increasing cost:*

1. **State the anchor honestly** (§15.3 item 1), in Ch. 3 and again in Ch. 9. One
   paragraph, no proof work.
2. **Cheap internal adequacy evidence.** Determinism of `pstep` modulo the
   special-call nondeterminism; a progress lemma for well-formed configurations;
   an executable `pstep` interpreter run against the regression corpus, so the
   semantics is exercised rather than only reasoned about. None needs a second
   language.
3. **One triangulation artifact for Ch. 12.** A single scalar, deterministic,
   check-free program carried through both worlds: IMP2's VCG proves the exact
   postcondition, the analyzer proves the envelope, and the two are shown
   consistent. This is what the deleted `IMP2_VCG_Example` did, and it is the
   defensible version of the idea — a *demonstration that the two paradigms
   agree on one program*, explicitly not the semantic foundation. Scope it as
   optional, and only after Chapters 5 to 9 exist.

*What would change the recommendation.* If arrays are ever added to VIMP,
IMP2's array-valued state stops being an impedance mismatch and becomes the
reason to adopt it, and the question should be reopened at that point rather
than now.
