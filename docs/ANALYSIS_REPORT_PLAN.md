# Analysis report and solver boundary refactor

Branch `refactor/analysis-report`, from `origin/main`. The thesis and the site follow on
`writing` after the merge.

## Goal

The public soundness theorems should speak about one object, the analysis report
`res` that `analyse_program` returns, and should need no termination premise. Three
facts carry the whole guarantee:

| Fact | Statement | Uses |
| --- | --- | --- |
| `analyse_program_covers` | `𝒞 v ⊆ ⟦res⟧ᵥ` | compiler, traces, routing, equations, solver |
| `analysis_report_checks_sound` | `⟦res⟧ᵥ ⊆ 𝒱(res, v)` | the report alone, no executions |
| `analysis_report_dead` | `DEAD res v ⟹ ⟦res⟧ᵥ = ∅` | the report alone |

`PROVED` and `REFUTED` constrain the stores inside `⟦res⟧ᵥ`; `DEAD` says there are
none. With the first fact, `DEAD` gives `𝒞 v ⊆ ⟦res⟧ᵥ = ∅`. The source-level theorem
keeps its existential node: a finite `pstep` run reaches some `v` related by `csim`,
and its store lies in `𝒞 v`. No set of "source stores at `v`" is introduced, since
the simulation is not functional.

The third fact is one direction only. A `Lifted` entry passed the product's
emptiness test, which is sound and incomplete: `mcp_empty_v` reports a state empty
when one active analysis does, so a state with Interval `x = 2` and Parity `x odd`
passes it although it concretizes to no store. `⟦res⟧ᵥ = ∅` therefore does not
imply `DEAD res v`, and `UNKNOWN` does not imply `⟦res⟧ᵥ ≠ ∅`.

## Why

- `run_voblint as rule ctx p = Analysed res` does not imply termination in HOL:
  `analyse_program` calls the total specification `solve`, whose value outside its
  domain is unspecified. Hence the premise `config_terminates`. The vendored
  executable form `solve_c` is a `partial_function (option)` that is `None` exactly
  outside the domain, and `solve_dom_of_solve_c` bridges it.
- The two current conclusions read different objects. `checks_sound_at` reads the
  printed result; `analysis_result_covers` reaches past it into the internal table
  `mcp_rule.result …`, because the report's `res_states` hold display projections
  (`mcp_render`), not the semantic state.
- `analysis_result`, `config_terminates` and `analysis_result_covers` each repeat the
  same three-way split over the context policy (`mcp_rule`, `mcp_es_rule`,
  `mcp_cs_rule`).
- The generated carrier spreads one analysis over parallel functions
  (`local_spec_of`, `part_gamma`, `part_empty`, `val_answer`, `field_of`, …), each
  with its own split over `analysis_domain`.

## Target architecture

```text
manifests/analyses.yaml
      │  generator
      ▼
registration_of :: analysis_domain ⇒ registration       (one split over analyses)
      │
analysis_config  (analyses, globals rule, context policy)
      │
      ▼
analysis_report_of config p                              (one split over the policy)
      │  per policy: a dg_analysis interpretation, solved by solve_c
      ▼
('c, mcp_val) solved_run      solved_table + shared + seeds + steps + successors
      │  report_of: finite rows indexed by context number
      ▼
analysis_report               semantic, exported; theorems read only this
      │
      ├── ⟦res⟧ᵥ, 𝒱(res, v), PROVED / REFUTED / UNKNOWN / DEAD
      │
══════ generated API boundary: analyse_program, report selectors, projections ══════
      │
      ▼
OCaml / browser adapters
      ├── render_report (an exported projection: mcp_render, string_of_abstract_value)
      └── text, JSON, HTML, graphs
```

Rendering is a projection the adapters apply to the report after the call. It is
defined in Isabelle only so that generated code computes it, and no theorem reads
it. `run_voblint` (analysis plus rendering in one call) stays until phase 8 as a
compatibility shim and is then deleted; `analyse_program` is the exported
operation.

Proofs flow downward only: solver, routing and table facts are consumed by the
report theorems, and nothing above the report reads them.

| Theory | Owns |
| --- | --- |
| `Framework/Result/Analysis_Result` (renamed `Solved_Table`) | `solved_table`, coverage metadata, `lookup_table` |
| `Analyses/Shared/Result/DG_Analysis` | `solved_run`, `solved_run_of`, `run`, `solve_c_run` |
| `Solver/Solver_Trace` | `solve_c_traced` |
| `CLI/generated/MCP_Carrier` | `registration_of` and its accessors |
| `CLI/Analysis_Run` | `analysis_config`, `analysis_report`, the one policy dispatch, `analyse_program` |
| `CLI/Analysis_Render` (new) | `run_result` (rendered), `render_report`, the `run_voblint` shim |
| `CLI/Analysis_Report` (new) | `⟦res⟧ᵥ`, `𝒱`, CAPS queries, the three facts |
| `CLI/Analysis_Certified` | source-level corollaries |

## Target types

```isabelle
datatype analysis_config = Analysis_Config
  (config_analyses: "analysis_domain list")
  (config_rule: globals_rule)
  (config_context: context_mode)

record ('c, 'v) solved_run =
  run_table :: "('c, 'v) solved_table"
  run_shared :: "'v lifted"
  run_seed :: "pname ⇒ 'c ⇒ 'v lifted"
  run_step :: "pp ⇒ 'c ⇒ edge_action ⇒ 'v lifted"
  run_succ :: "cfg_node ⇒ 'c ⇒ call_action ⇒ pname ⇒ 'c option"

record 's result_state =            (* 's: semantic or rendered state *)
  state_point :: pp
  state_context :: nat               (* index into the context list *)
  state_value :: "'s lifted"
  state_checks, state_diagnostics    (* unchanged *)
  state_steps :: "(pp × 's lifted) list"

datatype report_context =
  Report_Unit | Report_Entry mcp_ctx | Report_Call_String "pp list"

record analysis_report =
  report_config :: analysis_config
  report_vars :: "vname list"
  report_cfg :: cfg
  report_contexts :: "report_context list"
  report_states :: "mcp_val result_state list"
  report_routes :: "call_route list"
  report_checks :: "result_check list"
  report_globals :: "mcp_val result_global list"
  report_diagnostics :: "arithmetic_diagnostic list"

record 'v run_result =              (* rendered, unchanged for OCaml *)
  res_contexts :: "'v analysis_context list"
  res_states :: "'v analysis_view result_state list"
  res_globals :: "'v analysis_view result_global list"
  res_cfg, res_routes, res_checks, res_diagnostics

datatype 'r analysis_answer =
  Invalid_Activation | Malformed_Program | No_Answer | Analysed 'r
```

`analysis_config` is a datatype: a record would export as
`analysis_config_ext` with a trailing unit field, which every OCaml caller would
have to build. The selectors give the record reading in Isabelle.

Contexts are erased from the semantics. A row carries a context index into
`report_contexts`, whose entries keep each policy's own context as a tagged semantic
value (`mcp_ctx` for entry states, the call string for call strings). No theorem
reads them; rendering maps them to `analysis_context`. So one report type serves all
three policies, and the report holds no rendered value.

The Int modes are one surface constructor over three registrations:
`Int_Analysis Refine_Fixpoint`, `Refine_Once` and `Refine_Never` each keep their own
carrier slot, which is why two modes may run together. Collapsing them to one slot
would change which configurations are valid.

## Semantic definitions

Write `σ ∈ rows(res, v)` for the `state_value` of a row of `res_states res` at
point `v`, and `γ = mcp_gamma_v (activation (config_analyses (report_config res)))`.

```text
⟦res⟧ᵥ      = ⋃ { γ⊥ σ | σ ∈ rows(res, v) }
Checks(res,v) = the rows of res_checks res with check_point = v
𝒱(res, v)   = { s | ∀ chk ∈ Checks(res, v).
                     (verdict = PROVED  ⟶ truthy ⟦e_chk⟧ s)
                   ∧ (verdict = REFUTED ⟶ ¬ truthy ⟦e_chk⟧ s) }
PROVED res v e  ⟷ ∃ chk ∈ Checks(res, v). e_chk = e ∧ verdict = PROVED
REFUTED res v e ⟷ ∃ chk ∈ Checks(res, v). e_chk = e ∧ verdict = REFUTED
UNKNOWN res v e ⟷ ∃ chk ∈ Checks(res, v). e_chk = e ∧ verdict = UNKNOWN
DEAD res v      ⟷ ∀ σ ∈ rows(res, v). σ = Bot
```

`UNKNOWN` and `DEAD` impose no per-store condition in `𝒱`.

`DEAD` is a property of the program point, not of a condition, hence its arity. A
check row's `Dead` verdict is one presentation of it: the row is `Dead` exactly when
every context at its point is `Bot`, so it implies `DEAD res v`. `DEAD` is
structural on purpose. The rows are canonical lifted values: the report's table
collapses a state the emptiness test rejects to `Bot`, and `Bot` denotes no store, so
`DEAD res v ⟹ ⟦res⟧ᵥ = ∅` is nearly definitional. The converse would need the
incomplete test to be exact, so `DEAD` does not rerun it.

`⟦res⟧ᵥ` is the constant `report_sem` with mixfix `⟦_⟧⇩_`. Overloading it under a
`gamma_at` constant waits for a second representation; with one instance it buys
nothing.

## Target theorems

```text
analyse_program_covers:        analyse_program config p = Analysed res
                               ⟹ 𝒞 v ⊆ ⟦res⟧ᵥ
analysis_report_checks_sound:  ⟦res⟧ᵥ ⊆ 𝒱(res, v)
analysis_report_proved:        PROVED res v e ⟹ s ∈ ⟦res⟧ᵥ ⟹ truthy ⟦e⟧ s
analysis_report_refuted:       REFUTED res v e ⟹ s ∈ ⟦res⟧ᵥ ⟹ ¬ truthy ⟦e⟧ s
analysis_report_dead:          DEAD res v ⟹ ⟦res⟧ᵥ = ∅
analysis_report_unknown:       UNKNOWN res v e ⟹ ¬ DEAD res v          (lemma)

analyse_program_source_sound:
  s0 ∈ cinit_stores 𝒢
  𝒢, Π ⊢ (main_body Π, s0, []) →p* (c, s, frs)
  analyse_program config p = Analysed res
  ⟹ ∃ v stk. Π, g ⊢ (c, s, frs) ≈ (v, s, stk) ∧ s ∈ 𝒞 v ∧ s ∈ ⟦res⟧ᵥ
analyse_program_check_sound, analyse_program_dead_unreached,
analyse_program_arithmetic_safe: the existing corollaries, restated over res.
```

`analyse_program_covers` needs the run that built the report; the
`analysis_report_*` facts read the report alone. `analysis_report_unknown` is a
structural lemma kept at the user's request, not a semantic guarantee: it says the
report makes no unreachability claim at an `UNKNOWN` check. Termination is internal: `Analysed res` implies the policy's
`terminates`, through `solve_c_run`.

## Migration

| Old | New | Fate |
| --- | --- | --- |
| `Int_Analysis`, `Int_Once_Analysis`, `Int_Never_Analysis` | `Int_Analysis refine_mode` | done |
| loose `as rule ctx` | `analysis_config` | done |
| `result_with_globals` (5-tuple) | `solved_run` record, `solved_run_of`, `run` | replace |
| `('ctx, 'a) analysis_result` | `solved_table` | rename |
| `result_unknowns`, `result_at` | `covered_keys`, `table_at` | rename |
| `lookup_context`, `lookup_context_result`, `contexts_at` | `lookup_table`, `lookup_coverage`, `table_contexts` | rename, internal |
| `analysis_surface` | report projections | absorb or delete |
| `analysis_result` (CLI, 3-way) | `analysis_report_of` | replace |
| `config_terminates` premise | `solve_c_run` | internal |
| `analysis_result_covers`, `table_covers` | `s ∈ ⟦res⟧ᵥ` | retire publicly |
| `checks_sound_at` | `𝒱(res, v)` | retire publicly |
| `run_voblint_sound_at`, `run_voblint_certified_source_sound` | report theorems, `analyse_program_source_sound` | replace |
| `sound_table` | `covered_table` + `sound_classifier` | split |
| parallel carrier functions | `registration_of` | replace |

## Done when

These are grep targets on `src/` outside the theory that owns each name:

- no `mcp_rule.result`, `mcp_es_rule.result`, `mcp_cs_rule.result`,
  `result_with_globals`, `table_covers`, `checks_sound_at`,
  `analysis_result_covers`, `gamma_reader_eq_lookup` above `Analysis_Report`;
- no `config_terminates` premise in any public theorem;
- `Ctx_None`, `Ctx_EntryState`, `Ctx_CallString` split only in
  `analysis_report_of` (and its traced code equation);
- `Sign_Analysis`, `Interval_Analysis`, … split only in `registration_of`, apart
  from generated exhaustiveness lemmas; consumers use its selectors, and the old
  per-capability functions are gone rather than kept as accessors;
- no `run_result`, `mcp_render` or `string_of_abstract_value` in
  `Analysis_Run` or `Analysis_Report`;
- no `run_voblint`.

## Invariants

- After `analysis_config` is resolved, no theory case-splits on an analysis kind,
  context policy, refinement mode or update rule.
- After a solve becomes an `analysis_report`, no public theorem mentions solver
  tables, context representations or rendering projections.
- One canonical API per concept: concretization through `γ`/`⟦·⟧` (with `⟦res⟧ᵥ`
  as the located form), solved data through `solved_table`, analyzer output through
  `analysis_report`, verdict truth through `𝒱(res, v)` and the CAPS queries.
- CLI text, JSON and the verbose solver trace stay byte-identical (`golden-check`).
- Each phase ends with the batch build, the codegen regression, the CLI corpus and
  the golden diff green.

## Phases and proof obligations

0. **Guardrails.** Golden output for the corpus. Done.
1. **Typed configuration.** `Int_Analysis refine_mode`, `analysis_config`,
   `valid_config` (non-empty, distinct). Done.
2. **Solver boundary and solved run.**
   - `certified_solver` gains `solve_of_solve_c: solve_c eqs x = Some sol ⟹ solve eqs x = sol`,
     discharged from TD's `solve_code_equation`.
   - `solved_run_of 𝒢 p sol`, `run 𝒢 p = solved_run_of 𝒢 p (solution 𝒢 p)`;
     obligations `run_table (run 𝒢 p) = result 𝒢 p`, `run_succ (run 𝒢 p) = live_succ 𝒢 p`.
   - `solve_c_run`: `solve_c (equations 𝒢 p) (root_query p) = Some sol ⟹ terminates 𝒢 p ∧ solved_run_of 𝒢 p sol = run 𝒢 p`.
   - `solve_c_traced`, equal to `solve_c`, so a code equation calling the solver
     directly keeps the trace's start and stop events.
3. **Semantic report and one dispatch.**
   - `report_of` builds the semantic report from a `solved_run` (the old
     `run_result_of` without `render`); `result_state` and `result_global` gain the
     state parameter.
   - `analysis_report_of config p :: analysis_report option`, the one split, each
     branch `map_option (… solved_run_of …) (solve_c …)`.
   - `analyse_program`: `None` becomes `No_Answer`. In `Analysis_Render`,
     `render_report` applies `mcp_render` and `string_of_abstract_value`, and the shim
     `run_voblint = map_analysis_answer render_report ∘ analyse_program`.
   - Obligations: per policy, `analysis_report_of config p = Some res` implies the
     policy's `terminates` and `res` is built from `run`; the rendered output equals
     the old `map_run_result string_of_abstract_value (analysis_result …)` (checked
     by the golden diff); row values are `lookup_table` of the run's table.
4. **Report theorems.** The definitions and theorems above, in
   `CLI/Analysis_Report`; `Analysis_Certified` restated over `res`; examples and
   OCaml adapted.
5. **Solved table rename.** Mechanical: the renames in the migration table, one
   commit. It lands after the report so the report theories are renamed by the same
   pass rather than written twice.
6. **One registration per analysis.** Generator emits `registration_of` and its
   record; consumers move to the selectors and the old per-capability functions
   are deleted. During migration each old function is proved equal to its selector
   (by `cases a rule: analysis_domain_cases`, generated), then removed.
7. **Contracts and classification.**
   - Split `sound_table` into `covered_table` and `sound_classifier`.
   - One contextual classification helper shared by the check column and
     `arithmetic_diagnostics`; arithmetic keeps its own presentation policy
     (proved and dead emit nothing, refuted an error, unknown a warning).
   - Absorb `analysis_surface` into report projections, or delete what has no
     consumer.
   - `sound_empty` / `exact_empty` and a representation locale, only where an
     inventory shows repeated proofs. Candidates: `is_empty_state`, `val_empty`,
     `mcp_empty_v` (sound); `default_st_to_fun`, `mcp_rd` (readbacks).
8. **Export and docs.** Export `analyse_program`, the report selectors and
   `render_report`; the adapters call them in sequence and handle `No_Answer`;
   delete `run_voblint`. Docs
   that name the retired constants (`docs/CHECK_ARCHITECTURE.md`,
   `docs/RUN_VOBLINT_INTERFACE.md`, `src/Executable_Surface/CLI/README.md`).
9. **Consumers, on `writing` after the merge.** Thesis chapters 9, 10 and 12, the
   README, the notation table, the site's theorem cards, metro map and alignment
   rows.

Out of scope: replacing the fixed generated MCP product with a carrier keyed by
analysis instance. It would remove the slot lenses and per-analysis dispatch,
but it changes the core of MCP composition and needs its own design.

## Risks

- Phase 3 changes the exported result type; OCaml consumers that name
  `run_result_ext` (`cli/result/context_graph.ml`) follow.
- Phase 5 touches every framework theory that names the table; it is mechanical
  but wide, and runs as host edits verified by batch build.
- Byte-identical output constrains phases 3 and 8; the golden diff makes it
  checkable.
