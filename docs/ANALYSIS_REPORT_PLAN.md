# Analysis report and solver boundary refactor

Branch `refactor/analysis-report`, from `origin/main`. The thesis and the site follow on
`writing` after the merge.

## Goal

The public soundness theorems should speak about one object, the analysis report
`res` that `run_voblint` returns, and should need no termination premise. Three
facts carry the whole guarantee:

| Fact | Statement | Uses |
| --- | --- | --- |
| `run_voblint_covers` | `𝒞 v ⊆ ⟦res⟧ᵥ` | compiler, traces, routing, equations, solver |
| `analysis_report_verdicts_sound` | `⟦res⟧ᵥ ⊆ 𝒱(res, v)` | the report alone, no executions |
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
  `run_voblint` calls the total specification `solve`, whose value outside its
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
══════ generated API boundary: run_voblint, report selectors, projections ══════
      │
      ▼
OCaml / browser adapters
      ├── render_report (an exported projection: mcp_render, string_of_abstract_value)
      └── text, JSON, HTML, graphs
```

Rendering is a projection the adapters apply to the report after the call. It is
defined in Isabelle only so that generated code computes it, and no theorem reads
it. `run_voblint` keeps its name and becomes the semantic operation: it returns
the report, and the adapters call `render_report` on it. No other public name for
the analysis exists.

Proofs flow downward only: solver, routing and table facts are consumed by the
report theorems, and nothing above the report reads them.

| Theory | Owns |
| --- | --- |
| `Framework/Result/Analysis_Result` (renamed `Solved_Table`) | `solved_table`, coverage metadata, `lookup_table` |
| `Analyses/Shared/Result/DG_Analysis` | `solved_run`, `solved_run_of`, `run`, `solve_c_run` |
| `Solver/Solver_Trace` | `solve_c_traced` |
| `CLI/generated/MCP_Carrier` | `registration_of` and its accessors |
| `CLI/Analysis_Run` | `analysis_config`, `analysis_report`, the one policy dispatch, `run_voblint` |
| `CLI/Analysis_Render` (new) | `run_result` (rendered), `render_report` |
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
run_voblint_covers:        run_voblint config p = Analysed res
                               ⟹ 𝒞 v ⊆ ⟦res⟧ᵥ
analysis_report_verdicts_sound:  ⟦res⟧ᵥ ⊆ 𝒱(res, v)
analysis_report_proved:        PROVED res v e ⟹ s ∈ ⟦res⟧ᵥ ⟹ truthy ⟦e⟧ s
analysis_report_refuted:       REFUTED res v e ⟹ s ∈ ⟦res⟧ᵥ ⟹ ¬ truthy ⟦e⟧ s
analysis_report_dead:          DEAD res v ⟹ ⟦res⟧ᵥ = ∅
analysis_report_unknown:       UNKNOWN res v e ⟹ ¬ DEAD res v          (lemma)

run_voblint_source_sound:
  s0 ∈ cinit_stores 𝒢
  𝒢, Π ⊢ (main_body Π, s0, []) →p* (c, s, frs)
  run_voblint config p = Analysed res
  ⟹ ∃ v stk. Π, g ⊢ (c, s, frs) ≈ (v, s, stk)
             ∧ s ∈ 𝒞 v ∧ s ∈ ⟦res⟧ᵥ ∧ s ∈ 𝒱(res, v)
run_voblint_check_sound, run_voblint_dead_unreached,
run_voblint_arithmetic_safe: the existing corollaries, restated over res.
```

Below the point where contexts are erased, one theorem per policy states the full
chain for a source run: a valid activation trace carrying some context `c`, and
`s ∈ 𝒜(v, c) ⊆ ⋃c'. 𝒜(v, c') = 𝒞 v ⊆ ⟦res⟧ᵥ ⊆ 𝒱(res, v)`. It composes
`source_run_has_activation_trace`, `node_collect_eq_Union_activation_collect` and
the report facts; its value is stating the whole spine in one checked statement.
The context-erased theorem above is the public one.

`run_voblint_covers` needs the run that built the report; the
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
| `run_voblint_sound_at`, `run_voblint_certified_source_sound` | report theorems, `run_voblint_source_sound` | replace |
| `sound_table` | `covered_table` + `sound_classifier` | split |
| parallel carrier functions | `registration_of` | replace |

## Done when

These are grep targets on `src/` outside the theory that owns each name:

- no `mcp_rule.result`, `mcp_es_rule.result`, `mcp_cs_rule.result`,
  `result_with_globals`, `table_covers`, `checks_sound_at`,
  `analysis_result_covers`, `gamma_reader_eq_lookup` above `Analysis_Report`;
- no `config_terminates` premise in any public theorem;
- exactly one executable dispatch on the context policy, `analysis_report_of`
  (its traced code equation restates the same three branches), and one proof-side
  elimination of it, `analysis_report_of_sound`; the per-policy semantic spine
  theorems name a policy in their statements and do not dispatch;
- `Sign_Analysis`, `Interval_Analysis`, … split at runtime only in
  `registration_of`; consumers use its selectors, and the old per-capability
  functions are gone rather than kept as accessors. The proof-only
  concretizations (`part_gamma`, `val_gamma`) and `val_empty` stay functions,
  since the exported code builds the record and a record field must be executable;
- no `run_result`, `mcp_render` or `string_of_abstract_value` in
  `Analysis_Run` or `Analysis_Report`;
- no `analyse_program`; OCaml reaches the generated core only through the
  handwritten `Voblint` facade.

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
   - `run_voblint`: `None` becomes `No_Answer`. In `Analysis_Render`,
     `render_report` applies `mcp_render` and `string_of_abstract_value`; the
     adapters call `run_voblint` and then `render_report`.
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
8. **Export and docs.** Export `run_voblint` and `render_report`; the adapters
   handle `No_Answer`. The report is an opaque token to OCaml: its selectors are not
   exported, and every reader goes through the `render_report` projection, so no
   OCaml code depends on the report's representation. The generated module becomes
   `Voblint_Generated`, and a handwritten facade `cli/voblint.ml` (module `Voblint`)
   re-exposes the export unchanged (its signature is the export's root list). The
   native entry moves to `cli/entry/voblint_main.ml` with dune
   `public_name voblint`, which frees the module name. Consumers (parser, printer,
   CLI, web entry, regression and build scripts) name `Voblint`, not the generated
   module. The native and
   browser entries stay separate executables (subprocess containment and files on one
   side, the JavaScript API and worker messages on the other), but share one module,
   `cli/result/analysis_request.ml`: the analysis, globals, context and refinement
   names in both directions, `resolve`, which checks a whole request (unknown
   names, a refinement without int, a narrow bound without its rule, a call-string
   depth) with typed errors each entry words itself, and `analyse` wrapping
   `run_voblint` and `render_report`. Docs
   that name the retired constants (`docs/CHECK_ARCHITECTURE.md`,
   `docs/RUN_VOBLINT_INTERFACE.md`, `src/Executable_Surface/CLI/README.md`).
8a. **A carrier-specialized generated-code boundary.** Each policy branch of
   `analysis_report_of` instantiates the generic solver at the MCP product, so the
   generated OCaml rebuilds the product's `equal`, `semilattice_sup`,
   `bounded_semilattice_sup_bot` and `warrowing` dictionaries inline, once per branch.
   Give each policy one concrete constant (`solve_unit`, `solve_entry`,
   `solve_call_string k`) whose type fixes the carrier, with a code equation that
   unfolds to the generic solver once; `analysis_report_of` calls those. The proofs
   keep the type classes; only the export boundary is specialised. Measure the
   generated file before and after. A record for the nested product is a separate
   readability question and does not remove the dictionaries.
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

## Status at the end of the first PR

Done and verified (batch build of `Voblint_Examples`, codegen regression, golden
diff of all 322 corpus fixtures: text, JSON, graph snapshot and verbose trace):

- phases 0 to 4: typed configuration, `Int_Analysis refine_mode`, the solver
  boundary (`solve_of_solve_c`, `solved_run`, `solve_c_run`, `solve_c_traced`), the
  semantic `analysis_report`, the one policy dispatch `analysis_report_of`, and the
  report theorems with no termination premise;
- the per-policy semantic spine (`run_voblint_unit_chain`,
  `run_voblint_entry_state_chain`, `run_voblint_call_string_chain`);
- an injective entry-state context key (`mcp_ctx_key`) and the listing lemmas
  (`ordered_by_key_set`, `report_states_at_report_of`), which the covering proof needs;
- phase 8 in part: `render_report` as the adapters' projection, the shared
  `cli/result/analysis_request.ml`, and phase 8a, the carrier-specialized boundary
  (`mcp_equations`, `mcp_solve_c`, `mcp_run_of`);
- the site's theorem cards, the README and the docs that named the retired theorems.

Phase 5, the `solved_table` rename, landed in the second stacked PR.
`well_formed_report` (index ranges, unique rows, row verdicts from the row's own
state, and with consistency the aggregate column from the rows) landed in the third,
with `run_voblint_well_formed`.
Phase 6, `registration_of` and its `analysis_registration` record, landed in the
fourth. Phase 7 landed in the fifth: `sound_table` is `covered_table` (the table's
obligation, one lemma per policy) plus `sound_classifier` (proved once,
`mcp_sound_classifier`), and `point_verdict` is the one aggregation of a condition
over a point's contexts, read by the check column and the arithmetic diagnostics
alike. `analysis_surface` stays: the per-domain registrations' `state_at` and
`report` are its readings, and the domain examples and the entry-state lemmas in
`DG_Live_Unknowns` read them. The representation locale (`sound_empty`) is not
introduced; no inventory showed repeated proofs it would remove.
The `Voblint` facade of phase 8 landed in the sixth: the export is
`codegen/generated/ml/Voblint_Generated.ml`, `cli/voblint.ml` includes it unchanged,
every handwritten module, the parser and the printer name `Voblint`, and the native
entry is `cli/entry/voblint_main.ml` with dune `public_name voblint`. The codegen
regression driver opens `Voblint_Generated.Generated` directly, since it tests the
export itself.

Not done, one stacked PR each:

- phase 9, the thesis chapters on `writing`; `docs/THESIS_BLUEPRINT.md` still names
  the old theorems.
