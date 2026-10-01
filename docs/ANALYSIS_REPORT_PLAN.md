# Analysis report and solver boundary refactor

Branch `refactor/analysis-report`, from `main`. The thesis and the site follow on
`writing` after the merge.

## Goal

The public soundness theorems should speak about one object, the analysis report
`res` that `analyse_program` returns, and should need no termination premise. Three
facts carry the whole guarantee:

| Fact | Statement | Uses |
| --- | --- | --- |
| `analysis_report_covers` | `𝒞 v ⊆ ⟦res⟧ᵥ` | compiler, traces, routing, equations, solver |
| `analysis_report_checks_sound` | `⟦res⟧ᵥ ⊆ 𝒱(res, v)` | the report alone, no executions |
| `analysis_report_dead` | `dead(res, v) ⟹ ⟦res⟧ᵥ = ∅` | the report alone |

`PROVED` and `REFUTED` constrain the stores inside `⟦res⟧ᵥ`; `DEAD` says there are
none. With the first fact, `DEAD` gives `𝒞 v ⊆ ⟦res⟧ᵥ = ∅`. The source-level theorem
keeps its existential node: a finite `pstep` run reaches some `v` related by `csim`,
and its store lies in `𝒞 v`. No set of "source stores at `v`" is introduced, since
the simulation is not functional.

The converse of the third fact does not hold. A `Lifted` entry passed the
product's emptiness test, which is sound and incomplete: `mcp_empty_v` reports a
state empty when one active analysis does, so a state with Interval `x = 2` and Parity
`x odd` passes it although it concretizes to no store. `⟦res⟧ᵥ = ∅` therefore does not
imply `dead(res, v)`, and `UNKNOWN` does not imply `⟦res⟧ᵥ ≠ ∅`. The `UNKNOWN`
corollary states what does hold: an `UNKNOWN` check's point is not `dead`, so the
report makes no unreachability claim there.

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
- The configuration travels as loose arguments, and the web entry passes
  `context_depth` and `int_refinement` as strings.

## Names and notation

| Concept | Isabelle | Thesis and site |
| --- | --- | --- |
| analysis report | variable `res`, type `analysis_report` | "analysis report", `res` |
| configuration | datatype `analysis_config`, variable `config` | spelled out |
| report semantics | `report_sem res v`, syntax `⟦res⟧⇩v` | `⟦res⟧_v` |
| verdict semantics | `verdict_stores res v` | `𝒱(res, v)` |
| reported checks at a node | `report_checks res v` | `Checks(res, v)` |
| emptiness | `dead res v` | `dead(res, v)` |
| missing result | `No_Answer` | |

Avoided: `R` (call-context relation), `r` (internal table), `cfg` (CFG), `A`, `σ`.
`⟦res⟧⇩v` is its own constant with mixfix syntax, since the overloaded `gamma_S`
takes one argument. `𝒱` joins the store-set family `𝒞`, `𝒜`; it is defined from
`Checks(res, v)`: the stores in which every definite verdict at `v` is valid.
`UNKNOWN` and `DEAD` contribute no constraint to `𝒱`; `DEAD` is handled by
`analysis_report_dead`.

The verdicts get one corollary each: `analysis_report_proved` and
`analysis_report_refuted` restate the second fact for one check, and
`analysis_report_unknown` states `UNKNOWN ⟹ ¬ dead(res, v)` (see above for why
not `⟦res⟧ᵥ ≠ ∅`), so every verdict word has a theorem.

## Invariants

- After `analysis_config` is resolved, no theory case-splits on an analysis kind,
  context policy, refinement mode or update rule. The one split over the context
  policy sits in the function that builds the report; each policy is a generic
  locale instance below it, since the three context types differ.
- After a solve becomes an `analysis_report`, no public theorem mentions solver
  tables, context representations or rendering projections.
- One canonical API per concept: concretization through `γ`/`⟦·⟧` (with `⟦res⟧ᵥ`
  as the located form), solved data through `solved_table`, analyzer output through
  `analysis_report`, verdict truth through `𝒱(res, v)` and the CAPS queries.

- CLI text and JSON stay byte-identical. Phase 0 records the golden output; every
  later phase reproduces it.
- Each phase ends with the batch build, the codegen regression, the CLI corpus and
  the golden diff green.

## Phases

0. **Guardrails.** Snapshot CLI text and JSON for the regression corpus, the
   playground fixtures and the registered thesis and site claims.
1. **Typed configuration.** `analysis_domain` gains `Int_Analysis refine_mode` in
   place of `Int_Analysis`, `Int_Once_Analysis` and `Int_Never_Analysis` (manifest
   `constructor` field). The fixpoint registration becomes `Int_Fixpoint`, beside
   `Int_Once` and `Int_Never`. The existing `context_mode` (`Ctx_None`,
   `Ctx_EntryState`, `Ctx_CallString nat`) is already typed and stays; renaming it
   would churn every consumer for no gain. Datatype `analysis_config` with
   selectors, so the export is one constructor, and one `valid_config`.
   Validity keeps today's meaning, a non-empty distinct list, so two refinement
   modes may still be active together. This is a deliberate compatibility choice.
2. **One context dispatch.** Resolve `analysis_config` once into the
   policy-specific pipeline (a record of operations or a locale parameter). Prove it
   equal to the current three-way splits before switching callers. Later phases
   never inspect the context policy again.
3. **`solve_c` at the boundary.** `analyse_program` matches on `solve_c`; `None`
   becomes `No_Answer`, which the generated code never produces. Prove
   `Analysed res ⟹ config_terminates config p`. `config_terminates` remains
   available internally as a theorem derived from `Analysed res`, but no public
   source-soundness theorem takes it as a premise. The Int reduction loop and the
   query-depth abort remain ways the code can fail to return; neither yields
   `Analysed`.
4. **Semantic `analysis_report`.** The report reuses the finite shape of
   `run_result` (context list, states, routes, checks, diagnostics, graph) with a
   semantic payload: `run_result` gains a state type parameter, the report fills it
   with `mcp_val` and the presentation with the rendered view. `result_with_globals`
   yields a set-and-function table, so it is not stored; one bridge lemma relates the
   report's finite states to `lookup_context` on that table. The report also stores
   the configuration and the program variables rendering needs.
   `mcp_render` becomes presentation-only and is not part of the theorem object.
   Define `lookup_report`, `⟦res⟧ᵥ`, `verdict_stores`, `report_checks` and a
   structural `dead`; show the existing verdict aggregation computes `dead`.
5. **Public theorems.** The three facts above, then the corollaries
   `analyse_program_source_sound`, `analyse_program_check_sound`,
   `analyse_program_dead_unreached` and `analyse_program_arithmetic_safe`.
   Arithmetic safety is a diagnostic guarantee and stays apart from the verdicts.
   Implementation lemmas (`gamma_reader_eq_lookup`, `table_covers`, …) stay as the
   proofs underneath.
6. **Export.** Export `analysis_config`, `analysis_report`, `analyse_program`, and
   the projection and string helpers as functions the adapters call. Rendering stays
   outside the theorem object. The OCaml and web adapters build the typed config
   once; playground URL parameters do not change. The external CLI and JSON text
   remains byte-identical even though the exported Isabelle function signature
   changes.
7. **API tidy.** Nothing above the report theory mentions `mcp_rule.result`. One
   lookup vocabulary, thin public theorem names, and ad-hoc overloading only where
   one concept has several representations. Concretely:
   - rename the framework's `('ctx, 'a) analysis_result` to `analysis_table`, so
     table, report and answer read as three layers;
   - absorb `analysis_surface` (`state_at`, `reach_state_at`, `report`,
     `report_with_state`) into report projections, or delete what has no consumer;
   - retire `checks_sound_at`, `table_covers` and `analysis_result_covers` from the
     public layer; `𝒱(res, v)` and the CAPS corollaries replace them;
   - keep `Uncovered`/`Covered`, `Bot`/`Lifted` and `Dead` apart below the report:
     coverage, emptiness and the verdict are different facts, and only the report
     theorems hide them;
   - keep the emptiness tests (`is_empty_state`, `val_empty`, `mcp_empty_v`, …) and
     the executable readbacks (`mcp_rd`, `default_st_to_fun`) as named constants; their
     exactness differs, and an overloaded name would hide which one a proof uses.
   - if it falls out cheaply, one contextual classification helper shared by the
     check column and the arithmetic diagnostics.
7a. **Named solve and split contracts.**
   - `result_with_globals` returns a record `solved_run` (table, shared global,
     seeds, steps, successors) in place of a five-tuple; no caller destructures a
     tuple.
   - Rename the framework table: `analysis_result` → `solved_table`,
     `result_unknowns` → `covered_keys`, `result_at` → `table_at`,
     `lookup_context` → `lookup_table`, `lookup_context_result` →
     `lookup_coverage`, `contexts_at` → `table_contexts`. This supersedes the
     `analysis_table` name above.
   - Split `sound_table` into `covered_table` (finite contexts, coverage) and
     `sound_classifier` (proved, refuted); the classifier is not a table property.
   - CAPS queries `PROVED res v e`, `REFUTED res v e`, `UNKNOWN res v e` and
     `DEAD res v` on the report; clients stop destructuring `check_verdict`.
   - `⟦res⟧ᵥ` as an overloaded located concretization (`consts gamma_at`), so a
     later table representation can register under the same notation.
7b. **One registration per analysis.** The generator emits one record of
   operations per `analysis_domain` (`registration_of`) in place of the parallel
   functions `local_spec_of`, `part_gamma`, `part_live`, `part_empty`, `val_gamma`,
   `val_empty`, `val_answer`, `field_of`; the old names become accessors. With
   `Int_Analysis refine_mode` the mode is then read in one equation. Optional for
   this branch: it touches only generated theories and their consumers. The
   Int modes keep one carrier slot each behind the parameterized constructor, which
   is why two modes may still run together.
7c. **Shared contracts where proofs repeat.** `sound_empty` / `exact_empty` locales
   for the emptiness tests, and a representation locale for executable readbacks
   that commute with an operation, adopted only where they remove repeated
   proofs. Exactness stays visible in which locale a test interprets.

Out of scope: replacing the fixed generated MCP product with a carrier keyed by
analysis instance. It would remove the slot lenses and per-analysis dispatch,
but it changes the core of MCP composition and needs its own design.
8. **Consumers, on `writing` after the merge.** Thesis chapters 9, 10 and 12, the
   README, the notation table, and the site's theorem cards, metro map (result side
   collapses to `⟦res⟧ᵥ` with checks, `DEAD` and SAFE branches) and alignment rows.

## Risks

- Phases 1 and 2 carry most of the proof churn: the generator, the three global
  interpretations and every per-domain registration.
- The report's table must stay executable; the plan reuses the structure the solver
  already builds rather than a HOL function field.
- Byte-identical output constrains phase 6; the golden diff makes it checkable.
- Without the interactive Isabelle server, every step runs on batch builds.
