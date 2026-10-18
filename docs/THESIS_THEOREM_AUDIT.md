# Theorem audit for the thesis argument

Read-only audit to accompany `docs/THESIS_ARGUMENT_STORYBOARD.md`. For each
chapter it asks one question: can the reader identify one theorem that
answers the chapter's central question, and see how that result reaches the
end-to-end guarantee? No theory was changed.

"Used downstream" means another theorem on the path to
`run_voblint_source_sound` invokes it. Uses were found with `rg` over
`src/**/*.thy` and confirmed by reading the invoking proof.

## Audit table

| Ch | Claim in prose | Isabelle theorem | Used downstream? | Proposed action |
| --- | --- | --- | --- | --- |
| 3 | Source runs are matched by graph runs | `csim_star`, wrapped by `source_run_has_activation_trace` (`Source_To_Trace.thy`) | Yes: `source_run_has_activation_trace` → `source_store_in_activation_collect` → `run_voblint_spine`; `source_reaches_node_collect` → `run_voblint_source_sound` | Keep. Thesis already cites both. |
| 4 | Claims meeting the contract cover each context | `activation_collect_sound` (`Activation_Backbone.thy`) | Yes, through `routed_context` interpretations of `activation_coverage` (`Routed_Context.thy:642`) | Keep. |
| 4 | Contexts exhaust the node collecting semantics | locale form `node_collect_eq_Union_activation_collect`; run-level form `node_collect_eq_Union_activation_of_has_context` (`Activation_Trace_Collect.thy:182`) | Locale form: no. Run-level form: yes, per policy, into `covered_table_of_activation` (`Analysis_Run_Sound.thy:210`) | Done in Pass 1: thesis now cites the run-level form. |
| 7 | Any nonempty selection of distinct analyses meets the analysis contract | `mcp_combine_sound` (generic), `mcp_comp_sound` (shipped selection, `MCP_Analyses.thy:92`), `dg_spec_of_contract` | Yes: `mcp_comp_sound` feeds the run-level analyses (`MCP_Analyses.thy:274`, `MCP_Split.thy:520`); `dg_spec_of_contract` feeds `DG_Analysis.thy:1367` | Keep. `mcp_comp_sound` already has a readable statement and is cited (`07:340`); it is the chapter's endpoint. No corollary needed. |
| 8 | Every post-solution on a closed solved set covers each context | `activation_collect_dg_sound` (`Routed_Context.thy`) | Yes: `DG_Live_Unknowns.thy:517, 729`, `DG_Analysis.thy:1068, 1227` | Keep. |
| 8 | A terminated solve induces an entry-state policy that is total and covered | `entry_state_has_context_of_terminates` + `entry_state_activation_collect_sound_of_terminates` (`DG_Live_Unknowns.thy:703, 743`), policy `admitted_contexts` (`DG_Analysis.thy:598`) | Yes: both feed `mcp_es_rule_table` (`Analysis_Run_Ctx_Sound.thy:20-40`) | **Candidate corollary** (see below). At minimum, cite both in §8.2 next to the non-circularity paragraph. |
| 9 | A returned solve gives a usable certificate | `td_certified_solver` (`Globals_Rule.thy`), `live_unknowns_cover` (`DG_Live_Unknowns.thy`) | Yes: `td_certified_solver` in every generated registration; `live_unknowns_cover` inside the entry-state and functional routes | Keep. |
| 10 | Per-policy context-sensitive chain | `run_voblint_spine` (+ `run_voblint_call_string_chain`, `run_voblint_unit_chain`, entry-state variants) | Not used by the headline; it is a parallel endpoint | Keep as the context-sensitive statement; Pass 1 already cites it. |
| 10 | Context-erased public guarantee | `run_voblint_source_sound` | Endpoint | Keep. Its proof: `source_reaches_node_collect` → `run_voblint_covers` → `analysis_report_verdicts_sound`. |
| 10 | Report coverage | `run_voblint_covers` ← `run_voblint_sound` ← `analysis_report_of_sound` ← per policy `covered_table_of_activation` (union premise + per-context bound) | Yes | Keep. Thesis now says contexts enter here. |
| 10 | Report contract | `run_voblint_report_contract` | Packaging theorem | Keep. It already bundles validity, well-formedness and `sound_report`. |
| 12 | Executable operations preserve the contract | `exec_local_spec_sound` (`DG_Local_State_Exec_Refinement.thy:266`), commutation `sound_nonrelational_ops.tf_st_for_commute`, `sound_nonrelational_ops.dg_analysis_execI` | Yes: `exec_local_spec_sound` → `dg_spec_of_contract` (`:305`) | **Cite `exec_local_spec_sound`** in §12.1: it states the refinement boundary directly (the executable local spec is a sound local spec for γ). No new theorem. |
| 13 | Some obligations are necessary | `ret_weak_obligations` + `return_at_caller_context_unsound`; `tot_weak_obligations` + `total_dropped_unsound`; `prefix_congruence_mod_unsound` | Not on the path (counterexamples) | Keep as cited. No collecting theorem: the three differ in kind (locale assumptions vs. domain operator). |

## Relationship between the two endpoints

Both `run_voblint_source_sound` and `run_voblint_spine` pass through the
context split. They differ in where it appears:

- `run_voblint_source_sound` states only `C`, `R`, `V`. The split lives inside
  `run_voblint_covers`, whose per-policy proof (`covered_table_of_activation`)
  needs `C u ⊆ ∪_c A u c` and `A u c ⊆ γ(...)`.
- `run_voblint_spine` states the split explicitly for one policy, and needs
  `has_ctx` and `buckets` as premises, which each policy-specific corollary
  discharges.

Replacing the headline proof with the spine would add a case split over
policies and duplicate what `run_voblint_covers` already does. I recommend
against it. The thesis now presents the spine as the context-sensitive
statement and the headline as the context-erased one (`10:216-233`).

## Candidate corollaries

Only the first passes the test "materially clearer than the existing results".

1. **Entry-state policy from a terminated solve** (recommended, low cost).
   Conjoin `entry_state_has_context_of_terminates` and
   `entry_state_activation_collect_sound_of_terminates`:

   ```isabelle
   corollary entry_state_policy_of_terminates:
     assumes "wf_program_compile_input p" and "terminates (declared_global p) p"
     shows "∀t ∈ 𝒯. ∃c. activation_context_rel ... (admitted_contexts (declared_global p) p) root_ctx ... t c"
       and "𝒜 ... (admitted_contexts (declared_global p) p) ... v ctx ⊆ pgam p (reader ... (Inl (v, ctx))) (gsol p)"
   ```

   It states the quantifier order of the non-circularity argument (fix the
   solve, define the policy from it, get totality and coverage) as one
   result that §8.2 can display. Schematic: the exact statement must reuse
   the existing constants unchanged.
2. **Unified verdict theorem** (not recommended). `run_voblint_source_sound`
   already gives coverage and the verdict set; `run_voblint_check_sound`,
   `run_voblint_dead_check_unreached` and the arithmetic theorems cover the
   rest. A conjunction would add maintenance without a new interpretation.
3. **Cooperation corollary** (not needed). `mcp_comp_sound` already is the
   readable endpoint of Ch. 7.

No new formalization has been done. Corollary 1 needs an Isabelle edit
following `docs/ISABELLE_AGENT_NOTES.md` and a batch build.
