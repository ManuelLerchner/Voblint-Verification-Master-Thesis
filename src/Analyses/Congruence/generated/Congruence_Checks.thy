theory Congruence_Checks
  imports
    Congruence_Assembly
    "Voblint_Framework.Check_Report"
    "Voblint_Result.Analysis_Surface"
begin

section \<open>What a whole-program Congruence run reports\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Congruence's public runtime API: the names a caller outside this session uses, each
  bound to one of the shared unit-context assembly's 2 instances. Those instances
  define the equation system, the solve, the result table and the classified report;
  nothing is computed at this point, and nothing is rebuilt here.

  A context-sensitive run pairs the same classifier with a different solved system and
  reaches none of the names below, so no routing policy is needed here.
\<close>

subsection \<open>The solved system, under the name the CLI already uses\<close>

text \<open>
  These are notation, not a layer: an \<^theory_text>\<open>abbreviation\<close> introduces no constant, so
  nothing has to be unfolded to get back to the assembly and nothing extra reaches the
  code generator.
\<close>

abbreviation congruence_conf_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "congruence_conf_eqs_prog \<equiv> congruence_unit_equations"

abbreviation congruence_conf_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "congruence_conf_sol_prog \<equiv> congruence_unit_solution"

abbreviation congruence_conf_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "congruence_conf_terminates_prog \<equiv> congruence_unit_terminates"

text \<open>
  The one side condition a caller discharges per program. It is not a decision
  procedure: \<^const>\<open>congruence_conf_terminates_prog\<close> follows when the solver's own
  executable entry point returns a result on this program's equations, and nothing here
  says that entry point returns on every input.
\<close>

lemmas congruence_conf_terminates_prog_via_solve_c = congruence_join.terminates_of_solve_c
lemmas congruence_conf_vars_finite = congruence_join.vars_finite_of_terminates

subsection \<open>Solved-result table and check report\<close>

definition analyse_congruence_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_for = congruence_unit_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_congruence_result ::
    "imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result p = analyse_congruence_result_for (declared_global p) p"

text \<open>
  The report the exported \<open>analyse\<close> API dispatches to. It reads its per-node state
  through \<^const>\<open>analyse_congruence_result_for\<close>'s \<^type>\<open>analysis_result\<close> table ---
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point
  classifies at its projected state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two
  are not distinguishable here) classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s
  three-way verdict rather than introducing a fourth, \<open>Dead\<close> outcome the type does not
  carry.
\<close>

definition analyse_congruence_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_for = congruence_unit_report"

definition analyse_congruence_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report p = analyse_congruence_report_for (declared_global p) p"

text \<open>
  The state-carrying sibling: same table, with the per-check Congruence environment
  attached to each entry instead of discarded, and an \<open>unreachable\<close> flag read straight
  off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split. The flag is \<^term>\<open>True\<close> exactly when
  that unknown is \<^const>\<open>Bot\<close>; what \<^const>\<open>Bot\<close> certifies about concrete reachability is the
  surrounding soundness statement's business, not this definition's.
\<close>

definition analyse_congruence_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> congruence abs_state) list" where
  "analyse_congruence_report_for_with_state = congruence_unit_report_with_state"

definition analyse_congruence_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> congruence abs_state) list" where
  "analyse_congruence_report_with_state p =
     analyse_congruence_report_for_with_state (declared_global p) p"

text \<open>
  Both halves of one solve: the locals table every check report already reads, and the
  globals beside it. Binding the solve once is what keeps a report that shows both from
  solving twice.
\<close>

definition analyse_congruence_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, congruence abs_state) analysis_result
          \<times> (String.literal \<times> congruence abs_state lifted) list" where
  "analyse_congruence_ctx_solved_for = congruence_unit_solved"

lemma fst_analyse_congruence_ctx_solved_for [simp]:
  "fst (analyse_congruence_ctx_solved_for gs p) = analyse_congruence_result_for gs p"
  by (simp add: analyse_congruence_ctx_solved_for_def analyse_congruence_result_for_def
      congruence_join.solved_eq)

subsection \<open>Solver-choice variant: the per-origin update rule\<close>

text \<open>
  The same equation system solved under the per-origin update rule instead of the
  always-join rule production uses, so \<open>analyse_with_solver\<close> can compare solver choices
  on one system (\<open>congruence_po_equations_eq\<close> is what makes "one system" a theorem
  rather than a claim). These are bindings onto the assembly's own instance for this
  rule, so the sibling carries the same soundness endpoints the default does --- the
  update rule is a parameter of the assembly, not a reason to leave it.
\<close>

abbreviation congruence_conf_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "congruence_conf_sol_prog_per_origin \<equiv> congruence_po_solution"

definition analyse_congruence_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_per_origin_for = congruence_po_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_congruence_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_per_origin p =
     analyse_congruence_result_per_origin_for (declared_global p) p"

text \<open>
  The report the exported \<open>analyse\<close> API dispatches to. It reads its per-node state
  through \<^const>\<open>analyse_congruence_result_per_origin_for\<close>'s \<^type>\<open>analysis_result\<close> table ---
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point
  classifies at its projected state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two
  are not distinguishable here) classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s
  three-way verdict rather than introducing a fourth, \<open>Dead\<close> outcome the type does not
  carry.
\<close>

definition analyse_congruence_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_per_origin_for = congruence_po_report"

definition analyse_congruence_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_per_origin p =
     analyse_congruence_report_per_origin_for (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Congruence's 2 disciplines through the shared \<^locale>\<open>analysis_surface\<close>. There is one
  interpretation for each discipline Congruence publishes and none for any it does not,
  so the absent interpretation and the absent solver route agree by construction rather
  than by a separately maintained legality table. Why Congruence publishes these
  disciplines and not others is recorded in its README, not here.
\<close>

interpretation congruence_join_surface: analysis_surface
  analyse_congruence_result bot congruence_classify_check
  by unfold_locales

interpretation congruence_per_origin: analysis_surface
  analyse_congruence_result_per_origin bot congruence_classify_check
  by unfold_locales

lemma congruence_report_join_eq:
  "analyse_congruence_report p = congruence_join_surface.report p"
  by (simp add: analyse_congruence_report_def analyse_congruence_report_for_def
      analyse_congruence_result_def analyse_congruence_result_for_def
      congruence_join.report_def surface_unfold)

lemma congruence_report_per_origin_eq:
  "analyse_congruence_report_per_origin p = congruence_per_origin.report p"
  by (simp add: analyse_congruence_report_per_origin_def
      analyse_congruence_report_per_origin_for_def analyse_congruence_result_per_origin_def
      analyse_congruence_result_per_origin_for_def congruence_po_asm.report_def surface_unfold)

end
