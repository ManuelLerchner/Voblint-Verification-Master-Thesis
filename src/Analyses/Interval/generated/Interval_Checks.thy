theory Interval_Checks
  imports
    Interval_Assembly
    "Voblint_Framework.Check_Report"
    "Voblint_Result.Analysis_Surface"
begin

hide_const phase.N

section \<open>What a whole-program Interval run reports\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Interval's public runtime API: the names a caller outside this session uses, each
  bound to one of the shared unit-context assembly's 4 instances. Those instances
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

abbreviation interval_conf_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
            (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "interval_conf_eqs_prog \<equiv> interval_td_equations"

abbreviation interval_conf_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_warrow \<equiv> interval_td_solution"

abbreviation interval_conf_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_warrow \<equiv> interval_td_terminates"

text \<open>
  The one side condition a caller discharges per program. It is not a decision
  procedure: \<^const>\<open>interval_conf_terminates_prog_warrow\<close> follows when the solver's own
  executable entry point returns a result on this program's equations, and nothing here
  says that entry point returns on every input.
\<close>

lemmas interval_conf_terminates_prog_warrow_via_solve_c =
  interval_warrow_asm.terminates_of_solve_c
lemmas interval_conf_vars_finite_warrow = interval_warrow_asm.vars_finite_of_terminates

subsection \<open>Solved-result table and check report\<close>

definition analyse_interval_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_for = interval_td_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_interval_result :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result p = analyse_interval_result_for (declared_global p) p"

text \<open>
  The production discipline's report. It reads its per-node state through
  \<^const>\<open>analyse_interval_result_for\<close>'s \<^type>\<open>analysis_result\<close> table --- \<^const>\<open>lookup_context\<close>, not
  a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point classifies at its projected
  state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two are not distinguishable here)
  classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s three-way verdict rather than
  introducing a fourth, \<open>Dead\<close> outcome the type does not carry.
\<close>

definition analyse_interval_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_for = interval_td_report"

definition analyse_interval_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report p = analyse_interval_report_for (declared_global p) p"

text \<open>
  The state-carrying sibling: same table, with the per-check Interval environment
  attached to each entry instead of discarded, and an \<open>unreachable\<close> flag read straight
  off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split. The flag is \<^term>\<open>True\<close> exactly when
  that unknown is \<^const>\<open>Bot\<close>; what \<^const>\<open>Bot\<close> certifies about concrete reachability is the
  surrounding soundness statement's business, not this definition's.
\<close>

definition analyse_interval_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_report_for_with_state = interval_td_report_with_state"

definition analyse_interval_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_report_with_state p =
     analyse_interval_report_for_with_state (declared_global p) p"

text \<open>
  Both halves of one solve: the locals table every check report already reads, and the
  globals beside it. Binding the solve once is what keeps a report that shows both from
  solving twice.
\<close>

definition analyse_interval_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, ivl abs_state) analysis_result
          \<times> (String.literal \<times> ivl abs_state lifted) list" where
  "analyse_interval_ctx_solved_for = interval_td_solved"

lemma fst_analyse_interval_ctx_solved_for [simp]:
  "fst (analyse_interval_ctx_solved_for gs p) = analyse_interval_result_for gs p"
  by (simp add: analyse_interval_ctx_solved_for_def analyse_interval_result_for_def
      interval_warrow_asm.solved_eq)

subsection \<open>Solver-choice variant: the always-join update rule\<close>

text \<open>
  The same equation system solved under the always-join update rule instead of the
  Apinis-warrowing rule of the unsuffixed names, so solver choices can be compared on
  one system (\<open>interval_join_equations_eq\<close> is what makes "one system" a theorem rather
  than a claim). These are bindings onto the assembly's own instance for this rule, so
  the sibling carries the same soundness endpoints the first does --- the update rule
  is a parameter of the assembly, not a reason to leave it.
\<close>

abbreviation interval_conf_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog \<equiv> interval_join_solution"

abbreviation interval_conf_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog \<equiv> interval_join_terminates"

lemmas interval_conf_terminates_prog_via_solve_c = interval_join_asm.terminates_of_solve_c

definition analyse_interval_result_join_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_join_for = interval_join_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_interval_result_join ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_join p = analyse_interval_result_join_for (declared_global p) p"

text \<open>
  The production discipline's report. It reads its per-node state through
  \<^const>\<open>analyse_interval_result_join_for\<close>'s \<^type>\<open>analysis_result\<close> table --- \<^const>\<open>lookup_context\<close>,
  not a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point classifies at its
  projected state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two are not
  distinguishable here) classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s
  three-way verdict rather than introducing a fourth, \<open>Dead\<close> outcome the type does not
  carry.
\<close>

definition analyse_interval_report_join_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_join_for = interval_join_report"

definition analyse_interval_report_join :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_join p = analyse_interval_report_join_for (declared_global p) p"

subsection \<open>Solver-choice variant: the per-origin update rule\<close>

text \<open>
  The same equation system solved under the per-origin update rule instead of the
  Apinis-warrowing rule of the unsuffixed names, so solver choices can be compared on
  one system (\<open>interval_po_equations_eq\<close> is what makes "one system" a theorem rather
  than a claim). These are bindings onto the assembly's own instance for this rule, so
  the sibling carries the same soundness endpoints the first does --- the update rule
  is a parameter of the assembly, not a reason to leave it.
\<close>

abbreviation interval_conf_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_per_origin \<equiv> interval_po_solution"

abbreviation interval_conf_terminates_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_per_origin \<equiv> interval_po_terminates"

lemmas interval_conf_terminates_prog_per_origin_via_solve_c =
  interval_po_asm.terminates_of_solve_c

definition analyse_interval_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_per_origin_for = interval_po_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_interval_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_per_origin p =
     analyse_interval_result_per_origin_for (declared_global p) p"

text \<open>
  The production discipline's report. It reads its per-node state through
  \<^const>\<open>analyse_interval_result_per_origin_for\<close>'s \<^type>\<open>analysis_result\<close> table ---
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point
  classifies at its projected state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two
  are not distinguishable here) classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s
  three-way verdict rather than introducing a fourth, \<open>Dead\<close> outcome the type does not
  carry.
\<close>

definition analyse_interval_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin_for = interval_po_report"

definition analyse_interval_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin p =
     analyse_interval_report_per_origin_for (declared_global p) p"

subsection \<open>Solver-choice variant: the warrowing-per-origin update rule\<close>

text \<open>
  The same equation system solved under the warrowing-per-origin update rule instead of
  the Apinis-warrowing rule of the unsuffixed names, so solver choices can be compared
  on one system (\<open>interval_wpo_equations_eq\<close> is what makes "one system" a theorem
  rather than a claim). These are bindings onto the assembly's own instance for this
  rule, so the sibling carries the same soundness endpoints the first does --- the
  update rule is a parameter of the assembly, not a reason to leave it.
\<close>

abbreviation interval_conf_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_wpo \<equiv> interval_wpo_solution"

abbreviation interval_conf_terminates_prog_wpo :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_wpo \<equiv> interval_wpo_terminates"

lemmas interval_conf_terminates_prog_wpo_via_solve_c = interval_wpo_asm.terminates_of_solve_c

definition analyse_interval_result_wpo_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_wpo_for = interval_wpo_result"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every caller with only
  an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_interval_result_wpo ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_result_wpo p = analyse_interval_result_wpo_for (declared_global p) p"

text \<open>
  The production discipline's report. It reads its per-node state through
  \<^const>\<open>analyse_interval_result_wpo_for\<close>'s \<^type>\<open>analysis_result\<close> table --- \<^const>\<open>lookup_context\<close>,
  not a raw solver-environment lookup --- so a \<^const>\<open>Lifted\<close> point classifies at its
  projected state and a \<^const>\<open>Bot\<close> one (dead, or never covered; the two are not
  distinguishable here) classifies at \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s
  three-way verdict rather than introducing a fourth, \<open>Dead\<close> outcome the type does not
  carry.
\<close>

definition analyse_interval_report_wpo_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo_for = interval_wpo_report"

definition analyse_interval_report_wpo :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo p = analyse_interval_report_wpo_for (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Interval's 4 disciplines through the shared \<^locale>\<open>analysis_surface\<close>. There is one
  interpretation for each discipline Interval publishes and none for any it does not,
  so the absent interpretation and the absent solver route agree by construction rather
  than by a separately maintained legality table. Why Interval publishes these
  disciplines and not others is recorded in its README, not here.
\<close>

interpretation interval_warrow: analysis_surface
  analyse_interval_result bot interval_classify_check
  by unfold_locales

interpretation interval_join: analysis_surface
  analyse_interval_result_join bot interval_classify_check
  by unfold_locales

interpretation interval_per_origin: analysis_surface
  analyse_interval_result_per_origin bot interval_classify_check
  by unfold_locales

interpretation interval_wpo: analysis_surface
  analyse_interval_result_wpo bot interval_classify_check
  by unfold_locales

lemma interval_report_warrow_eq: "analyse_interval_report p = interval_warrow.report p"
  by (simp add: analyse_interval_report_def analyse_interval_report_for_def
      analyse_interval_result_def analyse_interval_result_for_def
      interval_warrow_asm.report_def surface_unfold)

lemma interval_report_join_eq: "analyse_interval_report_join p = interval_join.report p"
  by (simp add: analyse_interval_report_join_def analyse_interval_report_join_for_def
      analyse_interval_result_join_def analyse_interval_result_join_for_def
      interval_join_asm.report_def surface_unfold)

lemma interval_report_per_origin_eq:
  "analyse_interval_report_per_origin p = interval_per_origin.report p"
  by (simp add: analyse_interval_report_per_origin_def
      analyse_interval_report_per_origin_for_def analyse_interval_result_per_origin_def
      analyse_interval_result_per_origin_for_def interval_po_asm.report_def surface_unfold)

lemma interval_report_wpo_eq: "analyse_interval_report_wpo p = interval_wpo.report p"
  by (simp add: analyse_interval_report_wpo_def analyse_interval_report_wpo_for_def
      analyse_interval_result_wpo_def analyse_interval_result_wpo_for_def
      interval_wpo_asm.report_def surface_unfold)

end
