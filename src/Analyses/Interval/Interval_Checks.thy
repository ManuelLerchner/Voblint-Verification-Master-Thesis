theory Interval_Checks
  imports Interval_Assembly "Voblint_Result.Analysis_Surface"
    "Voblint_Framework.Check_Report"
begin

hide_const phase.N

section \<open>What a whole-program Interval run reports\<close>

text \<open>
  Interval's public runtime API. Every name here is a binding onto one of
  \<open>Interval_Assembly\<close>'s four instances of the shared unit-context assembly, one per
  update rule. Those instances define the equation system, the solve, the result
  table and the classified report; nothing is computed at this point, and nothing is
  rebuilt.

  Naming a discipline here is what publishes it. Omitting one would leave a solved
  table nothing reads --- which is how warrowing per origin once came to have a table
  and no way to see the states in it.
\<close>

subsection \<open>The solved systems, under the names the CLI already uses\<close>

text \<open>
  One equation system, four solves. \<^theory_text>\<open>abbreviation\<close> introduces no constant, so
  these are notation for the assembly's own names rather than a layer over them, and
  \<open>Interval_Assembly\<close>'s \<open>interval_join_equations_eq\<close> and its two siblings are what
  make "one equation system" a theorem rather than a comment.
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

abbreviation interval_conf_terminates_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_warrow \<equiv> interval_td_terminates"

abbreviation interval_conf_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog \<equiv> interval_join_solution"

abbreviation interval_conf_terminates_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog \<equiv> interval_join_terminates"

abbreviation interval_conf_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_per_origin \<equiv> interval_po_solution"

abbreviation interval_conf_terminates_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_per_origin \<equiv> interval_po_terminates"

abbreviation interval_conf_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_wpo \<equiv> interval_wpo_solution"

abbreviation interval_conf_terminates_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_wpo \<equiv> interval_wpo_terminates"

text \<open>
  The side condition a caller discharges per program, once per discipline. It is not
  a decision procedure: each follows when that solver's own executable entry point
  returns a result on this program's equations, and nothing here says the entry point
  returns on every input.
\<close>

lemmas interval_conf_terminates_prog_warrow_via_solve_c =
  interval_warrow_asm.terminates_of_solve_c
lemmas interval_conf_terminates_prog_via_solve_c = interval_join_asm.terminates_of_solve_c
lemmas interval_conf_terminates_prog_per_origin_via_solve_c =
  interval_po_asm.terminates_of_solve_c
lemmas interval_conf_terminates_prog_wpo_via_solve_c = interval_wpo_asm.terminates_of_solve_c

lemmas interval_conf_vars_finite_warrow = interval_warrow_asm.vars_finite_of_terminates

subsection \<open>Solved-result tables, one per discipline\<close>

text \<open>
  Apinis warrowing is the production default: Interval's local lattice has infinite
  height, so plain join has no termination guarantee on a loop with unbounded growth.
  The other three are published so \<open>analyse_with_solver\<close> can compare update rules on
  the identical equation system.
\<close>

definition analyse_interval_td_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result_for = interval_td_result"

definition analyse_interval_td_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result p = analyse_interval_td_result_for (declared_global p) p"

definition analyse_interval_join_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result_for = interval_join_result"

definition analyse_interval_join_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result p = analyse_interval_join_result_for (declared_global p) p"

definition analyse_interval_per_origin_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_per_origin_result_for = interval_po_result"

definition analyse_interval_per_origin_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_per_origin_result p =
     analyse_interval_per_origin_result_for (declared_global p) p"

definition analyse_interval_wpo_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_wpo_result_for = interval_wpo_result"

definition analyse_interval_wpo_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_wpo_result p = analyse_interval_wpo_result_for (declared_global p) p"

text \<open>Both halves of the production solve: the locals table every check report reads,
  and the globals beside it. Binding the solve once is what keeps a report that shows
  both from solving twice.\<close>

definition analyse_interval_ctx_solved_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, ivl abs_state) analysis_result
          \<times> (String.literal \<times> ivl abs_state lifted) list" where
  "analyse_interval_ctx_solved_warrow_for = interval_td_solved"

lemma fst_analyse_interval_ctx_solved_warrow_for:
  "fst (analyse_interval_ctx_solved_warrow_for gs p) = analyse_interval_td_result_for gs p"
  by (simp add: analyse_interval_ctx_solved_warrow_for_def analyse_interval_td_result_for_def
      interval_warrow_asm.solved_eq)

subsection \<open>Whole-program check reports\<close>

text \<open>
  Each report reads its per-node state through its own result table's
  \<^const>\<open>lookup_context\<close> rather than a raw solver-environment lookup, so a
  \<^const>\<open>Lifted\<close> point classifies at its projected state and a \<^const>\<open>Bot\<close> one
  classifies at \<^const>\<open>bot\<close> --- preserving \<^type>\<open>check_result\<close>'s three-way verdict
  rather than introducing a fourth, \<open>Dead\<close> outcome the type does not carry.
\<close>

definition analyse_interval_td_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report_for = interval_td_report"

definition analyse_interval_td_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report p = analyse_interval_td_report_for (declared_global p) p"

definition analyse_interval_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_for = interval_join_report"

definition analyse_interval_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report p = analyse_interval_report_for (declared_global p) p"

definition analyse_interval_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin_for = interval_po_report"

definition analyse_interval_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin p =
     analyse_interval_report_per_origin_for (declared_global p) p"

definition analyse_interval_report_wpo_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo_for = interval_wpo_report"

definition analyse_interval_report_wpo :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo p = analyse_interval_report_wpo_for (declared_global p) p"

text \<open>
  The state-carrying sibling of the production report: the same table, with each
  check's Interval environment attached instead of discarded, and an \<open>unreachable\<close>
  flag read straight off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> split
  (@{thm report_lifted_state_unreachable_iff}).
\<close>

definition analyse_interval_td_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_for_with_state = interval_td_report_with_state"

definition analyse_interval_td_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_with_state p =
     analyse_interval_td_report_for_with_state (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Interval carries all four disciplines, so it is where the shared surface meets its
  richest case. Each interpretation names one solved table and Interval's own
  classifier; \<^locale>\<open>analysis_surface\<close> supplies the state reading and the check
  report.
\<close>

interpretation interval_join: analysis_surface
  analyse_interval_join_result bot interval_classify_check
  by unfold_locales

interpretation interval_per_origin: analysis_surface
  analyse_interval_per_origin_result bot interval_classify_check
  by unfold_locales

interpretation interval_warrow: analysis_surface
  analyse_interval_td_result bot interval_classify_check
  by unfold_locales

interpretation interval_wpo: analysis_surface
  analyse_interval_wpo_result bot interval_classify_check
  by unfold_locales

text \<open>
  The report names the rest of the development cites, shown to be the shared surface.
  Both sides are the same \<^const>\<open>classify_checks\<close> assembly over the same solved
  table, so these are definitional: every existing theorem about these reports keeps
  both its statement and its proof.
\<close>

lemma interval_report_join_eq: "analyse_interval_report p = interval_join.report p"
  by (simp add: analyse_interval_report_def analyse_interval_report_for_def
      analyse_interval_join_result_def analyse_interval_join_result_for_def
      interval_join_asm.report_def surface_unfold)

lemma interval_report_per_origin_eq:
  "analyse_interval_report_per_origin p = interval_per_origin.report p"
  by (simp add: analyse_interval_report_per_origin_def
      analyse_interval_report_per_origin_for_def analyse_interval_per_origin_result_def
      analyse_interval_per_origin_result_for_def interval_po_asm.report_def surface_unfold)

lemma interval_report_warrow_eq:
  "analyse_interval_td_report p = interval_warrow.report p"
  by (simp add: analyse_interval_td_report_def analyse_interval_td_report_for_def
      analyse_interval_td_result_def analyse_interval_td_result_for_def
      interval_warrow_asm.report_def surface_unfold)

lemma interval_report_wpo_eq:
  "analyse_interval_report_wpo p = interval_wpo.report p"
  by (simp add: analyse_interval_report_wpo_def analyse_interval_report_wpo_for_def
      analyse_interval_wpo_result_def analyse_interval_wpo_result_for_def
      interval_wpo_asm.report_def surface_unfold)

end

