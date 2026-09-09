theory Congruence_Checks
  imports Congruence_Assembly
    "Voblint_Framework.Check_Report"
    "Voblint_Result.Analysis_Surface"
begin

section \<open>What a whole-program Congruence run reports\<close>

text \<open>
  Congruence's public runtime API: the names a caller outside this session uses,
  each bound to one of \<open>Congruence_Assembly\<close>'s two instances of the shared
  unit-context assembly. Those instances define the equation system, the solve,
  the result table and the classified report; nothing is computed at this point,
  and nothing is rebuilt here.

  This theory needs neither routing policy from \<open>Congruence_Analyses\<close>: a
  context-sensitive run pairs the same classifier with a different solved system
  and reaches none of the names below.
\<close>

subsection \<open>The solved system, under the name the CLI already uses\<close>

text \<open>
  These three are notation, not a layer: an \<^theory_text>\<open>abbreviation\<close> introduces no
  constant, so nothing has to be unfolded to get back to the assembly and nothing
  extra reaches the code generator.
\<close>

abbreviation cctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "cctx_eqs_prog \<equiv> congruence_unit_equations"

abbreviation cctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "cctx_sol_prog \<equiv> congruence_unit_solution"

abbreviation cctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "cctx_terminates_prog \<equiv> congruence_unit_terminates"

text \<open>
  The one side condition a caller discharges per program. It is not a decision
  procedure: \<^const>\<open>cctx_terminates_prog\<close> follows when the solver's own executable
  entry point returns a result on this program's equations, and nothing here says
  that entry point returns on every input.
\<close>

lemmas cctx_terminates_prog_via_solve_c = congruence_join.terminates_of_solve_c
lemmas cctx_vars_finite = congruence_join.vars_finite_of_terminates

subsection \<open>Solved-result table and check report\<close>

definition analyse_congruence_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_for = congruence_unit_result"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.\<close>

definition analyse_congruence_result ::
    "imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result p = analyse_congruence_result_for (declared_global p) p"

text \<open>
  The report the exported \<open>analyse\<close> API dispatches to. It reads its per-node state
  through \<^const>\<open>analyse_congruence_result_for\<close>'s \<^type>\<open>analysis_result\<close> table ---
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a
  \<^const>\<open>Lifted\<close> point classifies at its projected state and a \<^const>\<open>Bot\<close> one
  (dead, or never covered; the two are not distinguishable here) classifies at
  \<^const>\<open>bot\<close>.
\<close>

definition analyse_congruence_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_for = congruence_unit_report"

definition analyse_congruence_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report p = analyse_congruence_report_for (declared_global p) p"

text \<open>
  The state-carrying sibling: same table, with the per-check Congruence
  environment attached to each entry instead of discarded, and an \<open>unreachable\<close>
  flag read straight off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close>
  case split.
\<close>

definition analyse_congruence_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> congruence abs_state) list" where
  "analyse_congruence_report_for_with_state = congruence_unit_report_with_state"

definition analyse_congruence_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> congruence abs_state) list" where
  "analyse_congruence_report_with_state p =
     analyse_congruence_report_for_with_state (declared_global p) p"

text \<open>Both halves of one solve: the locals table every check report already reads,
  and the globals beside it. Binding the solve once is what keeps a report that
  shows both from solving twice.\<close>

definition analyse_congruence_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, congruence abs_state) analysis_result
          \<times> (String.literal \<times> congruence abs_state lifted) list" where
  "analyse_congruence_ctx_solved_for = congruence_unit_solved"

lemma fst_analyse_congruence_ctx_solved_for:
  "fst (analyse_congruence_ctx_solved_for gs p) = analyse_congruence_result_for gs p"
  by (simp add: analyse_congruence_ctx_solved_for_def analyse_congruence_result_for_def
      congruence_join.solved_eq)

subsection \<open>Solver-choice variant: the per-origin update rule\<close>

text \<open>
  The same equation system under the per-origin update rule instead of the
  always-join rule production uses, so \<open>Analyse_Dispatch\<close>'s \<open>analyse_with_solver\<close>
  can compare solver choices on one system (\<open>congruence_po_equations_eq\<close> is what
  makes "one system" a theorem rather than a claim).
\<close>

abbreviation cctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "cctx_sol_prog_per_origin \<equiv> congruence_po_solution"

definition analyse_congruence_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_per_origin_for = congruence_po_result"

definition analyse_congruence_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, congruence abs_state) analysis_result" where
  "analyse_congruence_result_per_origin p =
     analyse_congruence_result_per_origin_for (declared_global p) p"

definition analyse_congruence_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_per_origin_for = congruence_po_report"

definition analyse_congruence_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_congruence_report_per_origin p =
     analyse_congruence_report_per_origin_for (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Congruence's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. Like
  Sign and Parity, it has no warrowing interpretation: its widening is plain join,
  and a strictly ascending chain of residue classes is a chain of proper divisors
  of the modulus, so there is nothing for widening to accelerate.
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
