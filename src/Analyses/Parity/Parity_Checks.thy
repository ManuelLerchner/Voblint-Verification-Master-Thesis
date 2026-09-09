theory Parity_Checks
  imports Parity_Assembly
    "Voblint_Framework.Check_Report"
    "Voblint_Result.Analysis_Surface"
begin

section \<open>What a whole-program Parity run reports\<close>

text \<open>
  Parity's public runtime API: the names a caller outside this session uses, each
  bound to one of \<open>Parity_Assembly\<close>'s two instances of the shared unit-context
  assembly. Those instances define the equation system, the solve, the result table
  and the classified report; nothing is computed at this point, and nothing is
  rebuilt here.

  This theory needs neither routing policy from \<open>Parity_Analyses\<close>: a
  context-sensitive run pairs the same classifier with a different solved system
  and reaches none of the names below.
\<close>

subsection \<open>The solved system, under the name the CLI already uses\<close>

text \<open>
  These three are notation, not a layer: an \<^theory_text>\<open>abbreviation\<close> introduces no
  constant, so nothing has to be unfolded to get back to the assembly and nothing
  extra reaches the code generator.
\<close>

abbreviation pctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
            (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs_prog \<equiv> parity_unit_equations"

abbreviation pctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog \<equiv> parity_unit_solution"

abbreviation pctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pctx_terminates_prog \<equiv> parity_unit_terminates"

text \<open>
  The one side condition a caller discharges per program. It is not a decision
  procedure: \<^const>\<open>pctx_terminates_prog\<close> follows when the solver's own executable
  entry point returns a result on this program's equations, and nothing here says
  that entry point returns on every input.
\<close>

lemmas pctx_terminates_prog_via_solve_c = parity_join.terminates_of_solve_c
lemmas pctx_vars_finite = parity_join.vars_finite_of_terminates

subsection \<open>Solved-result table and check report\<close>

definition analyse_parity_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_for = parity_unit_result"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.\<close>

definition analyse_parity_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result p = analyse_parity_result_for (declared_global p) p"

text \<open>
  The report the exported \<open>analyse\<close> API dispatches to. It reads its per-node state
  through \<^const>\<open>analyse_parity_result_for\<close>'s \<^type>\<open>analysis_result\<close> table ---
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a
  \<^const>\<open>Lifted\<close> point classifies at its projected state and a \<^const>\<open>Bot\<close> one
  (dead, or never covered; the two are not distinguishable here) classifies at
  \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s three-way verdict rather than
  introducing a fourth, \<open>Dead\<close> outcome the type does not carry.
\<close>

definition analyse_parity_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_for = parity_unit_report"

definition analyse_parity_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report p = analyse_parity_report_for (declared_global p) p"

text \<open>
  The state-carrying sibling: same table, with the per-check Parity environment
  attached to each entry instead of discarded, and an \<open>unreachable\<close> flag read
  straight off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split.
  The flag is \<^term>\<open>True\<close> exactly when that unknown is \<^const>\<open>Bot\<close>; what
  \<^const>\<open>Bot\<close> certifies about concrete reachability is the surrounding soundness
  statement's business, not this definition's.
\<close>

definition analyse_parity_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> parity abs_state) list" where
  "analyse_parity_report_for_with_state = parity_unit_report_with_state"

definition analyse_parity_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> parity abs_state) list" where
  "analyse_parity_report_with_state p =
     analyse_parity_report_for_with_state (declared_global p) p"

text \<open>Both halves of one solve: the locals table every check report already reads,
  and the globals beside it. Binding the solve once is what keeps a report that
  shows both from solving twice.\<close>

definition analyse_parity_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, parity abs_state) analysis_result
          \<times> (String.literal \<times> parity abs_state lifted) list" where
  "analyse_parity_ctx_solved_for = parity_unit_solved"

lemma fst_analyse_parity_ctx_solved_for [simp]:
  "fst (analyse_parity_ctx_solved_for gs p) = analyse_parity_result_for gs p"
  by (simp add: analyse_parity_ctx_solved_for_def analyse_parity_result_for_def
      parity_join.solved_eq)

subsection \<open>Solver-choice variant: the per-origin update rule\<close>

text \<open>
  The same equation system under the per-origin update rule instead of the
  always-join rule production uses, so \<open>Analyse_Dispatch\<close>'s \<open>analyse_with_solver\<close>
  can compare solver choices on one system (\<open>parity_po_equations_eq\<close> is what makes
  "one system" a theorem rather than a claim). These are bindings onto
  \<open>Parity_Assembly\<close>'s second instance, so the sibling carries the same soundness
  endpoints the default does --- the update rule is a parameter of the assembly,
  not a reason to leave it.
\<close>

abbreviation pctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog_per_origin \<equiv> parity_po_solution"

definition analyse_parity_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin_for = parity_po_result"

definition analyse_parity_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin p =
     analyse_parity_result_per_origin_for (declared_global p) p"

definition analyse_parity_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin_for = parity_po_report"

definition analyse_parity_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin p =
     analyse_parity_report_per_origin_for (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Parity's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. Like Sign,
  it has no warrowing interpretation: the four-element lattice has finite height, so
  widening has nothing to accelerate and no solved table of its own.
\<close>

interpretation parity_join_surface: analysis_surface
  analyse_parity_result bot parity_classify_check
  by unfold_locales

interpretation parity_per_origin: analysis_surface
  analyse_parity_result_per_origin bot parity_classify_check
  by unfold_locales

lemma parity_report_join_eq: "analyse_parity_report p = parity_join_surface.report p"
  by (simp add: analyse_parity_report_def analyse_parity_report_for_def
      analyse_parity_result_def analyse_parity_result_for_def
      parity_join.report_def surface_unfold)

lemma parity_report_per_origin_eq:
  "analyse_parity_report_per_origin p = parity_per_origin.report p"
  by (simp add: analyse_parity_report_per_origin_def
      analyse_parity_report_per_origin_for_def analyse_parity_result_per_origin_def
      analyse_parity_result_per_origin_for_def parity_po_asm.report_def surface_unfold)

end

