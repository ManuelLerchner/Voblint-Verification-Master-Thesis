theory Sign_Checks
  imports Sign_Classify
    "Voblint_Framework.Check_Report"
    "Voblint_Result.Analysis_Surface"
    Sign_Analyses
begin

section \<open>What a whole-program Sign run reports\<close>

text \<open>
  Sign's public runtime API. Every name here is a binding onto
  \<open>Sign_Assembly\<close>'s instance of the shared unit-context assembly, which already
  built the equation system, ran the solver, read the solution back into a result
  table and classified the compiled checks against it. Only two things are Sign's
  own and are therefore defined rather than bound: the per-origin solver sibling,
  which solves the same equations under a second update rule, and the globals
  published beside the table.

  A context-sensitive run pairs the same classifier with a different solved
  system, so it needs \<open>Sign_Classify\<close> alone and none of the names below.
\<close>

subsection \<open>The solved system, under the name the CLI already uses\<close>

text \<open>
  These three are notation, not a layer: an \<^theory_text>\<open>abbreviation\<close> introduces no
  constant, so nothing has to be unfolded to get back to the assembly and nothing
  extra reaches the code generator.
\<close>

abbreviation sctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
            (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_eqs_prog \<equiv> sign_unit_equations"

abbreviation sctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog \<equiv> sign_unit_solution"

abbreviation sctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sctx_terminates_prog \<equiv> sign_unit_terminates"

text \<open>
  The one side condition a caller decides per program, in the shape that decides
  it: run the solver's own executable termination check on this program's
  equations.
\<close>

lemmas sctx_terminates_prog_via_solve_c = sign_join.terminates_of_solve_c
lemmas sctx_vars_finite = sign_join.vars_finite_of_terminates

subsection \<open>Solved-result table and check report\<close>

definition analyse_sign_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_for = sign_unit_result"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.\<close>

definition analyse_sign_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result p = analyse_sign_result_for (declared_global p) p"

text \<open>
  The report the exported \<open>analyse\<close> API dispatches to. It reads its per-node
  state through \<^const>\<open>analyse_sign_result_for\<close>'s \<^type>\<open>analysis_result\<close> table
  --- \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup --- so a
  \<^const>\<open>Lifted\<close> point classifies at its projected state and a \<^const>\<open>Bot\<close> one
  (dead, or never covered; the two are not distinguishable here) classifies at
  \<^const>\<open>bot\<close>. That preserves \<^type>\<open>check_result\<close>'s three-way verdict rather
  than introducing a fourth, \<open>Dead\<close> outcome the type does not carry.
\<close>

definition analyse_sign_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_for = sign_unit_report"

definition analyse_sign_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report p = analyse_sign_report_for (declared_global p) p"

text \<open>
  The state-carrying sibling: same table, with the per-check Sign environment
  attached to each entry instead of discarded, and an \<open>unreachable\<close> flag read
  straight off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split.
  The flag is \<^term>\<open>True\<close> exactly when that unknown is \<^const>\<open>Bot\<close>; what
  \<^const>\<open>Bot\<close> certifies about concrete reachability is the surrounding soundness
  statement's business, not this definition's.
\<close>

definition analyse_sign_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> sign abs_state) list" where
  "analyse_sign_report_for_with_state = sign_unit_report_with_state"

definition analyse_sign_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> sign abs_state) list" where
  "analyse_sign_report_with_state p = analyse_sign_report_for_with_state (declared_global p) p"

text \<open>Both halves of one solve: the locals table every check report already
  reads, and the globals beside it. Binding the solve once is what keeps a report
  that shows both from solving twice.\<close>

definition analyse_sign_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, sign abs_state) analysis_result
          \<times> (String.literal \<times> sign abs_state lifted) list" where
  "analyse_sign_ctx_solved_for = sign_unit_solved"

lemma fst_analyse_sign_ctx_solved_for [simp]:
  "fst (analyse_sign_ctx_solved_for gs p) = analyse_sign_result_for gs p"
  by (simp add: analyse_sign_ctx_solved_for_def analyse_sign_result_for_def
      sign_join.solved_eq)

subsection \<open>Solver-choice variant: the per-origin update rule\<close>

text \<open>
  The same \<^const>\<open>sctx_eqs_prog\<close> equation system solved under the per-origin
  update rule instead of the always-join rule production uses, so
  \<open>Analyse_Dispatch\<close>'s \<open>analyse_with_solver\<close> can compare solver choices on one
  system (\<open>sign_po_equations_eq\<close> is what makes "one system" a theorem rather than a
  claim). These are bindings onto \<open>Sign_Assembly\<close>'s second instance, so the sibling
  carries the same soundness endpoints the default does --- the update rule is a
  parameter of the assembly, not a reason to leave it.
\<close>

abbreviation sctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
            \<times> (pp \<times> unit + (unit, unit) routed_gk
                 \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog_per_origin \<equiv> sign_po_solution"

definition analyse_sign_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin_for = sign_po_result"

definition analyse_sign_result_per_origin :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin p = analyse_sign_result_per_origin_for (declared_global p) p"

definition analyse_sign_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_per_origin p =
     sign_po_report (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Sign's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. There is no
  warrowing interpretation because there is no warrowing table to name: Sign's
  carrier has finite height, so warrowing has nothing to accelerate and no solved
  table of its own was ever built. The absent interpretation and the absent solver
  route agree by construction rather than by a separately maintained legality
  table.
\<close>

interpretation sign_join_surface: analysis_surface
  analyse_sign_result bot sign_classify_check
  by unfold_locales

interpretation sign_per_origin: analysis_surface
  analyse_sign_result_per_origin bot sign_classify_check
  by unfold_locales

lemma sign_report_join_eq: "analyse_sign_report p = sign_join_surface.report p"
  by (simp add: analyse_sign_report_def analyse_sign_report_for_def
      analyse_sign_result_def analyse_sign_result_for_def
      sign_join.report_def surface_unfold)

lemma sign_report_per_origin_eq:
  "analyse_sign_report_per_origin p = sign_per_origin.report p"
  by (simp add: analyse_sign_report_per_origin_def analyse_sign_result_per_origin_def
      analyse_sign_result_per_origin_for_def sign_po_asm.report_def surface_unfold)

end
