section \<open>Flagship: interval analysis of a counting loop, executed and certified on the D/G spine\<close>

text \<open>
  A bounded counting loop is compiled to a CFG, the D/G framework turns that graph into
  an equation system, the verified seed-joining warrowing solver computes an interval
  solution for it inside Isabelle, and the context-insensitive analysis turns that
  solution into a statement about every VIMP run of the source:
  \<open>flagship_source_run_sound\<close> bounds every store a run reaches by the published state at
  its matched program point. The bound is informative --- \<open>x in [0,20]\<close> at the loop head,
  \<open>[0,19]\<close> in the body, \<open>[20,20]\<close> on exit --- and \<open>flagship_head_bound_proper\<close> exhibits a
  store it rejects.

  The analysis is \<open>interval_seed_join\<close> below: \<open>unit_dg_analysis\<close> --- the routed
  analysis at the unit context --- at Interval's own transfer and the seed-joining
  warrowing solver, which no production Interval registration selects. It is generic
  in the program, so \<open>Example_Interval_DG_IP_Flagship\<close> reuses it.
\<close>

theory Example_Interval_DG_Flagship
  imports
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

text \<open>The phase datatype's constructor \<open>N\<close> would shadow the numeral
  constructor the source program below is written with.\<close>
hide_const (open) phase.N

subsection \<open>The analysis: Interval at the seed-joining warrowing solver\<close>

text \<open>
  An activation seed is joined and never widened, which is what
  \<^const>\<open>is_activation_seed\<close> tells the solver's key-selected update rule; every
  other unknown is warrowed. Every obligation is discharged exactly as Interval's
  production registrations discharge it, and only the three solver contracts name
  the update rule. The \<^theory_text>\<open>defines\<close> clause is what gives the published
  constants code equations, so the readings below evaluate.
\<close>

global_interpretation interval_seed_join: unit_dg_analysis
    ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
    "TD_side_seed_join_warrowing_Interp_solve is_activation_seed"
    "TD_side_seed_join_warrowing_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) is_activation_seed"
    bot interval_classify_check
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    enter_ivl_ci_for event_ivl
    "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed"
  defines
    interval_sj_spec = interval_seed_join.analysis_spec
    and interval_sj_root_query = interval_seed_join.root_query
    and interval_sj_equations = interval_seed_join.equations
    and interval_sj_solution = interval_seed_join.solution
    and interval_sj_terminates = interval_seed_join.terminates
    and interval_sj_vars = interval_seed_join.sol_vars
    and interval_sj_env = interval_seed_join.sol_env
    and interval_sj_result = interval_seed_join.result
    and interval_sj_state_at = interval_seed_join.state_at
proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,
       goal_cases)
  case (1 gs) show ?case by (rule ivl_tf.is_sound_transfer_for)
next
  case (2 gs a s) then show ?case
    unfolding fun_of_exec_dg_st_for_def
    by (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def])
next
  case (3 gs ci s) show ?case
    unfolding fun_of_exec_dg_st_for_def by (rule ivl_enter_st_for_commute)
next
  case (4 gs u ctx d ca) show ?case by simp
next
  case (5 v ctx) show ?case by simp
next
  case (6 eqs x) then show ?case
    by (rule TD_side_seed_join_warrowing_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (7 eqs x) then show ?case
    by (rule TD_side_seed_join_warrowing_Interp.finite_stabl_solve)
next
  case (8 c d s) then show ?case by (rule interval_classify_check_proved)
next
  case (9 c d s) then show ?case by (rule interval_classify_check_refuted)
next
  case 10 show ?case by (rule refl)
next
  case (11 gs) show ?case by (rule interval_cinit_gamma)
next
  case (12 eqs x) then show ?case
    by (rule TD_side_seed_join_warrowing_Interp.solve_dom_of_solve_c)
qed

declare interval_sj_spec_def [code_unfold]

subsection \<open>The VIMP source program\<close>

text \<open>
  A bounded counting loop: initialise \<open>x\<close> to \<open>0\<close>, increment while \<open>x < 20\<close>.  On
  exit \<open>x = 20\<close>.  No procedures, no globals; \<open>x\<close> is a single flow-sensitive local.
  The analysis must \<^emph>\<open>discover\<close> the bound, not assume it.
  \<open>Example_Interval_Loop_Coverage\<close> carries the same loop under the name
  \<open>loop_prog\<close> and reads it backwards through the guard instead of forwards
  on the D/G spine.
\<close>

definition flagship_prog :: imp_prog where
  "flagship_prog = program { fun main() { x = 0; while (x < 20) { x = x + 1; } } }"

text \<open>The storage classifier: \<open>flagship_prog\<close> declares no globals, so \<open>flagship_gs\<close>
  classifies \<open>x\<close> as local.\<close>
abbreviation flagship_gs :: "vname \<Rightarrow> bool" where
  "flagship_gs \<equiv> declared_global flagship_prog"

subsection \<open>CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  The whole program is
  the body of \<open>main\<close>, so it runs between \<open>FunctionEntry (STR ''main'')\<close> and
  \<open>FunctionResult (STR ''main'')\<close>; inside, \<open>x := 0\<close> falls directly into the loop head \<open>1\<close> (the
  continuation-passing compiler needs no separate join node), the guard \<open>x < 20\<close> branches
  to body \<open>2\<close> or exit \<open>3\<close>, and the increment at \<open>2\<close> jumps back to \<open>1\<close>.
\<close>

definition flagship_pi :: proc_table where
  "flagship_pi = prog_table flagship_prog"

definition flagship_cfg :: cfg where
  "flagship_cfg = compile_prog flagship_pi (prog_procs flagship_prog)"

interpretation flagship: compiled_cfg flagship_pi "prog_procs flagship_prog" flagship_cfg
  by (unfold_locales; unfold flagship_cfg_def; simp add: compile_prog_finite)

lemmas flagship_entry = flagship.entry[unfolded prog_main_name_def]

lemma flagship_calls: "calls flagship_cfg = {}"
  unfolding flagship_cfg_def flagship_pi_def
  by (rule compile_prog_calls_empty)
     (simp_all add: flagship_prog_def main_body_def prog_main_name_def)

lemma flagship_cfg_prog_cfg: "flagship_cfg = prog_cfg flagship_prog"
  by (simp add: flagship_cfg_def flagship_pi_def prog_cfg_def)

subsection \<open>Equation generation and the executable solve\<close>

text \<open>
  The seed-joining warrowing solver --- pointwise interval widening for termination
  --- \<^emph>\<open>computes\<close> a solution.  Termination is a code-generated \<^verbatim>\<open>by eval\<close> fact;
  the solution is not written by hand.
\<close>

definition flagship_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
       (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "flagship_eqs = interval_sj_equations flagship_gs flagship_prog"

lemma flagship_terminates_c:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed flagship_eqs
     (cfg_exit flagship_cfg, ()) \<noteq> None"
  by eval

lemma flagship_terminates: "interval_sj_terminates flagship_gs flagship_prog"
  unfolding interval_seed_join.terminates_code
  using TD_side_seed_join_warrowing_Interp.solve_dom_of_solve_c[OF flagship_terminates_c]
  by (simp add: flagship_eqs_def flagship_cfg_prog_cfg)

subsection \<open>Coverage\<close>

text \<open>
  Coverage is read off the solved key set: a routed callee entry is solved only once
  a caller publishes its seed, so which nodes a run visited is a fact about the run,
  decided by \<^const>\<open>vars_cover_exec\<close> over the two edge enumerations. \<open>flagship_cfg\<close>
  has no calls, so here it says every intra target was solved.
\<close>

lemma flagship_vars_cover:
  "vars_cover (prog_cfg flagship_prog) (interval_sj_vars flagship_gs flagship_prog)"
  by (rule interval_seed_join.vars_cover_of_exec_prog) eval

subsection \<open>Inspecting the certified result\<close>

lemma flagship_head_computed:
  "interval_sj_state_at flagship_gs flagship_prog (Statement 1) (STR ''x'')
     = Ivl (Fin 0) (Fin 20)"
  by eval

lemma flagship_body_computed:
  "interval_sj_state_at flagship_gs flagship_prog (Statement 2) (STR ''x'')
     = Ivl (Fin 0) (Fin 19)"
  by eval

lemma flagship_exit_computed:
  "interval_sj_state_at flagship_gs flagship_prog (Statement 3) (STR ''x'')
     = Ivl (Fin 20) (Fin 20)"
  by eval

subsection \<open>Source-level soundness\<close>

text \<open>
  \<open>interval_seed_join.source_sound\<close> turns the single \<^verbatim>\<open>by eval\<close> solver success
  \<open>flagship_terminates_c\<close> into a source-level guarantee: every reachable VIMP store
  is bounded by the published interval state at its matched program point.
\<close>

lemma flagship_wf:
  "wf_compile_input flagship_gs flagship_pi (prog_procs flagship_prog)"
  by (auto simp: wf_compile_input_simps flagship_pi_def flagship_prog_def split: if_splits)

theorem flagship_source_run_sound:
  assumes run: "star (pstep flagship_gs flagship_pi)
                  (prog_main flagship_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores flagship_gs"
  shows "\<exists>v stk. csim flagship_pi flagship_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> \<lbrakk>interval_sj_state_at flagship_gs flagship_prog v\<rbrakk>"
proof -
  have run': "star (pstep flagship_gs (prog_table flagship_prog))
                (main_body (prog_table flagship_prog), s, []) (residual, t, frs)"
    using run by (simp add: flagship_pi_def)
  have wf: "wf_compile_input flagship_gs (prog_table flagship_prog) (prog_procs flagship_prog)"
    using flagship_wf by (simp add: flagship_pi_def)
  show ?thesis
    using interval_seed_join.source_sound[OF flagship_terminates flagship_vars_cover wf init run']
    by (simp add: flagship_cfg_prog_cfg flagship_pi_def)
qed

text \<open>
  \<^bold>\<open>The bound is proper.\<close>  The published loop-head state constrains \<open>x\<close> to exactly
  \<open>[0,20]\<close> and rejects, e.g., a store with \<open>x = 100\<close>.  The guarantee therefore says
  something --- it is not the trivial \<open>gamma top = UNIV\<close>.
\<close>

theorem flagship_head_bound_proper:
  "(\<lambda>_. 100) \<notin> \<lbrakk>interval_sj_state_at flagship_gs flagship_prog (Statement 1)\<rbrakk>"
proof
  assume "(\<lambda>_. 100) \<in> \<lbrakk>interval_sj_state_at flagship_gs flagship_prog (Statement 1)\<rbrakk>"
  then have "(100::int) \<in> gamma (interval_sj_state_at flagship_gs flagship_prog (Statement 1)
      (STR ''x''))"
    by (simp add: gamma_state_def)
  then show False using flagship_head_computed by simp
qed


end

