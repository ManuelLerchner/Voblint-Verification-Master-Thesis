theory Example_Cooperating_Demo
  imports
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Framework.Local_Spec_Product"
    "Voblint_Framework.Oracle_Wrappers"
    "Voblint_Analysis_Relational.Rel_Order_Local"
    "Voblint_Analysis_Interval.Interval_Sound"
    "Voblint_Analysis_Interval.Interval_Classify"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>Two cooperating analyses on one program\<close>

text \<open>
  Interval and the order analysis run as one product. Interval consults the
  product's answer at a Boolean assignment (\<^const>\<open>assign_ask\<close>); the order
  analysis answers comparisons from its relation (\<^const>\<open>rel_qry\<close>). On the
  program below, \<open>x <= y\<close> and \<open>y <= x\<close> leave both intervals unbounded, but the
  order analysis records both pairs, so it answers \<open>x == y\<close> as true. Interval,
  asking the product at \<open>z = (x == y)\<close>, assigns \<open>1\<close>. Neither analysis alone
  knows \<open>z = 1\<close> at the end.
\<close>

definition coop_program :: imp_prog where
  "coop_program = program {
   fun main() {
     if (x <= y) {
       if (y <= x) {
         z = (x == y);
       }
     }
   }
}"

abbreviation coop_gs :: "vname \<Rightarrow> bool" where
  "coop_gs \<equiv> declared_global coop_program"

abbreviation coop_bot :: "ivl exec_dg_st \<Rightarrow> bool" where
  "coop_bot \<equiv> resolved_st_q_is_bot_for (declared_global_vars coop_program)"

definition coop_pi :: proc_table where
  "coop_pi = prog_table coop_program"

definition coop_cfg :: cfg where
  "coop_cfg = compile_prog coop_pi (prog_procs coop_program)"

subsection \<open>The Interval component\<close>

interpretation coop_ivl: routed_dg_domain_exec
  coop_gs coop_bot "ivl_tf_st_for coop_gs" "ivl_enter_st_for coop_gs"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for coop_gs" event_ivl
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def], assumption,
      rule ivl_enter_st_for_commute,
      rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])

text \<open>Interval answers a query by its own check decision on the state it holds.\<close>

fun ivl_qry :: "ivl exec_dg_st lifted \<Rightarrow> query \<Rightarrow> bool set" where
  "ivl_qry Bot q = {}"
| "ivl_qry (Lifted st) (EvalBool e) =
     admitted (interval_check_query e (fun_of_resolved_st_q_for coop_gs st))"

lemma ivl_qry_sound:
  "sound_query_handler truth_holds ivl_qry (\<lambda>d. \<lbrakk>coop_ivl.reader d\<rbrakk>\<^sub>\<bottom>)"
proof
  fix s d q
  assume "s \<in> \<lbrakk>coop_ivl.reader d\<rbrakk>\<^sub>\<bottom>"
  then show "truth_holds q (ivl_qry d q) s"
    by (cases d; cases q)
       (auto intro!: truth_holds_admitted
         dest: interval_check_domain.check_query_sound)
qed

end
