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
  product's answer at an assignment (\<^const>\<open>assign_ask\<close>); the order
  analysis answers comparisons from its relation (\<^const>\<open>rel_qry\<close>). On the
  program below, \<open>x <= y\<close> and \<open>y <= x\<close> leave both intervals unbounded, but the
  order analysis records both pairs, so it answers \<open>x == y\<close> with \<open>[1,1]\<close>.
  Interval, asking the product at \<open>z = (x == y)\<close>, assigns \<open>1\<close>. Interval alone
  only knows \<open>z \<in> [0,1]\<close> there, and the order analysis tracks no values.
\<close>

definition coop_program :: imp_prog where
  "coop_program = program {
   fun main() {
     if (x <= y) {
       if (y <= x) {
         z = (x == y);
         __voblint_check(z == 1);
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

text \<open>Interval answers \<open>EvalInt e\<close> by evaluating \<open>e\<close> in the state it holds, as
  Goblint's base analysis does.\<close>

fun ivl_qry :: "ivl exec_dg_st lifted \<Rightarrow> answers" where
  "ivl_qry lifted.Bot q = \<bottom>"
| "ivl_qry (Lifted st) (EvalInt e) = aval_ivl e (fun_of_resolved_st_q_for coop_gs st)"

lemma ivl_qry_sound:
  assumes "s \<in> \<lbrakk>coop_ivl.reader d\<rbrakk>\<^sub>\<bottom>"
  shows "eval_holds q (ivl_qry d q) s"
proof (cases d)
  case (Lifted st)
  obtain e where q: "q = EvalInt e" by (cases q)
  show ?thesis
    using assms Lifted unfolding q by (auto intro: aval_ivl_sound)
qed (use assms in simp)

subsection \<open>The product\<close>

text \<open>
  The Interval component is the executable whole-state carrier with its
  assignment wrapped by \<^const>\<open>assign_ask\<close>; the order component is
  the one of \<open>rel_local_component\<close> over the program's three variables.
\<close>

abbreviation coop_vars :: "vname list" where
  "coop_vars \<equiv> [STR ''x'', STR ''y'', STR ''z'']"

abbreviation coop_ivl_tf :: "edge_action \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> ivl exec_dg_st lifted" where
  "coop_ivl_tf a \<equiv> transfer_lift coop_bot (ivl_tf_st_for coop_gs a)"

definition coop_spec ::
  "('x, 'k, unit, (ivl exec_dg_st lifted, relc) analysis_product,
    (ivl exec_dg_st lifted, relc) analysis_product) dg_spec"
where
  "coop_spec = local_dg_spec
     (qs_prod (assign_ask_qs (\<lambda>_ _. [])) (rel_qs coop_vars)) (qry_prod ivl_qry rel_qry)
     (\<lambda>A. pmap (coop_ivl_tf EA_Nop) (\<lambda>d. d))
     (\<lambda>A x e. pmap (assign_ask (\<lambda>_ x e. coop_ivl_tf (EA_Assign x e)) A x e)
                   (\<lambda>d. rel_learn A coop_vars x e (forget_relc x d)))
     (\<lambda>A sc x. pmap (coop_ivl_tf (EA_Special sc x)) (forget_relc x))
     (\<lambda>A b pol. pmap (coop_ivl_tf (if pol then EA_Assume b else EA_AssumeNot b))
                     (branch_step_rel b pol))
     (\<lambda>A p. pmap (coop_ivl_tf (EA_Body p)) (\<lambda>d. d))
     (\<lambda>A e p. pmap (coop_ivl_tf (EA_Ret e p)) (rel_ret e))
     (\<lambda>ci. prod_enter (\<lambda>d. [(d, transfer_lift coop_bot (ivl_enter_st_for coop_gs ci) d)])
                      (\<lambda>d. [(d, top_relc)]))
     (\<lambda>A ev. pmap (coop_ivl_tf (case ev of Check_Event l bc \<Rightarrow> EA_Check l bc)) (\<lambda>d. d))
     (\<lambda>ci. pmap2
        (\<lambda>dc de. case dc of lifted.Bot \<Rightarrow> lifted.Bot | Lifted x \<Rightarrow>
           (case de of lifted.Bot \<Rightarrow> lifted.Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
        (\<lambda>dc de. dc))
     (\<lambda>ci. pmap2
        (\<lambda>dcM de. transfer_lift2 coop_bot
           (\<lambda>env0 de0. combine_assign_resolved_q coop_gs (ci_dst ci)
              (lookup_resolved_st_q de0 (location_of coop_gs ret_var)) env0)
           dcM de)
        (\<lambda>d de. top_relc))"

declare coop_spec_def [code_unfold]

subsection \<open>One solver run\<close>

abbreviation coop_init :: "(ivl exec_dg_st lifted, relc) analysis_product" where
  "coop_init \<equiv> Product (Lifted (initial_resolved_st_q ivl_top ivl_top)) top_relc"

definition coop_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
     ((ivl exec_dg_st lifted, relc) analysis_product,
      (ivl exec_dg_st lifted, relc) analysis_product) dg_state) strategy_tree"
where
  "coop_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     coop_spec coop_cfg coop_init coop_init"

definition coop_sol where
  "coop_sol = TD_side_always_join_Interp_solve coop_eqs (cfg_exit coop_cfg, ())"

lemma coop_terminates:
  "TD_side_always_join_Interp_solve_c coop_eqs (cfg_exit coop_cfg, ()) \<noteq> None"
  by eval

subsection \<open>What the run establishes\<close>

text \<open>
  \<open>Statement 3\<close> is the point right after \<open>z = (x == y)\<close> and before the check
  \<open>z == 1\<close>. There the order analysis holds both \<open>(x, y)\<close> and \<open>(y, x)\<close>, and
  Interval, having received the answer \<open>[1,1]\<close> for \<open>x == y\<close>, holds \<open>z = [1,1]\<close>.
\<close>

abbreviation coop_z :: "(ivl exec_dg_st lifted, relc) analysis_product \<Rightarrow> ivl option" where
  "coop_z p \<equiv> (case pleft p of lifted.Bot \<Rightarrow> None
     | Lifted st \<Rightarrow> Some (lookup_resolved_st_q st (location_of coop_gs (STR ''z''))))"

lemma coop_after_assignment:
  "coop_z (locals (snd coop_sol (Inl (Statement 3, ())))) = Some (ivl_of_int 1)"
  "pright (locals (snd coop_sol (Inl (Statement 3, ()))))
     = RelC {(STR ''x'', STR ''y''), (STR ''y'', STR ''x'')}"
  unfolding coop_sol_def coop_eqs_def by eval+

text \<open>Interval on its own, on the same program and solver, only knows that the
  comparison yields \<open>0\<close> or \<open>1\<close>: from two unbounded intervals it cannot decide
  \<open>x == y\<close>.\<close>

definition coop_ivl_alone_sol where
  "coop_ivl_alone_sol = TD_side_always_join_Interp_solve
     (compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
        (local_state_dg_spec_st_for_lifted coop_gs coop_bot
           (ivl_tf_st_for coop_gs) (ivl_enter_st_for coop_gs))
        coop_cfg (Lifted (initial_resolved_st_q ivl_top ivl_top))
        (Lifted (initial_resolved_st_q ivl_top ivl_top)))
     (cfg_exit coop_cfg, ())"

lemma coop_ivl_alone_after_assignment:
  "(case locals (snd coop_ivl_alone_sol (Inl (Statement 3, ()))) of
      lifted.Bot \<Rightarrow> None
    | Lifted st \<Rightarrow> Some (lookup_resolved_st_q st (location_of coop_gs (STR ''z''))))
   = Some (Ivl (Fin 0) (Fin 1))"
  unfolding coop_ivl_alone_sol_def by eval

subsection \<open>The product is sound\<close>

lemma coop_ivl_component:
  "sound_local_dg_spec ivl_qry
     (\<lambda>_. coop_ivl_tf EA_Nop)
     (assign_ask (\<lambda>_ x e. coop_ivl_tf (EA_Assign x e)))
     (\<lambda>_ sc x. coop_ivl_tf (EA_Special sc x))
     (\<lambda>_ b pol. coop_ivl_tf (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>_ p. coop_ivl_tf (EA_Body p))
     (\<lambda>_ e p. coop_ivl_tf (EA_Ret e p))
     (\<lambda>ci d. [(d, transfer_lift coop_bot (ivl_enter_st_for coop_gs ci) d)])
     (\<lambda>_ ev. coop_ivl_tf (case ev of Check_Event l bc \<Rightarrow> EA_Check l bc))
     (\<lambda>ci dc de. case dc of lifted.Bot \<Rightarrow> lifted.Bot | Lifted x \<Rightarrow>
        (case de of lifted.Bot \<Rightarrow> lifted.Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
     (\<lambda>ci dcM de. transfer_lift2 coop_bot
        (\<lambda>env0 de0. combine_assign_resolved_q coop_gs (ci_dst ci)
           (lookup_resolved_st_q de0 (location_of coop_gs ret_var)) env0)
        dcM de)
     (\<lambda>d. \<lbrakk>coop_ivl.reader d\<rbrakk>\<^sub>\<bottom>) coop_gs"
  by (rule sound_local_assign_ask,
      rule sound_local_dg_spec_with_qry[OF coop_ivl.sound_local_spec_st[OF ivl_tf.is_sound_transfer_for]],
      rule ivl_qry_sound)

theorem coop_contract:
  "analysis_contract coop_spec
     (\<lambda>d g. gamma_prod (\<lambda>d. \<lbrakk>coop_ivl.reader d\<rbrakk>\<^sub>\<bottom>) gamma_rel d) coop_gs"
  unfolding coop_spec_def
  by (rule product_contract[OF coop_ivl_component rel_local_component])

end
