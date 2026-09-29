theory Int_Exec
  imports
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    "Voblint_Nonrelational.Nonrelational_Ops"
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Solver.TD_Solver_Bridge"
    Int_Transfer
begin

section \<open>Composite integer domain: executable transfer mirror\<close>

text \<open>
  The executable mirror of \<open>int_tf_abs\<close>/\<open>enter_int_dom_ci_for\<close> on
  \<^typ>\<open>int_dom resolved_st_q\<close>: \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle \<open>int_dom_ops mode\<close>. The mode is an argument
  like any other, chosen by public production reporting; it is orthogonal to
  equation generation and solver choice.
\<close>

subsection \<open>The state a run starts in\<close>

text \<open>A declared global holds the abstraction of \<open>0\<close>, a local the whole-value element.\<close>

abbreviation cinit_int_dom_st :: "int_dom resolved_st_q" where
  "cinit_int_dom_st \<equiv> initial_resolved_st_q top (int_dom_of_int 0)"

subsection \<open>The executable step and entry\<close>

definition int_tf_st_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow>
    int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_tf_st_for mode = generic_tf_st_for (int_dom_ops mode)"

lemmas int_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of "int_dom_ops mode" for mode, folded int_tf_st_for_def]

definition int_dom_enter_st_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q"
where
  "int_dom_enter_st_for mode = generic_enter_st_for (int_dom_ops mode)"

lemma int_dom_enter_st_for_eq [simp]:
  "int_dom_enter_st_for mode \<G> ci s =
    bind_formals_resolved_q \<G> (ci_formals ci)
      (map (\<lambda>e. aval_int_dom mode e (fun_of_resolved_st_q_for \<G> s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: int_dom_enter_st_for_def generic_enter_st_for_def)

subsection \<open>Executable/abstract correspondence\<close>

text \<open>The liveness premise is the guard's: the derived filter commutes with the
  abstract branch on a live state. \<open>int_tf.tf_st_for_commute\<close> settles every
  action, at every mode.\<close>

theorem int_tf_st_for_commute:
  assumes live: "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (int_tf_st_for mode \<G> a s) =
     int_tf_abs mode a (fun_of_resolved_st_q_for \<G> s)"
  unfolding int_tf_st_for_def
  by (rule int_tf.tf_st_for_commute[OF live])

lemma int_dom_enter_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (int_dom_enter_st_for mode \<G> ci s) =
   enter_int_dom_ci_for mode \<G> ci (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: int_tf.op_defs enter_binding_def enter_frame_def)

end
