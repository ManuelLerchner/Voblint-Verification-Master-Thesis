theory Int_Exec_Sound
  imports
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Int_Exec
    Int_Warrowing
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
    "Voblint_Solver.TD_Solver_Bridge"
begin

section \<open>Choosing the composite integer transfer by refinement mode\<close>

text \<open>
  The composite domain \<open>int_dom\<close> refines its four components against each other, and
  how often it does so is a \<^typ>\<open>refine_mode\<close>: \<^const>\<open>Refine_Never\<close>,
  \<^const>\<open>Refine_Once\<close>, or \<^const>\<open>Refine_Fixpoint\<close>, which public production reporting
  selects. The mode is orthogonal to equation generation and solver choice, so it is
  chosen here, once, by two dispatchers over the executable transfer and entry
  operations of \<open>Int_Exec\<close>.

  Each mode case is a bare reference to its own \<open>Int_Exec\<close> definition, so none of the
  three modes' distinct capabilities collapse into the dispatchers. In particular they
  do not imply a uniform monotonicity fact across modes --- \<^const>\<open>Refine_Fixpoint\<close>
  still has none (\<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>'s own header explains
  why), and no soundness route cites transfer monotonicity.
\<close>

fun int_tf_st_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow>
    int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_tf_st_for Refine_Never gs = int_tf_st_never_for gs"
| "int_tf_st_for Refine_Once gs = int_tf_st_once_for gs"
| "int_tf_st_for Refine_Fixpoint gs = int_tf_st_fixpoint_for gs"

fun int_dom_enter_st_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow>
      int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_dom_enter_st_for Refine_Never gs = int_dom_enter_never_st_for gs"
| "int_dom_enter_st_for Refine_Once gs = int_dom_enter_once_st_for gs"
| "int_dom_enter_st_for Refine_Fixpoint gs = int_dom_enter_fixpoint_st_for gs"

end

