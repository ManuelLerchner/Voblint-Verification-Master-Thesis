theory Exec_St_Restriction_Refinement
  imports Exec_St_Transfer "Voblint_Framework.State_Restriction"
begin

section \<open>Refinement between executable and abstract split states\<close>

text \<open>
  \<^const>\<open>fun_of_resolved_st_q_for\<close> reads an executable \<^typ>\<open>'a resolved_st_q\<close>
  back as an abstract \<^typ>\<open>'a abs_state\<close>. It is a homomorphism for the
  local/global projections and for the routed combine, so an executable step
  and its abstract counterpart agree after readback.
\<close>

subsection \<open>Readback of ownership projections\<close>
lemma fun_of_resolved_st_q_for_restrict_local_for [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) =
     restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_restrict_global_for [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) =
     restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

subsection \<open>Readback of joins\<close>

lemma map_lift_fun_of_resolved_st_q_for_sup [simp]:
  "map_lift (fun_of_resolved_st_q_for gs) (a \<squnion> b) =
   map_lift (fun_of_resolved_st_q_for gs) a \<squnion> map_lift (fun_of_resolved_st_q_for gs) b"
  by (cases a; cases b; simp)

lemma map_lift_fun_of_resolved_st_q_for_mono:
  assumes "x \<le> y"
  shows "map_lift (fun_of_resolved_st_q_for gs) x \<le> map_lift (fun_of_resolved_st_q_for gs) y"
  using assms by (cases x; cases y; simp add: fun_of_resolved_st_q_for_mono)

end
