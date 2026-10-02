theory Default_St_Restriction_Refinement
  imports Default_St_Transfer "Voblint_Framework.State_Restriction"
begin

section \<open>Refinement between executable and abstract split states\<close>

text \<open>
  \<^const>\<open>default_st_to_fun\<close> maps an executable \<^typ>\<open>'a default_st\<close>
  to the abstract \<^typ>\<open>'a abs_state\<close> it represents. It is a homomorphism
  for the local/global projections and for the routed combine, so an executable
  step and its abstract counterpart agree on the represented functions.
\<close>

subsection \<open>The represented function of ownership projections\<close>
lemma default_st_to_fun_restrict_local_for [simp]:
  "readback \<G> (restrict_local_default_st s) =
     restrict_local_for \<G> (readback \<G> s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma default_st_to_fun_restrict_global_for [simp]:
  "readback \<G> (restrict_global_default_st s) =
     restrict_global_for \<G> (readback \<G> s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

subsection \<open>The represented function of joins\<close>

lemma map_lift_default_st_to_fun_sup [simp]:
  "map_lift (default_st_to_fun \<G>) (a \<squnion> b) =
   map_lift (default_st_to_fun \<G>) a \<squnion> map_lift (default_st_to_fun \<G>) b"
  by (cases a; cases b; simp)

lemma map_lift_default_st_to_fun_mono:
  assumes "x \<le> y"
  shows "map_lift (default_st_to_fun \<G>) x \<le> map_lift (default_st_to_fun \<G>) y"
  using assms by (cases x; cases y; simp add: default_st_to_fun_mono)

end
