theory Default_St_Restriction_Refinement
  imports Default_St_Reachability "Voblint_Framework.State_Restriction"
begin

unbundle default_st_syntax

section \<open>Refinement between executable and abstract split states\<close>

text \<open>
  The readback \<open>\<rho>\<^bsub>\<G>\<^esub>\<close> maps an executable \<^typ>\<open>'a default_st\<close>
  to the abstract \<^typ>\<open>'a abs_state\<close> it represents. It is a homomorphism
  for the local/global projections and for the routed combine, so an executable
  step and its abstract counterpart agree on the represented functions.
\<close>

subsection \<open>The represented function of ownership projections\<close>
lemma default_st_to_fun_restrict_local_for [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (restrict_local_default_st s) = restrict_local_for \<G> (\<rho>\<^bsub>\<G>\<^esub> s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma default_st_to_fun_restrict_global_for [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (restrict_global_default_st s) = restrict_global_for \<G> (\<rho>\<^bsub>\<G>\<^esub> s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

subsection \<open>The represented function of joins\<close>

text \<open>
  The lifted readback commutes with joins and is monotone. The join law is
  stated for the lifted carrier itself: the generic \<^const>\<open>map_lift\<close> form
  matches a schematic function and sends the simplifier into higher-order
  search.
\<close>

lemma map_lift_default_st_to_fun_sup [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (a \<squnion> b :: _ default_st lifted) = \<rho>\<^bsub>\<G>\<^esub> a \<squnion> \<rho>\<^bsub>\<G>\<^esub> b"
  by (cases a; cases b) simp_all

lemma map_lift_default_st_to_fun_mono:
  assumes "x \<le> (y :: _ default_st lifted)"
  shows "\<rho>\<^bsub>\<G>\<^esub> x \<le> \<rho>\<^bsub>\<G>\<^esub> y"
  using assms by (cases x; cases y; simp add: default_st_to_fun_mono)

end
