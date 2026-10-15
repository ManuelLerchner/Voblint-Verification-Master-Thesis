theory State_Restriction
  imports "Voblint_VIMP.VIMP_Globals" "Voblint_Domain.Nonrelational_State"
    "Voblint_Domain.Reachability_Lift"
begin

section \<open>Reading one name of a combined state\<close>

text \<open>The two pointwise equations, so a proof about a single variable never has
  to unfold \<^const>\<open>combine_env\<close>. The nesting law is what lets a combine step
  read a returned value straight out of the callee exit: every call site owns
  \<open>ret_var\<close> as its own compiler-internal name and never a user-declared global
  (\<open>reserved_ret_var\<close>), so routing it through \<^const>\<open>combine_env\<close> a second
  time would change nothing.\<close>

lemma combine_env_local_eq [simp]:
  "\<not> \<G> x \<Longrightarrow> combine_env \<G> sc se x = sc x"
  by (simp add: combine_env_def)

lemma combine_env_global_eq [simp]:
  "\<G> x \<Longrightarrow> combine_env \<G> sc se x = se x"
  by (simp add: combine_env_def)

lemma combine_env_combine_env_left [simp]:
  "combine_env \<G> (combine_env \<G> dc g) (combine_env \<G> de g) = combine_env \<G> dc g"
  by (auto simp: combine_env_def)

end
