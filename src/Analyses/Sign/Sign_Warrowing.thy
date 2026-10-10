theory Sign_Warrowing
  imports "Voblint_Domain.Sign_Lattice"
begin

section \<open>Sign warrowing and domain instance\<close>

text \<open>
  Sign is finite, so widening is join and narrowing keeps the left argument.
\<close>

definition narrow_sign_td :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "narrow_sign_td a b = a"

instantiation sign :: warrowing begin
  definition "((a :: sign) \<nabla> b) = join_sign a b"
  definition "((a :: sign) \<Delta> b) = narrow_sign_td a b"
instance proof intro_classes
  fix a b :: sign
  show "a \<le> (a \<nabla> b)"
    unfolding less_eq_sign_def widen_sign_def by (rule join_sign_ub1)
  show "b \<le> (a \<nabla> b)"
    unfolding less_eq_sign_def widen_sign_def by (rule join_sign_ub2)
  show "b \<le> a \<Longrightarrow> b \<le> (a \<Delta> b)"
    unfolding narrow_sign_def narrow_sign_td_def by simp
  show "b \<le> a \<Longrightarrow> (a \<Delta> b) \<le> a"
    unfolding narrow_sign_def narrow_sign_td_def by simp
qed
end

instantiation sign :: numeric_domain begin
definition gamma_abs_sign [simp]: "numeric_domain_class.gamma (a :: sign) = gamma_sign a"
definition is_empty_sign [simp]: "is_empty (a :: sign) = is_bottom_sign a"
definition to_string_sign [simp]: "to_string (a :: sign) = string_of_sign a"
instance proof intro_classes
  show "numeric_domain_class.gamma (bot :: sign) = {}"
    unfolding bot_sign_def by simp
next
  show "numeric_domain_class.gamma (top :: sign) = UNIV"
    by (simp add: gamma_sign_top)
next
  fix a b :: sign
  assume H: "a \<le> b"
  show "numeric_domain_class.gamma a \<subseteq> numeric_domain_class.gamma b"
  proof -
    have "gamma_sign a \<subseteq> gamma_sign b"
      using H unfolding less_eq_sign_def by (rule gamma_sign_mono)
    then show ?thesis by simp
  qed
next
  fix a :: sign
  show "is_empty a \<longleftrightarrow> numeric_domain_class.gamma a = {}"
    by (simp add: is_bottom_sign_correct)
qed
end

end
