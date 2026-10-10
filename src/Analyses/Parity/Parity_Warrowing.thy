theory Parity_Warrowing
  imports "Voblint_Domain.Parity_Lattice"
begin

section \<open>Parity warrowing and domain instance\<close>

text \<open>
  Parity is finite, so widening is join and narrowing keeps the left argument.
\<close>

instantiation parity :: warrowing begin
  definition "((a :: parity) \<nabla> b) = join_parity a b"
  definition "((a :: parity) \<Delta> b) = a"
instance proof
  fix a b :: parity
  show "a \<le> (a \<nabla> b)" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub1)
  show "b \<le> (a \<nabla> b)" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub2)
  show "b \<le> a \<Longrightarrow> b \<le> (a \<Delta> b)" unfolding narrow_parity_def by simp
  show "b \<le> a \<Longrightarrow> (a \<Delta> b) \<le> a"
    unfolding narrow_parity_def by (simp add: less_eq_parity_def)
qed
end

instantiation parity :: numeric_domain begin
definition gamma_abs_parity [simp]: "numeric_domain_class.gamma (a :: parity) = gamma_parity a"
definition is_empty_parity [simp]: "is_empty (a :: parity) = is_bottom_parity a"
definition to_string_parity [simp]:
  "to_string (a :: parity) = (if is_top_parity a then sym_top else string_of_parity a)"
instance proof
  show "numeric_domain_class.gamma (bot :: parity) = {}" unfolding bot_parity_def by simp
next
  show "numeric_domain_class.gamma (top :: parity) = UNIV" by (simp add: gamma_parity_top)
next
  fix a b :: parity
  assume H: "a \<le> b"
  have "gamma_parity a \<subseteq> gamma_parity b"
    using H unfolding less_eq_parity_def by (rule gamma_parity_mono)
  then show "numeric_domain_class.gamma a \<subseteq> numeric_domain_class.gamma b" by simp
next
  fix a :: parity
  show "is_empty a \<longleftrightarrow> numeric_domain_class.gamma a = {}"
    by (simp add: is_bottom_parity_correct)
qed
end

end
