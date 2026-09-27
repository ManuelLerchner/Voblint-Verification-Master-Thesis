theory Parity_Warrowing
  imports "Voblint_Domain.Parity_Lattice"
begin

section \<open>Parity warrowing and domain instance\<close>

text \<open>
  Parity is finite, so widening is join and narrowing keeps the left argument.
\<close>

instantiation parity :: warrowing begin
  definition "widen (a :: parity) b = join_parity a b"
  definition "narrow (a :: parity) b = a"
instance proof
  fix a b :: parity
  show "a \<le> widen a b" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub1)
  show "b \<le> widen a b" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub2)
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b" unfolding narrow_parity_def by simp
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_parity_def by (simp add: less_eq_parity_def)
qed
end

instantiation parity :: numeric_domain begin
definition gamma_abs_parity [simp]: "\<gamma> (a :: parity) = gamma_parity a"
definition is_empty_parity [simp]: "is_empty (a :: parity) = is_bottom_parity a"
definition to_string_parity [simp]:
  "to_string (a :: parity) = (if is_top_parity a then sym_top else string_of_parity a)"
instance proof
  show "\<gamma> (bot :: parity) = {}" unfolding bot_parity_def by simp
next
  show "\<gamma> (top :: parity) = UNIV" by (simp add: gamma_parity_top)
next
  fix a b :: parity
  assume H: "a \<le> b"
  have "gamma_parity a \<subseteq> gamma_parity b"
    using H unfolding less_eq_parity_def by (rule gamma_parity_mono)
  then show "\<gamma> a \<subseteq> \<gamma> b" by simp
next
  fix a :: parity
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (simp add: is_bottom_parity_correct)
qed
end

lemma to_string_parity_regression:
  "to_string PTop = STR ''<top>''"
  "to_string POdd = STR ''1+2<int>''"
  by eval+

end
