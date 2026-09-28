(* src/Analyses/Parity/Parity_Warrowing.thy *)
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
