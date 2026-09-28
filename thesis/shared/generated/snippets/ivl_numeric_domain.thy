(* src/Analyses/Interval/Interval_Warrowing.thy *)
instantiation ivl :: numeric_domain begin
definition gamma_abs_ivl [simp]: "\<gamma> (a :: ivl) = gamma_ivl a"
definition is_empty_ivl [simp]: "is_empty (a :: ivl) = is_bottom_ivl a"
definition to_string_ivl [simp]:
  "to_string (a :: ivl) = (if is_top_ivl a then sym_top else string_of_ivl a)"
instance proof intro_classes
  show "\<gamma> (bot :: ivl) = {}"
    by (simp add: gamma_ivl_bot)
next
  show "\<gamma> (top :: ivl) = UNIV"
    by (simp add: gamma_ivl_top top_ivl_def)
next
  fix a b :: ivl
  assume H: "a \<le> b"
  show "\<gamma> a \<subseteq> \<gamma> b"
  proof -
    have "gamma_ivl a \<subseteq> gamma_ivl b" using H by (rule gamma_ivl_mono)
    then show ?thesis by simp
  qed
next
  fix a :: ivl
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (simp add: is_bottom_ivl_correct)
qed
end

lemma to_string_ivl_regression:
  "to_string (top :: ivl) = STR ''<top>''"
  "to_string (Ivl (Fin 0) PlusInf) = STR ''[0,+<infinity>]''"
  by eval+

end
