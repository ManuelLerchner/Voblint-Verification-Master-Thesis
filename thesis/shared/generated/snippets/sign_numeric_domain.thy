(* src/Analyses/Sign/Sign_Warrowing.thy *)
instantiation sign :: numeric_domain begin
definition gamma_abs_sign [simp]: "\<gamma> (a :: sign) = gamma_sign a"
definition is_empty_sign [simp]: "is_empty (a :: sign) = is_bottom_sign a"
definition to_string_sign [simp]: "to_string (a :: sign) = string_of_sign a"
instance proof intro_classes
  show "\<gamma> (bot :: sign) = {}"
    unfolding bot_sign_def by simp
next
  show "\<gamma> (top :: sign) = UNIV"
    by (simp add: gamma_sign_top)
next
  fix a b :: sign
  assume H: "a \<le> b"
  show "\<gamma> a \<subseteq> \<gamma> b"
  proof -
    have "gamma_sign a \<subseteq> gamma_sign b"
      using H unfolding less_eq_sign_def by (rule gamma_sign_mono)
    then show ?thesis by simp
  qed
next
  fix a :: sign
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (simp add: is_bottom_sign_correct)
qed
end

end
