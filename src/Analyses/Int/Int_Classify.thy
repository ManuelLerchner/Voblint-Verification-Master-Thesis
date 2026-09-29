theory Int_Classify
  imports Int_Exec "Voblint_Framework.Check_Answer"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Result.DG_Result_Construction"
begin

section \<open>Int instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Int's bundle: the Boolean recursion over
  \<^typ>\<open>exp\<close>, the three-way classification, and the node-indexed bridge to
  \<^const>\<open>checks_proven\<close> come from the comparison queries
  \<^const>\<open>int_less\<close>/\<^const>\<open>int_eq\<close> and the mode's evaluator, through the
  \<open>int_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>. Their
  soundness is \<open>int_tf.check.classify_check_proved\<close> and
  \<open>int_tf.check.classify_check_refuted\<close>.
\<close>

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained (\<open>top\<close>)
  environment, classified at the most precise mode, \<^const>\<open>Refine_Fixpoint\<close>.\<close>

definition test_env_int_bounded :: "int_dom abs_state" where
  "test_env_int_bounded =
     (\<lambda>_. top)((STR ''x'') := int_dom_sipc SPos (Ivl (Fin 4) (Fin 7)) PTop top)"

lemma int_classify_less_proved:
  "int_classify_check Refine_Fixpoint (Less (V (STR ''x'')) (N 11)) test_env_int_bounded
     = Check_Proved"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_less_refuted:
  "int_classify_check Refine_Fixpoint (Less (V (STR ''x'')) (N 0)) test_env_int_bounded
     = Check_Refuted"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_eq_unknown:
  "int_classify_check Refine_Fixpoint (Eq (V (STR ''x'')) (N 5)) test_env_int_bounded
     = Check_Unknown"
  unfolding test_env_int_bounded_def by eval

end
