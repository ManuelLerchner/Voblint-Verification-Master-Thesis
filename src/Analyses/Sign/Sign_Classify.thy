theory Sign_Classify
  imports Sign_Numeric_Queries "Voblint_Framework.Check_Answer"
    "Voblint_Framework.Analysis_Result" Sign_Exec
    "Voblint_Result.DG_Result_Construction"
begin

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Sign's bundle: the Boolean recursion over
  \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from the bundle's queries
  \<^const>\<open>sign_less\<close>/\<^const>\<open>sign_eq\<close> and evaluator, through the
  \<open>sign_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Transfer\<close>.
  Their facts stay under \<open>sign_tf.check.\<close>; \<open>classify_check\<close>'s two soundness
  directions are \<open>sign_tf.check.classify_check_proved\<close> and
  \<open>sign_tf.check.classify_check_refuted\<close>. This theory exercises them.
\<close>


subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>STop\<close>) environment, so each test exercises exactly the comparison it names.\<close>

definition test_env_pos :: "sign abs_state" where
  "test_env_pos = (\<lambda>_. STop)((STR ''x'') := SPos)"

lemma sign_classify_less_proved:
  "sign_classify_check (Less (N 0) (V (STR ''x''))) test_env_pos = Check_Proved"
  unfolding test_env_pos_def by eval

lemma sign_classify_less_refuted:
  "sign_classify_check (Less (V (STR ''x'')) (N 0)) test_env_pos = Check_Refuted"
  unfolding test_env_pos_def by eval

lemma sign_classify_eq_unknown:
  "sign_classify_check (Eq (V (STR ''x'')) (N 1)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

text \<open>Negation: \<open>!(x < 0)\<close> is provable under \<open>SNonNeg\<close>, going through
  \<open>check_query\<close>'s \<open>Not\<close> case (\<open>map_option HOL.Not\<close> on the un-negated
  \<open>x < 0\<close> query) rather than a one-sided reading of the positive answer.\<close>

definition test_env_nonneg :: "sign abs_state" where
  "test_env_nonneg = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

lemma sign_classify_not_proved:
  "sign_classify_check (Not (Less (V (STR ''x'')) (N 0))) test_env_nonneg = Check_Proved"
  unfolding test_env_nonneg_def by eval

text \<open>Nested \<open>And\<close>/\<open>Or\<close>: proved through the \<open>And\<close> branch alone, and unknown
  when neither branch resolves.\<close>

definition test_env_nested_proved :: "sign abs_state" where
  "test_env_nested_proved = (\<lambda>_. STop)((STR ''x'') := SPos, (STR ''y'') := SPos)"

lemma sign_classify_nested_proved:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

definition test_env_nested_unknown :: "sign abs_state" where
  "test_env_nested_unknown = (\<lambda>_. STop)((STR ''x'') := SNonNeg, (STR ''y'') := SPos)"

lemma sign_classify_nested_unknown:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

end
