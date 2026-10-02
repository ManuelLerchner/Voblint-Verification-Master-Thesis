theory Sign_Regression
  imports
    "Voblint_Analysis_Sign.Sign_Transfer"
begin

section \<open>Sign regression assertions\<close>

text \<open>
  Build-checked regression assertions for the Sign domain, moved out of the core
  theories. Each lemma evaluates a Sign operation on concrete values; nothing cites them.
\<close>

subsection \<open>Executable equality-narrowing tests\<close>

text \<open>
  Representative @{const inv_eq_sign} cases, directly matching the behavioral
  examples from the design: the true branch always meets, and the false
  branch narrows exactly when one operand is exactly @{term SZero} and the
  other's sign bounds it away from zero on one side.
\<close>

lemma inv_eq_sign_true_meets: "inv_eq_sign True SNonNeg SNonPos = (SZero, SZero)"
  by eval

lemma inv_eq_sign_false_zero_zero_unreachable:
  "inv_eq_sign False SZero SZero = (SBot, SBot)"
  by eval

lemma inv_eq_sign_false_nonneg_zero_narrows_pos:
  "inv_eq_sign False SNonNeg SZero = (SPos, SZero)"
  by eval

lemma inv_eq_sign_false_zero_nonneg_narrows_pos:
  "inv_eq_sign False SZero SNonNeg = (SZero, SPos)"
  by eval

lemma inv_eq_sign_false_nonpos_zero_narrows_neg:
  "inv_eq_sign False SNonPos SZero = (SNeg, SZero)"
  by eval

lemma inv_eq_sign_false_zero_nonpos_narrows_neg:
  "inv_eq_sign False SZero SNonPos = (SZero, SNeg)"
  by eval

text \<open>Neither operand is exactly @{term SZero}: the conservative identity fallback.\<close>
lemma inv_eq_sign_false_unrepresentable_identity:
  "inv_eq_sign False SPos SPos = (SPos, SPos)"
  by eval

text \<open>@{term SBot} on either side stays bottom-consistent.\<close>
lemma inv_eq_sign_false_bot_consistent:
  "inv_eq_sign False SBot SZero = (SBot, SBot)"
  by eval

subsection \<open>Executable end-to-end bfilter tests\<close>

text \<open>
  Pins \<open>bfilter_sign\<close> on \<open>x = 0\<close> over an \<open>SNonNeg\<close> store: the true branch
  narrows \<open>x\<close> to \<open>SZero\<close>, the false branch to \<open>SPos\<close>.
\<close>

definition test_env_nonneg_eq :: "sign abs_state" where
  "test_env_nonneg_eq = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

text \<open>@{text \<open>x = 0\<close>} known true meets \<open>x\<close>'s bound with @{term SZero}.\<close>
lemma bfilter_sign_eq_true_narrows:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) True test_env_nonneg_eq (STR ''x'') = SZero"
  unfolding test_env_nonneg_eq_def by eval

text \<open>@{text \<open>x != 0\<close>} known true (i.e. the guard @{text \<open>x = 0\<close>} is false) on
  @{term SNonNeg} narrows to @{term SPos}: the disequality narrowing
  @{const inv_eq_sign} supplies.\<close>
lemma bfilter_sign_eq_false_narrows_to_pos:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) False test_env_nonneg_eq (STR ''x'') = SPos"
  unfolding test_env_nonneg_eq_def by eval

subsection \<open>Executable classification tests\<close>

text \<open>
  Pins \<open>sign_classify_check\<close>'s three verdicts, including the \<open>Not\<close> case and
  nested \<open>And\<close>/\<open>Or\<close> recursion.
\<close>

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
