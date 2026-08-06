theory Sign_Checks
  imports Sign_Numeric_Queries "Voblint_Core.Abstract_Checks"
begin

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here: the Sign lattice comparison tables
  (\<open>sign_less_true\<close>/\<open>sign_less_false\<close>/\<open>sign_eq_true\<close>/\<open>sign_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Sign_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Sign expression
  evaluator \<open>aval_sign\<close> lives in \<^theory>\<open>Voblint_Analysis.Sign_Arithmetic\<close>. The
  Boolean recursion over \<^typ>\<open>bexp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way
  classification, and the node-indexed bridge to \<^const>\<open>checks_proven\<close> come
  from interpreting \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>)
  once, below, reusing the numeric-query facts already proved sound in
  \<open>sign_numeric_queries\<close> rather than re-deriving the comparison tables ---
  the same way \<open>sign_backward_domain\<close> in \<open>Sign_Backward.thy\<close> interprets
  \<open>backward_domain\<close> for guard narrowing.
\<close>

global_interpretation sign_check_domain:
  abstract_check_domain gamma_sign sign_less_true sign_less_false sign_eq_true sign_eq_false
    gamma_state aval_sign
  defines
    sign_check_true = sign_check_domain.check_true
    and sign_check_false = sign_check_domain.check_false
    and sign_classify_check = sign_check_domain.classify_check
    and sign_checks_proven = sign_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: aexp and \<sigma> :: "sign abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_sign (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_sign (aval_sign e \<sigma>)" using aval_sign_sound by blast
qed

lemmas sign_check_true_sound = sign_check_domain.check_true_sound
lemmas sign_check_false_sound = sign_check_domain.check_false_sound
lemmas sign_check_true_false_vacuous = sign_check_domain.check_true_false_vacuous
lemmas sign_classify_check_proved = sign_check_domain.classify_check_proved
lemmas sign_classify_check_refuted = sign_check_domain.classify_check_refuted
lemmas sign_checks_provenI = sign_check_domain.abstract_checks_provenI
lemmas sign_checks_proven_sound = sign_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>STop\<close>) environment, so each test exercises exactly the comparison it names.\<close>

definition test_env_pos :: "sign abs_state" where
  "test_env_pos = (\<lambda>_. STop)(''x'' := SPos)"

lemma sign_classify_less_proved:
  "sign_classify_check (Less (N 0) (V ''x'')) test_env_pos = Check_Proved"
  unfolding test_env_pos_def by eval

lemma sign_classify_less_refuted:
  "sign_classify_check (Less (V ''x'') (N 0)) test_env_pos = Check_Refuted"
  unfolding test_env_pos_def by eval

lemma sign_classify_eq_unknown:
  "sign_classify_check (Eq (V ''x'') (N 1)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

text \<open>Negation: \<open>!(x < 0)\<close> is provable under \<open>SNonNeg\<close>, going through
  \<open>check_false\<close> on the un-negated \<open>x < 0\<close> rather than a one-sided
  negation of \<open>check_true\<close>.\<close>

definition test_env_nonneg :: "sign abs_state" where
  "test_env_nonneg = (\<lambda>_. STop)(''x'' := SNonNeg)"

lemma sign_classify_not_proved:
  "sign_classify_check (Not (Less (V ''x'') (N 0))) test_env_nonneg = Check_Proved"
  unfolding test_env_nonneg_def by eval

text \<open>Nested \<open>And\<close>/\<open>Or\<close>: proved through the \<open>And\<close> branch alone, and unknown
  when neither branch resolves.\<close>

definition test_env_nested_proved :: "sign abs_state" where
  "test_env_nested_proved = (\<lambda>_. STop)(''x'' := SPos, ''y'' := SPos)"

lemma sign_classify_nested_proved:
  "sign_classify_check
     (Or (And (Less (N 0) (V ''x'')) (Less (N 0) (V ''y''))) (Eq (V ''z'') (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

definition test_env_nested_unknown :: "sign abs_state" where
  "test_env_nested_unknown = (\<lambda>_. STop)(''x'' := SNonNeg, ''y'' := SPos)"

lemma sign_classify_nested_unknown:
  "sign_classify_check
     (Or (And (Less (N 0) (V ''x'')) (Less (N 0) (V ''y''))) (Eq (V ''z'') (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

end

