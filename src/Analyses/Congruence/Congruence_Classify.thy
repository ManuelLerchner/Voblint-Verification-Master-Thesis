theory Congruence_Classify
  imports
    Congruence_Exec
begin

section \<open>Deciding a check from a map of residue classes\<close>

text \<open>
  The check classifier is derived from Congruence's bundle: the Boolean recursion
  over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from the comparison tables
  \<^const>\<open>congruence_lt\<close>/\<^const>\<open>congruence_eqb\<close> and the evaluator, through the
  \<open>congruence_tf\<close> interpretation in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Transfer\<close>. Their facts stay under
  \<open>congruence_tf.check.\<close>; this theory exercises them.
\<close>

subsection \<open>Executable classification tests\<close>

text \<open>
  What Congruence can and cannot decide, pinned as executable witnesses. A
  residue class with modulus \<open>0\<close> is a single integer, so equality against a
  literal is decided in both directions. A class with a larger modulus is not,
  and ordering a non-singleton remains undecided: knowing a value modulo \<open>2\<close>
  places no bound on it.
\<close>

definition test_env_four :: "congruence abs_state" where
  "test_env_four = (\<lambda>_. top)((STR ''x'') := congruence_of_int 4)"

lemma congruence_classify_eq_proved:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 4)) test_env_four = Check_Proved"
  unfolding test_env_four_def by eval

lemma congruence_classify_eq_refuted:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_four = Check_Refuted"
  unfolding test_env_four_def by eval

text \<open>Singleton ordering is exact, including values produced by arithmetic.\<close>

lemma congruence_classify_less_proved:
  "congruence_classify_check (Less (V (STR ''x'')) (N 9)) test_env_four = Check_Proved"
  unfolding test_env_four_def by eval

text \<open>
  An even value against an odd literal. The two residue classes are disjoint, so
  this is refutable in principle; \<^const>\<open>congruence_eqb\<close> answers only when both
  sides are singletons, so the current table returns \<^const>\<open>Check_Unknown\<close>. The
  witness records the implementation's reach, not the domain's.
\<close>

definition test_env_even :: "congruence abs_state" where
  "test_env_even = (\<lambda>_. top)((STR ''x'') := mk_congruence 0 2)"

lemma congruence_classify_even_vs_odd_unknown:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 3)) test_env_even = Check_Unknown"
  unfolding test_env_even_def by eval

text \<open>Negation and the Boolean connectives go through \<open>check_query\<close>'s own
  recursion, not through a one-sided reading of the positive answer.\<close>

lemma congruence_classify_not_proved:
  "congruence_classify_check (Not (Eq (V (STR ''x'')) (N 5))) test_env_four = Check_Proved"
  unfolding test_env_four_def by eval

lemma congruence_classify_and_proved:
  "congruence_classify_check
     (And (Eq (V (STR ''x'')) (N 4)) (Not (Eq (V (STR ''x'')) (N 5)))) test_env_four
   = Check_Proved"
  unfolding test_env_four_def by eval

end
