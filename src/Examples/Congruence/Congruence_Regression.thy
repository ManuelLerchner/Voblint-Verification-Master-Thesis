theory Congruence_Regression
  imports
    "Voblint_Analysis_Congruence.Congruence_Classify"
begin

section \<open>Congruence regression assertions\<close>

text \<open>
  The build-checked regression assertions for the Congruence domain, moved out of
  core. Each lemma evaluates a concrete value, so a change to the executable
  carrier, its rendering or the classifier fails the build here.
\<close>

subsection \<open>Lattice and executable tests\<close>

text \<open>
  Joining two classes of one modulus keeps their common residue modulo the gcd of
  modulus and residue difference; \<open>is_bottom_congruence\<close> and
  \<open>is_top_congruence\<close> separate bottom and top from a singleton and an even class.
\<close>

lemma join_congruence_same_modulus_regression:
  "mk_congruence 1 4 \<squnion> mk_congruence 3 4 =
   mk_congruence 1 2"
  by eval

lemma is_bottom_congruence_regression:
  "is_bottom_congruence bottom_congruence \<and>
   \<not> is_bottom_congruence (mk_congruence 0 0)"
  by eval

lemma is_top_congruence_regression:
  "is_top_congruence (top :: congruence) \<and>
   \<not> is_top_congruence (mk_congruence 0 2)"
  by eval

subsection \<open>Rendering\<close>

text \<open>
  \<open>string_of_congruence\<close> follows Goblint's notation, dropping a zero residue and a
  unit modulus; \<open>to_string\<close> prints top as \<open>sym_top\<close>.
\<close>

lemma string_of_congruence_regression:
  "string_of_congruence bottom_congruence = sym_bottom"
  "string_of_congruence (mk_congruence (-7) 0) = STR ''-7''"
  "string_of_congruence (mk_congruence 0 1) = sym_int"
  "string_of_congruence (mk_congruence 0 3) = STR ''3<int>''"
  "string_of_congruence (mk_congruence 4 3) = STR ''1+3<int>''"
  by eval+

lemma to_string_congruence_regression:
  "to_string (top :: congruence) = sym_top"
  "to_string (mk_congruence 1 2) = STR ''1+2<int>''"
  by eval+

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
  this is refutable in principle; \<open>congruence_eqb\<close> answers only when both
  sides are singletons, so the current table returns \<open>Check_Unknown\<close>. The
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
