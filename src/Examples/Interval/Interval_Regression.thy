theory Interval_Regression
  imports
    "Voblint_Analysis_Interval.Interval_Transfer"
begin

section \<open>Interval regression assertions\<close>

text \<open>
  Build-checked regression assertions for the Interval domain, moved out of the
  core theories. Each lemma evaluates a concrete value; nothing cites them.
\<close>

subsection \<open>Rendering\<close>

text \<open>
  \<open>string_of_ivl\<close> prints bounds as \<open>[l,u]\<close> and every empty representation as
  \<open>sym_bottom\<close>; \<open>to_string\<close> prints the standalone top as \<open>sym_top\<close>.
\<close>

lemma string_of_ivl_regression:
  "string_of_ivl (Ivl (Fin (-3)) (Fin 5)) = STR ''[-3,5]''"
  "string_of_ivl (Ivl MinInf (Fin 0)) = STR ''[-<infinity>,0]''"
  "string_of_ivl (Ivl MinInf PlusInf) = STR ''[-<infinity>,+<infinity>]''"
  "string_of_ivl (Ivl (Fin 5) (Fin (-1))) = sym_bottom"
  "string_of_ivl (Ivl PlusInf PlusInf) = sym_bottom"
  by eval+

lemma to_string_ivl_regression:
  "to_string (top :: ivl) = sym_top"
  "to_string (Ivl (Fin 0) PlusInf) = STR ''[0,+<infinity>]''"
  by eval+

subsection \<open>Check classification\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>ivl_top\<close>) environment, so each test exercises exactly the comparison it
  names, and one showing the precision gain over Sign: a bounded range proves
  both a wider upper bound and a tighter lower bound in one classification,
  which Sign's four-value lattice cannot distinguish from \<open>STop\<close>.\<close>

definition test_env_bounded :: "ivl abs_state" where
  "test_env_bounded = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_less_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 11)) test_env_bounded = Check_Proved"
  unfolding test_env_bounded_def by eval

lemma interval_classify_less_refuted:
  "interval_classify_check (Less (V (STR ''x'')) (N 0)) test_env_bounded = Check_Refuted"
  unfolding test_env_bounded_def by eval

lemma interval_classify_eq_unknown:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_bounded = Check_Unknown"
  unfolding test_env_bounded_def by eval

text \<open>The precision gain over Sign: \<open>0 < x\<close> and \<open>x < 8\<close> both hold outright
  once \<open>x\<close> is known to lie strictly between \<open>3\<close> and \<open>8\<close>, a fact only a
  domain that tracks numeric bounds can prove; Sign's \<open>SPos\<close>/\<open>SNonNeg\<close> would
  classify \<open>x < 8\<close> \<^term>\<open>Check_Unknown\<close> on the same information.\<close>

definition test_env_precision :: "ivl abs_state" where
  "test_env_precision = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_precision_lower_proved:
  "interval_classify_check (Less (N 2) (V (STR ''x''))) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

lemma interval_classify_precision_upper_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 9)) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

subsection \<open>Numeric queries\<close>

text \<open>
  Permanent regression witnesses for the touching-boundary case: before
  \<open>Interval_Numeric_Queries\<close>'s \<open>u2 < l1\<close> was weakened to \<open>u2 \<le> l1\<close>,
  \<open>interval_less_false\<close> could not refute \<open>0 < x\<close> for \<open>x = [-inf,0]\<close> (a range entirely \<open>\<le> 0\<close>) because the
  witnessing bound touches rather than strictly separates.
\<close>

lemma interval_less_false_witness_touching_boundary:
  "interval_less_false (Ivl (Fin 0) (Fin 0)) (Ivl MinInf (Fin 0))"
  by simp

lemma interval_less_false_witness_touching_boundary_finite:
  "interval_less_false (Ivl (Fin 1) (Fin 1)) (Ivl MinInf (Fin 1))"
  by simp

text \<open>\<open>interval_eq_false\<close> refutes equality of the disjoint intervals \<open>[1,2]\<close>
  and \<open>[5,6]\<close>, the witness whose raw meet is not \<open>bot\<close>.\<close>

lemma interval_eq_false_witness_disjoint:
  "interval_eq_false (Ivl (Fin 1) (Fin 2)) (Ivl (Fin 5) (Fin 6))"
  by (simp add: less_eint_def)

end
