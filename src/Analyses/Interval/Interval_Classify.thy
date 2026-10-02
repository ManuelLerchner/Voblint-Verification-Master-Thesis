theory Interval_Classify
  imports Interval_Numeric_Queries Interval_Backward "Voblint_Framework.Check_Answer"
    "Voblint_Framework.Solved_Table" Interval_Exec "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_Result.DG_Result_Construction"
begin

section \<open>Interval instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Interval's bundle, mirroring
  \<open>Sign_Classify\<close>: the Boolean recursion over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the
  three-way classification, and the node-indexed bridge to
  \<^const>\<open>checks_proven\<close> come from the bundle's bound-comparison queries
  \<^const>\<open>interval_less\<close>/\<^const>\<open>interval_eq\<close> and evaluator, through the
  \<open>ivl_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Interval.Interval_Transfer\<close>.

  The classifier sits below \<open>Interval_Analyses\<close>: each registration there discharges
  its \<open>ClProved\<close>/\<open>ClRefuted\<close> obligations with \<open>ivl_tf.check.classify_check_proved\<close>
  and \<open>ivl_tf.check.classify_check_refuted\<close>.
\<close>

subsection \<open>Executable classification tests\<close>

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
  once \<open>x\<close> is known to lie strictly between \<open>3\<close> and \<open>8\<close> --- a fact only a
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

end
