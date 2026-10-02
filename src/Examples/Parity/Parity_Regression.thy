theory Parity_Regression
  imports
    "Voblint_Analysis_Parity.Parity_Exec"
begin

section \<open>Parity regression assertions\<close>

text \<open>
  Build-checked regression assertions for the Parity domain, moved out of core.
  Each lemma evaluates a Parity operation on concrete values; nothing cites them,
  the build is their consumer.
\<close>

subsection \<open>Rendering\<close>

text \<open>
  \<open>string_of_parity\<close> prints parities in Goblint's congruence notation, and the
  \<open>numeric_domain\<close> instance's \<open>to_string\<close> prints a standalone top as \<open>sym_top\<close>.
\<close>

lemma string_of_parity_regression:
  "string_of_parity PBot = sym_bottom"
  "string_of_parity PEven = STR ''2<int>''"
  "string_of_parity POdd = STR ''1+2<int>''"
  "string_of_parity PTop = sym_int"
  by eval+

lemma to_string_parity_regression:
  "to_string PTop = sym_top"
  "to_string POdd = STR ''1+2<int>''"
  by eval+

subsection \<open>Backward refinement\<close>

text \<open>
  Evaluated regression cases: an odd sum with an even operand forces the other
  odd, and an odd product forces both factors odd.
\<close>

lemma parity_inverse_regression:
  "inv_plus_parity POdd PTop PEven = (POdd, PEven)"
  "inv_minus_parity PEven PTop POdd = (POdd, POdd)"
  "inv_times_parity POdd PTop PTop = (POdd, POdd)"
  "inv_eq_parity True PTop PEven = (PEven, PEven)"
  by eval+

subsection \<open>Guard filters\<close>

text \<open>
  \<open>bfilter_parity\<close> uses the inverse operators to narrow a variable through an
  arithmetic equality guard, and leaves it alone under an order guard.
\<close>

definition test_env_parity :: "parity abs_state" where
  "test_env_parity = (\<lambda>_. PTop)((STR ''y'') := PEven)"

text \<open>\<open>x + 1 == y\<close> with \<open>y\<close> even makes \<open>x\<close> odd.\<close>
lemma bfilter_parity_plus_narrows:
  "bfilter_parity (Eq (Plus (V (STR ''x'')) (N 1)) (V (STR ''y''))) True test_env_parity
     (STR ''x'') = POdd"
  unfolding test_env_parity_def by eval

text \<open>An order guard says nothing about parity.\<close>
lemma bfilter_parity_less_identity:
  "bfilter_parity (Less (V (STR ''x'')) (N 3)) True test_env_parity (STR ''x'') = PTop"
  unfolding test_env_parity_def by eval

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>PTop\<close>) environment, so each test exercises exactly the comparison it
  names.\<close>

definition test_env_eo :: "parity abs_state" where
  "test_env_eo = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

text \<open>Disjoint parity classes: the direct equality is refuted, and its
  negation is proved --- going through \<open>check_query\<close>'s \<open>Not\<close> case on the
  un-negated equality, not a one-sided reading of the positive answer.\<close>

lemma parity_classify_eq_refuted:
  "parity_classify_check (Eq (V (STR ''x'')) (V (STR ''y''))) test_env_eo = Check_Refuted"
  unfolding test_env_eo_def by eval

lemma parity_classify_not_eq_proved:
  "parity_classify_check (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) test_env_eo = Check_Proved"
  unfolding test_env_eo_def by eval

text \<open>Same abstract value on both sides: \<open>x\<close> is \<open>PEven\<close> and the literal \<open>4\<close>
  is also \<open>PEven\<close>, but Parity has no singleton representation, so the
  equality stays unknown rather than falsely proved.\<close>

lemma parity_classify_eq_unknown:
  "parity_classify_check (Eq (V (STR ''x'')) (N 4)) test_env_eo = Check_Unknown"
  unfolding test_env_eo_def by eval

text \<open>Nested \<open>Or\<close>: proved through the negated-equality branch alone.\<close>

definition test_env_nested_proved :: "parity abs_state" where
  "test_env_nested_proved = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

lemma parity_classify_nested_proved:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

text \<open>Nested \<open>Or\<close>, unknown: neither branch resolves when both sides share a
  parity class.\<close>

definition test_env_nested_unknown :: "parity abs_state" where
  "test_env_nested_unknown = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := PEven)"

lemma parity_classify_nested_unknown:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

end
