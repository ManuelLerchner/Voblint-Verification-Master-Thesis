section \<open>Regression: machine-integer wraparound at the check boundary\<close>

theory Example_Wraparound_Regression
  imports "Voblint_VIMP.VIMP_Elaborated" "Voblint_Analysis.Interval_Classify"
begin

text \<open>
  One source expression, two interpretations. Unbounded evaluation
  (\<^const>\<open>aval\<close>) answers \<open>2147483648\<close> for \<open>MAX_INT + 1\<close>; the machine
  semantics wraps it to \<open>-2147483648\<close> at \<^const>\<open>I32\<close>. Elaboration is
  where the difference is decided: \<^const>\<open>elaborate_to\<close> bakes the operating
  kind into every arithmetic node and the destination conversion into a
  \<^const>\<open>TCast\<close>, and \<^const>\<open>teval\<close> then reads those kinds off the tree.

  A check about such a value is classified from the elaborated tree, so the
  two interpretations disagree on a decidable guard: \<open>0 < MAX_INT + 1\<close>
  holds unbounded and fails at \<open>I32\<close>. The abstract classifier follows the
  machine semantics and refutes it.

  Each pin fixes a store and an abstract environment so that both sides are
  closed terms. Neither expression reads a variable, so the choice
  constrains nothing.
\<close>

definition wrap_store :: store where
  "wrap_store = (\<lambda>_. 0)"

definition max_int_succ :: exp where
  "max_int_succ = Plus (N 2147483647) (N 1)"

subsection \<open>Elaboration records the operating kind and the destination cast\<close>

text \<open>The shape an \<^const>\<open>EA_Assign\<close> edge into an \<^const>\<open>I32\<close> destination
  carries: the sum wraps at \<^const>\<open>I32\<close>, and the outer \<^const>\<open>TCast\<close> is the
  write site's own conversion.\<close>

lemma elaborate_to_max_int_succ:
  "elaborate_to default_tyenv I32 max_int_succ
     = TCast I32 (TPlus I32 (TN I32 2147483647) (TN I32 1))"
  unfolding max_int_succ_def by eval

subsection \<open>The two interpretations of one expression\<close>

lemma aval_max_int_succ_unbounded:
  "aval max_int_succ wrap_store = 2147483648"
  unfolding max_int_succ_def wrap_store_def by eval

lemma teval_max_int_succ_wraps:
  "teval (elaborate_to default_tyenv I32 max_int_succ) wrap_store = - 2147483648"
  unfolding max_int_succ_def wrap_store_def by eval

subsection \<open>The guard the two interpretations classify differently\<close>

definition wrap_guard :: exp where
  "wrap_guard = Less (N 0) max_int_succ"

lemma aval_wrap_guard_holds_unbounded:
  "aval wrap_guard wrap_store = 1"
  unfolding wrap_guard_def max_int_succ_def wrap_store_def by eval

lemma teval_wrap_guard_fails_at_I32:
  "teval (elaborate_syn default_tyenv wrap_guard) wrap_store = 0"
  unfolding wrap_guard_def max_int_succ_def wrap_store_def by eval

text \<open>The abstract classifier reads the same elaborated guard the compiler
  records on a check edge, so it refutes what the unbounded reading would
  have proved. \<^const>\<open>ivl_top\<close> everywhere makes the verdict depend on the
  guard alone.\<close>

definition wrap_env :: "ivl abs_state" where
  "wrap_env = (\<lambda>_. ivl_top)"

lemma interval_classify_wrap_guard_refuted:
  "interval_classify_check (elaborate_syn default_tyenv wrap_guard) wrap_env
     = Check_Refuted"
  unfolding wrap_guard_def max_int_succ_def wrap_env_def by eval

end
