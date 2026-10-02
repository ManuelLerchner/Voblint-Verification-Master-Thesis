theory Interval_Classify
  imports
    Interval_Exec
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

end
