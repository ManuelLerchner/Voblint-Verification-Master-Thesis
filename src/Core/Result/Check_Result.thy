theory Check_Result
  imports Main
begin

section \<open>A flat three-valued check verdict\<close>

text \<open>
  \<open>check_result\<close> as a flat join-semilattice: \<open>Check_Unknown\<close> is the top element,
  \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> are incomparable, and their join is
  \<open>Check_Unknown\<close>. The canonical use is aggregating a check's verdict across
  several independently-sound sources of evidence (e.g. one abstract state per
  reachable calling context) without joining the underlying abstract states
  first: two sources agreeing stay that verdict, any disagreement collapses to
  \<open>Check_Unknown\<close> rather than asserting a verdict neither source alone
  established.
\<close>

datatype check_result = Check_Proved | Check_Refuted | Check_Unknown

instantiation check_result :: semilattice_sup
begin

definition less_eq_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> bool" where
  "less_eq_check_result x y \<longleftrightarrow> x = y \<or> y = Check_Unknown"

definition less_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> bool" where
  "less_check_result x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

definition sup_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> check_result" where
  "sup_check_result x y = (if x = y then x else Check_Unknown)"

instance
  by standard
     (auto simp: less_eq_check_result_def less_check_result_def sup_check_result_def)

end

end
