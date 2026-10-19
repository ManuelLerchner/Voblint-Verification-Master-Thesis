theory Forward_Domain
  imports State_Concretization "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Truth tests on a numeric domain\<close>

text \<open>
  A truth test answers \<open>Some b\<close> only when every integer the abstract value
  concretizes to has truthiness \<open>b\<close>; \<open>None\<close> means the value cannot decide.
\<close>

locale sound_truth_test =
  fixes tobool :: "'a::numeric_domain \<Rightarrow> bool option"
  assumes tobool_sound:
    "tobool p = Some b \<Longrightarrow> i \<in> \<gamma> p \<Longrightarrow> truthy i = b"

end
