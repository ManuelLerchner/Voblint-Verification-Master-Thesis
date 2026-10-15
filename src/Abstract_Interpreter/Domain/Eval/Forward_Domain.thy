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

text \<open>
  Monotonicity is not needed for soundness.  The solver's least-solution theorem and
  the monotone transfer interfaces ask for it, so it is a separate layer.
  \<open>tobool_mono\<close> reads downward: a definite answer at a coarser value survives at a
  sharper non-empty one.
\<close>

text \<open>
  \<open>mono_truth_test\<close> adds \<open>tobool_mono\<close> on top of the sound truth test,
  the downward monotonicity described above for non-empty values.
\<close>

locale mono_truth_test = sound_truth_test +
  assumes tobool_mono:
    "\<not> is_empty p1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some bv \<Longrightarrow> tobool p1 = Some bv"

end
