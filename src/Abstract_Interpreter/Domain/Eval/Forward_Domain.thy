theory Forward_Domain
  imports State_Concretization "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Forward evaluation over a numeric domain\<close>

text \<open>
  Every expression-level interface of a domain needs the same two operations: an
  evaluator of expressions over an abstract state and a truth test on abstract values.
  Guard refinement (\<open>sound_refinement\<close>), the special calls of the transfer
  functions (\<open>sound_minmax_ops\<close>), the arithmetic of an expression domain
  (\<open>sound_arith_ops\<close>) and the check layer (\<open>sound_check_query\<close>)
  all build on them.  Stating the operations and their laws once lets a domain prove
  them once: the first interpretation registers them, and every later interface over
  the same operations inherits them instead of asking again.

  The evaluator is stated over any state type \<open>'d\<close> together with the stores
  \<open>\<gamma>\<^sub>S d\<close> a state describes.  The pointwise abstract states of the
  numeric domains are the instance at their pointwise \<open>gamma_state\<close>; the check layer keeps
  the state type open.
\<close>

locale sound_evaluator =
  fixes \<gamma>\<^sub>S :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain" ("\<lbrakk>_\<rbrakk>\<^sup>\<sharp>")
  assumes aval_abs_sound[intro]:
    "s \<in> \<gamma>\<^sub>S d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d)"

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

locale mono_evaluator = sound_evaluator \<gamma>\<^sub>S aval_abs
  for \<gamma>\<^sub>S :: "'d::order \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain" ("\<lbrakk>_\<rbrakk>\<^sup>\<sharp>") +
  assumes aval_abs_mono[intro]:
    "d1 \<le> d2 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sup>\<sharp> d1 \<le> \<lbrakk>e\<rbrakk>\<^sup>\<sharp> d2"

text \<open>
  \<open>mono_truth_test\<close> adds \<open>tobool_mono\<close> on top of the sound truth test,
  the downward monotonicity described above for non-empty values.
\<close>

locale mono_truth_test = sound_truth_test +
  assumes tobool_mono:
    "\<not> is_empty p1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some bv \<Longrightarrow> tobool p1 = Some bv"

end
