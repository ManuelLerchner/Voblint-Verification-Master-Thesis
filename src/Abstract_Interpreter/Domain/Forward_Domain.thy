theory Forward_Domain
  imports Abstract_Domain "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Forward evaluation over a numeric domain\<close>

text \<open>
  Every expression-level interface of a domain needs the same two operations: an
  evaluator of expressions over an abstract state and a truth test on abstract values.
  Guard refinement (\<open>backward_domain\<close>), the special calls of the transfer
  functions (\<open>sound_special_ops\<close>), the arithmetic of an expression domain
  (\<open>expression_domain_sound\<close>) and the check layer (\<open>abstract_expression_domain\<close>)
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
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain"
  assumes aval_abs_sound[intro]:
    "s \<in> \<gamma>\<^sub>S d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (aval_abs e d)"

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
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain" +
  assumes aval_abs_mono[intro]:
    "d1 \<le> d2 \<Longrightarrow> aval_abs e d1 \<le> aval_abs e d2"

locale mono_truth_test = sound_truth_test +
  assumes tobool_mono:
    "\<not> is_empty p1 \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some bv \<Longrightarrow> tobool p1 = Some bv"

end
