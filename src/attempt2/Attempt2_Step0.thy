theory Attempt2_Step0
  imports Main
begin

(* See attempt2/PLAN.md section "Where the solver actually is":
   this theory does NOT import TD_plain; it only factors the lfp_lowerbound
   pattern used later on cfg_collect / collecting soundness (chain (2)). *)

text \<open>Step~0 of \texttt{attempt2/PLAN.md}: the Knaster--Tarski lower bound in isolation.
  Later, the CFG collecting environment is a least fixed point on a pointwise
  @{text \<open>(\<subseteq>)\<close>}-lattice of maps into powersets; this is the same one-premise rule
  (no @{text mono} in @{thm lfp_lowerbound}).\<close>

lemma attempt2_lfp_le_if_prefixed:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a" and x :: 'a
  assumes "f x \<le> x"
  shows "lfp f \<le> x"
proof (rule lfp_lowerbound)
  show "f x \<le> x"
    by (fact assms)
qed

lemma attempt2_lfp_le_fun_pointwise:
  fixes F :: "('k \<Rightarrow> 'v::complete_lattice) \<Rightarrow> 'k \<Rightarrow> 'v" and X :: "'k \<Rightarrow> 'v"
  assumes "\<And>i. F X i \<le> X i"
  shows "\<And>i. lfp F i \<le> X i"
proof -
  have "F X \<le> X"
    unfolding le_fun_def using assms by simp
  then have "lfp F \<le> X"
    by (rule lfp_lowerbound)
  then show "\<And>i. lfp F i \<le> X i"
    by (simp add: le_fun_def)
qed

end
