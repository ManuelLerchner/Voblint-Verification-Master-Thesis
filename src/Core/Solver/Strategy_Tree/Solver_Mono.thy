theory Solver_Mono
  imports "TD.TD_side"
begin

(* TD_side defines a record field \<sigma> for its internal state; hide the short
   name so our \<sigma> variables (abstract state maps) are unambiguous. *)
hide_const (open) \<sigma>

section \<open>The solver's threefold monotonicity contract\<close>

text \<open>\<open>threefold_mono\<close> bundles the conditions the optimized solver
  requires: equation values and side effects are monotone in the environment,
  while dependency sets can only shrink as the environment grows. Together they
  guarantee a least partial post-solution.\<close>

definition threefold_mono ::
  "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT \<Rightarrow> bool"
where
  "threefold_mono T \<equiv> is_mono_eq T \<and> mono_sides T \<and> mono_deps T"

lemma threefold_monoD_eq:   "threefold_mono T \<Longrightarrow> is_mono_eq T"
  unfolding threefold_mono_def by blast

lemma threefold_monoD_sides: "threefold_mono T \<Longrightarrow> mono_sides T"
  unfolding threefold_mono_def by blast

lemma threefold_monoD_deps:  "threefold_mono T \<Longrightarrow> mono_deps T"
  unfolding threefold_mono_def by blast

text \<open>Accumulating into one slot of a side map preserves the pointwise order:
  the update is a join with a slot-indexed constant, which is monotone.\<close>

lemma fun_upd_sup_mono:
  fixes m1 m2 :: "'b \<Rightarrow> 'a::bounded_semilattice_sup_bot"
  assumes "m1 \<le> m2"
  shows "m1(y := m1 y \<squnion> cd) \<le> m2(y := m2 y \<squnion> cd)"
proof -
  have eq: "\<And>m::'b \<Rightarrow> 'a. m(y := m y \<squnion> cd) = m \<squnion> ((\<lambda>_. bot)(y := cd))"
    by (rule ext) (simp add: fun_upd_def sup_fun_def)
  show ?thesis unfolding eq by (rule sup_mono[OF assms order_refl])
qed

end
