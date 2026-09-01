theory TD_Solver_Bridge
  imports "TD.TD_side_upd_rule"
begin

section \<open>The semantic boundary between Voblint and the vendored TD solver\<close>

text \<open>
  What the rest of Voblint is entitled to assume once an executable TD solve
  terminates, for any concrete update rule: solver-domain membership
  (\<open>solve_dom\<close>) and, from that, a \<^const>\<open>part_post_solution\<close> -- the exact
  fact every soundness endpoint upstream consumes. Both are proved once
  \<^emph>\<open>inside\<close> the vendored \<^locale>\<open>TD_side_upd_rule\<close>, so they are available on
  every concrete interpretation without restating TD's own proof
  vocabulary (\<open>term_equivalence\<close>, \<open>solve_c_dom_def\<close>, \<open>partial_post_solution\<close>)
  at each call site.
\<close>

subsection \<open>Generic: an executable termination check yields solver-domain membership\<close>

text \<open>Every domain instance restates the same three-line bridge --- unfold its own
  \<open>_terminates_def\<close>, then \<open>term_equivalence\<close> and \<open>solve_c_dom_def\<close> turn the executable
  \<open>solve_c x \<noteq> None\<close> check into \<open>solve_dom x\<close> --- once per update rule (join, warrowing, ...)
  and once per domain (Sign, Interval, Parity). Stating it generically \<^emph>\<open>inside\<close> the vendored
  \<^locale>\<open>TD_side_upd_rule\<close> makes it available on every concrete interpretation as
  \<open>TD_side_<rule>_Interp.solve_dom_of_solve_c\<close>, so a domain's \<open>_terminates_via_solve_c\<close> lemma
  reduces to unfolding its own definition and citing this fact.\<close>

lemma (in TD_side_upd_rule) solve_dom_of_solve_c:
  assumes "solve_c x \<noteq> None"
  shows "solve_dom x"
  unfolding term_equivalence solve_c_dom_def using assms by (cases "solve_c x") auto

subsection \<open>Generic: executable termination yields a post-solution, for every update rule\<close>

text \<open>Any interpretation of the vendored \<^locale>\<open>TD_side_upd_rule\<close> --- \<open>join\<close>, \<open>per_origin\<close>,
  \<open>warrowing_apinis\<close>, and the rest --- turns a single executable termination check
  (\<open>solve_c x \<noteq> None\<close>) into a \<^const>\<open>part_post_solution\<close>, the exact fact the analyzer
  soundness spine consumes.  Proving it once \<^emph>\<open>inside the locale\<close> makes it available on every
  concrete solver as \<open>TD_side_<rule>_Interp.part_post_solution_of_solve_c\<close>, so an analysis
  instance discharges update-rule soundness with one lemma call instead of the three-step
  \<open>solve_c \<Rightarrow> solve_dom \<Rightarrow> partial_post_solution\<close> boilerplate repeated per rule.\<close>

lemma (in TD_side_upd_rule) part_post_solution_of_solve_c:
  assumes "solve_c x \<noteq> None"
  shows "part_post_solution T x (snd (solve x)) (fst (solve x))"
proof -
  from partial_post_solution[OF solve_dom_of_solve_c[OF assms], of "fst (solve x)" "snd (solve x)"]
  show ?thesis by simp
qed

end
