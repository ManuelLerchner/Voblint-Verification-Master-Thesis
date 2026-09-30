theory TD_Solver_Bridge
  imports "TD.TD_side_Interface"
begin

section \<open>The semantic boundary between Voblint and the vendored TD solver\<close>

subsection \<open>What a pipeline asks of its solver\<close>

text \<open>
  Three facts are everything the analysis pipeline uses about a solver: a solve in
  the solver's domain answers a partial post-solution over finitely many keys, and
  the executable check \<open>solve_c\<close> succeeding places the query in that domain. TD
  proves all three inside \<^locale>\<open>TD_side_upd_rule\<close>
  (\<open>partial_post_solution\<close>, \<open>finite_stabl_solve\<close>, \<open>solve_dom_of_solve_c\<close>).
  \<open>certified_solver\<close> names that contract once, over any equation system, so a
  pipeline assumes one locale instead of three facts and a solver discharges it
  once for all of its instances.
\<close>

locale certified_solver =
  fixes solve :: "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT
                  \<Rightarrow> 'x \<Rightarrow> 'x set \<times> ('x + 'g \<Rightarrow> 'd)"
    and solve_dom :: "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> bool"
    and solve_c :: "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> ('x set \<times> ('x + 'g \<Rightarrow> 'd)) option"
  assumes solve_pp:
      "\<And>eqs x. solve_dom eqs x
         \<Longrightarrow> part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    and solve_fin: "\<And>eqs x. solve_dom eqs x \<Longrightarrow> finite (fst (solve eqs x))"
    and dom_of_solve_c: "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow> solve_dom eqs x"

end
