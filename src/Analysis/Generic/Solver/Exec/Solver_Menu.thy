theory Solver_Menu
  imports Solver_Side_RG
begin

section \<open>A menu of side-effecting update-rule solvers\<close>

text \<open>
  The vendored side solver comes in several \<^emph>\<open>update rules\<close> --- disciplines for how a
  global's incoming contributions are combined: plain join, per-origin join, Apinis
  warrowing (widening on globals), and their combinations.  They share one signature, so
  an example can run the \<^emph>\<open>same\<close> equation system under each discipline and compare the
  results in a single \<^theory_text>\<open>value\<close> or lemma, instead of duplicating a \<^theory_text>\<open>definition\<close> plus a read
  per solver.

  \<^item> \<open>join\<close> --- \<^const>\<open>TD_side_always_join_Interp_solve\<close>: fold every contribution into one
    slot, join.  Precise; no termination guarantee for unbounded global chains.
  \<^item> \<open>per_origin\<close> --- \<^const>\<open>TD_side_per_origin_Interp_solve\<close>: keep each write origin's
    contribution separate, join per origin.  Reproduces digest separation without the
    solver knowing about digests.
  \<^item> \<open>warrow\<close> --- \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>: widen globals for
    termination (narrow/warrow locals).  Terminates on unbounded loops; over-approximates
    globals (collapses digest partitions).

  Not on the menu: \<^const>\<open>TD_side_warrowing_per_origin_Interp_solve\<close> (widen per origin ---
  the ideal for a loop plus a precise digest, but it does not code-generate here, P11) and
  \<^const>\<open>TD_side_bounded_narrowing_Interp_solve\<close> (untested on these systems).
\<close>

type_synonym ('x, 'g, 'd) side_solver =
  "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> ('x set \<times> ('x + 'g \<Rightarrow> 'd))"

definition solver_menu where
  "solver_menu =
     [(STR ''join'',       TD_side_always_join_Interp_solve),
      (STR ''per_origin'', TD_side_per_origin_Interp_solve),
      (STR ''warrow'',     TD_side_warrowing_apinis_Interp_solve)]"

text \<open>Read one global/local slot's variable under every solver on the menu, in one call.
  \<open>eqs\<close> the equation system, \<open>entry\<close> the solver entry unknown, \<open>k\<close> the slot to read
  (e.g. \<^term>\<open>Inr ctx\<close> for a keyed global), \<open>var\<close> the program variable.\<close>
definition run_menu where
  "run_menu eqs entry k var =
     map (\<lambda>(nm, solve). (nm, lookup_st (snd (solve eqs entry) k) var)) solver_menu"

end
