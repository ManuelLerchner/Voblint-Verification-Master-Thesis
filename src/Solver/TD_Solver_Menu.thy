theory TD_Solver_Menu
  imports TD_Solver_Bridge
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
    globals, because it widens the value already joined across every origin.
  \<^item> \<open>warrow_per_origin\<close> --- \<^const>\<open>TD_side_warrowing_per_origin_Interp_solve\<close>: widen each
    origin's own contribution against that origin's previous contribution, and join the
    widened contributions only when reading the target.  Keeps the termination guarantee
    while stopping one producer's growth from driving another producer's widening.

  \<open>warrow\<close> and \<open>warrow_per_origin\<close> are the two halves of the same choice: both widen, and
  they differ only in whether the join happens before or after the widening.  \<open>join\<close> and
  \<open>per_origin\<close> agree on every terminating run of a monotone system --- storing a
  contribution per origin and then taking \<^const>\<open>sup_over_origins\<close> reconstructs exactly the
  value accumulating them into one slot produces --- so the origin split is only observable
  once an update rule is non-monotone in the stored value, which is what widening is.

  The menu omits \<^const>\<open>TD_side_bounded_narrowing_Interp_solve\<close>, whose executable contract
  is not established here.
\<close>

type_synonym ('x, 'g, 'd) side_solver =
  "('x, 'g, 'd) eqsT \<Rightarrow> 'x \<Rightarrow> ('x set \<times> ('x + 'g \<Rightarrow> 'd))"

definition solver_menu where
  "solver_menu =
     [(STR ''join'',              TD_side_always_join_Interp_solve),
      (STR ''per_origin'',        TD_side_per_origin_Interp_solve),
      (STR ''warrow'',            TD_side_warrowing_apinis_Interp_solve),
      (STR ''warrow_per_origin'', TD_side_warrowing_per_origin_Interp_solve)]"

text \<open>Read one slot under every solver on the menu, in one call. \<open>rd\<close> projects the
  solver's value at that slot down to whatever the caller wants to compare (a single
  variable's abstract value, say); \<open>eqs\<close> is the equation system, \<open>entry\<close> the solver
  entry unknown, and \<open>k\<close> the slot to read (e.g. \<^term>\<open>Inr ctx\<close> for a keyed global).

  The projection is a parameter for a layering reason, not a convenience one:
  this theory sits below the D/G framework, so it cannot name that framework's
  \<open>locals\<close>/\<open>globs\<close> without inverting the dependency. Taking \<open>rd\<close> from the
  caller is what keeps the menu generic in the solver's value type at its own
  level.\<close>
definition run_menu where
  "run_menu rd eqs entry k =
     map (\<lambda>(nm, solve). (nm, rd (snd (solve eqs entry) k))) solver_menu"

end
