theory TD_Solver_Menu
  imports TD_Solver_Bridge
begin

section \<open>The vendored solver's update-rule disciplines\<close>

text \<open>
  This theory is a deliberate facade: it imports \<^theory>\<open>Voblint_Solver.TD_Solver_Bridge\<close>
  so that every domain's \<open>*_Analyses\<close> theory and several \<open>Example_*_DG_*\<close> theories, which
  import \<open>TD_Solver_Menu\<close> to name a concrete update-rule interpretation directly (e.g.
  \<^const>\<open>TD_side_always_join_Interp_solve\<close>), also reach the bridge facts those
  interpretations carry (\<open>TD_side_<rule>_Interp.solve_dom_of_solve_c\<close>,
  \<open>TD_side_<rule>_Interp.part_post_solution_of_solve_c\<close>) in the same import.

  The vendored side solver comes in several \<^emph>\<open>update rules\<close> --- disciplines for how a
  global's incoming contributions are combined: plain join, per-origin join, Apinis
  warrowing (widening on globals), and their combinations.

  \<^item> \<open>join\<close> --- \<^const>\<open>TD_side_always_join_Interp_solve\<close>: fold every contribution into one
    slot, join.  Precise; no termination guarantee for unbounded global chains.
  \<^item> \<open>per_origin\<close> --- \<^const>\<open>TD_side_per_origin_Interp_solve\<close>: keep each write origin's
    contribution separate, join per origin.  Reproduces digest separation without the
    solver knowing about digests.
  \<^item> \<open>warrow\<close> --- uses Apinis warrowing, widening global updates and narrowing/warrowing
    local updates.  The domain's \<^class>\<open>warrowing\<close> instance supplies the well-founded
    value evolution needed by the solver's termination argument; termination of a
    concrete system still depends on the solver's remaining hypotheses.
    Over-approximates globals, because it widens the value already joined across every
    origin.
  \<^item> \<open>warrow_per_origin\<close> --- applies the same widening discipline separately to each
    origin before joining contributions on reads.  This can prevent one producer's
    growth from forcing another producer's widening while retaining the same
    domain-level termination mechanism.

  \<open>warrow\<close> and \<open>warrow_per_origin\<close> are the two halves of the same choice: both widen, and
  they differ only in whether the join happens before or after the widening.  For monotone
  contribution systems, \<open>join\<close> and \<open>per_origin\<close> are intended to have the same joined
  declarative meaning: joining the separately stored per-origin contributions
  reconstructs the aggregate contribution; no theory here proves that result equivalence,
  and the same caveat applies to the claim that origin splitting is only observable once
  an update rule is non-monotone in the stored value, which is what widening is.

  Solver choice reaches the CLI as \<open>solver_choice\<close> (\<open>Analysis_Config\<close>), dispatched to one
  of these concrete interpretations by \<open>analyse_with_solver\<close> (\<open>Analyse_Dispatch\<close>) ---
  independently of this theory, which exists only to carry the facade import above.
\<close>

end
