theory Globals_Rule
  imports TD_Solver_Bridge
begin

section \<open>Which rule updates a side-effected global\<close>

text \<open>
  The vendored solver warrows every local unknown at a widening point, whichever
  instance runs. What its instances differ in is how a contribution side-effected into
  a global unknown is merged: joined into the value, joined per origin, warrowed into
  the value, or warrowed per origin. That merge is the one choice a caller makes, so it
  is a value here rather than a choice between four solvers: a single interpretation
  takes the rule as a parameter, and every solver fact holds for all four at once.
\<close>

datatype globals_rule =
    Globals_Join
  | Globals_Per_Origin
  | Globals_Warrow
  | Globals_Warrow_Per_Origin

definition update_global_of ::
    "globals_rule \<Rightarrow> 'd \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd::{bounded_semilattice_sup_bot,warrowing}
       \<Rightarrow> ('x, 'g, 'd) ug_state \<Rightarrow> 'd option \<times> ('x, 'g, 'd) ug_state" where
  "update_global_of r =
     (case r of
        Globals_Join \<Rightarrow> update_global_always_join
      | Globals_Per_Origin \<Rightarrow> update_global_per_origin
      | Globals_Warrow \<Rightarrow> update_global_warrowing_apinis
      | Globals_Warrow_Per_Origin \<Rightarrow> update_global_warrowing_per_origin)"

lemma update_rule_update_global_of:
  "update_rule init_basic_ug_state (update_global_of r)"
  by (cases r)
     (simp_all add: update_global_of_def always_join.update_rule_axioms
        per_origin.update_rule_axioms warrowing_apinis.update_rule_axioms
        warrowing_per_origin.update_rule_axioms)

global_interpretation TD_side_rule_Interp:
  TD_side_upd_rule init_basic_ug_state "update_global_of r" T for r T
  defines TD_side_rule_Interp_solve = TD_side_rule_Interp.solve
  and TD_side_rule_Interp_solve_c = TD_side_rule_Interp.solve_c
  and TD_side_rule_Interp_solve_rec_c = TD_side_rule_Interp.solve_rec_c
  by (simp add: TD_side_upd_rule.intro update_rule_update_global_of)

end
