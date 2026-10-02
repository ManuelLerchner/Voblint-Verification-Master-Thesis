theory Globals_Rule
  imports TD_Solver_Bridge
begin

section \<open>Which rule updates a side-effected global\<close>

text \<open>
  The vendored solver warrows every local unknown at a widening point, whichever
  instance runs. What its instances differ in is how a contribution side-effected into
  a global unknown is merged: joined into the value, joined per origin, warrowed into
  the value, warrowed per origin, or widened per origin with narrowing cut short once
  an origin has switched from widening to narrowing a given number of times. That
  merge is the one choice a caller makes, so it is a value here rather than a choice
  between five solvers: a single interpretation takes the rule as a parameter, and
  every solver fact holds for all five at once.
\<close>

datatype globals_rule =
    Globals_Join
  | Globals_Per_Origin
  | Globals_Warrow
  | Globals_Warrow_Per_Origin
  | Globals_Bounded_Narrowing nat

subsection \<open>One update state for every rule\<close>

text \<open>
  The bounded-narrowing rule keeps a counter per global and origin beside the
  recorded contributions; the other four rules keep only the contributions. So the
  single interpretation runs on the state with the counter, and each of the four
  runs on its contribution part and leaves the counter unchanged. Every
  \<^locale>\<open>update_rule\<close> obligation speaks about the contributions alone, so the
  lifted rule inherits them.
\<close>

definition lift_basic_rule ::
    "('d \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd \<Rightarrow> ('x, 'g, 'd) ug_state \<Rightarrow> 'd option \<times> ('x, 'g, 'd) ug_state)
     \<Rightarrow> 'd \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd \<Rightarrow> ('x, 'g, 'd) ug_state_with_gas
     \<Rightarrow> 'd option \<times> ('x, 'g, 'd) ug_state_with_gas" where
  "lift_basic_rule f d orig g d' state =
     (let (res, st) = f d orig g d' (ug_state.truncate state)
      in (res, ug_state.\<rho>_update (\<lambda>_. ug_state.\<rho> st) state))"

lemma lift_basic_ruleE:
  assumes "(res, state') = lift_basic_rule f d orig g d' state"
  obtains st where "(res, st) = f d orig g d' (ug_state.truncate state)"
    and "ug_state.\<rho> state' = ug_state.\<rho> st"
  using assms by (auto simp: lift_basic_rule_def split: prod.splits)

lemma update_rule_lift_basic_rule:
  assumes f: "update_rule init_basic_ug_state f"
  shows "update_rule init_ug_state_with_gas (lift_basic_rule f)"
proof
  show "\<forall>g orig. rho_lookup (ug_state.\<rho> init_ug_state_with_gas) g orig \<le> \<bottom>"
    by (simp add: init_ug_state_with_gas_def fmlookup_default_def)
next
  fix res state' d orig g d' state g' orig'
  assume step: "(res, state') = lift_basic_rule f d orig g d' state" and ne: "g' \<noteq> g"
  from step obtain st where e: "(res, st) = f d orig g d' (ug_state.truncate state)"
    and r: "ug_state.\<rho> state' = ug_state.\<rho> st" by (rule lift_basic_ruleE)
  show "rho_lookup (ug_state.\<rho> state') g' orig' = rho_lookup (ug_state.\<rho> state) g' orig'"
    using update_rule.update_global_untouched(1)[OF f e ne] by (simp add: r)
next
  fix res state' d orig g d' state g' orig'
  assume step: "(res, state') = lift_basic_rule f d orig g d' state" and ne: "orig' \<noteq> orig"
  from step obtain st where e: "(res, st) = f d orig g d' (ug_state.truncate state)"
    and r: "ug_state.\<rho> state' = ug_state.\<rho> st" by (rule lift_basic_ruleE)
  show "rho_lookup (ug_state.\<rho> state') g' orig' = rho_lookup (ug_state.\<rho> state) g' orig'"
    using update_rule.update_global_untouched(2)[OF f e ne] by (simp add: r)
next
  fix res state' d orig g d' state
  assume step: "(res, state') = lift_basic_rule f d orig g d' state"
  from step obtain st where e: "(res, st) = f d orig g d' (ug_state.truncate state)"
    and r: "ug_state.\<rho> state' = ug_state.\<rho> st" by (rule lift_basic_ruleE)
  show "d' \<le> rho_lookup (ug_state.\<rho> state') g orig"
    using update_rule.update_global_recorded_in_rho[OF f e] by (simp add: r)
next
  fix state' d orig g d' state
  assume step: "(None, state') = lift_basic_rule f d orig g d' state"
    and inv: "\<forall>orig. rho_lookup (ug_state.\<rho> state) g orig \<le> d"
  from step obtain st where e: "(None, st) = f d orig g d' (ug_state.truncate state)"
    and r: "ug_state.\<rho> state' = ug_state.\<rho> st" by (rule lift_basic_ruleE)
  show "rho_lookup (ug_state.\<rho> state') g orig \<le> d"
    using update_rule.update_global_preserves_rho_invariant(1)[OF f e] inv by (simp add: r)
next
  fix d'' state' d orig g d' state orig'
  assume step: "(Some d'', state') = lift_basic_rule f d orig g d' state"
    and inv: "\<forall>orig. rho_lookup (ug_state.\<rho> state) g orig \<le> d"
  from step obtain st where e: "(Some d'', st) = f d orig g d' (ug_state.truncate state)"
    and r: "ug_state.\<rho> state' = ug_state.\<rho> st" by (rule lift_basic_ruleE)
  show "rho_lookup (ug_state.\<rho> state') g orig' \<le> d''"
    using update_rule.update_global_preserves_rho_invariant(2)[OF f e] inv by (simp add: r)
qed

subsection \<open>The rule as a value\<close>

definition update_global_of ::
    "globals_rule \<Rightarrow> 'd \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd::{bounded_semilattice_sup_bot,warrowing}
       \<Rightarrow> ('x, 'g, 'd) ug_state_with_gas \<Rightarrow> 'd option \<times> ('x, 'g, 'd) ug_state_with_gas" where
  "update_global_of r =
     (case r of
        Globals_Join \<Rightarrow> lift_basic_rule update_global_always_join
      | Globals_Per_Origin \<Rightarrow> lift_basic_rule update_global_per_origin
      | Globals_Warrow \<Rightarrow> lift_basic_rule update_global_warrowing_apinis
      | Globals_Warrow_Per_Origin \<Rightarrow> lift_basic_rule update_global_warrowing_per_origin
      | Globals_Bounded_Narrowing n \<Rightarrow> update_global_bounded_narrowing n)"

lemma update_rule_update_global_of:
  "update_rule init_ug_state_with_gas (update_global_of r)"
  by (cases r)
     (simp_all add: update_global_of_def update_rule_lift_basic_rule
        always_join.update_rule_axioms per_origin.update_rule_axioms
        warrowing_apinis.update_rule_axioms warrowing_per_origin.update_rule_axioms
        bounded_narrowing.update_rule_axioms)

global_interpretation TD_side_rule_Interp:
  TD_side_upd_rule init_ug_state_with_gas "update_global_of r" T for r T
  defines TD_side_rule_Interp_solve = TD_side_rule_Interp.solve
    and TD_side_rule_Interp_solve_c = TD_side_rule_Interp.solve_c
    and TD_side_rule_Interp_solve_rec_c = TD_side_rule_Interp.solve_rec_c
  by (simp add: TD_side_upd_rule.intro update_rule_update_global_of)

text \<open>The solver contract of the pipeline, once for every rule.\<close>

lemma td_certified_solver:
  "certified_solver (TD_side_rule_Interp_solve r)
     (TD_side_rule_Interp.solve_dom TYPE('g) TYPE('d::{bounded_semilattice_sup_bot,warrowing}) r)
     (TD_side_rule_Interp_solve_c r)"
  by unfold_locales
     (erule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing],
      erule TD_side_rule_Interp.finite_stabl_solve,
      erule TD_side_rule_Interp.solve_dom_of_solve_c,
      simp add: TD_side_rule_Interp.solve_code_equation)

end
