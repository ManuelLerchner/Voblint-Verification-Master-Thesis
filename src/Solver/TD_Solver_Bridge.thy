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

text \<open>Unfolds \<open>term_equivalence\<close> and \<open>solve_c_dom_def\<close> to turn the executable
  \<open>solve_c x \<noteq> None\<close> check into \<open>solve_dom x\<close>. A domain's own
  \<open>_terminates_via_solve_c\<close> lemma need only unfold its own \<open>_terminates_def\<close>
  and cite \<open>TD_side_<rule>_Interp.solve_dom_of_solve_c\<close>.\<close>

lemma (in TD_side_upd_rule) solve_dom_of_solve_c:
  assumes "solve_c x \<noteq> None"
  shows "solve_dom x"
  unfolding term_equivalence solve_c_dom_def using assms by (cases "solve_c x") auto

subsection \<open>Generic: executable termination yields a post-solution, for every update rule\<close>

text \<open>Composes \<open>solve_dom_of_solve_c\<close> with \<open>partial_post_solution\<close>, so an
  analysis instance discharges update-rule soundness with one lemma call instead of
  restating the \<open>solve_c \<Rightarrow> solve_dom \<Rightarrow> partial_post_solution\<close> chain per rule.\<close>

lemma (in TD_side_upd_rule) part_post_solution_of_solve_c:
  assumes "solve_c x \<noteq> None"
  shows "part_post_solution T x (snd (solve x)) (fst (solve x))"
proof -
  from partial_post_solution[OF solve_dom_of_solve_c[OF assms], of "fst (solve x)" "snd (solve x)"]
  show ?thesis by simp
qed

subsection \<open>Key-selected update rules\<close>

text \<open>
  A solved system's global unknowns are not all alike. Some hold what the
  analysis itself publishes and keep whatever widening policy it configured;
  others exist only to activate a local unknown --- a callee's entry is the join
  of the entry states its callers publish --- and widening one of those widens
  the callee's entry before the callee has iterated at all. \<open>update_global_keyed
  P sel other\<close> applies \<open>sel\<close> on the keys \<open>P\<close> selects and \<open>other\<close> everywhere
  else. Every \<^locale>\<open>update_rule\<close> obligation speaks about one key at a time, so
  a case split on \<open>P g\<close> discharges them from the two component rules.
\<close>

definition update_global_keyed ::
  "('g \<Rightarrow> bool)
   \<Rightarrow> ('d \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd \<Rightarrow> ('x,'g,'d,'a) ug_state_scheme
        \<Rightarrow> 'd option \<times> ('x,'g,'d,'a) ug_state_scheme)
   \<Rightarrow> ('d \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd \<Rightarrow> ('x,'g,'d,'a) ug_state_scheme
        \<Rightarrow> 'd option \<times> ('x,'g,'d,'a) ug_state_scheme)
   \<Rightarrow> 'd \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 'd \<Rightarrow> ('x,'g,'d,'a) ug_state_scheme
        \<Rightarrow> 'd option \<times> ('x,'g,'d,'a) ug_state_scheme"
where
  "update_global_keyed P sel other d orig g d' state =
     (if P g then sel d orig g d' state else other d orig g d' state)"

lemma update_rule_keyed:
  assumes sel: "update_rule init sel" and other: "update_rule init other"
  shows "update_rule init (update_global_keyed P sel other)"
proof
  show "\<forall>g orig. rho_lookup (\<rho> init) g orig \<le> \<bottom>"
    by (rule update_rule.init_rho_leq_bot[OF sel])
next
  fix "do" state' d orig g d' state g' orig'
  assume "(do, state') = update_global_keyed P sel other d orig g d' state" "g' \<noteq> g"
  then show "rho_lookup (\<rho> state') g' orig' = rho_lookup (\<rho> state) g' orig'"
    unfolding update_global_keyed_def
    by (auto split: if_splits intro: update_rule.update_global_untouched(1)[OF sel]
          update_rule.update_global_untouched(1)[OF other])
next
  fix "do" state' d orig g d' state g' orig'
  assume "(do, state') = update_global_keyed P sel other d orig g d' state" "orig' \<noteq> orig"
  then show "rho_lookup (\<rho> state') g' orig' = rho_lookup (\<rho> state) g' orig'"
    unfolding update_global_keyed_def
    by (auto split: if_splits intro: update_rule.update_global_untouched(2)[OF sel]
          update_rule.update_global_untouched(2)[OF other])
next
  fix "do" state' d orig g d' state
  assume "(do, state') = update_global_keyed P sel other d orig g d' state"
  then show "d' \<le> rho_lookup (\<rho> state') g orig"
    unfolding update_global_keyed_def
    by (auto split: if_splits intro: update_rule.update_global_recorded_in_rho[OF sel]
          update_rule.update_global_recorded_in_rho[OF other])
next
  fix state' d orig g d' state
  assume "(None, state') = update_global_keyed P sel other d orig g d' state"
    "\<forall>orig. rho_lookup (\<rho> state) g orig \<le> d"
  then show "rho_lookup (\<rho> state') g orig \<le> d"
    unfolding update_global_keyed_def
    by (auto split: if_splits intro: update_rule.update_global_preserves_rho_invariant(1)[OF sel]
          update_rule.update_global_preserves_rho_invariant(1)[OF other])
next
  fix d'' state' d orig g d' state orig'
  assume "(Some d'', state') = update_global_keyed P sel other d orig g d' state"
    "\<forall>orig. rho_lookup (\<rho> state) g orig \<le> d"
  then show "rho_lookup (\<rho> state') g orig' \<le> d''"
    unfolding update_global_keyed_def
    by (auto split: if_splits intro: update_rule.update_global_preserves_rho_invariant(2)[OF sel]
          update_rule.update_global_preserves_rho_invariant(2)[OF other])
qed

text \<open>The rule a routed analysis with widening wants: join-only on the keys \<open>P\<close>
  selects (its activation seeds), Apinis warrowing on the rest. Interpreted with
  \<open>P\<close> free, so a routed key space names its own seed predicate.\<close>

global_interpretation TD_side_seed_join_warrowing_Interp:
  TD_side_upd_rule init_basic_ug_state
    "update_global_keyed P update_global_always_join update_global_warrowing_apinis" T for P T
  defines TD_side_seed_join_warrowing_Interp_solve = TD_side_seed_join_warrowing_Interp.solve
  and TD_side_seed_join_warrowing_Interp_solve_c = TD_side_seed_join_warrowing_Interp.solve_c
  and TD_side_seed_join_warrowing_Interp_solve_rec_c =
    TD_side_seed_join_warrowing_Interp.solve_rec_c
  by (simp add: TD_side_upd_rule.intro update_rule_keyed always_join.update_rule_axioms
        warrowing_apinis.update_rule_axioms)

end
