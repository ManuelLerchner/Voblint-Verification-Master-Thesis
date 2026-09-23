theory Int_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Int_Exec_Sound
    Int_Classify
begin

section \<open>What Int supplies to the framework\<close>

text \<open>
  Two reader-commutation facts and an initial-state contract. None of the three
  mentions a context, a routing function, a seed key, or a solver.

  A commutation fact says that running Int's executable transfer and then
  reading the state back gives the same answer as reading back first and running
  the abstract transfer --- once for an edge action, once for a call entry. Each
  collapses to the commute lemma of whichever of the three refinement modes is
  in play, so neither proof knows anything about refinement beyond the case
  split.

  Int's specification, its concretization and the soundness of the one against
  the other are not restated here. Those are constants and theorems of
  \<^locale>\<open>routed_dg_domain_exec\<close>, which an assembly reaches by interpreting
  that locale from the two lemmas below --- so a per-domain copy would only
  rename what the locale already proves.
\<close>

lemma int_tf_st_for_commute:
  assumes "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (int_tf_st_for mode \<G> a s) =
       int_tf_abs mode a (fun_of_resolved_st_q_for \<G> s)"
  using assms
  by (cases mode)
     (simp_all add: int_tf_st_never_for_commute int_tf_st_once_for_commute
       int_tf_st_fixpoint_for_commute)

lemma int_dom_enter_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (int_dom_enter_st_for mode \<G> ci s) =
     enter_int_dom_ci_for mode \<G> ci (fun_of_resolved_st_q_for \<G> s)"
proof (cases mode)
  case Refine_Never
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_never_st_for_commute)
next
  case Refine_Once
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_once_st_for_commute)
next
  case Refine_Fixpoint
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_fixpoint_st_for_commute)
qed

subsection \<open>What the initial abstract state describes\<close>

text \<open>
  The stores a run may start in are described by the entry state read back
  through the executable bridge. This mentions neither a solver nor a coverage
  assumption --- only the entry state and the global-variable predicate --- so
  it is stated here rather than inside a solved-system context.
\<close>

lemma int_cinit_gamma:
  "cinit_stores \<G>
     \<subseteq> \<lbrakk>map_lift (fun_of_exec_dg_st_for \<G>) (Lifted cinit_int_dom_st)\<rbrakk>\<^sub>\<bottom>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def
      fun_of_resolved_st_q_for_def fun_of_initial_resolved_st_q gamma_int_dom_top)

end
