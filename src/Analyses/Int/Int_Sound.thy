theory Int_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Int_Exec
    Int_Classify
begin

section \<open>What Int supplies to the framework\<close>

text \<open>
  Two reader-commutation facts and an initial-state contract. None of the three
  mentions a context, a routing function, a seed key, or a solver. The
  commutation facts are \<^theory>\<open>Voblint_Analysis_Int.Int_Exec\<close>'s
  \<open>int_tf_st_for_commute\<close> and \<open>int_dom_enter_st_for_commute\<close>, proved once for
  every refinement mode.

  Int's specification, its concretization and the soundness of the one against
  the other are not restated here. Those are constants and theorems of
  \<^locale>\<open>dg_domain_exec\<close>, which an assembly reaches by interpreting that locale
  from the commutation facts --- so a per-domain copy would only rename what the
  locale already proves.
\<close>

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
