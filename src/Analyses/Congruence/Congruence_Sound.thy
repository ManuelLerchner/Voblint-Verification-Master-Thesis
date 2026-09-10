theory Congruence_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Congruence_Transfer
    Congruence_Exec
begin

section \<open>What a run's initial abstract state describes\<close>

text \<open>
  A run starts with every declared global at zero and every local
  unconstrained. The one lemma here says \<^const>\<open>cinit_congruence_st\<close>
  describes exactly that: the singleton residue class \<^term>\<open>congruence_of_int 0\<close>
  covers a declared global precisely, and \<^const>\<open>top\<close> covers an unconstrained
  local trivially. It is the one place the zero-initialization of globals is
  turned into a residue class.

  Congruence's specification, its concretization and the soundness of the one
  against the other are not restated here. Those are constants and theorems of
  \<^locale>\<open>routed_dg_domain_exec\<close>, and an assembly reaches them by interpreting
  that locale from Congruence's own commute lemmas in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Exec\<close> --- so a per-domain copy
  would only rename what the locale already proves.
\<close>

lemma congruence_cinit_gamma:
  "cinit_stores gs
     \<subseteq> gamma_state_lift (map_lift (fun_of_exec_dg_st_for gs) (Lifted cinit_congruence_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def
      fun_of_resolved_st_q_for_def fun_of_st_cinit_congruence_st_for)

end
