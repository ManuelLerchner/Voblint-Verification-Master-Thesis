theory Parity_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Parity_Exec
begin

section \<open>What a run's initial abstract state describes\<close>

text \<open>
  A run starts with every declared global at zero and every local
  unconstrained. The one lemma here says \<^const>\<open>cinit_parity_st\<close> describes
  exactly that: zero is even, so \<^const>\<open>PEven\<close> covers a declared global
  precisely, and \<^const>\<open>PTop\<close> covers an unconstrained local trivially.
  Choosing \<^const>\<open>PEven\<close> rather than \<^const>\<open>PTop\<close> for globals is what makes
  this a fact worth owning: it is the one place the zero-initialization of
  globals is turned into a parity.

  Parity's specification, its concretization and the soundness of the one
  against the other are not restated here. Those are constants and theorems of
  \<^locale>\<open>dg_domain_exec\<close>, and an assembly reaches them by interpreting
  that locale from Parity's own commute lemmas in
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Exec\<close> --- so a per-domain copy would
  only rename what the locale already proves.
\<close>

lemma parity_cinit_gamma:
  "cinit_stores \<G>
     \<subseteq> \<lbrakk>map_lift (default_st_to_fun \<G>) (Lifted cinit_parity_st)\<rbrakk>\<^sub>\<bottom>"
  by (auto simp: cinit_stores_def gamma_state_def
      default_st_to_fun_def default_st_to_fun_initial)


end
