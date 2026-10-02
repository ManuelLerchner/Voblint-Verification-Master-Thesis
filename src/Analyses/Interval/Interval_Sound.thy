theory Interval_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Interval_Transfer
    Interval_Exec
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
begin

section \<open>What the initial abstract state describes\<close>

text \<open>
  Interval's specification, its concretization and the soundness of the one against the
  other are not restated here: they are \<open>ivl_tf.spec_exec\<close>, \<open>ivl_tf.spec_gamma\<close>,
  \<open>ivl_tf.sound_exec\<close> and \<open>ivl_tf.entry_cover_exec\<close>, which every non-relational
  bundle gets from \<^locale>\<open>sound_nonrelational_ops\<close>.
\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each of the four
  assembly instances: every concrete store a run may start in is described by
  \<^const>\<open>cinit_ivl_st\<close>. A declared global starts at zero, which the singleton
  interval describes exactly; a local starts unconstrained, which the unbounded
  interval describes trivially. The solver discipline does not enter into it, which
  is why one lemma serves all four.
\<close>

lemma interval_cinit_gamma:
  "cinit_stores \<G> \<subseteq> default_st_gamma \<G> cinit_ivl_st"
  by (auto simp: cinit_stores_def gamma_state_def default_st_gamma_initial)

end
