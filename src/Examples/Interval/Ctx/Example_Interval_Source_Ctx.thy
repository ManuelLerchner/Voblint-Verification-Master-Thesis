theory Example_Interval_Source_Ctx
  imports
    Example_Interval_DG_Ctx_Collect
    "Voblint_Soundness.Source_Activation_Sound"
begin

section \<open>Source-level context-sensitive certification for repeated calls\<close>

text \<open>
  The \<open>twice\<close> program calls one procedure from two sites.  The theorems below connect each
  source configuration to the production entry-state analysis' own slot
  (\<^const>\<open>entry_state_sg_st\<close>) for an activation admitted for the trace that produced it, read
  back and then through the lifted concretization \<^const>\<open>gamma_state_lift\<close>.  The context
  relation \<^const>\<open>entry_state_context_rel\<close> keeps the two calls separate while the source/CFG
  simulation preserves the concrete frame stack; being a relation rather than a function, what a
  trace admits is membership in \<^const>\<open>trace_context\<close>, not equality under \<^const>\<open>key\<close>.
\<close>

text \<open>The analysis' own solved reader, abbreviated for the two statements below.\<close>

abbreviation twice_ctx_sg :: "pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "twice_ctx_sg \<equiv> entry_state_sg_st twice_gs twice_empty_pred twice_pi twice_procs"

abbreviation twice_ctx_gamma :: "ivl exec_dg_st lifted \<Rightarrow> store set" where
  "twice_ctx_gamma m \<equiv> gamma_state_lift (map_lift (fun_of_resolved_st_q_for twice_gs) m)"

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the
  interval slot indexed by some context the trace that produced it admits.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s0, []) (residual, s, frs)"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v stk t c.
           csim twice_pi (compile_prog twice_pi twice_procs)
             (residual, s, frs) (v, s, stk)
           \<and> trace_context twice_gs (entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs)
               [] (compile_prog twice_pi twice_procs) t c
           \<and> s \<in> twice_ctx_gamma (twice_ctx_sg (Inl (v, c)))"
proof -
  have run': "star (pstep twice_gs twice_pi) (main_body twice_pi, s0, []) (residual, s, frs)"
    using run by simp
  show ?thesis
    by (rule source_sound_from_collecting_cap
          [where R = "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs"
             and startcontext = "[]"
             and gammaM = twice_ctx_gamma,
           OF twice_wf init run' entry_state_has_context[OF twice_entry_state_hyps]
              twice_activation_collect_sound])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source
  frame stack) is certified at the concrete seed context \<open>[]\<close> (no formal binds the root
  activation) --- no \<^typ>\<open>ltr\<close> witness, no context existential.  This is the clean user-facing
  statement for main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s0, []) (residual, s, [])"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v. csim twice_pi (compile_prog twice_pi twice_procs)
               (residual, s, []) (v, s, [])
             \<and> s \<in> twice_ctx_gamma (twice_ctx_sg (Inl (v, [])))"
proof -
  have run': "star (pstep twice_gs twice_pi) (main_body twice_pi, s0, []) (residual, s, [])"
    using run by simp
  show ?thesis
    by (rule source_sound_toplevel_from_collecting_cap
          [where R = "entry_state_context_rel twice_gs twice_empty_pred twice_pi twice_procs"
             and startcontext = "[]"
             and gammaM = twice_ctx_gamma,
           OF twice_wf init run' twice_activation_collect_sound])
qed

end


