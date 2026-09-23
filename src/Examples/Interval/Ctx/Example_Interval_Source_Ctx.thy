theory Example_Interval_Source_Ctx
  imports
    Example_Interval_DG_Ctx_Collect
    "Voblint_Result.Source_Activation_Sound"
begin

section \<open>Source-level context-sensitive certification for repeated calls\<close>

text \<open>
  The \<open>twice\<close> program calls one procedure from two sites.  The theorems below connect each
  source configuration to the solved reader of Interval's entry-state registration
  \<open>interval_es_rule\<close> at \<^const>\<open>Globals_Warrow\<close>, for an activation admitted for the
  trace that produced it, read back and then through the lifted concretization
  \<^const>\<open>gamma_state_lift\<close>.  The admitted-context relation
  \<^const>\<open>routed_dg_analysis.admitted_contexts\<close> keeps the two calls separate while the
  source/CFG simulation preserves the concrete frame stack; being a relation rather than a
  function, what a trace admits is membership in \<^const>\<open>trace_context\<close>, not an equation.
\<close>

text \<open>The analysis' own solved reader, abbreviated for the two statements below.\<close>

abbreviation twice_ctx_sg ::
  "pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "twice_ctx_sg \<equiv> interval_es_rule.reader Globals_Warrow twice_gs twice_program"

abbreviation twice_ctx_gamma :: "ivl exec_dg_st lifted \<Rightarrow> store set" where
  "twice_ctx_gamma m \<equiv> \<lbrakk>map_lift (fun_of_resolved_st_q_for twice_gs) m\<rbrakk>\<^sub>\<bottom>"

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the
  interval slot indexed by some context the trace that produced it admits.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "twice_gs, twice_pi \<turnstile> (twice_main, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v stk t c.
           twice_pi, compile_prog twice_pi twice_procs \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> trace_context twice_gs
               (interval_es_rule.admitted_contexts Globals_Warrow twice_gs twice_program)
               [] (compile_prog twice_pi twice_procs) t c
           \<and> s \<in> twice_ctx_gamma (twice_ctx_sg (Inl (v, c)))"
proof -
  have run': "twice_gs, twice_pi \<turnstile> (main_body twice_pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    using run by simp
  show ?thesis
    by (rule source_sound_from_collecting_cap
          [where R = "interval_es_rule.admitted_contexts Globals_Warrow twice_gs twice_program"
             and startcontext = "[]"
             and \<gamma>\<^sub>M = twice_ctx_gamma,
           OF twice_wf init run'
              interval_es_rule.entry_state_has_context[OF twice_entry_state_hyps,
                unfolded twice_cfg_alt]
              twice_activation_collect_sound])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source
  frame stack) is certified at the concrete seed context \<open>[]\<close> (no formal binds the root
  activation) --- no \<^typ>\<open>ltr\<close> witness, no context existential.  This is the clean user-facing
  statement for main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "twice_gs, twice_pi \<turnstile> (twice_main, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, [])"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v. twice_pi, compile_prog twice_pi twice_procs \<turnstile> (residual, s, []) \<approx> (v, s, [])
             \<and> s \<in> twice_ctx_gamma (twice_ctx_sg (Inl (v, [])))"
proof -
  have run': "twice_gs, twice_pi \<turnstile> (main_body twice_pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, [])"
    using run by simp
  show ?thesis
    by (rule source_sound_toplevel_from_collecting_cap
          [where R = "interval_es_rule.admitted_contexts Globals_Warrow twice_gs twice_program"
             and startcontext = "[]"
             and \<gamma>\<^sub>M = twice_ctx_gamma,
           OF twice_wf init run' twice_activation_collect_sound])
qed

end


