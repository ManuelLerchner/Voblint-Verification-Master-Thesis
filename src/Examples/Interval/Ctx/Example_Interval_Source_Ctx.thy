theory Example_Interval_Source_Ctx
  imports
    Example_Interval_DG_Ctx_Collect
    Example_Interval_DG_IP_Flagship
    "Voblint_Formalization.Source_Activation_Sound"
begin

section \<open>Source-level context-sensitive certification for repeated calls\<close>

text \<open>
  The \<open>twice\<close> program calls one procedure from two sites.  The theorem below connects each source
  configuration to the solver-computed interval slot for the activation that produced it.  The
  context key keeps the two calls separate while the source/CFG simulation preserves the concrete
  frame stack.
\<close>

text \<open>\<open>twice_program\<close> declares no globals, so \<^const>\<open>twice_gs\<close> is trivially false
  on every name \<^const>\<open>twice_pi\<close> can touch: reprove \<open>twice_wf\<close>'s obligations at
  \<^const>\<open>twice_gs\<close> directly, so the source-level run relation and the \<open>twice_gs\<close>-indexed
  collecting semantics share one classifier end to end.\<close>
lemma twice_wf_gs: "wf_compile_input twice_gs twice_pi twice_procs (STR ''main'') twice_main"
  unfolding wf_compile_input_simps
    twice_pi_def twice_procs_def twice_main_def twice_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_aexp_def ret_var_def
      split: if_splits option.splits)

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the interval
  slot indexed by the stable context of the activation that produced it.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s0, []) (residual, s, frs)"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v stk t.
           csim twice_pi (compile_prog twice_pi twice_procs (STR ''main'') twice_main)
             (residual, s, frs) (v, s, stk)
           \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, key ivl_enterc [] t))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect twice_gs ivl_enterc []
                      (compile_prog twice_pi twice_procs (STR ''main'') twice_main) (cinit_stores twice_gs) v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_activation_collect_sound)
  show ?thesis
    by (rule source_sound_from_collecting_cap[OF twice_wf_gs init run cap])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source frame
  stack) is certified at the concrete seed context \<open>[]\<close> (no formal binds the root activation) ---
  no \<^typ>\<open>ltr\<close> witness, no context existential.  This is the clean user-facing statement for
  main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s0, []) (residual, s, [])"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v. csim twice_pi (compile_prog twice_pi twice_procs (STR ''main'') twice_main)
               (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, []))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect twice_gs ivl_enterc []
                      (compile_prog twice_pi twice_procs (STR ''main'') twice_main) (cinit_stores twice_gs) v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_activation_collect_sound)
  show ?thesis
    by (rule source_sound_toplevel_from_collecting_cap
              [OF twice_wf_gs init run cap])
qed

end


