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

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the interval
  slot indexed by the stable context of the activation that produced it.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "star (pstep is_global twice_pi) (twice_main, s0, []) (residual, s, frs)"
    and init: "s0 \<in> cinit_stores is_global"
  shows "\<exists>v stk t.
           csim twice_pi (compile_prog twice_pi twice_procs ''main'' twice_main)
             (residual, s, frs) (v, s, stk)
           \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, key ivl_enterc bot t))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect is_global ivl_enterc bot
                      (compile_prog twice_pi twice_procs ''main'' twice_main) (cinit_stores is_global) v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_activation_collect_sound)
  show ?thesis
    by (rule source_sound_from_collecting_cap[OF twice_wf init run cap])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source frame
  stack) is certified at the concrete seed context \<open>\<bottom>\<close> --- no \<^typ>\<open>ltr\<close> witness, no context
  existential.  This is the clean user-facing statement for main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "star (pstep is_global twice_pi) (twice_main, s0, []) (residual, s, [])"
    and init: "s0 \<in> cinit_stores is_global"
  shows "\<exists>v. csim twice_pi (compile_prog twice_pi twice_procs ''main'' twice_main)
               (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, bot))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect is_global ivl_enterc bot
                      (compile_prog twice_pi twice_procs ''main'' twice_main) (cinit_stores is_global) v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_activation_collect_sound)
  show ?thesis
    by (rule source_sound_toplevel_from_collecting_cap
              [OF twice_wf init run cap])
qed

end


