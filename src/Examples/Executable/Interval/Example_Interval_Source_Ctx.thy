theory Example_Interval_Source_Ctx
  imports
    Example_Interval_DG_Ctx_Collect
    Example_Interval_DG_IP_Flagship
    "Voblint_Formalization.Source_Activation_Sound"
begin

section \<open>Source-level context-sensitive certification for the recursive flagship\<close>

text \<open>
  The end-to-end payoff: for the compiled \<open>twice\<close> program, an actual IMP2 source run is certified
  against the solver-computed interval solution AT THE ACTIVATION CONTEXT.  It feeds the routed
  interval activation soundness \<open>twice_ctx_collect_ctx_act_sound\<close> as the collecting cap to the
  generic composition \<open>source_sound_from_collecting_cap\<close> (\<open>Source_Activation_Sound\<close>), which chains
  in the stack-faithful source bridge.  It is strictly more precise than the monovariant capstone
  \<open>twice_source_run_sound\<close>: the store is bounded at its own \<open>(program point, context)\<close> slot, not
  merely at the flat point.
\<close>

lemma twice_source_com: "source_com twice_main"
  using twice_wf unfolding wf_compile_input_def by simp

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the interval
  slot indexed by the stable context of the activation that produced it.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "star (pstep twice_pi) (twice_main, s0, []) (residual, s, frs)"
    and init: "s0 \<in> cinit_stores"
  shows "\<exists>v stk t.
           concrete_program_match twice_pi twice_procs twice_main (residual, s, frs) (v, s, stk)
           \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, key ivl_enterc bot t))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. cfg_collect_ctx_act ivl_enterc bot
                      (compile_prog twice_pi twice_procs twice_main) cinit_stores v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_ctx_collect_ctx_act_sound)
  show ?thesis
    by (rule source_sound_from_collecting_cap[OF twice_wf twice_source_com init run cap])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source frame
  stack) is certified at the concrete seed context \<open>\<bottom>\<close> --- no \<^typ>\<open>ltr\<close> witness, no context
  existential.  This is the clean user-facing statement for main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "star (pstep twice_pi) (twice_main, s0, []) (residual, s, [])"
    and init: "s0 \<in> cinit_stores"
  shows "\<exists>v. concrete_program_match twice_pi twice_procs twice_main (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>ivl_ctx_sg (Inl (v, bot))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. cfg_collect_ctx_act ivl_enterc bot
                      (compile_prog twice_pi twice_procs twice_main) cinit_stores v ctx
                    \<subseteq> \<lbrakk>ivl_ctx_sg (Inl (v, ctx))\<rbrakk>"
    unfolding twice_cfg_def[symmetric] by (rule twice_ctx_collect_ctx_act_sound)
  show ?thesis
    by (rule source_sound_toplevel_from_collecting_cap[OF twice_wf twice_source_com init run cap])
qed

end
