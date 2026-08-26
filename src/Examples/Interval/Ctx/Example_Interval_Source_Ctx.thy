theory Example_Interval_Source_Ctx
  imports
    Example_Interval_DG_Ctx_Collect
    "Voblint_Soundness.Source_Activation_Sound"
begin

section \<open>Source-level context-sensitive certification for repeated calls\<close>

text \<open>
  The \<open>twice\<close> program calls one procedure from two sites.  The theorems below connect each
  source configuration to the production entry-state analysis' own slot
  (\<^const>\<open>entry_state_sg\<close>) for the activation that produced it, read through the lifted
  concretization \<^const>\<open>gamma_state_lift\<close> the whole-state carrier denotes with.  The
  context key \<^const>\<open>entry_state_context\<close> keeps the two calls separate while the
  source/CFG simulation preserves the concrete frame stack.
\<close>

text \<open>The analysis' own context function and solved reader, abbreviated for the two
  statements below.\<close>

abbreviation twice_ctx :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "twice_ctx \<equiv> entry_state_context twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main"

abbreviation twice_ctx_sg :: "pp \<times> ivl list + gk \<Rightarrow> ivl abs_state lifted" where
  "twice_ctx_sg \<equiv> entry_state_sg twice_gs (prog_tyenv twice_program) twice_is_bot_pred twice_pi twice_procs (STR ''main'') twice_main"

text \<open>Context-sensitive source soundness.  Any \<open>twice\<close> run reaches a store bounded at the interval
  slot indexed by the stable context of the activation that produced it.\<close>
theorem twice_source_ctx_run_sound:
  assumes run: "star (pstep (prog_tyenv twice_program) twice_gs twice_pi)
                  (twice_main, s0, [], proc_ret_kind twice_pi (STR ''main''))
                  (residual, s, frs, rk)"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v stk t c.
           csim (prog_tyenv twice_program) twice_pi
             (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main)
             (residual, s, frs, rk) (v, s, stk)
           \<and> ctx_key (admiss_exact twice_ctx) [] t c
           \<and> s \<in> gamma_state_lift (twice_ctx_sg (Inl (v, c)))"
proof -
  have tot: "\<And>u c s. \<exists>c'. admiss_exact twice_ctx u c s c'"
    by (simp add: admiss_exact_def)
  show ?thesis
    by (rule source_sound_from_collecting_cap[where admiss = "admiss_exact twice_ctx"
            and gammaM = gamma_state_lift,
          OF twice_wf init run tot twice_activation_collect_sound])
qed

text \<open>The witness-free specialisation: a \<open>twice\<close> store reached at the top level (empty source frame
  stack) is certified at the concrete seed context \<open>[]\<close> (no formal binds the root activation) ---
  no \<^typ>\<open>ltr\<close> witness, no context existential.  This is the clean user-facing statement for
  main-level program points.\<close>
theorem twice_source_toplevel_at_bot:
  assumes run: "star (pstep (prog_tyenv twice_program) twice_gs twice_pi)
                  (twice_main, s0, [], proc_ret_kind twice_pi (STR ''main''))
                  (residual, s, [], rk)"
    and init: "s0 \<in> cinit_stores twice_gs"
  shows "\<exists>v. csim (prog_tyenv twice_program) twice_pi
                 (compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main)
                 (residual, s, [], rk) (v, s, [])
             \<and> s \<in> gamma_state_lift (twice_ctx_sg (Inl (v, [])))"
  by (rule source_sound_toplevel_from_collecting_cap
            [where admiss = "admiss_exact twice_ctx" and gammaM = gamma_state_lift,
             OF twice_wf init run twice_activation_collect_sound])

end

