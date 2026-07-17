theory Source_Activation_Sound
  imports "Voblint_Analysis.Activation_Backbone" "Voblint_CFG.Located_LTR"
begin

section \<open>End-to-end source-level activation soundness\<close>

text \<open>
  The final composition of the activation-local spine: a reachable store of a compiled source
  program is bounded by the abstract analysis at the STABLE activation context of the trace that
  produced it.  It chains the stack-faithful source bridge \<open>source_store_in_cfg_collect_ctx_act\<close>
  (\<open>Located_LTR\<close>) --- source execution reaches a valid \<^const>\<open>valid_ltr\<close> trace whose sink is the
  current store at context \<^const>\<open>key\<close> --- with the domain-level backbone
  \<open>activation_collect_sound\<close>.  The four semantic obligations are exactly the backbone's; no
  compiler, solver, or domain assumption is added.
\<close>

theorem source_activation_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cfg_entry (compile_prog Pi ps main), seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> edges (compile_prog Pi ps main) \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c x x' xs es. (u, EA_Enter xs es, v) \<in> edges (compile_prog Pi ps main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step (EA_Enter xs es) x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, enterc c x'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 x y es. (cl, ex, v, dst) \<in> combines (compile_prog Pi ps main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> y \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store (compile_prog Pi ps main) cl x es
        \<Longrightarrow> combine_collect dst x y \<in> \<lbrakk>sg (Inl (v, c1))\<rbrakk>"
  shows "\<exists>v stk t. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps main"
  from source_store_in_cfg_collect_ctx_act[OF wf src s0 run, where enterc=enterc and seedc=seedc]
  obtain v stk t where m: "concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> cfg_collect_ctx_act enterc seedc ?g S v (key enterc seedc t)"
    by blast
  have "cfg_collect_ctx_act enterc seedc ?g S v (key enterc seedc t)
          \<subseteq> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
    by (rule activation_collect_sound[where sg=sg and enterc=enterc and seedc=seedc
          and S=S and g="?g" and v=v and ctx="key enterc seedc t",
          OF ENTRY_G EDGE SEED_G COMB])
  then show ?thesis using m mem by blast
qed

end
