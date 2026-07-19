theory Source_Activation_Sound
  imports "Voblint_Analysis.Activation_Backbone" "Voblint_CFG.Located_LTR"
begin

section \<open>End-to-end source-level activation soundness\<close>

text \<open>
  A reachable store of a compiled source program is bounded by the abstract analysis at the stable
  activation context of the trace that produced it.  The composition joins the stack-faithful source
  bridge \<open>source_store_in_activation_collect\<close> with \<open>activation_collect_sound\<close>.
\<close>

theorem source_sound_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
    and cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v stk t. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps main"
  from source_store_in_activation_collect[OF wf src s0 run, where enterc=enterc and seedc=seedc]
  obtain v stk t where m: "concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect enterc seedc ?g S v (key enterc seedc t)"
    by blast
  have "s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
    using cap[of v "key enterc seedc t"] mem by blast
  then show ?thesis using m by blast
qed

text \<open>The witness-free specialisation of the composition at top-level program points: an empty
  source frame stack lands at the fixed seed context, no \<^typ>\<open>ltr\<close> witness exposed.\<close>
theorem source_sound_toplevel_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, [])"
    and cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v. concrete_program_match Pi ps main (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps main"
  from source_toplevel_in_activation_collect[OF wf src s0 run, where enterc=enterc and seedc=seedc]
  obtain v where m: "concrete_program_match Pi ps main (residual, s, []) (v, s, [])"
    and mem: "s \<in> activation_collect enterc seedc ?g S v seedc" by blast
  have "s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>" using cap[of v seedc] mem by blast
  then show ?thesis using m by blast
qed

subsection \<open>Backbone corollaries: discharge the four obligations to build the cap\<close>

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
  have cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE SEED_G COMB])
  show ?thesis by (rule source_sound_from_collecting_cap[OF wf src s0 run cap])
qed

text \<open>The witness-free specialisation at top-level program points: a store reached with an empty
  source frame stack is bounded at the fixed seed context, with no \<^typ>\<open>ltr\<close> witness and no
  context existential exposed.\<close>
theorem source_activation_sound_toplevel:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, [])"
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
  shows "\<exists>v. concrete_program_match Pi ps main (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE SEED_G COMB])
  show ?thesis by (rule source_sound_toplevel_from_collecting_cap[OF wf src s0 run cap])
qed

subsection \<open>Monovariant source bridge into the trace collecting\<close>

text \<open>
  The context-forgetting specialisation projects the activation collector at trivial routing to
  \<^const>\<open>ltr_collect_keyed\<close>, then to \<^const>\<open>ltr_collect\<close>.
\<close>

theorem source_reaches_ltr_collect:
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                 \<and> s \<in> ltr_collect (compile_prog Pi ps main) S v"
proof -
  let ?g = "compile_prog Pi ps main"
  from source_store_in_activation_collect[OF wf src s0 run,
        where enterc = "\<lambda>_ _. ()" and seedc = "()"]
  obtain v stk t where m: "concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect (\<lambda>_ _. ()) () ?g S v (key (\<lambda>_ _. ()) () t)" by blast
  have "s \<in> ltr_collect_keyed (key (\<lambda>_ _. ()) ()) ?g S v (key (\<lambda>_ _. ()) () t)"
    using mem by (simp add: activation_collect_eq_ltr_collect_keyed)
  then have "s \<in> ltr_collect ?g S v"
    by (rule subsetD[OF ltr_collect_keyed_le_collect])
  then show ?thesis using m by blast
qed

end
