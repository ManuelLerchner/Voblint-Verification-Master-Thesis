theory DG_Route_Soundness
  imports DG_Context_Soundness "Voblint_Analysis.Ctx_Collect_Backbone"
begin

section \<open>DG instantiation: context-keyed collecting soundness\<close>

text \<open>
  The DG endpoint replacing \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>: the
  carrier-agnostic \<open>collect_ctx_sound_meaning\<close> instantiated at the two-gamma
  reading of the context-keyed slots (\<open>dg_gamma_c\<close>), with the routing read the local
  slot's Answer (\<open>dg_D_c\<close>).  The eight obligations keep the shape of the homogeneous
  theorem but read through \<open>gammaDG\<close>.  As on the homogeneous spine the intra \<open>EDGE\<close> /
  seed \<open>ENTRY\<close> and the switching \<open>COMB\<close> stay premises, discharged per analysis instance
  (the concrete witness supplies them from \<open>step_sound\<close> / \<open>combine_sound\<close> / a
  post-solution).
\<close>

context sound_dg_spec
begin

theorem dg_collect_ctx_sound:
  fixes sigma :: "pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S0 \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> dg_gamma_c sigma ctx (cfg_entry g)"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S0
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> dg_gamma_c sigma ctx v"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> dg_gamma_c sigma ctx u \<Longrightarrow> s' \<in> dg_gamma_c sigma ctx v"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> dg_gamma_c sigma ctx cl
        \<Longrightarrow> last rho \<in> dg_gamma_c sigma (rt cl ctx (dg_D_c sigma ctx cl)) ex
        \<Longrightarrow> <last tau|last rho> \<in> dg_gamma_c sigma ctx v"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> dg_gamma_c sigma ctx cl
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (dg_D_c sigma ctx cl))"
  shows "cfg_collect_ctx dg cmp g S0 v ctx \<subseteq> dg_gamma_c sigma ctx v"
proof -
  have "cfg_collect_ctx dg cmp g S0 v ctx
          \<subseteq> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
  proof (rule collect_ctx_sound_meaning
      [where M = "\<lambda>(p, c). dg_gamma_c sigma c p"
         and rd = "\<lambda>(p, c). dg_D_c sigma c p"
         and rt = rt and entdg = entdg and dg = dg and cmp = cmp and S = S0 and g = g])
    show "\<And>ctx s. s \<in> S0 \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cfg_entry g, ctx)"
      using ENTRY by simp
  next
    show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S0
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
      using PROC_ENTRY by simp
  next
    show "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
            \<Longrightarrow> last tr \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (u, ctx)
            \<Longrightarrow> s' \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
      using EDGE by simp
  next
    fix ctx cl ex v' tau rho
    assume comb: "(cl, ex, v') \<in> combines g"
      and cr: "last tau \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cl, ctx)"
      and ce: "last rho \<in> (\<lambda>(p, c). dg_gamma_c sigma c p)
                  (ex, rt cl ctx ((\<lambda>(p, c). dg_D_c sigma c p) (cl, ctx)))"
    show "<last tau|last rho> \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v', ctx)"
      using COMB[OF comb] cr ce by simp
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
      using DG_INTRA by blast
  next
    show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
      using DG_RETURN by blast
  next
    show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
      using DG_CALLEE by blast
  next
    fix ctx cl s
    assume "s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cl, ctx)"
    thus "cmp (entdg s) (rt cl ctx ((\<lambda>(p, c). dg_D_c sigma c p) (cl, ctx)))"
      using ENTER_MONO by simp
  qed
  thus ?thesis by simp
qed

end

end
