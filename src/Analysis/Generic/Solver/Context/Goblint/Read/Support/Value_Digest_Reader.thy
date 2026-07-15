theory Value_Digest_Reader
  imports Digest_Global_Read
begin

section \<open>Generic value-carried digest reader\<close>

text \<open>
  The domain-agnostic core of the value-derived (``mode'') digest family: a reader
  that is a \<^emph>\<open>projection of the solved local state\<close> rather than an external map.
  The digest is a \<^class>\<open>finite\<close> key read straight out of the abstract value of a
  \<^emph>\<open>designated program variable\<close> --- via a domain-supplied \<open>decode\<close> --- so the context
  is generated automatically from the existing value solution, with no separate
  dataflow.  The projected variable can be any program variable; it need not be
  instrumentation.

  The locale fixes only \<open>decode\<close> (the projection from an abstract value to the finite
  digest) and \<open>proj_var\<close> (the projected variable name); everything else --- the read, its
  reduced shape, and the context-sliced collecting soundness --- is generic over any
  \<^class>\<open>bounded_semilattice_sup_bot\<close> abstract value.  A concrete domain interprets
  the locale by supplying its own \<open>decode\<close>; nothing in \<^theory>\<open>Voblint_Analysis.Digest_Global_Read\<close>
  changes.  The sign instance is \<open>Value_Digest_Read\<close> (\<open>Instances/Sign\<close>).
\<close>

locale value_digest_reader =
  fixes decode :: "'d::sound_domain \<Rightarrow> 'm::finite"
    and proj_var :: vname
begin

text \<open>The reader recovers the digest from the solved local slot at the read point.\<close>
definition vd_reader ::
  "((nat \<times> 'c) + 'm \<Rightarrow> 'd abs_state) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'm" where
  "vd_reader \<sigma> v ctx = decode (\<sigma> (Inl (v, ctx)) proj_var)"

text \<open>@{const digest_global_read.obs_digest} specialised to the projection reader and
  equality compatibility.  The kernel is instantiated, not modified.\<close>
definition vd_obs ::
  "((nat \<times> 'c) + 'm \<Rightarrow> 'd abs_state) \<Rightarrow> (nat \<times> 'c) \<Rightarrow> 'd abs_state" where
  "vd_obs \<sigma> = digest_global_read.obs_digest (vd_reader \<sigma>) (=) \<sigma>"

lemma vd_compatible_singleton: "{g. (d::'m) = g} = {d}" by auto

text \<open>The read collapses to the local slot joined with the single partition slot the
  point's decoded digest selects.\<close>
lemma vd_obs_reduce:
  "vd_obs \<sigma> (v, ctx)
     = \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (decode (\<sigma> (Inl (v, ctx)) proj_var)))"
  unfolding vd_obs_def digest_global_read.obs_digest_def vd_reader_def
  by (simp add: glob_env_cmp_singleton[OF vd_compatible_singleton])

subsection \<open>Context-sliced collecting soundness\<close>

theorem vd_collect_ctx_sound_bot:
  fixes sigma :: "(nat \<times> 'c) + 'm \<Rightarrow> 'd abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "nat \<Rightarrow> 'c \<Rightarrow> 'd abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>vd_obs sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>vd_obs sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and CMP_SOUND: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> vd_obs sigma (v, ctx) x"
    and RET_SOUND: "\<And>ctx cl ex v dst y. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> dst = Some y
        \<Longrightarrow> vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) ret_var \<le> vd_obs sigma (v, ctx) y"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>vd_obs sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
  using assms unfolding vd_obs_def
  by (rule digest_global_read.obs_digest_collect_ctx_sound_bot)

text \<open>\<open>GLOB_BOT\<close> is exactly @{const inr_slot_locals_bot_ctx}.\<close>
lemma vd_glob_bot_ctx:
  assumes "inr_slot_locals_bot_ctx \<sigma>"
  shows "local_bot_on_locals (\<sigma> (Inr gk))"
  using assms by (simp add: inr_slot_locals_bot_ctx_def local_bot_on_locals_def)

text \<open>At a global variable the read collapses to the single selected partition slot.\<close>
lemma vd_obs_global:
  assumes inl: "inl_slot_globals_bot_ctx \<sigma>"
  assumes gx: "is_global x"
  shows "vd_obs \<sigma> (v, ctx) x = \<sigma> (Inr (decode (\<sigma> (Inl (v, ctx)) proj_var))) x"
proof -
  have "\<sigma> (Inl (v, ctx)) x = bot" using inl gx by (simp add: inl_slot_globals_bot_ctx_def)
  thus ?thesis by (simp add: vd_obs_reduce)
qed

text \<open>
  The reduced collecting theorem: \<open>GLOB_BOT\<close> and \<open>CMP_SOUND\<close> are discharged from the
  two slot invariants and digest stability \<open>DIGEST_AGREE\<close> --- the projected-variable read at a
  callee-exit under its routed context matches the read at the return node.  That is
  the sole genuinely new obligation the value-carried digest introduces; the generator
  supplies it.
\<close>
theorem vd_collect_ctx_sound_bot_reduced:
  fixes sigma :: "(nat \<times> 'c) + 'm \<Rightarrow> 'd abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "nat \<Rightarrow> 'c \<Rightarrow> 'd abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>vd_obs sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>vd_obs sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and INR_BOT: "inr_slot_locals_bot_ctx sigma"
    and INL_BOT: "inl_slot_globals_bot_ctx sigma"
    and DIGEST_AGREE: "\<And>ctx cl ex v dst. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) proj_var)
              = decode (sigma (Inl (v, ctx)) proj_var)"
    and RET_SOUND: "\<And>ctx cl ex v dst y. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> dst = Some y
        \<Longrightarrow> vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) ret_var \<le> vd_obs sigma (v, ctx) y"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>vd_obs sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>vd_obs sigma (v, ctx)\<rbrakk>"
proof -
  have GB: "\<And>gk. local_bot_on_locals (sigma (Inr gk))" by (rule vd_glob_bot_ctx[OF INR_BOT])
  have CS: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> vd_obs sigma (v, ctx) x"
  proof -
    fix ctx cl ex v dst x
    assume comb: "(cl, ex, v, dst) \<in> combines g" and gx: "is_global x"
    have ag: "decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) proj_var)
                = decode (sigma (Inl (v, ctx)) proj_var)"
      by (rule DIGEST_AGREE[OF comb])
    have "vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
            = sigma (Inr (decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) proj_var))) x"
      by (rule vd_obs_global[OF INL_BOT gx])
    also have "\<dots> = sigma (Inr (decode (sigma (Inl (v, ctx)) proj_var))) x" by (simp add: ag)
    also have "\<dots> = vd_obs sigma (v, ctx) x" by (rule vd_obs_global[OF INL_BOT gx, symmetric])
    finally show "vd_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> vd_obs sigma (v, ctx) x"
      by simp
  qed
  show ?thesis
    using ENTRY PROC_ENTRY EDGE LOCAL_POST GB CS RET_SOUND DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO
    by (rule vd_collect_ctx_sound_bot)
qed

subsection \<open>The projection read is the certified context read\<close>

text \<open>
  Under the alignment invariant \<open>ctx = decode (sigma (Inl (v, ctx)) proj_var)\<close> --- the
  context channel carries the projected digest (Goblint's \<open>C.t = context D\<close>) --- the
  projection read equals the context-keyed read @{const side_env_cmp}.  So the executable
  generator run through @{const side_env_cmp} discharges @{const vd_obs} soundness with
  no separate solve.
\<close>
lemma vd_obs_eq_side_env_cmp:
  fixes sigma :: "(nat \<times> 'm) + 'm \<Rightarrow> 'd abs_state"
  assumes align: "decode (sigma (Inl (v, ctx)) proj_var) = ctx"
  shows "vd_obs sigma (v, ctx) = side_env_cmp (=) sigma (v, ctx)"
proof -
  have single: "{k. (=) ctx k} = {ctx}" by auto
  have "vd_obs sigma (v, ctx)
          = sigma (Inl (v, ctx)) \<squnion> sigma (Inr (decode (sigma (Inl (v, ctx)) proj_var)))"
    by (rule vd_obs_reduce)
  also have "\<dots> = sigma (Inl (v, ctx)) \<squnion> sigma (Inr ctx)" using align by simp
  also have "\<dots> = side_env_cmp (=) sigma (v, ctx)"
    by (simp add: side_env_cmp_singleton[where cmp = "(=)", OF single])
  finally show ?thesis .
qed

end

end
