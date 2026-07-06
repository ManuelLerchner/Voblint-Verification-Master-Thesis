theory RD_Set_Edge_Backbone
  imports Reaching_Defs TD_Side_Eff_Sound
begin

section \<open>Set-indexed EDGE backbone for the reaching-definition reader\<close>

text \<open>
  The reaching-definition collecting theorems \<open>reaching_def_collect_sound\<close> and
  \<open>reaching_def_collect_sound_bot\<close> carry the concrete per-edge premise \<open>EDGE\<close>
  unproven: a store covered by the set read \<^const>\<open>rd_obs\<close> at an edge source, stepped
  along a CFG edge, is covered by the set read at the target.  The context-only and
  mode instances discharge the same premise through the single-slot bound
  \<open>side_cfg_T_eff_cmp_edge_le\<close>, but only because their compatible key set is a
  singleton (\<open>side_env_pull_gk_eq_cmp\<close>); the reaching set is a genuine set, so the
  transfer would have to be run on a join of many global slots --- which monotonicity
  alone does not commute past.

  This theory isolates exactly the residual obligation.  The concrete step soundness
  is free: read the reaching-set-merged global into a unit-global environment and the
  existing \<open>edge_collect_etf_sound\<close> applies verbatim.
  What remains is one purely abstract inequality --- the transfer, run on the
  reach-merged read at the source, sits below the reaching read at the target.
  \<open>rd_obs_edge_from_merged_bound\<close> turns \<open>EDGE\<close> into that inequality; a set-reading
  generator's post-fixpoint is what must ultimately supply it.
\<close>

subsection \<open>The reaching-merged unit-global environment\<close>

text \<open>
  The unit-global environment whose local slots are \<^term>\<open>sigma\<close>'s context-\<^term>\<open>ctx\<close>
  locals and whose single global slot is the reaching-set join at the source point
  \<^term>\<open>u\<close>.  Reading \<^const>\<open>side_env\<close> at \<^term>\<open>u\<close> recovers \<^const>\<open>rd_obs\<close>.
\<close>

definition rd_merge_env ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'g::finite set)
   \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state)"
where
  "rd_merge_env reach sigma ctx u =
     (\<lambda>z. case z of Inl w \<Rightarrow> sigma (Inl (w, ctx))
                  | Inr _ \<Rightarrow> glob_env_cmp (\<lambda>_ g. rd_compatible (reach u ctx) g) ctx sigma)"

lemma rd_merge_env_Inl:
  "rd_merge_env reach sigma ctx u (Inl w) = sigma (Inl (w, ctx))"
  by (simp add: rd_merge_env_def)

lemma rd_merge_env_Inr:
  "rd_merge_env reach sigma ctx u (Inr y) = glob_env_cmp (\<lambda>_ g. rd_compatible (reach u ctx) g) ctx sigma"
  by (simp add: rd_merge_env_def)

text \<open>Reading the merged environment at the source point is the reaching read.\<close>
lemma side_env_rd_merge_env:
  "side_env (rd_merge_env reach sigma ctx u) u = rd_obs reach sigma (u, ctx)"
  unfolding side_env_def digest_global_read.obs_digest_def
  by (simp add: glob_env_unit rd_merge_env_Inl rd_merge_env_Inr)

text \<open>The merged global slot is \<open>bot\<close> on locals whenever every keyed slot is.\<close>
lemma inr_slot_locals_bot_rd_merge_env:
  assumes GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
  shows "inr_slot_locals_bot (rd_merge_env reach sigma ctx u)"
  unfolding inr_slot_locals_bot_def
proof (intro allI impI)
  fix y :: unit and x
  assume x: "\<not> is_global x"
  have "local_bot_on_locals (glob_env_cmp (\<lambda>_ g. rd_compatible (reach u ctx) g) ctx sigma)"
    by (rule glob_env_cmp_local_bot) (rule GLOB_BOT)
  thus "rd_merge_env reach sigma ctx u (Inr y) x = bot"
    using x by (simp add: rd_merge_env_Inr local_bot_on_locals_def)
qed

subsection \<open>The residual obligation: an abstract merged-edge bound closes EDGE\<close>

text \<open>
  The decisive reduction.  Given the abstract merged-edge bound --- the effectful
  transfer, run on the reach-merged read at the source \<^term>\<open>u\<close>, over-approximates the
  reaching read at the target \<^term>\<open>v\<close> --- one concrete edge step preserves coverage by
  the reaching read.  The proof is the \<open>cfg_witness_gamma_eff\<close> edge case with the
  reach-merged environment in the role of the unit-global post-solution: concrete step
  soundness comes free from \<open>edge_collect_etf_sound\<close>, and
  the abstract bound carries it to the target read by \<open>gamma_state_mono\<close>.
\<close>
lemma rd_obs_edge_from_merged_bound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes stf: "sound_effectful_transfer etf"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and ABS: "etf_collecting_full (apply_etf etf a u) (rd_merge_env reach sigma ctx u)
                \<le> rd_obs reach sigma (v, ctx)"
    and step: "edge_step a s = Some s'"
    and s_in: "s \<in> \<lbrakk>rd_obs reach sigma (u, ctx)\<rbrakk>"
  shows "s' \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
proof -
  let ?env = "rd_merge_env reach sigma ctx u"
  have inr': "inr_slot_locals_bot ?env"
    by (rule inr_slot_locals_bot_rd_merge_env) (rule GLOB_BOT)
  have s_env: "s \<in> \<lbrakk>side_env ?env u\<rbrakk>"
    using s_in by (simp add: side_env_rd_merge_env)
  have s': "s' \<in> edge_collect a {s}"
    using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
  proof -
    have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>side_env ?env u\<rbrakk>"
      by (rule edge_collect_mono) (use s_env in blast)
    also have "\<dots> \<subseteq> \<lbrakk>etf_collecting_full (apply_etf etf a u) ?env\<rbrakk>"
      by (rule sound_effectful_transfer.edge_collect_etf_sound[OF stf inr'])
    also have "\<dots> \<subseteq> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
      by (rule gamma_state_mono[OF ABS])
    finally show ?thesis .
  qed
  thus ?thesis using s' by blast
qed

subsection \<open>Kill-compatible RD collecting soundness from merged-edge bounds\<close>

text \<open>
  \<open>reaching_def_collect_sound_bot\<close> with its assumed concrete \<open>EDGE\<close> premise replaced by
  the family of abstract merged-edge bounds \<open>MERGED_EDGE\<close> --- one algebraic inequality
  per CFG edge.  The bot-on-locals invariant needed by
  \<open>rd_obs_edge_from_merged_bound\<close> is the same \<open>GLOB_BOT\<close> the theorem already carries.
\<close>
theorem reaching_def_collect_sound_bot_from_merged:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and reach :: "pp \<Rightarrow> 'c \<Rightarrow> 'g set"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes stf: "sound_effectful_transfer etf"
    and ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and MERGED_EDGE: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> etf_collecting_full (apply_etf etf a u) (rd_merge_env reach sigma ctx u)
              \<le> rd_obs reach sigma (v, ctx)"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> rd_obs reach sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
              \<le> rd_obs reach sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs reach sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
proof (rule reaching_def_collect_sound_bot
         [where reach = reach and sigma = sigma and dg = dg and cmp = cmp
            and rt = rt and entdg = entdg])
  fix ctx u a v tr s'
  assume e: "(u, a, v) \<in> edges g" and st: "edge_step a (last tr) = Some s'"
    and cov: "last tr \<in> \<lbrakk>rd_obs reach sigma (u, ctx)\<rbrakk>"
  show "s' \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    by (rule rd_obs_edge_from_merged_bound[OF stf GLOB_BOT MERGED_EDGE[OF e] st cov])
qed (fact ENTRY PROC_ENTRY LOCAL_POST GLOB_BOT CMP_SOUND
          DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+

text \<open>
  The reaching-set-inclusion sibling: \<open>reaching_def_collect_sound_bot_incl\<close> with its
  concrete \<open>EDGE\<close> premise replaced by the abstract merged-edge family \<open>MERGED_EDGE\<close>.
  This is the variant a concrete witness plugs into once its generator supplies the
  per-edge bounds: the combine-side \<open>CMP_SOUND\<close> is still derived from the two
  dataflow/structural facts \<open>INL_GLOB_BOT\<close> + \<open>CALLEE_INCL\<close> (via
  \<open>rd_obs_cmp_sound_from_incl\<close>), and the per-edge side is now \<open>MERGED_EDGE\<close> rather than
  an assumed gamma-level step.  So a witness built on this carries \<^emph>\<open>no\<close> opaque
  \<open>EDGE\<close> hypothesis --- only the algebraic \<open>MERGED_EDGE\<close> inequalities its solution must
  meet.
\<close>
theorem reaching_def_collect_sound_bot_incl_from_merged:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and reach :: "pp \<Rightarrow> 'c \<Rightarrow> 'g set"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes stf: "sound_effectful_transfer etf"
    and ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and MERGED_EDGE: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> etf_collecting_full (apply_etf etf a u) (rd_merge_env reach sigma ctx u)
              \<le> rd_obs reach sigma (v, ctx)"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and INL_GLOB_BOT: "\<And>p x. is_global x \<Longrightarrow> sigma (Inl p) x = bot"
    and CALLEE_INCL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> reach ex (rt cl ctx (sigma (Inl (cl, ctx)))) \<subseteq> reach v ctx"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs reach sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
proof -
  have CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> rd_obs reach sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
              \<le> rd_obs reach sigma (v, ctx) x"
  proof -
    fix ctx cl ex v x
    assume comb: "(cl, ex, v) \<in> combines g" and gl: "is_global x"
    show "rd_obs reach sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
            \<le> rd_obs reach sigma (v, ctx) x"
    proof (rule rd_obs_cmp_sound_from_incl)
      show "reach ex (rt cl ctx (sigma (Inl (cl, ctx)))) \<subseteq> reach v ctx"
        by (rule CALLEE_INCL[OF comb])
      show "\<And>p. is_global x \<Longrightarrow> sigma (Inl p) x = bot" by (rule INL_GLOB_BOT)
      show "is_global x" by (rule gl)
    qed
  qed
  show ?thesis
  proof (rule reaching_def_collect_sound_bot_from_merged
           [where reach = reach and sigma = sigma and etf = etf and dg = dg
              and cmp = cmp and rt = rt and entdg = entdg])
    show "sound_effectful_transfer etf" by (rule stf)
  qed (fact ENTRY PROC_ENTRY MERGED_EDGE LOCAL_POST GLOB_BOT CMP_SOUND
            DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+
qed

end
