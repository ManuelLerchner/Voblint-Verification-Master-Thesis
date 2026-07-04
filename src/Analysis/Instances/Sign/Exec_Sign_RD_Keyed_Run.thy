theory Exec_Sign_RD_Keyed_Run
  imports Reaching_Defs RD_Set_Edge_Backbone Sign_Domain
begin

section \<open>Reaching-definition global reads: sound concrete witness (sign)\<close>

text \<open>
  The reaching-definition counterpart of \<open>Exec_Sign_Cmp_Keyed_Run\<close>.  Where the
  context-keyed witness separates two \<^emph>\<open>contexts\<close> by their global slot \<^term>\<open>Inr ctx\<close>,
  this witness separates two \<^emph>\<open>program points\<close> under a single call-only context by
  keying global writes on their \<^emph>\<open>definition site\<close> (\<^type>\<open>def_site\<close>) and reading
  through the reaching-definition digest \<^const>\<open>rd_obs\<close>.

  It realises the flat program of the migration note (\<open>DIGEST_INDEXED_READER_MIGRATION\<close>
  \<section>7/\<section>8): the callee-writes shape
  \begin{verbatim}
    main:  G := 0  (DS1);   f();   ...;   GH := G
    f:     G := 1  (DS3)
  \end{verbatim}
  with call node \<^term>\<open>4::pp\<close>, callee exit \<^term>\<open>5::pp\<close>, return \<^term>\<open>6::pp\<close>.  The
  callee must-write of \<open>G\<close> \<^bold>\<open>kills\<close> the caller's incoming \<open>DS1\<close> and \<^bold>\<open>gens\<close> \<open>DS3\<close>,
  so the return reaches \<^term>\<open>{DS3}\<close> --- not \<^term>\<open>{DS1}\<close>, which naive intra RD would
  read (unsound, concrete value \<open>1\<close>).

  Because a proper kill drops the caller's def at the return, \<^term>\<open>rd_reach 4\<close> is
  \<^emph>\<open>not\<close> contained in \<^term>\<open>rd_reach 6\<close> (\<open>reach cl \<subseteq> reach v\<close> fails).  So the local
  combine case is discharged through the \<open>bot\<close>-on-locals route, i.e. this witness
  matches the premise shape of \<open>reaching_def_collect_sound_bot\<close>
  (\<open>LOCAL_POST\<close> + \<open>GLOB_BOT\<close> + \<open>CMP_SOUND\<close>), not the monotone
  \<open>reaching_def_collect_sound\<close>.
\<close>

subsection \<open>The def-site-keyed solution\<close>

text \<open>Per-def-site global slot: \<open>DS1\<close> published \<^const>\<open>SZero\<close>, \<open>DS3\<close> published \<^const>\<open>SPos\<close>.\<close>
definition rd_slot :: "def_site \<Rightarrow> sign abs_state" where
  "rd_slot d = (\<lambda>n. if n = ''G'' then (case d of DS1 \<Rightarrow> SZero | DS3 \<Rightarrow> SPos) else SBot)"

text \<open>
  Local unknown at a program point (publish discipline): globals sit in the
  def-site slots, so the \<open>Inl\<close> slot is \<^const>\<open>SBot\<close> on every global.  The caller
  local \<open>x\<close> flows \<^const>\<open>SPos\<close> at the call to \<^const>\<open>STop\<close> at the return.
\<close>
definition rd_loc :: "pp \<Rightarrow> sign abs_state" where
  "rd_loc p = (\<lambda>n. if is_global n then SBot
                   else if n = ''x'' then (if p = 4 then SPos else if p = 6 then STop else SBot)
                   else SBot)"

definition rd_sig :: "pp \<times> unit + def_site \<Rightarrow> sign abs_state" where
  "rd_sig u = (case u of Inl (p, ctx) \<Rightarrow> rd_loc p | Inr d \<Rightarrow> rd_slot d)"

text \<open>
  Reaching-definition reader.  Under one call-only context (\<^typ>\<open>unit\<close>) the reader
  separates the points: the call node \<^term>\<open>4\<close> reaches the caller's own \<open>DS1\<close>; the
  callee exit \<^term>\<open>5\<close> and the return \<^term>\<open>6\<close> reach the callee's \<open>DS3\<close> (the caller's
  \<open>DS1\<close> is killed by the callee must-write).
\<close>
definition rd_reach :: "pp \<Rightarrow> unit \<Rightarrow> def_site set" where
  "rd_reach p ctx = (if p = 4 then {DS1} else {DS3})"

text \<open>Trivial routing: a single call-only context.\<close>
definition rd_rt :: "pp \<Rightarrow> unit \<Rightarrow> sign abs_state \<Rightarrow> unit" where
  "rd_rt cl ctx s = ()"

subsection \<open>The digest read collapses to the reaching slot\<close>

lemma rd_glob_read_singleton:
  assumes "R = {d}"
  shows "glob_env_cmp (\<lambda>_ g. rd_compatible R g) ctx \<sigma> = \<sigma> (Inr d)"
proof (rule order_antisym)
  show "glob_env_cmp (\<lambda>_ g. rd_compatible R g) ctx \<sigma> \<le> \<sigma> (Inr d)"
  proof (rule glob_env_cmp_le)
    fix k assume "(\<lambda>_ g. rd_compatible R g) ctx k"
    hence "k = d" using assms by (simp add: rd_compatible_def)
    thus "\<sigma> (Inr k) \<le> \<sigma> (Inr d)" by simp
  qed
  have "(\<lambda>_ g. rd_compatible R g) ctx d" using assms by (simp add: rd_compatible_def)
  thus "\<sigma> (Inr d) \<le> glob_env_cmp (\<lambda>_ g. rd_compatible R g) ctx \<sigma>"
    by (rule glob_env_cmp_upper)
qed

lemma rd_read_at:
  assumes "reach v ctx = {d}"
  shows "rd_obs reach \<sigma> (v, ctx) = \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr d)"
  unfolding digest_global_read.obs_digest_def
  by (simp add: rd_glob_read_singleton[OF assms])

subsection \<open>The three combine obligations, in premise shape\<close>

definition rd_combines :: "(pp \<times> pp \<times> pp) set" where
  "rd_combines = {(4, 5, 6)}"

text \<open>\<open>LOCAL_POST\<close>: the caller local flows to the return local (here \<open>x\<close>: \<^term>\<open>SPos \<le> STop\<close>).\<close>
lemma LOCAL_POST_inst:
  "(cl, ex, v) \<in> rd_combines \<Longrightarrow> \<not> is_global x
     \<Longrightarrow> rd_sig (Inl (cl, ctx)) x \<le> rd_sig (Inl (v, ctx)) x"
  by (auto simp: rd_combines_def rd_sig_def rd_loc_def less_eq_sign_def is_global_def)

text \<open>\<open>GLOB_BOT\<close>: every def-site slot is \<^const>\<open>SBot\<close> on locals (publish discipline).\<close>
lemma GLOB_BOT_inst:
  "local_bot_on_locals (rd_sig (Inr gk))"
  by (simp add: local_bot_on_locals_def rd_sig_def rd_slot_def bot_sign_def is_global_def
         split: def_site.splits)

text \<open>
  \<open>CMP_SOUND\<close>: at a global variable the callee-exit read under the routed context is
  covered by the read at the return.  Both reach \<^term>\<open>{DS3}\<close> (the callee's write), so
  both collapse to slot \<^term>\<open>Inr DS3\<close>; the local summands are \<^const>\<open>SBot\<close> on globals.
\<close>
lemma rd_read_callee:
  assumes g: "is_global x" and p: "p \<noteq> 4"
  shows "rd_obs rd_reach rd_sig (p, u) x = \<bottom> \<squnion> rd_sig (Inr DS3) x"
proof -
  have r: "rd_reach p u = {DS3}" using p by (simp add: rd_reach_def)
  have "rd_obs rd_reach rd_sig (p, u) x = rd_sig (Inl (p, u)) x \<squnion> rd_sig (Inr DS3) x"
    using rd_read_at[where reach = rd_reach and \<sigma> = rd_sig and v = p and ctx = u and d = DS3, OF r]
    by (simp add: sup_fun_def)
  thus ?thesis using g by (simp add: rd_sig_def rd_loc_def bot_sign_def)
qed

lemma CMP_SOUND_inst:
  assumes "(cl, ex, v) \<in> rd_combines" and g: "is_global x"
  shows "rd_obs rd_reach rd_sig (ex, rd_rt cl ctx (rd_sig (Inl (cl, ctx)))) x
           \<le> rd_obs rd_reach rd_sig (v, ctx) x"
proof -
  from assms(1) have e: "ex = 5" and rv: "v = 6" by (auto simp: rd_combines_def)
  show ?thesis using e rv by (simp add: rd_read_callee[OF g])
qed

text \<open>
  The two facts the generic \<open>reaching_def_collect_sound_bot_incl\<close> consumes in place of a
  hand \<open>CMP_SOUND\<close>: the \<open>Inl\<close> slot is \<^const>\<open>bot\<close> on every global (\<open>INL_GLOB_BOT\<close>), and the
  callee-exit reaching set is contained in the return reaching set (\<open>CALLEE_INCL\<close>).  The
  latter holds here --- \<open>rd_reach 5 = {DS3}\<close> is contained in \<open>rd_reach 6 = {DS3}\<close> --- even
  though the \<^emph>\<open>caller\<close> inclusion \<open>rd_reach 4 = {DS1}\<close> into \<open>rd_reach 6 = {DS3}\<close> fails under
  the kill: the exit-to-return edge re-gens \<^const>\<open>DS3\<close>, so read soundness needs no
  monotone reader.
\<close>
lemma INL_GLOB_BOT_inst:
  "is_global x \<Longrightarrow> rd_sig (Inl pc) x = bot"
  by (cases pc) (simp add: rd_sig_def rd_loc_def bot_sign_def)

lemma CALLEE_INCL_inst:
  "(cl, ex, v) \<in> rd_combines
     \<Longrightarrow> rd_reach ex (rd_rt cl ctx (rd_sig (Inl (cl, ctx)))) \<subseteq> rd_reach v ctx"
  by (auto simp: rd_combines_def rd_reach_def)

subsection \<open>The obligations plug into the RD collecting theorem\<close>

text \<open>
  The three combine obligations above fill exactly the \<open>LOCAL_POST\<close> / \<open>GLOB_BOT\<close> /
  \<open>CMP_SOUND\<close> slots of \<open>reaching_def_collect_sound_bot\<close>.  Feeding them in --- with the
  generic collecting-layer premises (\<open>ENTRY\<close>/\<open>EDGE\<close>/digest laws/\<open>ENTER_MONO\<close>) carried as
  hypotheses --- discharges the RD-instance collecting soundness at the def-site-keyed
  reader \<^const>\<open>rd_obs\<close> \<^const>\<open>rd_reach\<close> \<^const>\<open>rd_sig\<close>.  This is the instantiation the
  migration note's step 3 gates on: \<open>CMP_SOUND\<close> is no longer an open premise for this
  witness but a proven fact.
\<close>
theorem rd_collect_sound_witness:
  fixes g :: cfg and S :: "store set"
    and dg :: "store list \<Rightarrow> unit" and cmp :: "unit \<Rightarrow> unit \<Rightarrow> bool" and entdg :: "store \<Rightarrow> unit"
  assumes comb: "combines g = rd_combines"
    and ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
          \<Longrightarrow> s \<in> \<lbrakk>rd_obs rd_reach rd_sig (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
          \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs rd_reach rd_sig (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
          \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs rd_reach rd_sig (u, ctx)\<rbrakk>
          \<Longrightarrow> s' \<in> \<lbrakk>rd_obs rd_reach rd_sig (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs rd_reach rd_sig (cl, ctx)\<rbrakk>
          \<Longrightarrow> cmp (entdg s) (rd_rt cl ctx (rd_sig (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs rd_reach rd_sig (v, ctx)\<rbrakk>"
proof (rule reaching_def_collect_sound_bot_incl
         [where sigma = rd_sig and reach = rd_reach and rt = rd_rt
            and dg = dg and cmp = cmp and entdg = entdg and S = S and g = g])
  show "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
          \<Longrightarrow> rd_sig (Inl (cl, ctx)) x \<le> rd_sig (Inl (v, ctx)) x"
    using LOCAL_POST_inst comb by blast
  show "\<And>gk. local_bot_on_locals (rd_sig (Inr gk))" by (rule GLOB_BOT_inst)
  show "\<And>p x. is_global x \<Longrightarrow> rd_sig (Inl p) x = bot" by (rule INL_GLOB_BOT_inst)
  show "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
          \<Longrightarrow> rd_reach ex (rd_rt cl ctx (rd_sig (Inl (cl, ctx)))) \<subseteq> rd_reach v ctx"
    using CALLEE_INCL_inst comb by blast
qed (fact ENTRY PROC_ENTRY EDGE DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+

text \<open>
  The same witness with the opaque gamma-level \<open>EDGE\<close> premise replaced by the
  algebraic merged-edge family \<open>MERGED_EDGE\<close> of \<^theory>\<open>Voblint_Analysis.RD_Set_Edge_Backbone\<close>.
  Where \<open>rd_collect_sound_witness\<close> assumes each edge step preserves \<^const>\<open>rd_obs\<close>
  coverage as a black box, this assumes only that the effectful transfer, run on the
  reaching-set-merged read at each source, sits below \<^const>\<open>rd_obs\<close> at the target ---
  a per-edge inequality a set-reading generator's post-fixpoint discharges.  The
  combine side is unchanged: \<open>LOCAL_POST\<close> / \<open>GLOB_BOT\<close> / \<open>INL_GLOB_BOT\<close> / \<open>CALLEE_INCL\<close>
  are the same proven instance facts.  So this witness carries \<^emph>\<open>no\<close> opaque per-edge
  step hypothesis.
\<close>
theorem rd_collect_sound_witness_merged:
  fixes g :: cfg and S :: "store set"
    and etf :: "(unit, sign) effectful_domain_transfer"
    and dg :: "store list \<Rightarrow> unit" and cmp :: "unit \<Rightarrow> unit \<Rightarrow> bool" and entdg :: "store \<Rightarrow> unit"
  assumes stf: "sound_effectful_transfer etf"
    and comb: "combines g = rd_combines"
    and ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
          \<Longrightarrow> s \<in> \<lbrakk>rd_obs rd_reach rd_sig (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
          \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs rd_reach rd_sig (v, ctx)\<rbrakk>"
    and MERGED_EDGE: "\<And>ctx u a v. (u, a, v) \<in> edges g
          \<Longrightarrow> etf_collecting_full (apply_etf etf a u) (rd_merge_env rd_reach rd_sig ctx u)
                \<le> rd_obs rd_reach rd_sig (v, ctx)"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs rd_reach rd_sig (cl, ctx)\<rbrakk>
          \<Longrightarrow> cmp (entdg s) (rd_rt cl ctx (rd_sig (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs rd_reach rd_sig (v, ctx)\<rbrakk>"
proof (rule reaching_def_collect_sound_bot_incl_from_merged
         [where sigma = rd_sig and reach = rd_reach and etf = etf and rt = rd_rt
            and dg = dg and cmp = cmp and entdg = entdg and S = S and g = g])
  show "sound_effectful_transfer etf" by (rule stf)
  show "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
          \<Longrightarrow> rd_sig (Inl (cl, ctx)) x \<le> rd_sig (Inl (v, ctx)) x"
    using LOCAL_POST_inst comb by blast
  show "\<And>gk. local_bot_on_locals (rd_sig (Inr gk))" by (rule GLOB_BOT_inst)
  show "\<And>p x. is_global x \<Longrightarrow> rd_sig (Inl p) x = bot" by (rule INL_GLOB_BOT_inst)
  show "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
          \<Longrightarrow> rd_reach ex (rd_rt cl ctx (rd_sig (Inl (cl, ctx)))) \<subseteq> rd_reach v ctx"
    using CALLEE_INCL_inst comb by blast
qed (fact ENTRY PROC_ENTRY MERGED_EDGE DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+

subsection \<open>The precision payoff, machine-checked\<close>

text \<open>
  Under one call-only context the reader separates the two points exactly: the call
  node reads the caller's \<^const>\<open>SZero\<close>, the return reads the callee's \<^const>\<open>SPos\<close>.
  The context-blind read (joining both def-site slots) merges them to \<^const>\<open>SNonNeg\<close>
  --- the precision the def-site keying recovers.
\<close>

lemma read_call4: "rd_obs rd_reach rd_sig (4, ()) ''G'' = SZero"
proof -
  have r: "rd_reach 4 () = {DS1}" by (simp add: rd_reach_def)
  have "rd_obs rd_reach rd_sig (4, ()) ''G''
          = rd_sig (Inl (4, ())) ''G'' \<squnion> rd_sig (Inr DS1) ''G''"
    using rd_read_at[where reach = rd_reach and \<sigma> = rd_sig and v = 4 and ctx = "()" and d = DS1, OF r]
    by (simp add: sup_fun_def)
  thus ?thesis
    by (simp add: rd_sig_def rd_loc_def rd_slot_def is_global_def sup_sign_def)
qed

lemma read_return6: "rd_obs rd_reach rd_sig (6, ()) ''G'' = SPos"
proof -
  have r: "rd_reach 6 () = {DS3}" by (simp add: rd_reach_def)
  have "rd_obs rd_reach rd_sig (6, ()) ''G''
          = rd_sig (Inl (6, ())) ''G'' \<squnion> rd_sig (Inr DS3) ''G''"
    using rd_read_at[where reach = rd_reach and \<sigma> = rd_sig and v = 6 and ctx = "()" and d = DS3, OF r]
    by (simp add: sup_fun_def)
  thus ?thesis
    by (simp add: rd_sig_def rd_loc_def rd_slot_def is_global_def sup_sign_def)
qed

lemma merge_join_all: "(rd_slot DS1 \<squnion> rd_slot DS3) ''G'' = SNonNeg"
  by (simp add: rd_slot_def sup_fun_def sup_sign_def)

lemma points_separated:
  "rd_obs rd_reach rd_sig (4, ()) ''G'' \<noteq> rd_obs rd_reach rd_sig (6, ()) ''G''"
  by (simp add: read_call4 read_return6)

text \<open>
  The kill is visible in the reader: the caller's reaching set \<^term>\<open>{DS1}\<close> is
  \<^emph>\<open>not\<close> contained in the return's \<^term>\<open>{DS3}\<close>, so \<open>RD_RETURN_INCL\<close> fails and the
  \<open>bot\<close>-on-locals route is the one this witness uses.
\<close>
lemma return_incl_fails:
  "\<not> rd_reach 4 ctx \<subseteq> rd_reach 6 ctx"
  by (simp add: rd_reach_def)

end
