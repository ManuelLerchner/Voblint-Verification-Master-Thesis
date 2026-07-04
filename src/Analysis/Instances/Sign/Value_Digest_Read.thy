theory Value_Digest_Read
  imports
    Digest_Global_Read
    Sign_Domain
begin

section \<open>Value-carried digest read: a finite two-valued mode partition\<close>

text \<open>
  A minimal, additive instance of \<^locale>\<open>digest_global_read\<close> whose reader is a
  \<^emph>\<open>projection of the solved local state\<close> rather than an external map.  The digest is a
  two-point \<^emph>\<open>mode\<close>, carried in a ghost local variable \<open>''mode''\<close> and read back out of the
  local slot.  Global partitions are keyed by the mode, a \<^class>\<open>finite\<close> type as the
  kernel's global-key sort requires --- the whole abstract state would not be.

  Nothing in \<^theory>\<open>Voblint_Analysis.Digest_Global_Read\<close> changes: the reader is passed as
  the locale's \<open>reader_digest\<close> parameter and closes over the same \<open>sigma\<close> that
  \<^const>\<open>digest_global_read.obs_digest\<close> reads.
\<close>

subsection \<open>The finite mode partition\<close>

datatype mode = MZero | MOne

instance mode :: finite
proof
  show "finite (UNIV :: mode set)"
  proof (rule finite_subset[of _ "{MZero, MOne}"])
    show "(UNIV :: mode set) \<subseteq> {MZero, MOne}" using mode.exhaust by blast
    show "finite {MZero, MOne}" by simp
  qed
qed

text \<open>An \<^class>\<open>enum\<close> instance so the mode-filtered read \<^const>\<open>glob_env_cmp\<close>
  code-generates: its filtered join folds over the finite mode key type.\<close>
instantiation mode :: enum
begin
definition "enum_mode = [MZero, MOne]"
definition "enum_all_mode P \<longleftrightarrow> P MZero \<and> P MOne"
definition "enum_ex_mode P \<longleftrightarrow> P MZero \<or> P MOne"
instance
proof
  show "(UNIV :: mode set) = set enum_class.enum"
    using mode.exhaust by (auto simp: enum_mode_def)
qed (auto simp: enum_mode_def enum_all_mode_def enum_ex_mode_def, (metis mode.exhaust)+)
end

subsection \<open>Decode, compatibility, and the projection reader\<close>

text \<open>The mode carried by a slot: the sign of the ghost variable, collapsed to two points.
  \<^const>\<open>SPos\<close> is mode one; every other sign --- including the unset default \<^const>\<open>STop\<close> ---
  is the initial mode zero, so an unkeyed initial global lands in \<^term>\<open>MZero\<close>, not \<^term>\<open>MOne\<close>.\<close>
definition mode_decode :: "sign \<Rightarrow> mode" where
  "mode_decode s = (if s = SPos then MOne else MZero)"

text \<open>A read at mode \<open>d\<close> sees exactly the partition keyed by \<open>d\<close>.\<close>
definition mode_compatible :: "mode \<Rightarrow> mode \<Rightarrow> bool" where
  "mode_compatible d g = (d = g)"

lemma mode_compatible_singleton: "{g. mode_compatible d g} = {d}"
  unfolding mode_compatible_def by auto

text \<open>
  The reader is the projection \<open>reader_digest v ctx := mode_decode (sigma (Inl (v,ctx)) ''mode'')\<close>:
  it recovers the mode from the solved local slot at the read point.
\<close>
definition mode_reader ::
  "((nat \<times> 'c) + mode \<Rightarrow> sign abs_state) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> mode" where
  "mode_reader \<sigma> v ctx = mode_decode (\<sigma> (Inl (v, ctx)) ''mode'')"

subsection \<open>The digest read and its reduced shape\<close>

text \<open>
  \<^const>\<open>digest_global_read.obs_digest\<close> specialised to the projection reader and mode
  compatibility.  The kernel is instantiated, not modified.
\<close>
definition mode_obs ::
  "((nat \<times> 'c) + mode \<Rightarrow> sign abs_state) \<Rightarrow> (nat \<times> 'c) \<Rightarrow> sign abs_state" where
  "mode_obs \<sigma> = digest_global_read.obs_digest (mode_reader \<sigma>) mode_compatible \<sigma>"

text \<open>
  The read collapses to the local slot joined with the \<^emph>\<open>single\<close> partition slot selected by
  the point's decoded mode: equality compatibility filters the global keys to a singleton.
\<close>
lemma mode_obs_reduce:
  "mode_obs \<sigma> (v, ctx)
     = \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (mode_decode (\<sigma> (Inl (v, ctx)) ''mode'')))"
  unfolding mode_obs_def digest_global_read.obs_digest_def mode_reader_def
  by (simp add: glob_env_cmp_singleton[OF mode_compatible_singleton])

subsection \<open>Context-sliced collecting soundness for the mode read\<close>

text \<open>
  The mode-specialised instance of \<^theory_text>\<open>obs_digest_collect_ctx_sound_bot\<close>: the
  context-sliced collecting set at \<open>(v, ctx)\<close> is covered by the mode digest read, given the
  standard collecting premises.  The bottom-on-locals route (\<open>GLOB_BOT\<close>) is used, so the read
  carries \<^emph>\<open>no\<close> projection-monotonicity obligation --- the local-variable combine case reduces
  to \<open>LOCAL_POST\<close> alone.  Every remaining hypothesis is a premise about a concrete solved
  \<open>sigma\<close> and the digest bookkeeping \<open>dg\<close> / \<open>cmp\<close> / \<open>rt\<close> / \<open>entdg\<close>; discharging them for an
  executable run is the next step.
\<close>
theorem mode_collect_ctx_sound_bot:
  fixes sigma :: "(nat \<times> 'c) + mode \<Rightarrow> sign abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "nat \<Rightarrow> 'c \<Rightarrow> sign abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>mode_obs sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>mode_obs sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> mode_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> mode_obs sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>mode_obs sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
  using assms unfolding mode_obs_def
  by (rule digest_global_read.obs_digest_collect_ctx_sound_bot)

subsection \<open>Discharging the substantive obligations\<close>

text \<open>
  The two structural obligations reduce to the standard context-keyed slot invariants, and
  the global-read obligation reduces to those plus \<^emph>\<open>mode stability across a call\<close>.  The
  remaining hypotheses of \<^theory_text>\<open>mode_collect_ctx_sound_bot\<close> --- the seed / edge / digest
  bookkeeping premises --- are context-channel conditions unchanged from the context spine.
\<close>

text \<open>\<open>GLOB_BOT\<close> is exactly \<^const>\<open>inr_slot_locals_bot_ctx\<close>: each partition slot is bot on locals.\<close>
lemma mode_glob_bot_ctx:
  assumes "inr_slot_locals_bot_ctx \<sigma>"
  shows "local_bot_on_locals (\<sigma> (Inr gk))"
  using assms by (simp add: inr_slot_locals_bot_ctx_def local_bot_on_locals_def)

text \<open>
  At a global variable the mode read collapses to the single selected partition slot: the
  local summand is bot there by \<^const>\<open>inl_slot_globals_bot_ctx\<close>.
\<close>
lemma mode_obs_global:
  assumes inl: "inl_slot_globals_bot_ctx \<sigma>"
  assumes gx: "is_global x"
  shows "mode_obs \<sigma> (v, ctx) x = \<sigma> (Inr (mode_decode (\<sigma> (Inl (v, ctx)) ''mode''))) x"
proof -
  have "\<sigma> (Inl (v, ctx)) x = bot" using inl gx by (simp add: inl_slot_globals_bot_ctx_def)
  thus ?thesis by (simp add: mode_obs_reduce)
qed

text \<open>
  \<open>CMP_SOUND\<close> at the globals: if the callee-exit node's mode agrees with the return node's
  mode, both reads select the same partition slot, so the read is sound (indeed equal).
  This is the mode-partition analogue of Goblint's privatised global read.
\<close>
lemma mode_cmp_sound:
  assumes inl: "inl_slot_globals_bot_ctx \<sigma>"
  assumes agree: "mode_decode (\<sigma> (Inl (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))) ''mode'')
                    = mode_decode (\<sigma> (Inl (v, ctx)) ''mode'')"
  assumes gx: "is_global x"
  shows "mode_obs \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x \<le> mode_obs \<sigma> (v, ctx) x"
proof -
  have "mode_obs \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x
          = \<sigma> (Inr (mode_decode (\<sigma> (Inl (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))) ''mode''))) x"
    by (rule mode_obs_global[OF inl gx])
  also have "\<dots> = \<sigma> (Inr (mode_decode (\<sigma> (Inl (v, ctx)) ''mode''))) x"
    by (simp add: agree)
  also have "\<dots> = mode_obs \<sigma> (v, ctx) x"
    by (rule mode_obs_global[OF inl gx, symmetric])
  finally show ?thesis by simp
qed

text \<open>
  The reduced collecting theorem: \<open>GLOB_BOT\<close> and \<open>CMP_SOUND\<close> are discharged from the two slot
  invariants and mode stability \<open>MODE_AGREE\<close>.  \<open>MODE_AGREE\<close> --- the ghost \<open>''mode''\<close> read at a
  callee-exit under its routed context matches the read at the return node --- is the sole
  genuinely new proof obligation the value-carried mode introduces; the generator supplies it.
\<close>
theorem mode_collect_ctx_sound_bot_reduced:
  fixes sigma :: "(nat \<times> 'c) + mode \<Rightarrow> sign abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "nat \<Rightarrow> 'c \<Rightarrow> sign abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>mode_obs sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>mode_obs sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and INR_BOT: "inr_slot_locals_bot_ctx sigma"
    and INL_BOT: "inl_slot_globals_bot_ctx sigma"
    and MODE_AGREE: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> mode_decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) ''mode'')
              = mode_decode (sigma (Inl (v, ctx)) ''mode'')"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>mode_obs sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>mode_obs sigma (v, ctx)\<rbrakk>"
proof -
  have GB: "\<And>gk. local_bot_on_locals (sigma (Inr gk))" by (rule mode_glob_bot_ctx[OF INR_BOT])
  have CS: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> mode_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> mode_obs sigma (v, ctx) x"
  proof -
    fix ctx cl ex v x
    assume comb: "(cl, ex, v) \<in> combines g" and gx: "is_global x"
    have ag: "mode_decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) ''mode'')
                = mode_decode (sigma (Inl (v, ctx)) ''mode'')"
      by (rule MODE_AGREE[OF comb])
    have "mode_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
            = sigma (Inr (mode_decode (sigma (Inl (ex, rt cl ctx (sigma (Inl (cl, ctx))))) ''mode''))) x"
      by (rule mode_obs_global[OF INL_BOT gx])
    also have "\<dots> = sigma (Inr (mode_decode (sigma (Inl (v, ctx)) ''mode''))) x"
      by (simp add: ag)
    also have "\<dots> = mode_obs sigma (v, ctx) x"
      by (rule mode_obs_global[OF INL_BOT gx, symmetric])
    finally show "mode_obs sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> mode_obs sigma (v, ctx) x"
      by simp
  qed
  show ?thesis
    using ENTRY PROC_ENTRY EDGE LOCAL_POST GB CS DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO
    by (rule mode_collect_ctx_sound_bot)
qed

subsection \<open>The projection read is the certified context read\<close>

text \<open>
  The keystone connecting the two soundness spines.  The executable keyed generator
  (\<open>side_cfg_T_eff_cmp\<close> with \<open>gkey = id\<close> on a \<^class>\<open>finite\<close> mode context) proves
  collecting soundness through \<^term>\<open>side_env_cmp (=) sigma (v, ctx)\<close> --- the read keyed by
  the \<^emph>\<open>context\<close>.  The digest kernel proves it through \<^const>\<open>mode_obs\<close> --- the read keyed by
  the \<^emph>\<open>projection\<close> \<open>mode_decode (sigma (Inl (v, ctx)) ''mode'')\<close>.  Under the alignment
  invariant \<open>ctx = mode_decode (sigma (Inl (v, ctx)) ''mode'')\<close> --- the context channel carries
  the ghost mode, Goblint's \<open>C.t = context D\<close> --- the two reads are \<^emph>\<open>identical\<close>.  So the
  projection reader is exactly the certified context read, and the executable generator run
  discharges \<^const>\<open>mode_obs\<close> soundness with no separate solve.
\<close>
lemma mode_obs_eq_side_env_cmp:
  fixes sigma :: "(nat \<times> mode) + mode \<Rightarrow> sign abs_state"
  assumes align: "mode_decode (sigma (Inl (v, ctx)) ''mode'') = ctx"
  shows "mode_obs sigma (v, ctx) = side_env_cmp (=) sigma (v, ctx)"
proof -
  have single: "{k. (=) ctx k} = {ctx}" by auto
  have "mode_obs sigma (v, ctx)
          = sigma (Inl (v, ctx)) \<squnion> sigma (Inr (mode_decode (sigma (Inl (v, ctx)) ''mode'')))"
    by (rule mode_obs_reduce)
  also have "\<dots> = sigma (Inl (v, ctx)) \<squnion> sigma (Inr ctx)" using align by simp
  also have "\<dots> = side_env_cmp (=) sigma (v, ctx)"
    by (simp add: side_env_cmp_singleton[where cmp = "(=)", OF single])
  finally show ?thesis .
qed

end
