theory Digest_Global_Read
  imports TD_Side_Eff_Cmp_Sound
begin

section \<open>Global read is bottom on local variables\<close>

text \<open>
  A join over states that are all \<open>bot\<close> at a coordinate is \<open>bot\<close> there.  With the
  \<open>inr_slot_locals_bot\<close> solution invariant (each global slot is \<open>bot\<close> on local
  variables), the filtered global read \<^const>\<open>glob_env_cmp\<close> is \<open>bot\<close> on locals ---
  regardless of the filter.  This is what lets the digest read discharge its
  local-variable combine case without constraining the reader digest.
\<close>

lemma fold_sup_bot_at:
  fixes F :: "('v \<Rightarrow> 'a::bounded_semilattice_sup_bot) set"
  assumes "finite F" and "\<And>a. a \<in> F \<Longrightarrow> a x = bot"
  shows "Finite_Set.fold (\<squnion>) bot F x = bot"
  using assms
proof (induction F rule: finite_induct)
  case empty thus ?case by simp
next
  case (insert a F)
  interpret ci: comp_fun_idem "(\<squnion>) :: ('v \<Rightarrow> 'a) \<Rightarrow> _ \<Rightarrow> _"
    by unfold_locales (auto simp: sup_left_commute)
  have step: "Finite_Set.fold (\<squnion>) bot (insert a F) = a \<squnion> Finite_Set.fold (\<squnion>) bot F"
    by (rule ci.fold_insert_idem[OF insert.hyps(1)])
  have ax: "a x = bot" using insert.prems by simp
  have ih: "Finite_Set.fold (\<squnion>) bot F x = bot"
  proof (rule insert.IH)
    fix b assume "b \<in> F" thus "b x = bot" using insert.prems by simp
  qed
  have "Finite_Set.fold (\<squnion>) bot (insert a F) x = a x \<squnion> Finite_Set.fold (\<squnion>) bot F x"
    unfolding step by (simp add: sup_fun_def)
  also have "... = bot" using ax ih by simp
  finally show ?case .
qed

lemma glob_env_cmp_local_bot:
  fixes sigma :: "'l + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes inr: "\<And>g. local_bot_on_locals (sigma (Inr g))"
  shows "local_bot_on_locals (glob_env_cmp cmp ctx sigma)"
  unfolding local_bot_on_locals_def glob_env_cmp_def abs_join_set_def
proof (clarify)
  fix x assume ng: "\<not> is_global x"
  have "\<And>a. a \<in> (\<lambda>k. sigma (Inr k)) ` {k. cmp ctx k} \<Longrightarrow> a x = bot"
    using inr ng unfolding local_bot_on_locals_def by auto
  thus "Finite_Set.fold (\<squnion>) bot ((\<lambda>k. sigma (Inr k)) ` {k. cmp ctx k}) x = bot"
    by (rule fold_sup_bot_at[OF finite_imageI[OF glob_env_cmp_finite_keys]])
qed

section \<open>Generic digest-refined global read\<close>

text \<open>
  The read interface for digest-refined global reads.  A reader at a program point
  carries a digest \<open>reader_digest v ctx\<close>, and joins exactly the global slots whose
  writer key is \<open>compatible\<close> with that digest.  This generalises
  \<^const>\<open>side_env_cmp\<close>, whose filter is the context alone: \<^const>\<open>side_env_cmp\<close>
  cannot distinguish two program points sharing a context, whereas the digest read
  can, because \<open>reader_digest\<close> takes the point \<^typ>\<open>pp\<close>.

  The interface fixes only the reader side (\<open>reader_digest\<close>, \<open>compatible\<close>); the
  writer key that tags a global contribution is a generator-level parameter, not a
  read-interface one --- no read or soundness theorem here mentions it.  The sole
  kernel assumption is the sort \<open>'g::finite\<close> on the key type, inherited from
  \<^const>\<open>glob_env_cmp\<close>.
\<close>

locale digest_global_read =
  fixes reader_digest :: "pp \<Rightarrow> 'c \<Rightarrow> 'd"
    and compatible    :: "'d \<Rightarrow> 'g::finite \<Rightarrow> bool"
begin

text \<open>
  The generic observation read: the local slot at \<open>(v, ctx)\<close> joined with the
  \<open>compatible\<close>-filtered globals for the point's digest.  Reuses
  \<^const>\<open>glob_env_cmp\<close> unchanged --- its filter argument is already free, so passing
  a point-dependent predicate needs no new global-read machinery.
\<close>
definition obs_digest ::
  "((pp \<times> 'c) + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
where
  "obs_digest \<sigma> p =
     \<sigma> (Inl p)
     \<squnion> glob_env_cmp (\<lambda>_ g. compatible (reader_digest (fst p) (snd p)) g) (snd p) \<sigma>"

text \<open>Filter-monotonicity of the reused global read: a wider compatible set joins more.\<close>
lemma glob_env_cmp_filter_mono:
  assumes "{k. cmp1 ctx1 k} \<subseteq> {k. cmp2 ctx2 k}"
  shows "glob_env_cmp cmp1 ctx1 \<sigma> \<le> glob_env_cmp cmp2 ctx2 \<sigma>"
proof (rule glob_env_cmp_le)
  fix k assume "cmp1 ctx1 k"
  hence "cmp2 ctx2 k" using assms by blast
  thus "\<sigma> (Inr k) \<le> glob_env_cmp cmp2 ctx2 \<sigma>" by (rule glob_env_cmp_upper)
qed

subsection \<open>Degenerate instance: recovering \<^const>\<open>side_env_cmp\<close>\<close>

text \<open>
  When the digest is the context and \<open>compatible\<close> is the context/key relation,
  \<^const>\<open>obs_digest\<close> is exactly \<^const>\<open>side_env_cmp\<close>.  This certifies the interface
  strictly generalises the current context-only read.
\<close>
lemma obs_digest_collapse_shape:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes "\<And>v ctx g. compatible (reader_digest v ctx) g = gcmp ctx g"
  shows "obs_digest \<sigma> (v, ctx) = side_env_cmp gcmp \<sigma> (v, ctx)"
proof -
  have "{g. compatible (reader_digest v ctx) g} = {g. gcmp ctx g}" using assms by simp
  thus ?thesis
    unfolding obs_digest_def side_env_cmp_def glob_env_cmp_def by simp
qed

subsection \<open>Combine reassembly at the digest read\<close>

text \<open>
  The reassembled combine value: locals from the caller read, globals from the
  callee-exit read at the routed context.  The keyed analogue of
  \<^const>\<open>combine_read_cmp\<close>, with the point-dependent \<^const>\<open>obs_digest\<close> in place of
  \<^const>\<open>side_env_cmp\<close>.  The routing read is the plain local slot \<open>\<sigma> (Inl (cl, ctx))\<close>
  --- point-independent, unchanged from the context spine.
\<close>
definition combine_read_obs ::
  "((pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state"
where
  "combine_read_obs \<sigma> rt cl ex ctx =
     \<langle> obs_digest \<sigma> (cl, ctx)
     | obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) \<rangle>"

text \<open>
  Combine soundness from a reassembly bound: merge caller/callee soundness through
  \<open>combine_states_sound\<close>, then carry to the return unknown by
  \<open>gamma_state_mono\<close>.  Read-agnostic --- identical in shape to
  \<open>combine_case_cmp_sound\<close>.
\<close>
lemma combine_case_obs_sound:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
  assumes caller: "last tau \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>"
  assumes callee: "last rho \<in> \<lbrakk>obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))\<rbrakk>"
  assumes bound: "combine_read_obs \<sigma> rt cl ex ctx \<le> obs_digest \<sigma> (v, ctx)"
  shows "<last tau|last rho> \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
proof -
  have "<last tau|last rho> \<in> \<lbrakk>combine_read_obs \<sigma> rt cl ex ctx\<rbrakk>"
    unfolding combine_read_obs_def using caller callee by (rule combine_states_sound)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

text \<open>
  The reassembly bound splits pointwise on the variable class.  At a \<^emph>\<open>global\<close>
  variable it is \<open>CMP_SOUND\<close> (Goblint read soundness).  At a \<^emph>\<open>local\<close> variable
  the \<^const>\<open>side_env_cmp\<close> spine cancelled a shared context-only global summand; the
  point-dependent reader breaks that cancellation, so the local case carries the
  extra \<open>READER_INCL\<close> premise --- the caller-node reader set is included in the
  return-node reader set --- discharged by \<open>glob_env_cmp_filter_mono\<close>.
\<close>
lemma combine_read_obs_le:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
  assumes LOCAL_POST:
    "\<And>x. \<not> is_global x \<Longrightarrow> \<sigma> (Inl (cl, ctx)) x \<le> \<sigma> (Inl (v, ctx)) x"
  assumes READER_INCL:
    "{g. compatible (reader_digest cl ctx) g} \<subseteq> {g. compatible (reader_digest v ctx) g}"
  assumes CMP_SOUND:
    "\<And>x. is_global x
       \<Longrightarrow> obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x
             \<le> obs_digest \<sigma> (v, ctx) x"
  shows "combine_read_obs \<sigma> rt cl ex ctx \<le> obs_digest \<sigma> (v, ctx)"
proof (rule le_funI)
  fix x
  show "combine_read_obs \<sigma> rt cl ex ctx x \<le> obs_digest \<sigma> (v, ctx) x"
  proof (cases "is_global x")
    case True
    thus ?thesis
      unfolding combine_read_obs_def combine_abs_def using CMP_SOUND[OF True] by simp
  next
    case False
    have g_le: "glob_env_cmp (\<lambda>_ g. compatible (reader_digest cl ctx) g) ctx \<sigma>
                  \<le> glob_env_cmp (\<lambda>_ g. compatible (reader_digest v ctx) g) ctx \<sigma>"
      by (rule glob_env_cmp_filter_mono) (use READER_INCL in auto)
    have "\<sigma> (Inl (cl, ctx)) x \<squnion> glob_env_cmp (\<lambda>_ g. compatible (reader_digest cl ctx) g) ctx \<sigma> x
            \<le> \<sigma> (Inl (v, ctx)) x \<squnion> glob_env_cmp (\<lambda>_ g. compatible (reader_digest v ctx) g) ctx \<sigma> x"
      by (rule sup_mono[OF LOCAL_POST[OF False] le_funD[OF g_le]])
    thus ?thesis
      unfolding combine_read_obs_def combine_abs_def obs_digest_def using False by simp
  qed
qed

subsection \<open>Trace soundness over the digest read\<close>

text \<open>
  The read-agnostic trace backbone \<open>post_fixpoint_sound_at_ctx_semantic_generic\<close>
  swallows \<^const>\<open>obs_digest\<close> as a pure instantiation of its \<open>renv\<close> parameter, with
  the plain local slot as the routing read \<open>rread\<close>.  Every seed / edge / combine /
  digest-propagation premise keeps its shape; only the read symbol changes.
\<close>
theorem post_fixpoint_sound_obs_digest:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and COMB_SEM: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (\<sigma> (Inl (cl, ctx))))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
  by (rule post_fixpoint_sound_at_ctx_semantic_generic
        [where renv = obs_digest and rread = "\<lambda>s vk. s (Inl vk)"
           and rt = rt and dg = dg and cmp = cmp and entdg = entdg,
         OF ENTRY PROC_ENTRY EDGE COMB_SEM DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO wit compat])

text \<open>
  Trace soundness resting on the checkable combine side conditions instead of the
  raw \<open>COMB_SEM\<close> black box: \<open>LOCAL_POST\<close> (caller local flows to the return local),
  \<open>READER_INCL\<close> (caller-node reader set included in the return-node reader set), and
  \<open>CMP_SOUND\<close> (Goblint read soundness at the globals).  The keyed analogue of
  \<open>post_fixpoint_sound_at_ctx_semantic_cmp_final\<close>.
\<close>
theorem post_fixpoint_sound_obs_digest_final:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> \<sigma> (Inl (cl, ctx)) x \<le> \<sigma> (Inl (v, ctx)) x"
    and READER_INCL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> {g. compatible (reader_digest cl ctx) g} \<subseteq> {g. compatible (reader_digest v ctx) g}"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x \<le> obs_digest \<sigma> (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (\<sigma> (Inl (cl, ctx))))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
proof (rule post_fixpoint_sound_obs_digest
        [where rt = rt and dg = dg and cmp = cmp and entdg = entdg])
  fix ctx cl ex v' tau rho
  assume comb: "(cl, ex, v') \<in> combines g"
    and cr: "last tau \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>"
    and ce: "last rho \<in> \<lbrakk>obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))\<rbrakk>"
  have bound: "combine_read_obs \<sigma> rt cl ex ctx \<le> obs_digest \<sigma> (v', ctx)"
  proof (rule combine_read_obs_le)
    fix x assume "\<not> is_global x"
    thus "\<sigma> (Inl (cl, ctx)) x \<le> \<sigma> (Inl (v', ctx)) x" by (rule LOCAL_POST[OF comb])
  next
    show "{g. compatible (reader_digest cl ctx) g} \<subseteq> {g. compatible (reader_digest v' ctx) g}"
      by (rule READER_INCL[OF comb])
  next
    fix x assume "is_global x"
    thus "obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x \<le> obs_digest \<sigma> (v', ctx) x"
      by (rule CMP_SOUND[OF comb])
  qed
  show "<last tau|last rho> \<in> \<lbrakk>obs_digest \<sigma> (v', ctx)\<rbrakk>"
    by (rule combine_case_obs_sound[OF cr ce bound])
qed (fact ENTRY PROC_ENTRY EDGE DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO wit compat)+

subsection \<open>Context-sliced collecting soundness\<close>

text \<open>
  Lifting \<open>post_fixpoint_sound_obs_digest_final\<close> from the trace level to the
  context-sliced collecting set \<^const>\<open>cfg_collect_ctx\<close>: every store reaching \<open>v\<close>
  along a trace whose digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> is covered by the digest
  read \<^const>\<open>obs_digest\<close> at \<open>(v, ctx)\<close>.  The keyed analogue of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>; the routing \<open>rt\<close> is a parameter,
  so a \<^locale>\<open>context_domain\<close> interpretation instantiates it with
  \<^const>\<open>context_domain.route\<close> at the use site.
\<close>
theorem obs_digest_collect_ctx_sound:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> \<sigma> (Inl (cl, ctx)) x \<le> \<sigma> (Inl (v, ctx)) x"
    and READER_INCL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> {g. compatible (reader_digest cl ctx) g} \<subseteq> {g. compatible (reader_digest v ctx) g}"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x \<le> obs_digest \<sigma> (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (\<sigma> (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
proof -
  have trace_sound:
    "\<And>tr. trace_witness g S v tr \<Longrightarrow> cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
  proof -
    fix tr assume w: "trace_witness g S v tr" and c: "cmp (dg tr) ctx"
    show "last tr \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
      by (rule post_fixpoint_sound_obs_digest_final
            [where rt = rt and dg = dg and cmp = cmp and entdg = entdg,
             OF ENTRY PROC_ENTRY EDGE LOCAL_POST READER_INCL CMP_SOUND
                DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO w c])
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using trace_sound by auto
qed

subsection \<open>Bottom-on-locals variant: the local case with no reader constraint\<close>

text \<open>
  A parallel combine reduction that discharges the local-variable case from the
  \<open>inr_slot_locals_bot\<close> solution invariant (each global slot is \<open>bot\<close> on locals)
  instead of a reader inclusion.  At a local variable both filtered global reads are
  \<open>bot\<close> (\<open>glob_env_cmp_local_bot\<close>), so the case reduces to \<open>LOCAL_POST\<close> alone ---
  the reader digest is left entirely unconstrained.  This is what a point-dependent,
  non-monotone reader (proper reaching definitions with kill) needs: a
  reader-inclusion premise like \<open>READER_INCL\<close> can fail across a call that overwrites
  a global, but the read at a local variable never depends on the global slots.
\<close>

lemma combine_read_obs_le_bot:
  fixes sigma :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
  assumes LOCAL_POST: "\<And>x. \<not> is_global x \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
  assumes GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
  assumes CMP_SOUND:
    "\<And>x. is_global x \<Longrightarrow> obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> obs_digest sigma (v, ctx) x"
  shows "combine_read_obs sigma rt cl ex ctx \<le> obs_digest sigma (v, ctx)"
proof (rule le_funI)
  fix x
  have lb1: "local_bot_on_locals (glob_env_cmp (\<lambda>_ g. compatible (reader_digest cl ctx) g) ctx sigma)"
    by (rule glob_env_cmp_local_bot) (rule GLOB_BOT)
  have lb2: "local_bot_on_locals (glob_env_cmp (\<lambda>_ g. compatible (reader_digest v ctx) g) ctx sigma)"
    by (rule glob_env_cmp_local_bot) (rule GLOB_BOT)
  show "combine_read_obs sigma rt cl ex ctx x \<le> obs_digest sigma (v, ctx) x"
  proof (cases "is_global x")
    case True
    thus ?thesis
      unfolding combine_read_obs_def combine_abs_def using CMP_SOUND[OF True] by simp
  next
    case False
    have b1: "glob_env_cmp (\<lambda>_ g. compatible (reader_digest cl ctx) g) ctx sigma x = bot"
      using lb1 False unfolding local_bot_on_locals_def by blast
    have b2: "glob_env_cmp (\<lambda>_ g. compatible (reader_digest v ctx) g) ctx sigma x = bot"
      using lb2 False unfolding local_bot_on_locals_def by blast
    show ?thesis
      unfolding combine_read_obs_def combine_abs_def obs_digest_def
      using False LOCAL_POST[OF False] b1 b2 by simp
  qed
qed

text \<open>
  Trace soundness with the \<open>bot\<close>-on-locals invariant \<open>GLOB_BOT\<close> in place of
  \<open>READER_INCL\<close>: the reader digest is unconstrained, so this is the variant a
  non-monotone (kill) reader instantiates.
\<close>
theorem post_fixpoint_sound_obs_digest_final_bot:
  fixes sigma :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> obs_digest sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>obs_digest sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
proof (rule post_fixpoint_sound_obs_digest
        [where rt = rt and dg = dg and cmp = cmp and entdg = entdg])
  fix ctx cl ex v' tau rho
  assume comb: "(cl, ex, v') \<in> combines g"
    and cr: "last tau \<in> \<lbrakk>obs_digest sigma (cl, ctx)\<rbrakk>"
    and ce: "last rho \<in> \<lbrakk>obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx))))\<rbrakk>"
  have bound: "combine_read_obs sigma rt cl ex ctx \<le> obs_digest sigma (v', ctx)"
  proof (rule combine_read_obs_le_bot)
    fix x assume "\<not> is_global x"
    thus "sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v', ctx)) x" by (rule LOCAL_POST[OF comb])
  next
    fix gk show "local_bot_on_locals (sigma (Inr gk))" by (rule GLOB_BOT)
  next
    fix x assume "is_global x"
    thus "obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> obs_digest sigma (v', ctx) x"
      by (rule CMP_SOUND[OF comb])
  qed
  show "<last tau|last rho> \<in> \<lbrakk>obs_digest sigma (v', ctx)\<rbrakk>"
    by (rule combine_case_obs_sound[OF cr ce bound])
qed (fact ENTRY PROC_ENTRY EDGE DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO wit compat)+

text \<open>Context-sliced collecting soundness, \<open>bot\<close>-on-locals variant (unconstrained reader).\<close>
theorem obs_digest_collect_ctx_sound_bot:
  fixes sigma :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> obs_digest sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>obs_digest sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
proof -
  have trace_sound:
    "\<And>tr. trace_witness g S v tr \<Longrightarrow> cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
  proof -
    fix tr assume w: "trace_witness g S v tr" and c: "cmp (dg tr) ctx"
    show "last tr \<in> \<lbrakk>obs_digest sigma (v, ctx)\<rbrakk>"
      by (rule post_fixpoint_sound_obs_digest_final_bot
            [where rt = rt and dg = dg and cmp = cmp and entdg = entdg,
             OF ENTRY PROC_ENTRY EDGE LOCAL_POST GLOB_BOT CMP_SOUND
                DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO w c])
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using trace_sound by auto
qed

end

section \<open>Degenerate instance: faithful subsumption of the context-only read\<close>

text \<open>
  The context-only read \<^const>\<open>side_env_cmp\<close> is the instance of the interface whose
  reader digest is the context itself and whose compatibility is the context/key
  relation.  Instantiating \<^const>\<open>digest_global_read.obs_digest\<close> with
  \<open>reader_digest = (\<lambda>v ctx. ctx)\<close> and \<open>compatible = gcmp\<close> collapses it to
  \<^const>\<open>side_env_cmp\<close> pointwise, so the generic collecting theorem re-derives the
  keyed collecting soundness with no residual obligation: the point-independent
  reader makes the extra \<open>READER_INCL\<close> premise trivially reflexive.  This certifies
  the interface strictly generalises the existing spine (it is not a weaker or
  differently-shaped statement).
\<close>

lemma obs_digest_ctx_reader_eq:
  "digest_global_read.obs_digest (\<lambda>v ctx. ctx) gcmp \<sigma> (v, ctx) = side_env_cmp gcmp \<sigma> (v, ctx)"
  by (rule digest_global_read.obs_digest_collapse_shape) simp

text \<open>
  The keyed collecting soundness \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>
  re-derived from the generic \<open>digest_global_read.obs_digest_collect_ctx_sound\<close>
  through the context-reader instance.  \<open>READER_INCL\<close> is discharged by reflexivity
  (the ctx reader ignores the point), the reads collapse by
  \<open>obs_digest_ctx_reader_eq\<close>, and the routing read \<^const>\<open>route_read_cmp\<close> is the
  same plain local slot.
\<close>
theorem obs_digest_recovers_cmp_collect:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (route_read_cmp sigma (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
proof -
  have R: "\<And>v ctx. digest_global_read.obs_digest (\<lambda>v ctx. ctx) gcmp sigma (v, ctx)
                   = side_env_cmp gcmp sigma (v, ctx)"
    by (rule obs_digest_ctx_reader_eq)
  show ?thesis
    unfolding route_read_cmp_def
    apply (subst R[symmetric])
    apply (rule digest_global_read.obs_digest_collect_ctx_sound
             [where reader_digest = "\<lambda>v ctx. ctx" and compatible = gcmp
                and rt = rt and entdg = entdg and dg = dg and cmp = cmp])
    subgoal using ENTRY by (simp add: R)
    subgoal using PROC_ENTRY by (simp add: R)
    subgoal using EDGE by (simp add: R)
    subgoal using LOCAL_POST by simp
    subgoal by simp
    subgoal using CMP_SOUND by (simp add: R route_read_cmp_def)
    subgoal using DG_INTRA by simp
    subgoal using DG_RETURN by simp
    subgoal using DG_CALLEE by simp
    subgoal using ENTER_MONO by (simp add: R route_read_cmp_def)
    done
qed

section \<open>Reaching-definitions instance (scaffold)\<close>

text \<open>
  The reaching-definitions reader.  A global write is tagged by its def-site --- an
  abstract finite key \<^typ>\<open>'g\<close>, of which \<open>def_site\<close> is a concrete witness --- and
  the reader at a point joins exactly the def-sites reaching it.  This is the
  \<^locale>\<open>digest_global_read\<close> instance with \<open>reader_digest = reach\<close> (the reaching set
  \<open>reach pp ctx\<close> at a point) and \<open>compatible d g = (g \<in> d)\<close>.

  The kernel \<open>READER_INCL\<close> premise then reduces to the interprocedural \<^emph>\<open>return
  inclusion\<close> \<open>reach cl ctx \<subseteq> reach v ctx\<close> (\<open>rd_reader_incl_iff\<close>): the caller node's
  reaching set is contained in the return node's.  That inclusion is the sole
  genuinely-new, \<open>sigma\<close>-independent per-instance obligation --- a pure reaching-def
  dataflow fact, not a solution property.  \<open>CMP_SOUND\<close> (read soundness at the
  def-site-keyed globals) stays a post-solution assumption, dischargeable only once
  the generator keys writers by def-site (the writer re-keying step).
\<close>

datatype def_site = DS1 | DS3

instance def_site :: finite
proof
  have "(UNIV :: def_site set) \<subseteq> {DS1, DS3}" using def_site.exhaust by auto
  thus "finite (UNIV :: def_site set)" by (simp add: finite_subset)
qed

text \<open>An \<^class>\<open>enum\<close> instance so the def-site-filtered read \<^const>\<open>glob_env_cmp\<close>
  code-generates (its filtered join folds over the finite key type).\<close>
instantiation def_site :: enum
begin
definition "enum_def_site = [DS1, DS3]"
definition "enum_all_def_site P \<longleftrightarrow> P DS1 \<and> P DS3"
definition "enum_ex_def_site P \<longleftrightarrow> P DS1 \<or> P DS3"
instance
proof
  show "(UNIV :: def_site set) = set enum_class.enum"
    using def_site.exhaust by (auto simp: enum_def_site_def)
qed (auto simp: enum_def_site_def enum_all_def_site_def enum_ex_def_site_def,
     (metis def_site.exhaust)+)
end

definition rd_compatible :: "'g set \<Rightarrow> 'g \<Rightarrow> bool" where
  "rd_compatible d g \<longleftrightarrow> g \<in> d"

lemma rd_compatible_set: "{g. rd_compatible d g} = d"
  by (auto simp: rd_compatible_def)

abbreviation rd_obs ::
  "(pp \<Rightarrow> 'c \<Rightarrow> 'g::finite set)
   \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
where
  "rd_obs reach \<equiv> digest_global_read.obs_digest reach rd_compatible"

text \<open>
  \<open>READER_INCL\<close> for the RD reader is exactly the reaching-def return inclusion: the
  membership compatibility turns the compatible-key set into the reaching set itself.
\<close>
lemma rd_reader_incl_iff:
  "({g. rd_compatible (reach cl ctx) g} \<subseteq> {g. rd_compatible (reach v ctx) g})
     = (reach cl ctx \<subseteq> reach v ctx)"
  by (simp add: rd_compatible_set)

text \<open>Witness at the concrete \<^typ>\<open>def_site\<close> key: the reduction holds unchanged.\<close>
lemma rd_reader_incl_def_site:
  fixes reach :: "pp \<Rightarrow> 'c \<Rightarrow> def_site set"
  shows "({g. rd_compatible (reach cl ctx) g} \<subseteq> {g. rd_compatible (reach v ctx) g})
           = (reach cl ctx \<subseteq> reach v ctx)"
  by (rule rd_reader_incl_iff)

text \<open>
  Generic \<open>CMP_SOUND\<close> at a global variable.  At a global \<open>x\<close> the local slot summand
  of \<^const>\<open>digest_global_read.obs_digest\<close> is \<open>bot\<close> (structural \<open>inl_slot_globals_bot\<close>
  invariant), so the read collapses to the \<^const>\<open>rd_compatible\<close>-filtered global join.
  The routed callee-exit read is then below the return read by pure filter
  monotonicity, driven only by the reaching-set inclusion \<open>reach ex ctx2 \<subseteq> reach v ctx1\<close>.
  This turns \<open>CMP_SOUND\<close> from a per-solution hand obligation into a dataflow fact
  (reach inclusion) plus the bot-on-globals invariant --- it does not depend on the
  solved solution.
\<close>
lemma rd_obs_cmp_sound_from_incl:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes INCL: "reach ex ctx2 \<subseteq> reach v ctx1"
    and INL_BOT: "\<And>p. is_global x \<Longrightarrow> sigma (Inl p) x = bot"
    and GLOB: "is_global x"
  shows "rd_obs reach sigma (ex, ctx2) x \<le> rd_obs reach sigma (v, ctx1) x"
proof -
  have L: "rd_obs reach sigma (ex, ctx2) x
             = glob_env_cmp (\<lambda>_ g. rd_compatible (reach ex ctx2) g) ctx2 sigma x"
    unfolding digest_global_read.obs_digest_def
    using INL_BOT[OF GLOB] by (simp add: sup_apply)
  have R: "rd_obs reach sigma (v, ctx1) x
             = glob_env_cmp (\<lambda>_ g. rd_compatible (reach v ctx1) g) ctx1 sigma x"
    unfolding digest_global_read.obs_digest_def
    using INL_BOT[OF GLOB] by (simp add: sup_apply)
  have "glob_env_cmp (\<lambda>_ g. rd_compatible (reach ex ctx2) g) ctx2 sigma
          \<le> glob_env_cmp (\<lambda>_ g. rd_compatible (reach v ctx1) g) ctx1 sigma"
    by (rule digest_global_read.glob_env_cmp_filter_mono) (simp add: rd_compatible_set INCL)
  thus ?thesis unfolding L R by (rule le_funD)
qed

text \<open>
  Context-sliced collecting soundness for the RD reader: the generic
  \<open>obs_digest_collect_ctx_sound\<close> with the \<open>READER_INCL\<close> premise replaced by the
  reaching-def return inclusion \<open>RD_RETURN_INCL\<close>.  \<open>CMP_SOUND\<close> is retained verbatim
  as the post-solution obligation the def-site generator must discharge.

  \<^bold>\<open>Caveat.\<close>  \<open>RD_RETURN_INCL\<close> (\<open>reach cl ctx \<subseteq> reach v ctx\<close>) holds only for a
  \<^emph>\<open>monotone\<close> (may-def, kill-free) reader: proper reaching definitions with kill
  can drop a caller's def at a return that must-overwrites the global, so the caller
  read is \<^emph>\<open>not\<close> included in the return read.  The kill-compatible instance is
  \<open>reaching_def_collect_sound_bot\<close> below, which discharges the local case from the
  \<open>bot\<close>-on-locals invariant and leaves \<open>reach\<close> unconstrained.
\<close>
theorem reaching_def_collect_sound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and reach :: "pp \<Rightarrow> 'c \<Rightarrow> 'g set"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs reach sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and RD_RETURN_INCL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g \<Longrightarrow> reach cl ctx \<subseteq> reach v ctx"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> rd_obs reach sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
              \<le> rd_obs reach sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs reach sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
  apply (rule digest_global_read.obs_digest_collect_ctx_sound
           [where reader_digest = reach and compatible = rd_compatible
              and rt = rt and entdg = entdg and dg = dg and cmp = cmp])
  subgoal using ENTRY by blast
  subgoal using PROC_ENTRY by blast
  subgoal using EDGE by blast
  subgoal using LOCAL_POST by blast
  subgoal using RD_RETURN_INCL by (simp add: rd_reader_incl_iff)
  subgoal using CMP_SOUND by blast
  subgoal using DG_INTRA by blast
  subgoal using DG_RETURN by blast
  subgoal using DG_CALLEE by blast
  subgoal using ENTER_MONO by blast
  done

text \<open>
  Necessity of the \<open>bot\<close>-on-locals route, machine-checked at the concrete
  \<^type>\<open>def_site\<close> key.  A proper reaching-definition combine that \<^bold>\<open>kills\<close> the
  caller's definition \<open>DS1\<close> and \<^bold>\<open>gens\<close> a fresh \<open>DS3\<close> at the return yields a \<open>reach\<close>
  whose caller set is not contained in the return set.  That is exactly the negation
  of \<open>RD_RETURN_INCL\<close>, the premise \<open>reaching_def_collect_sound\<close> carries and
  \<open>reaching_def_collect_sound_bot\<close> drops.  So the two routes are not interchangeable:
  kill forces the \<open>bot\<close> variant.
\<close>
lemma rd_kill_refutes_return_incl:
  fixes cl v :: pp and ctx :: 'c
  defines "reach_kill \<equiv> (\<lambda>p (c::'c). if p = cl then {DS1} else {DS3})"
  assumes "cl \<noteq> v"
  shows "\<not> reach_kill cl ctx \<subseteq> reach_kill v ctx"
  using assms unfolding reach_kill_def by simp

text \<open>
  The kill-compatible RD instance: the \<open>bot\<close>-on-locals variant with \<open>reach\<close> left
  \<^emph>\<open>entirely unconstrained\<close>.  Proper reaching definitions (with interprocedural
  kill/gen) instantiate \<open>reach\<close> here; the only per-instance obligations are
  \<open>GLOB_BOT\<close> (the \<open>inr_slot_locals_bot\<close> solution invariant, program-independent) and
  \<open>CMP_SOUND\<close> (read soundness at the def-site-keyed globals, discharged once the
  generator keys writers by def-site).  No reaching-def inclusion is required.
\<close>
theorem reaching_def_collect_sound_bot:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and reach :: "pp \<Rightarrow> 'c \<Rightarrow> 'g set"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs reach sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
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
  apply (rule digest_global_read.obs_digest_collect_ctx_sound_bot
           [where reader_digest = reach and compatible = rd_compatible
              and rt = rt and entdg = entdg and dg = dg and cmp = cmp])
  subgoal using ENTRY by blast
  subgoal using PROC_ENTRY by blast
  subgoal using EDGE by blast
  subgoal using LOCAL_POST by blast
  subgoal using GLOB_BOT by blast
  subgoal using CMP_SOUND by blast
  subgoal using DG_INTRA by blast
  subgoal using DG_RETURN by blast
  subgoal using DG_CALLEE by blast
  subgoal using ENTER_MONO by blast
  done

text \<open>
  The generic kill-compatible RD instance: \<open>reaching_def_collect_sound_bot\<close> with the
  per-solution \<open>CMP_SOUND\<close> obligation replaced by two structural/dataflow facts, so no
  hand discharge of read soundness is required per generator solution.

  \<^item> \<open>INL_GLOB_BOT\<close> --- Inl (local-unknown) slots carry \<open>bot\<close> at every global variable
    (the \<open>inl_slot_globals_bot\<close> post-solution invariant).
  \<^item> \<open>CALLEE_INCL\<close> --- the callee-exit reaching set at the routed context is included in
    the return-node reaching set (a pure dataflow fact about \<open>reach\<close>).

  \<open>CMP_SOUND\<close> then follows pointwise at every global by \<open>rd_obs_cmp_sound_from_incl\<close>:
  the local summand vanishes (\<open>INL_GLOB_BOT\<close>) and filter monotonicity carries the
  global join (\<open>CALLEE_INCL\<close>).  Unlike \<open>RD_RETURN_INCL\<close> in \<open>reaching_def_collect_sound\<close>,
  this needs no monotone (kill-free) reader --- the local case still rides the
  \<open>bot\<close>-on-locals route.
\<close>
theorem reaching_def_collect_sound_bot_incl:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and reach :: "pp \<Rightarrow> 'c \<Rightarrow> 'g set"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs reach sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>rd_obs reach sigma (v, ctx)\<rbrakk>"
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
    apply (rule reaching_def_collect_sound_bot
             [where sigma = sigma and reach = reach and rt = rt and dg = dg
                and cmp = cmp and entdg = entdg])
    subgoal using ENTRY by blast
    subgoal using PROC_ENTRY by blast
    subgoal using EDGE by blast
    subgoal using LOCAL_POST by blast
    subgoal using GLOB_BOT by blast
    subgoal using CMP_SOUND by blast
    subgoal using DG_INTRA by blast
    subgoal using DG_RETURN by blast
    subgoal using DG_CALLEE by blast
    subgoal using ENTER_MONO by blast
    done
qed

subsection \<open>Semantic reader (B2): reaching-compatible def-site union\<close>

text \<open>
  The B2 obligation is that a sound reader admits every def-site that may reach the
  point.  Realise \<open>reach\<close> concretely as the union of the per-trace live def-sites
  \<open>rd_of\<close> over the digest-compatible reaching traces --- the tightest sound reader.
  The per-trace def-site map \<open>rd_of\<close> stays abstract here; tagging it to concrete CFG
  assignments is a later slice.  \<open>dg\<close> / \<open>cmp\<close> are the same context digest the
  collecting semantics filters on, so the reader's compatible-trace set is exactly
  \<open>reaching_compat\<close>.
\<close>
definition reach_sem ::
  "(trace \<Rightarrow> 'g set) \<Rightarrow> (trace \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'g set"
where
  "reach_sem rd_of dg cmp g S v ctx = \<Union> (rd_of ` reaching_compat dg cmp ctx g S v)"

text \<open>Soundness by construction: the reader admits every reaching-compatible trace's
  live def-sites.\<close>
lemma reach_sem_admits:
  "tr \<in> reaching_compat dg cmp ctx g S v \<Longrightarrow> rd_of tr \<subseteq> reach_sem rd_of dg cmp g S v ctx"
  unfolding reach_sem_def by blast

text \<open>May-def return inclusion reduces to a per-combine no-kill condition: every
  caller-node reaching trace extends to a return-node reaching trace whose live
  def-sites are a superset.  (Proper kill breaks this --- see
  \<open>rd_kill_refutes_return_incl\<close> --- and is handled by the \<open>bot\<close>-on-locals route.)\<close>
lemma reach_sem_return_incl:
  assumes NOKILL: "\<And>tr. tr \<in> reaching_compat dg cmp ctx g S cl
        \<Longrightarrow> \<exists>tr'. tr' \<in> reaching_compat dg cmp ctx g S v \<and> rd_of tr \<subseteq> rd_of tr'"
  shows "reach_sem rd_of dg cmp g S cl ctx \<subseteq> reach_sem rd_of dg cmp g S v ctx"
proof
  fix d assume "d \<in> reach_sem rd_of dg cmp g S cl ctx"
  then obtain tr where tr: "tr \<in> reaching_compat dg cmp ctx g S cl" and d: "d \<in> rd_of tr"
    unfolding reach_sem_def by blast
  from NOKILL[OF tr] obtain tr'
    where tr': "tr' \<in> reaching_compat dg cmp ctx g S v" and sub: "rd_of tr \<subseteq> rd_of tr'"
    by blast
  have "rd_of tr' \<subseteq> reach_sem rd_of dg cmp g S v ctx" using tr' by (rule reach_sem_admits)
  thus "d \<in> reach_sem rd_of dg cmp g S v ctx" using d sub by blast
qed

text \<open>
  Structural discharge of the no-kill condition through the actual combine trace.
  A caller trace \<open>tau\<close> reaching \<open>cl\<close> extends to the return trace
  \<open>tau @ tl rho @ [<last tau|last rho>]\<close> reaching \<open>v\<close> (\<open>trace_witness_combineI\<close>); its
  context digest equals \<open>dg tau\<close> (\<open>DG_RETURN\<close>), so a \<^emph>\<open>compatible\<close> caller trace stays
  compatible at the return.  The whole no-kill content collapses to the local
  per-combine fact \<open>CALLEE\<close>: a callee run reaching \<open>ex\<close> from the caller's last store
  exists and \<^emph>\<open>preserves\<close> the caller's live def-sites (\<open>rd_of\<close> does not shrink across
  the return construction).  Proper must-kill breaks that \<open>rd_of\<close> inclusion, routing
  such combines to the \<open>bot\<close>-on-locals theorem instead.
\<close>
lemma reach_sem_NOKILL_via_combine:
  assumes comb: "(cl, ex, v) \<in> combines g"
  assumes DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  assumes CALLEE: "\<And>tau. tau \<in> reaching_compat dg cmp ctx g S cl
      \<Longrightarrow> \<exists>rho. trace_witness g S ex rho \<and> hd rho = enter_state (last tau)
            \<and> rd_of tau \<subseteq> rd_of (tau @ tl rho @ [<last tau|last rho>])"
  assumes tau: "tau \<in> reaching_compat dg cmp ctx g S cl"
  shows "\<exists>tr'. tr' \<in> reaching_compat dg cmp ctx g S v \<and> rd_of tau \<subseteq> rd_of tr'"
proof -
  from tau have tw_cl: "trace_witness g S cl tau" and compat: "cmp (dg tau) ctx"
    unfolding reaching_compat_def cfg_collect_trace_def by auto
  have tau_ne: "tau \<noteq> []" using tw_cl by (rule trace_witness_nonempty)
  from CALLEE[OF tau] obtain rho where
    tw_ex: "trace_witness g S ex rho" and enter: "hd rho = enter_state (last tau)"
    and rd_sub: "rd_of tau \<subseteq> rd_of (tau @ tl rho @ [<last tau|last rho>])" by blast
  define tr' where "tr' = tau @ tl rho @ [<last tau|last rho>]"
  have tw_v: "trace_witness g S v tr'"
    unfolding tr'_def using comb tw_cl tw_ex enter by (rule trace_witness_combineI) simp
  have dg_eq: "dg tr' = dg tau" unfolding tr'_def using tau_ne by (rule DG_RETURN)
  have "tr' \<in> cfg_collect_trace g S v" unfolding cfg_collect_trace_def using tw_v by simp
  moreover have "cmp (dg tr') ctx" using dg_eq compat by simp
  ultimately have "tr' \<in> reaching_compat dg cmp ctx g S v" unfolding reaching_compat_def by simp
  moreover have "rd_of tau \<subseteq> rd_of tr'" unfolding tr'_def using rd_sub by simp
  ultimately show ?thesis by blast
qed

text \<open>
  End-to-end RD collecting soundness with the \<^emph>\<open>concretely defined\<close> semantic reader
  \<open>reach_sem\<close>.  The abstract reaching-def obligation of \<open>reaching_def_collect_sound\<close>
  (\<open>RD_RETURN_INCL\<close>) is replaced by the per-combine trace-extension condition
  \<open>NOKILL\<close>, discharged through \<open>reach_sem_return_incl\<close>.  The remaining premises are the
  read-agnostic backbone plus \<open>CMP_SOUND\<close> --- the sole post-solution residue for the
  def-site-keyed generator.
\<close>
theorem reaching_def_collect_sound_sem:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and rd_of :: "trace \<Rightarrow> 'g set"
    and dg :: "trace \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and NOKILL: "\<And>ctx cl ex v tr. (cl, ex, v) \<in> combines g \<Longrightarrow> tr \<in> reaching_compat dg cmp ctx g S cl
        \<Longrightarrow> \<exists>tr'. tr' \<in> reaching_compat dg cmp ctx g S v \<and> rd_of tr \<subseteq> rd_of tr'"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> rd_obs (reach_sem rd_of dg cmp g S) sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x
              \<le> rd_obs (reach_sem rd_of dg cmp g S) sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>rd_obs (reach_sem rd_of dg cmp g S) sigma (v, ctx)\<rbrakk>"
  apply (rule reaching_def_collect_sound
           [where reach = "reach_sem rd_of dg cmp g S" and rt = rt and entdg = entdg and dg = dg and cmp = cmp])
  subgoal using ENTRY by blast
  subgoal using PROC_ENTRY by blast
  subgoal using EDGE by blast
  subgoal using LOCAL_POST by blast
  subgoal premises p for ctx cl ex v by (rule reach_sem_return_incl) (rule NOKILL[OF p(1)])
  subgoal using CMP_SOUND by blast
  subgoal using DG_INTRA by blast
  subgoal using DG_RETURN by blast
  subgoal using DG_CALLEE by blast
  subgoal using ENTER_MONO by blast
  done

end
