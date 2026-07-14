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

text \<open>
  Superset-reader monotone bridge: when the reader admits at least the
  context-compatible keys, the digest read dominates the context-only read
  \<^const>\<open>side_env_cmp\<close> pointwise.  Local slots coincide; the global part is
  \<open>glob_env_cmp_filter_mono\<close>.  This lets a superset reader inherit the
  \<^const>\<open>side_env_cmp\<close> collecting soundness (seed / edge) through
  \<open>gamma_state_mono\<close> --- no per-edge argument at \<^const>\<open>obs_digest\<close> is needed for
  such readers, only the already-discharged one at \<^const>\<open>side_env_cmp\<close>.
\<close>
lemma side_env_cmp_le_obs_digest:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes "{k. gcmp ctx k} \<subseteq> {k. compatible (reader_digest v ctx) k}"
  shows "side_env_cmp gcmp \<sigma> (v, ctx) \<le> obs_digest \<sigma> (v, ctx)"
proof -
  have H: "glob_env_cmp gcmp ctx \<sigma>
             \<le> glob_env_cmp (\<lambda>_ g. compatible (reader_digest v ctx) g) ctx \<sigma>"
    by (rule glob_env_cmp_filter_mono) (use assms in auto)
  show ?thesis
    unfolding side_env_cmp_def obs_digest_def fst_conv snd_conv
    by (rule sup_mono[OF order_refl H])
qed

text \<open>
  Payoff of the bridge: for a superset reader (\<open>admits\<close>) the context-sliced
  collecting bound at \<^const>\<open>obs_digest\<close> follows from the one at
  \<^const>\<open>side_env_cmp\<close> by \<open>gamma_state_mono\<close> --- the seed / edge / combine premises
  are discharged once at the context read and inherited, never restated at the
  digest read.  The context-collapse reader (\<open>reader_digest = (\<lambda>v ctx. ctx)\<close>) is
  the reflexive case.
\<close>
lemma obs_digest_collect_ctx_sound_of_cmp:
  fixes \<sigma> :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a::sound_domain abs_state"
  assumes admits: "{k. gcmp ctx k} \<subseteq> {k. compatible (reader_digest v ctx) k}"
  assumes cmp_bound: "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp \<sigma> (v, ctx)\<rbrakk>"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
proof (rule order_trans[OF cmp_bound])
  have "side_env_cmp gcmp \<sigma> (v, ctx) \<le> obs_digest \<sigma> (v, ctx)"
    using admits by (rule side_env_cmp_le_obs_digest)
  thus "\<lbrakk>side_env_cmp gcmp \<sigma> (v, ctx)\<rbrakk> \<le> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    by (rule gamma_state_mono)
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

subsection \<open>Context-sliced collecting soundness\<close>

text \<open>
  Instantiating the canonical backbone \<open>collect_ctx_sound_meaning\<close> at meaning
  \<open>[[obs_digest \<sigma> (p, c)]]\<close>, with the plain local slot as the routing read, lifts it to
  the context-sliced collecting set \<^const>\<open>cfg_collect_ctx\<close>: every store reaching \<open>v\<close>
  along a trace whose digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> is covered by the digest
  read \<^const>\<open>obs_digest\<close> at \<open>(v, ctx)\<close>.  The digest sibling of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>.
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
  \<comment> \<open>A digest-read instance of the canonical backbone \<open>collect_ctx_sound_meaning\<close>: meaning
      \<open>[[obs_digest \<sigma> (p, c)]]\<close>, routing read the plain local slot.  The switching combine
      discharges through \<open>combine_read_obs_le\<close> + \<open>combine_case_obs_sound\<close> as before.\<close>
proof -
  have "cfg_collect_ctx dg cmp g S v ctx \<subseteq> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (v, ctx)"
  proof (rule collect_ctx_sound_meaning
      [where M = "\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>" and rd = "\<lambda>(p, c). \<sigma> (Inl (p, c))"
         and rt = rt and entdg = entdg and dg = dg and cmp = cmp and S = S and g = g])
    show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (cfg_entry g, ctx)"
      using ENTRY by simp
  next
    show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (v, ctx)"
      using PROC_ENTRY by simp
  next
    show "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
            \<Longrightarrow> last tr \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (u, ctx)
            \<Longrightarrow> s' \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (v, ctx)"
      using EDGE by simp
  next
    fix ctx cl ex v' tau rho
    assume c: "(cl, ex, v') \<in> combines g"
      and caller0: "last tau \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (cl, ctx)"
      and callee0: "last rho \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>)
                      (ex, rt cl ctx ((\<lambda>(p, c). \<sigma> (Inl (p, c))) (cl, ctx)))"
    from caller0 have ct: "last tau \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>" by simp
    from callee0 have ce: "last rho \<in> \<lbrakk>obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx))))\<rbrakk>" by simp
    have bound: "combine_read_obs \<sigma> rt cl ex ctx \<le> obs_digest \<sigma> (v', ctx)"
    proof (rule combine_read_obs_le)
      fix x assume "\<not> is_global x"
      thus "\<sigma> (Inl (cl, ctx)) x \<le> \<sigma> (Inl (v', ctx)) x" by (rule LOCAL_POST[OF c])
    next
      show "{g. compatible (reader_digest cl ctx) g} \<subseteq> {g. compatible (reader_digest v' ctx) g}"
        by (rule READER_INCL[OF c])
    next
      fix x assume "is_global x"
      thus "obs_digest \<sigma> (ex, rt cl ctx (\<sigma> (Inl (cl, ctx)))) x \<le> obs_digest \<sigma> (v', ctx) x"
        by (rule CMP_SOUND[OF c])
    qed
    have "<last tau|last rho> \<in> \<lbrakk>obs_digest \<sigma> (v', ctx)\<rbrakk>"
      by (rule combine_case_obs_sound[OF ct ce bound])
    thus "<last tau|last rho> \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (v', ctx)" by simp
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
    assume "s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest \<sigma> (p, c)\<rbrakk>) (cl, ctx)"
    hence "s \<in> \<lbrakk>obs_digest \<sigma> (cl, ctx)\<rbrakk>" by simp
    thus "cmp (entdg s) (rt cl ctx ((\<lambda>(p, c). \<sigma> (Inl (p, c))) (cl, ctx)))"
      using ENTER_MONO by simp
  qed
  thus ?thesis by simp
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
  \<comment> \<open>The \<open>bot\<close>-on-locals variant, likewise a backbone instance; the combine bound is
      \<open>combine_read_obs_le_bot\<close> instead of \<open>combine_read_obs_le\<close>.\<close>
proof -
  have "cfg_collect_ctx dg cmp g S v ctx \<subseteq> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (v, ctx)"
  proof (rule collect_ctx_sound_meaning
      [where M = "\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>" and rd = "\<lambda>(p, c). sigma (Inl (p, c))"
         and rt = rt and entdg = entdg and dg = dg and cmp = cmp and S = S and g = g])
    show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (cfg_entry g, ctx)"
      using ENTRY by simp
  next
    show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (v, ctx)"
      using PROC_ENTRY by simp
  next
    show "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
            \<Longrightarrow> last tr \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (u, ctx)
            \<Longrightarrow> s' \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (v, ctx)"
      using EDGE by simp
  next
    fix ctx cl ex v' tau rho
    assume c: "(cl, ex, v') \<in> combines g"
      and caller0: "last tau \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (cl, ctx)"
      and callee0: "last rho \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>)
                      (ex, rt cl ctx ((\<lambda>(p, c). sigma (Inl (p, c))) (cl, ctx)))"
    from caller0 have ct: "last tau \<in> \<lbrakk>obs_digest sigma (cl, ctx)\<rbrakk>" by simp
    from callee0 have ce: "last rho \<in> \<lbrakk>obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx))))\<rbrakk>" by simp
    have bound: "combine_read_obs sigma rt cl ex ctx \<le> obs_digest sigma (v', ctx)"
    proof (rule combine_read_obs_le_bot)
      fix x assume "\<not> is_global x"
      thus "sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v', ctx)) x" by (rule LOCAL_POST[OF c])
    next
      fix gk show "local_bot_on_locals (sigma (Inr gk))" by (rule GLOB_BOT)
    next
      fix x assume "is_global x"
      thus "obs_digest sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) x \<le> obs_digest sigma (v', ctx) x"
        by (rule CMP_SOUND[OF c])
    qed
    have "<last tau|last rho> \<in> \<lbrakk>obs_digest sigma (v', ctx)\<rbrakk>"
      by (rule combine_case_obs_sound[OF ct ce bound])
    thus "<last tau|last rho> \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (v', ctx)" by simp
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
    assume "s \<in> (\<lambda>(p, c). \<lbrakk>obs_digest sigma (p, c)\<rbrakk>) (cl, ctx)"
    hence "s \<in> \<lbrakk>obs_digest sigma (cl, ctx)\<rbrakk>" by simp
    thus "cmp (entdg s) (rt cl ctx ((\<lambda>(p, c). sigma (Inl (p, c))) (cl, ctx)))"
      using ENTER_MONO by simp
  qed
  thus ?thesis by simp
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


end
