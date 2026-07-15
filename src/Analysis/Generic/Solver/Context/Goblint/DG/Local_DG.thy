theory Local_DG
  imports DG_Route_Soundness
begin

section \<open>Local-only DG adapter: the clean single-domain analysis as a DG instance\<close>

text \<open>
  The clean (sequential-faithful, R_read) analysis reads only the local slot and
  imposes no flow-insensitive global fact.  It is therefore a \<^emph>\<open>degenerate\<close> DG
  analysis: the Answer domain \<open>D\<close> is the existing local abstract state, and the Side
  domain \<open>G\<close> is the trivial one-element type \<^typ>\<open>unit\<close>, whose concretization is the
  whole store space.  \<open>local_gamma d () = [[d]]\<close> ignores \<open>G\<close> entirely, so the
  \<^locale>\<open>sound_dg_spec\<close> global obligations discharge automatically and \<^emph>\<open>no global
  machinery is exposed to clients\<close>: every proof obligation of \<open>dg_collect_ctx_sound\<close>
  at this instance is a fact about \<open>[[dg_D_c sigma ctx v]] = [[local slot]]\<close>, with the
  \<open>unit\<close> Side component never appearing.

  This makes the clean context-sliced theorem \<open>clean_ctx_collect_rread\<close> a direct
  corollary of the DG endpoint (\<open>clean_ctx_collect_rread_via_dg\<close> below), with the same
  premises, the same conclusion, and no unused \<open>G\<close> plumbing --- the single-framework
  end state, with the single-domain analysis a lightweight local-only DG instance
  rather than an independent proof foundation.
\<close>

subsection \<open>The adapter spec and its concretization\<close>

definition local_dg_spec ::
  "'a::sound_domain domain_transfer \<Rightarrow> ('a abs_state, unit) dg_spec"
where
  "local_dg_spec tf = \<lparr>
     dgs_nop        = (\<lambda>d _. ((), apply_tf tf EA_Nop d)),
     dgs_assign     = (\<lambda>x e d _. ((), apply_tf tf (EA_Assign x e) d)),
     dgs_assume     = (\<lambda>b d _. ((), apply_tf tf (EA_Assume b) d)),
     dgs_assume_not = (\<lambda>b d _. ((), apply_tf tf (EA_AssumeNot b) d)),
     dgs_enter      = (\<lambda>xs es d _. ((), apply_tf tf (EA_Enter xs es) d)),
     dgs_combine    = (\<lambda>dst dc de _. ((), combine_collect_abs dst dc de)) \<rparr>"

definition local_gamma :: "'a::sound_domain abs_state \<Rightarrow> unit \<Rightarrow> store set" where
  "local_gamma d u = \<lbrakk>d\<rbrakk>"

lemma dg_spec_step_local:
  "dg_spec_step (local_dg_spec tf) a d g = ((), apply_tf tf a d)"
  unfolding local_dg_spec_def by (cases a) simp_all

lemma dgs_combine_local:
  "dgs_combine (local_dg_spec tf) dst dc de g = ((), combine_collect_abs dst dc de)"
  unfolding local_dg_spec_def by simp

lemma local_gamma_mono:
  "d \<le> d' \<Longrightarrow> local_gamma d g \<subseteq> local_gamma d' g'"
  unfolding local_gamma_def by (rule gamma_state_mono)

lemma sound_dg_spec_local:
  assumes sound: "sound_transfer tf"
  shows "sound_dg_spec (local_dg_spec tf) local_gamma"
proof unfold_locales
  fix d d' :: "'a abs_state" and g g' :: unit
  assume "d \<le> d'"
  thus "local_gamma d g \<subseteq> local_gamma d' g'" by (rule local_gamma_mono)
next
  fix a and d :: "'a abs_state" and g :: unit
  have "edge_collect a \<lbrakk>d\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a d\<rbrakk>"
    by (rule sound_transfer.edge_collect_apply_tf_sound[OF sound])
  thus "edge_collect a (local_gamma d g)
          \<subseteq> (case dg_spec_step (local_dg_spec tf) a d g of (g', d') \<Rightarrow> local_gamma d' g')"
    by (simp add: dg_spec_step_local local_gamma_def)
next
  fix s t :: store and dst and dc de :: "'a abs_state" and g :: unit
  assume "s \<in> local_gamma dc g" and "t \<in> local_gamma de g"
  hence "combine_collect dst s t \<in> \<lbrakk>combine_collect_abs dst dc de\<rbrakk>"
    unfolding local_gamma_def by (rule combine_collect_sound)
  thus "combine_collect dst s t
          \<in> (case dgs_combine (local_dg_spec tf) dst dc de g of (g', d') \<Rightarrow> local_gamma d' g')"
    by (simp add: dgs_combine_local local_gamma_def)
qed

context sound_transfer
begin

sublocale local_dg: sound_dg_spec "local_dg_spec tf" local_gamma
  by (rule sound_dg_spec_local[OF sound_transfer_axioms])

subsection \<open>The clean context theorem as a DG corollary\<close>

text \<open>
  The DG solution built from a clean local solution \<open>sg\<close>: the local slot carries \<open>sg\<close>'s
  Answer, the Side slot is the trivial \<^term>\<open>()\<close>.  \<open>local_dg.dg_D_c\<close> reads back exactly
  \<open>sg (Inl (v, ctx))\<close> and \<open>local_dg.dg_gamma_c\<close> its concretization --- the \<open>G\<close> component
  contributes nothing.
\<close>

definition local_sigma ::
  "(pp \<times> 'c \<Rightarrow> 'a abs_state) \<Rightarrow> (pp \<times> 'c + 'c \<Rightarrow> ('a abs_state, unit) dg_state)"
where
  "local_sigma loc u = (case u of Inl vk \<Rightarrow> DG (loc vk) () | Inr ctx \<Rightarrow> DG bot ())"

lemma local_sigma_D: "local_dg.dg_D_c (local_sigma loc) ctx v = loc (v, ctx)"
  by (simp add: local_dg.dg_D_c_def local_sigma_def)

lemma local_sigma_gamma:
  "local_dg.dg_gamma_c (local_sigma loc) ctx v = \<lbrakk>loc (v, ctx)\<rbrakk>"
  by (simp add: local_dg.dg_gamma_c_def local_sigma_D local_gamma_def)

theorem clean_ctx_collect_rread_via_dg:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v dst tau rho. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof -
  define loc where "loc = (\<lambda>vk. sg (Inl vk))"
  have gam: "\<And>ctx v. local_dg.dg_gamma_c (local_sigma loc) ctx v = \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (simp add: local_sigma_gamma loc_def)
  have dval: "\<And>ctx v. local_dg.dg_D_c (local_sigma loc) ctx v = sg (Inl (v, ctx))"
    by (simp add: local_sigma_D loc_def)
  have "cfg_collect_ctx dg cmp g S v ctx \<subseteq> local_dg.dg_gamma_c (local_sigma loc) ctx v"
  proof (rule local_dg.dg_collect_ctx_sound
      [where sigma = "local_sigma loc" and rt = rt and entdg = entdg and dg = dg and cmp = cmp])
    show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> local_dg.dg_gamma_c (local_sigma loc) ctx (cfg_entry g)"
      using ENTRY by (simp add: gam)
  next
    show "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
            \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> local_dg.dg_gamma_c (local_sigma loc) ctx v"
      using PROC_ENTRY by (simp add: gam)
  next
    fix ctx u a v' tr s'
    assume e: "(u, a, v') \<in> edges g" and st: "edge_step a (last tr) = Some s'"
      and lt: "last tr \<in> local_dg.dg_gamma_c (local_sigma loc) ctx u"
    from lt have lt': "last tr \<in> \<lbrakk>sg (Inl (u, ctx))\<rbrakk>" by (simp add: gam)
    have "s' \<in> \<lbrakk>sg (Inl (v', ctx))\<rbrakk>"
      by (rule edge_of_bound[OF EDGE_BOUND[OF e] lt' st])
    thus "s' \<in> local_dg.dg_gamma_c (local_sigma loc) ctx v'" by (simp add: gam)
  next
    fix ctx cl ex v' dst tau rho
    assume c: "(cl, ex, v', dst) \<in> combines g"
      and ct: "last tau \<in> local_dg.dg_gamma_c (local_sigma loc) ctx cl"
      and ce: "last rho \<in> local_dg.dg_gamma_c (local_sigma loc)
                  (rt cl ctx (local_dg.dg_D_c (local_sigma loc) ctx cl)) ex"
    from ct have ct': "last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>" by (simp add: gam)
    from ce have ce': "last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>"
      by (simp add: gam dval)
    have "combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v', ctx))\<rbrakk>" by (rule COMB[OF c ct' ce'])
    thus "combine_collect dst (last tau) (last rho) \<in> local_dg.dg_gamma_c (local_sigma loc) ctx v'"
      by (simp add: gam)
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
      using DG_INTRA by blast
  next
    show "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
      using DG_RETURN by blast
  next
    show "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
      using DG_CALLEE by blast
  next
    fix ctx cl s
    assume "s \<in> local_dg.dg_gamma_c (local_sigma loc) ctx cl"
    hence "s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>" by (simp add: gam)
    thus "cmp (entdg s) (rt cl ctx (local_dg.dg_D_c (local_sigma loc) ctx cl))"
      using ENTER_MONO by (simp add: dval)
  qed
  thus ?thesis by (simp add: gam)
qed

text \<open>
  \<open>clean_ctx_collect_rread\<close> (in \<open>Clean_RRead_Sound\<close>) is a direct corollary of this
  endpoint --- same statement, same premises --- so the clean single-domain analysis
  rides the DG spine rather than a separate proof foundation.
\<close>
lemma clean_ctx_collect_rread_is_dg_corollary:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v dst tau rho. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  using assms by (rule clean_ctx_collect_rread_via_dg)

end

end
