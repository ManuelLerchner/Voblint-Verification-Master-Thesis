theory TD_Side_Eff_Cmp_Sound
  imports Global_Cmp_Read Context_Domain
    "Voblint_Analysis.Ctx_Collect_Backbone"
begin

section \<open>Keyed cmp-filtered global read\<close>

text \<open>
  Reads go through \<^const>\<open>side_env_cmp\<close> over a keyed global slot type
  \<^typ>\<open>'g::finite\<close>, so distinct contexts observe distinct global slots.
  \<open>route_read_cmp\<close> is the routing read the switching combine queries at a call site
  --- the plain local slot \<open>sigma (Inl vk)\<close> (Goblint's \<open>man.local\<close>).  Context-sliced
  collecting soundness (\<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>, below) is an
  instance of the canonical backbone \<open>collect_ctx_sound_meaning\<close>
  (\<open>Ctx_Collect_Backbone\<close>); only the keyed combine soundness is discharged here.
\<close>

definition route_read_cmp ::
  "(pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
where
  "route_read_cmp sigma vk = sigma (Inl vk)"

section \<open>Keyed combine soundness: reducing the combine to a reassembly bound\<close>

text \<open>
  The keyed read's switching combine --- the \<open>COMB\<close> obligation the
  \<^const>\<open>side_env_cmp\<close> instance of the backbone \<open>collect_ctx_sound_meaning\<close>
  discharges --- is a value-dependent combine.  This layer
  discharges it from a \<^emph>\<open>bound\<close> the same way the unit spine discharges its
  combine case: \<open>combine_case_ctx_sound\<close> merges the caller/callee soundness through
  \<open>combine_states_sound\<close> and carries the result to the return unknown with
  \<open>gamma_state_mono\<close>.  Here the read is \<^const>\<open>side_env_cmp\<close>: the callee
  context \<open>rt cl ctx sc\<close> is computed from the queried caller value \<open>sc\<close>, and both
  caller and callee globals are the \<open>gcmp\<close>-filtered join, not the join-all pot.

  \<open>combine_read_cmp\<close> is the reassembled keyed combine value the generator's
  reassembly must be bounded by --- the keyed analogue of \<open>etf_full_ctx_unit\<close>
  evaluated at \<open>unit_combine_tree_ctx\<close>.  It is kept tree-agnostic (a plain
  \<^const>\<open>combine_abs\<close> of two \<^const>\<open>side_env_cmp\<close> reads) to match the
  read-agnostic backbone: the executable QueryG-chain generator that produces the
  bound is a separate obligation.
\<close>

definition combine_read_cmp ::
  "('c \<Rightarrow> 'g \<Rightarrow> bool)
   \<Rightarrow> (pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state"
where
  "combine_read_cmp gcmp sigma rt cl ex ctx =
     \<langle> side_env_cmp gcmp sigma (cl, ctx)
     | side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) \<rangle>"

lemma combine_case_cmp_sound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
  assumes caller: "last tau \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>"
  assumes callee: "last rho \<in> \<lbrakk>side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx)))\<rbrakk>"
  assumes bound: "combine_read_cmp gcmp sigma rt cl ex ctx \<le> side_env_cmp gcmp sigma (v, ctx)"
  shows "<last tau|last rho> \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
proof -
  have "<last tau|last rho> \<in> \<lbrakk>combine_read_cmp gcmp sigma rt cl ex ctx\<rbrakk>"
    unfolding combine_read_cmp_def using caller callee by (rule combine_states_sound)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

text \<open>
  The keyed read for a call that also publishes a return value: Goblint's
  \<open>combine_assign\<close> writes the callee's \<^const>\<open>ret_var\<close> slot into the destination
  variable on top of \<^const>\<open>combine_abs\<close>.  \<^const>\<open>combine_read_cmp\<close> is the
  \<open>dst = None\<close> case.
\<close>

definition combine_collect_read_cmp ::
  "vname option \<Rightarrow> ('c \<Rightarrow> 'g \<Rightarrow> bool)
   \<Rightarrow> (pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state)
   \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state"
where
  "combine_collect_read_cmp dst gcmp sigma rt cl ex ctx =
     combine_collect_abs dst
       (side_env_cmp gcmp sigma (cl, ctx))
       (side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))))"

lemma combine_collect_read_cmp_None:
  "combine_collect_read_cmp None gcmp sigma rt cl ex ctx
     = combine_read_cmp gcmp sigma rt cl ex ctx"
  unfolding combine_collect_read_cmp_def combine_read_cmp_def combine_collect_abs_def
  by simp

lemma combine_collect_case_cmp_sound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
  assumes caller: "last tau \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>"
  assumes callee: "last rho \<in> \<lbrakk>side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx)))\<rbrakk>"
  assumes bound: "combine_collect_read_cmp dst gcmp sigma rt cl ex ctx
                    \<le> side_env_cmp gcmp sigma (v, ctx)"
  shows "combine_collect dst (last tau) (last rho) \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
proof -
  have "combine_collect dst (last tau) (last rho)
          \<in> \<lbrakk>combine_collect_read_cmp dst gcmp sigma rt cl ex ctx\<rbrakk>"
    unfolding combine_collect_read_cmp_def
    using caller callee by (rule combine_collect_sound)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

section \<open>Generator bound: reducing the reassembly bound to CMP_SOUND\<close>

text \<open>
  The keyed reassembly bound \<open>combine_read_cmp \<le> side_env_cmp\<close> splits pointwise on
  the variable class, because \<^const>\<open>combine_abs\<close> takes locals from the caller and globals from
  the callee.  At a \<^emph>\<open>local\<close> variable the read's global part is the shared
  \<^const>\<open>glob_env_cmp\<close> for \<open>ctx\<close> on both sides, so the bound reduces to the caller
  local unknown flowing to the return local unknown (\<open>LOCAL_POST\<close>, a post-solution
  fact).  At a \<^emph>\<open>global\<close> variable it is exactly Goblint's read soundness
  (\<open>CMP_SOUND\<close>): the callee-exit globals under the value-derived context are
  covered by the \<open>gcmp\<close>-filtered read at \<open>ctx\<close>.  This is the irreducible content
  the executable keyed generator must establish; isolating it here closes the
  semantic chain down to the two named obligations.
\<close>

lemma combine_read_cmp_le:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
  assumes LOCAL_POST:
    "\<And>x. \<not> is_global x \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
  assumes CMP_SOUND:
    "\<And>x. is_global x
       \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
             \<le> side_env_cmp gcmp sigma (v, ctx) x"
  shows "combine_read_cmp gcmp sigma rt cl ex ctx \<le> side_env_cmp gcmp sigma (v, ctx)"
proof (rule le_funI)
  fix x
  show "combine_read_cmp gcmp sigma rt cl ex ctx x \<le> side_env_cmp gcmp sigma (v, ctx) x"
  proof (cases "is_global x")
    case True
    thus ?thesis
      unfolding combine_read_cmp_def combine_abs_def using CMP_SOUND[OF True] by simp
  next
    case False
    have "sigma (Inl (cl, ctx)) x \<squnion> glob_env_cmp gcmp ctx sigma x
            \<le> sigma (Inl (v, ctx)) x \<squnion> glob_env_cmp gcmp ctx sigma x"
      by (rule sup_mono[OF LOCAL_POST[OF False] order_refl])
    thus ?thesis
      unfolding combine_read_cmp_def combine_abs_def side_env_cmp_def
      using False by simp
  qed
qed

text \<open>
  With a destination variable the pointwise split gains one case: at \<open>dst\<close>
  itself the read carries the callee's \<^const>\<open>ret_var\<close> slot rather than
  the class-split value, so covering it is a separate obligation \<open>RET_SOUND\<close>
  --- the read-side counterpart of Goblint's \<open>combine_assign\<close>.
\<close>

lemma combine_collect_read_cmp_le:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
  assumes LOCAL_POST:
    "\<And>x. \<not> is_global x \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
  assumes CMP_SOUND:
    "\<And>x. is_global x
       \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
             \<le> side_env_cmp gcmp sigma (v, ctx) x"
  assumes RET_SOUND:
    "\<And>y. dst = Some y
       \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) ret_var
             \<le> side_env_cmp gcmp sigma (v, ctx) y"
  shows "combine_collect_read_cmp dst gcmp sigma rt cl ex ctx
           \<le> side_env_cmp gcmp sigma (v, ctx)"
proof (cases dst)
  case None
  show ?thesis
    unfolding None combine_collect_read_cmp_None
    by (rule combine_read_cmp_le[where gcmp=gcmp and sigma=sigma and rt=rt and cl=cl
            and ex=ex and ctx=ctx and v=v, OF LOCAL_POST CMP_SOUND])
next
  case (Some y)
  have base: "combine_read_cmp gcmp sigma rt cl ex ctx \<le> side_env_cmp gcmp sigma (v, ctx)"
    by (rule combine_read_cmp_le[where gcmp=gcmp and sigma=sigma and rt=rt and cl=cl
            and ex=ex and ctx=ctx and v=v, OF LOCAL_POST CMP_SOUND])
  show ?thesis
  proof (rule le_funI)
    fix x
    show "combine_collect_read_cmp dst gcmp sigma rt cl ex ctx x
            \<le> side_env_cmp gcmp sigma (v, ctx) x"
    proof (cases "x = y")
      case True
      then show ?thesis
        using Some RET_SOUND[of y]
        unfolding combine_collect_read_cmp_def combine_collect_abs_def by simp
    next
      case False
      then show ?thesis
        using Some le_funD[OF base, of x]
        unfolding combine_collect_read_cmp_def combine_collect_abs_def
          combine_read_cmp_def by simp
    qed
  qed
qed

section \<open>Context-sliced collecting soundness (keyed globals)\<close>

text \<open>
  The reusable per-context kernel theorem.  Instantiating the canonical backbone
  \<open>collect_ctx_sound_meaning\<close> at meaning \<open>[[side_env_cmp gcmp sigma (p, c)]]\<close> and routing
  read \<open>route_read_cmp\<close> lifts it to the
  context-sliced collecting set \<^const>\<open>cfg_collect_ctx\<close>: every store reaching \<open>v\<close>
  along a trace whose digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> is covered by the
  keyed read \<^const>\<open>side_env_cmp\<close> at \<open>(v, ctx)\<close>.  This is the value-dependent
  (switching) analogue of the flat monovariant guarantee: because the flat
  \<^const>\<open>cfg_collect\<close> mixes all contexts, only its \<open>cmp\<close>-slice is soundly
  over-approximated by a single keyed slot; the flat statement is recovered by
  joining the (finite) context slices.

  The obligations are the switching-combine soundness contract, split into: the
  seed conditions \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>; the intra step \<open>EDGE\<close>; the combine
  bound \<open>LOCAL_POST\<close> (caller local flows to the return local) + \<open>CMP_SOUND\<close>
  (the value-derived callee-exit globals are covered by the keyed read at the
  return context --- Goblint's read-side compatibility); and the digest-propagation
  obligations \<open>DG_INTRA\<close> / \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close> / \<open>ENTER_MONO\<close> the concrete
  digest instance (A7.2) discharges.
\<close>

theorem side_cfg_T_eff_cmp_collect_ctx_sound_semantic:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and CMP_SOUND: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x"
    and RET_SOUND: "\<And>ctx cl ex v dst y. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> dst = Some y
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) ret_var
              \<le> side_env_cmp gcmp sigma (v, ctx) y"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> []
        \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (route_read_cmp sigma (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
  \<comment> \<open>A keyed-read instance of the canonical backbone \<open>collect_ctx_sound_meaning\<close>: meaning
      \<open>[[side_env_cmp gcmp sigma (p, c)]]\<close>, routing read \<open>route_read_cmp sigma\<close>.  The switching
      combine discharges through \<open>combine_read_cmp_le\<close> + \<open>combine_case_cmp_sound\<close> exactly as
      before; only the trace induction is now shared, not re-interpreted.\<close>
proof -
  have "cfg_collect_ctx dg cmp g S v ctx
          \<subseteq> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (v, ctx)"
  proof (rule collect_ctx_sound_meaning
      [where M = "\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>"
         and rd = "\<lambda>(p, c). route_read_cmp sigma (p, c)"
         and rt = rt and entdg = entdg and dg = dg and cmp = cmp and S = S and g = g])
    show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (cfg_entry g, ctx)"
      using ENTRY by simp
  next
    show "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (v, ctx)"
      using PROC_ENTRY by simp
  next
    show "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
            \<Longrightarrow> last tr \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (u, ctx)
            \<Longrightarrow> s' \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (v, ctx)"
      using EDGE by simp
  next
    fix ctx cl ex v' dst tau rho
    assume comb: "(cl, ex, v', dst) \<in> combines g"
      and caller0: "last tau \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (cl, ctx)"
      and callee0: "last rho \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>)
                      (ex, rt cl ctx ((\<lambda>(p, c). route_read_cmp sigma (p, c)) (cl, ctx)))"
    from caller0 have caller: "last tau \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>" by simp
    from callee0 have callee: "last rho \<in> \<lbrakk>side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx)))\<rbrakk>"
      by simp
    have bound: "combine_collect_read_cmp dst gcmp sigma rt cl ex ctx
                   \<le> side_env_cmp gcmp sigma (v', ctx)"
    proof (rule combine_collect_read_cmp_le)
      fix x assume "\<not> is_global x"
      thus "sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v', ctx)) x" by (rule LOCAL_POST[OF comb])
    next
      fix x assume "is_global x"
      thus "side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v', ctx) x" by (rule CMP_SOUND[OF comb])
    next
      fix y assume "dst = Some y"
      thus "side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) ret_var
              \<le> side_env_cmp gcmp sigma (v', ctx) y" by (rule RET_SOUND[OF comb])
    qed
    have "combine_collect dst (last tau) (last rho)
            \<in> \<lbrakk>side_env_cmp gcmp sigma (v', ctx)\<rbrakk>"
      by (rule combine_collect_case_cmp_sound[OF caller callee bound])
    thus "combine_collect dst (last tau) (last rho)
            \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (v', ctx)" by simp
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
      using DG_INTRA by blast
  next
    show "\<And>tau rho dst. tau \<noteq> []
        \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
      using DG_RETURN by blast
  next
    show "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
      using DG_CALLEE by blast
  next
    fix ctx cl s
    assume "s \<in> (\<lambda>(p, c). \<lbrakk>side_env_cmp gcmp sigma (p, c)\<rbrakk>) (cl, ctx)"
    hence "s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>" by simp
    thus "cmp (entdg s) (rt cl ctx ((\<lambda>(p, c). route_read_cmp sigma (p, c)) (cl, ctx)))"
      using ENTER_MONO by simp
  qed
  thus ?thesis by simp
qed

subsection \<open>Head-digest: discharging the digest-propagation obligations\<close>

text \<open>
  A digest that reads only the head store of the current activation discharges
  the digest-propagation obligations of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> generically: the head is stable
  under an intra extension (\<open>DG_INTRA\<close>) and under the return concatenation
  (\<open>DG_RETURN\<close>), and \<^const>\<open>enter_state\<close> makes a freshly entered callee's head its
  own enter-state (\<open>DG_CALLEE\<close>, with \<open>entdg = f \<circ> enter_state\<close>).  Program- and
  domain-independent; the concrete sign digest (A7.3) is \<open>head_digest\<close> of the
  sign of the global, and only the value-dependent \<open>ENTER_MONO\<close> compatibility
  remains as a per-instance obligation.
\<close>

definition head_digest :: "(store \<Rightarrow> 'c) \<Rightarrow> store list \<Rightarrow> 'c" where
  "head_digest f tr = f (hd tr)"

lemma head_digest_DG_INTRA:
  "tr \<noteq> [] \<Longrightarrow> cmp (head_digest f (tr @ [s'])) ctx \<Longrightarrow> cmp (head_digest f tr) ctx"
  by (simp add: head_digest_def)

lemma head_digest_DG_RETURN:
  "tau \<noteq> []
     \<Longrightarrow> head_digest f (tau @ tl rho @ [combine_collect dst (last tau) (last rho)])
         = head_digest f tau"
  by (simp add: head_digest_def)

text \<open>
  Writing a local into a store leaves any global-only digest unchanged, so
  binding the (local) formals over the entered store does not move the digest.
\<close>
lemma bind_formals_local_invariant:
  assumes "local_formals xs"
    and finv: "\<And>st x v. \<not> is_global x \<Longrightarrow> f (st(x := v)) = f st"
  shows "f (bind_formals xs vs s) = f s"
  using assms(1)
proof (induction xs arbitrary: vs s)
  case Nil
  show ?case by (simp add: bind_formals_def)
next
  case (Cons x xs)
  note IH = Cons.IH
  have nx: "\<not> is_global x" and lf: "local_formals xs"
    using Cons.prems by (auto simp: local_formals_def)
  show ?case
  proof (cases vs)
    case Nil
    thus ?thesis by (simp add: bind_formals_def)
  next
    case (Cons v vs')
    have "f (bind_formals (x # xs) vs s) = f (bind_formals xs vs' (s(x := v)))"
      using Cons by (simp add: bind_formals_def)
    also have "\<dots> = f (s(x := v))" by (rule IH[OF lf])
    also have "\<dots> = f s" by (rule finv[OF nx])
    finally show ?thesis .
  qed
qed

text \<open>
  A freshly entered callee's head store is the caller-derived enter store with
  the (local) formals bound to the passed actuals.  For a global-only digest
  \<open>f\<close> (insensitive to local writes) and enter edges with local formals, the head
  digest of the callee run is the caller's enter digest \<open>f \<circ> enter_state\<close>.
\<close>
lemma head_digest_DG_CALLEE:
  assumes rho: "rho \<noteq> []"
    and enter: "call_enter_store g cl (last tau) (hd rho)"
    and wf: "\<And>u xs es w. (u, EA_Enter xs es, w) \<in> edges g \<Longrightarrow> local_formals xs"
    and finv: "\<And>st x v. \<not> is_global x \<Longrightarrow> f (st(x := v)) = f st"
  shows "head_digest f rho = (f \<circ> enter_state) (last tau)"
proof -
  from enter obtain pe xs es where
    e: "(cl, EA_Enter xs es, pe) \<in> edges g"
    and hdrho: "hd rho = bind_formals xs (map (\<lambda>e. aval e (last tau)) es) (enter_state (last tau))"
    unfolding call_enter_store_def by blast
  have "head_digest f rho
      = f (bind_formals xs (map (\<lambda>e. aval e (last tau)) es) (enter_state (last tau)))"
    using hdrho by (simp add: head_digest_def)
  also have "\<dots> = f (enter_state (last tau))"
    by (rule bind_formals_local_invariant[OF wf[OF e] finv])
  finally show ?thesis by simp
qed

section \<open>Interface-level soundness: the A7.1 theorem over \<^locale>\<open>context_domain\<close>\<close>

text \<open>
  Restating \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> inside
  \<^locale>\<open>context_domain\<close> binds the routing to \<^const>\<open>context_domain.route\<close> and the
  digest / order to the locale's \<open>entdg\<close> / \<open>cmp\<close>.  An interpretation of the locale
  then specialises the reusable per-context kernel to a concrete instance without
  re-threading a bare routing helper: the combine obligation \<open>CMP_SOUND\<close> and the
  compatibility \<open>ENTER_MONO\<close> are phrased against \<open>route cl ctx sc = ctx_sel cl ctx
  (prep cl sc)\<close> --- exactly Goblint's \<open>context\<close> after \<open>enter\<close>.
\<close>

context context_domain
begin

theorem collect_ctx_sound_route:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and CMP_SOUND: "\<And>ctx cl ex v dst x. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, route cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x"
    and RET_SOUND: "\<And>ctx cl ex v dst y. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> dst = Some y
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, route cl ctx (route_read_cmp sigma (cl, ctx))) ret_var
              \<le> side_env_cmp gcmp sigma (v, ctx) y"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> []
        \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp sigma (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
  by (rule side_cfg_T_eff_cmp_collect_ctx_sound_semantic
        [where rt = route and entdg = entdg and cmp = cmp and gcmp = gcmp and dg = dg,
         OF ENTRY PROC_ENTRY EDGE LOCAL_POST CMP_SOUND RET_SOUND DG_INTRA DG_RETURN
            DG_CALLEE ENTER_MONO])

end

end
