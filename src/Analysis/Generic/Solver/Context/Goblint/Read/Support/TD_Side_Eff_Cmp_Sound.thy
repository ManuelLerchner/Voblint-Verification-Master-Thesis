theory TD_Side_Eff_Cmp_Sound
  imports TD_Side_Eff_Ctx_Sound Global_Cmp_Read Context_Domain
begin

section \<open>Read-agnostic semantic-context backbone\<close>

text \<open>
  \<open>post_fixpoint_sound_at_ctx_semantic\<close> (TD_Side_Eff_Ctx_Sound) fixes the global
  slot to \<^typ>\<open>unit\<close> and reads through \<^const>\<open>side_env_ctx\<close>.  The trace induction
  it runs, however, touches the read only through its per-step premises and the
  combine soundness step --- never through the read's internal shape.  Abstracting
  the read to a parameter \<open>renv\<close> isolates that: the backbone below is agnostic to
  whether globals are a single \<^typ>\<open>unit\<close> pot (\<^const>\<open>side_env_ctx\<close>) or a
  \<open>cmp\<close>-filtered family of keyed slots (\<^const>\<open>side_env_cmp\<close>).  Both are instances;
  only the combine premise \<open>COMB_SEM\<close> differs between them.

  The callee context is routed through \<open>rt :: pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c\<close>: the
  call site, the caller context, and the (queried) caller state.  This is the
  \<^const>\<open>context_domain.route\<close> the equation generator's switching combine
  computes; the prior cc-free \<open>ec\<close> is the \<open>rt cc = ec\<close> degenerate case.
\<close>

theorem post_fixpoint_sound_at_ctx_semantic_generic:
  fixes renv :: "(pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
    and rread :: "(pp \<times> 'c + 'g \<Rightarrow> 'a abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
    and \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>renv \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>renv \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and COMB_SEM: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>renv \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>renv \<sigma> (ex, rt cl ctx (rread \<sigma> (cl, ctx)))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>renv \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (rread \<sigma> (cl, ctx)))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
proof -
  from wit have "cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
  proof (induction arbitrary: ctx rule: trace_witness.induct)
    case (entry v s)
    have "s \<in> \<lbrakk>renv \<sigma> (cfg_entry g, ctx)\<rbrakk>"
      using ENTRY entry.hyps entry.prems by blast
    thus ?case using entry.hyps by simp
  next
    case (proc_entry v s)
    have "s \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
      using PROC_ENTRY proc_entry.hyps proc_entry.prems by blast
    thus ?case by simp
  next
    case (edge u a v tr s')
    have tr_ne: "tr \<noteq> []" using edge.hyps(2) by (rule trace_witness_nonempty)
    have ctr: "cmp (dg tr) ctx"
      by (rule DG_INTRA[OF tr_ne edge.prems])
    have lt: "last tr \<in> \<lbrakk>renv \<sigma> (u, ctx)\<rbrakk>" using edge.IH[OF ctr] .
    have "s' \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>" using EDGE edge.hyps lt by blast
    thus ?case by simp
  next
    case (combine cl ex v tau rho)
    have tau_ne: "tau \<noteq> []" using combine.hyps(2) by (rule trace_witness_nonempty)
    have rho_ne: "rho \<noteq> []" using combine.hyps(3) by (rule trace_witness_nonempty)
    have ctau: "cmp (dg tau) ctx"
      using combine.prems DG_RETURN[OF tau_ne, of rho] by simp
    have caller_sound: "last tau \<in> \<lbrakk>renv \<sigma> (cl, ctx)\<rbrakk>"
      using combine.IH(1)[OF ctau] .
    have crho: "cmp (dg rho) (rt cl ctx (rread \<sigma> (cl, ctx)))"
    proof -
      have "dg rho = entdg (last tau)" using DG_CALLEE[OF rho_ne combine.hyps(4)] .
      thus ?thesis using ENTER_MONO[OF caller_sound] by simp
    qed
    have callee_sound: "last rho \<in> \<lbrakk>renv \<sigma> (ex, rt cl ctx (rread \<sigma> (cl, ctx)))\<rbrakk>"
      using combine.IH(2)[OF crho] .
    have "<last tau|last rho> \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
      using COMB_SEM[OF combine.hyps(1) caller_sound callee_sound] .
    thus ?case
      by (metis last_appendR snoc_eq_iff_butlast)
  qed
  thus ?thesis using compat by blast
qed

section \<open>The context-soundness obligation bundle as a locale\<close>

text \<open>
  The read-agnostic trace backbone \<open>post_fixpoint_sound_at_ctx_semantic_generic\<close>
  is re-invoked at every context spine (seeded-clean R_read, retain
  \<^const>\<open>side_env_cmp\<close>, digest) with the same eight obligations --- the seed
  conditions \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>, the intra step \<open>EDGE\<close>, the switching combine
  \<open>COMB\<close>, the digest-propagation trio \<open>DG_INTRA\<close> / \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close>, and the
  routing compatibility \<open>ENTER_MONO\<close>.  Packaging them once as the assumptions of a
  locale extending \<^locale>\<open>context_domain\<close> binds the routing to
  \<^const>\<open>context_domain.route\<close> and the digest / order to the locale's \<open>entdg\<close> /
  \<open>cmp\<close> --- exactly Goblint's \<open>context\<close> after \<open>enter\<close>.  Each spine becomes an
  interpretation and inherits the context-sliced collecting theorem \<open>collect_sound\<close>
  without restating the wrapping from \<^const>\<open>cfg_collect_ctx\<close> down to the trace
  level.
\<close>

locale context_analysis_soundness = context_domain +
  fixes renv  :: "(pp \<times> 'a + 'g \<Rightarrow> 'b abs_state) \<Rightarrow> (pp \<times> 'a) \<Rightarrow> 'b abs_state"
    and rread :: "(pp \<times> 'a + 'g \<Rightarrow> 'b abs_state) \<Rightarrow> (pp \<times> 'a) \<Rightarrow> 'b abs_state"
    and \<sigma>  :: "pp \<times> 'a + 'g \<Rightarrow> 'b abs_state"
    and S  :: "store set"
    and g  :: cfg
    and dg :: "store list \<Rightarrow> 'a"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>renv \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>renv \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>renv \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>renv \<sigma> (ex, route cl ctx (rread \<sigma> (cl, ctx)))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>renv \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (route cl ctx (rread \<sigma> (cl, ctx)))"
begin

text \<open>
  The canonical context-sliced collecting soundness theorem: every store reaching
  \<open>v\<close> along a trace whose digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> is covered by the
  read \<^term>\<open>renv \<sigma> (v, ctx)\<close>.  Wraps the trace backbone through
  \<^const>\<open>cfg_collect_ctx\<close> once, for every interpretation.
\<close>

theorem collect_sound:
  "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
proof -
  have trace_sound:
    "\<And>tr. trace_witness g S v tr \<Longrightarrow> cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
  proof -
    fix tr assume w: "trace_witness g S v tr" and c: "cmp (dg tr) ctx"
    show "last tr \<in> \<lbrakk>renv \<sigma> (v, ctx)\<rbrakk>"
      by (rule post_fixpoint_sound_at_ctx_semantic_generic
            [where renv = renv and rread = rread and rt = route and \<sigma> = \<sigma>
               and dg = dg and cmp = cmp and entdg = entdg and S = S and g = g,
             OF ENTRY PROC_ENTRY EDGE COMB DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO w c])
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using trace_sound by auto
qed

end

section \<open>Instance 1: the existing unit-global theorem is a special case\<close>

text \<open>
  Recovering \<open>post_fixpoint_sound_at_ctx_semantic\<close> from the generic backbone with
  \<open>renv = side_env_ctx\<close> confirms the abstraction is faithful (not vacuous): the
  combine premise \<open>COMB_SEM\<close> is discharged by the already-proved
  \<open>combine_case_ctx_sound\<close> from the unit-global bound \<open>COMB_BOUND\<close>.  The unit route
  is call-site-agnostic, so it instantiates the routing parameter with the
  cc-free \<open>rt = (\<lambda>cc ctx a. ec ctx a)\<close> --- the \<open>route_cc_free\<close> shim.
\<close>

theorem post_fixpoint_sound_at_ctx_semantic_ctx:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and ec :: "'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_ctx \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
    and COMB_BOUND: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> etf_full_ctx_unit (unit_combine_tree_ctx ec cl ex ctx) \<sigma> \<le> side_env_ctx \<sigma> (v, ctx)"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (ec ctx (side_env_ctx \<sigma> (cl, ctx)))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
proof (rule post_fixpoint_sound_at_ctx_semantic_generic
        [where renv = side_env_ctx and rread = side_env_ctx
           and rt = "\<lambda>cc ctx a. ec ctx a" and dg = dg and cmp = cmp and entdg = entdg])
  fix ctx cl ex v' tau rho
  assume comb: "(cl, ex, v') \<in> combines g"
    and cr: "last tau \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>"
    and ce: "last rho \<in> \<lbrakk>side_env_ctx \<sigma> (ex, ec ctx (side_env_ctx \<sigma> (cl, ctx)))\<rbrakk>"
  show "<last tau|last rho> \<in> \<lbrakk>side_env_ctx \<sigma> (v', ctx)\<rbrakk>"
    by (rule combine_case_ctx_sound[OF cr ce COMB_BOUND[OF comb]])
qed (fact ENTRY PROC_ENTRY EDGE DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO wit compat)+

section \<open>Instance 2: cmp-filtered keyed globals\<close>

text \<open>
  The target of the redesign: reads go through \<^const>\<open>side_env_cmp\<close> over a keyed
  global slot type \<^typ>\<open>'g::finite\<close>, so distinct contexts observe distinct global
  slots.  \<open>route_read_cmp\<close> is the routing read the switching combine queries
  at a call site --- the plain local slot \<open>sigma (Inl vk)\<close> (Goblint's \<open>man.local\<close>).
  The trace backbone is the read-agnostic \<^locale>\<open>context_analysis_soundness\<close> with
  \<open>renv = side_env_cmp gcmp\<close> and \<open>rread = route_read_cmp\<close>; only the keyed combine
  soundness remains to discharge (below).
\<close>

definition route_read_cmp ::
  "(pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> (pp \<times> 'c) \<Rightarrow> 'a abs_state"
where
  "route_read_cmp sigma vk = sigma (Inl vk)"

section \<open>Keyed combine soundness: reducing the combine to a reassembly bound\<close>

text \<open>
  The keyed read's switching combine --- the case-4 obligation the
  \<^const>\<open>side_env_cmp\<close> interpretation of \<^locale>\<open>context_analysis_soundness\<close>
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

section \<open>Context-sliced collecting soundness (keyed globals)\<close>

text \<open>
  The reusable per-context kernel theorem (Route A, A7.1).  Interpreting
  \<^locale>\<open>context_analysis_soundness\<close> at \<open>renv = side_env_cmp gcmp\<close>,
  \<open>rread = route_read_cmp\<close> lifts the inherited \<open>collect_sound\<close> to the
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
  interpret L: context_analysis_soundness
      "undefined" "\<lambda>cc. id" rt entdg cmp
      "side_env_cmp gcmp" route_read_cmp sigma S g dg
  proof (unfold_locales, goal_cases)
    case (1 ctx s) then show ?case using ENTRY by blast
  next
    case (2 ctx v s) then show ?case using PROC_ENTRY by blast
  next
    case (3 ctx u a v tr s') then show ?case using EDGE by blast
  next
    case (4 ctx cl ex v tau rho)
    then have caller: "last tau \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>"
      and callee: "last rho \<in> \<lbrakk>side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx)))\<rbrakk>"
      and comb: "(cl, ex, v) \<in> combines g"
      by (auto simp: context_domain.route_def)
    have bound: "combine_read_cmp gcmp sigma rt cl ex ctx \<le> side_env_cmp gcmp sigma (v, ctx)"
    proof (rule combine_read_cmp_le)
      fix x assume "\<not> is_global x"
      thus "sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x" by (rule LOCAL_POST[OF comb])
    next
      fix x assume "is_global x"
      thus "side_env_cmp gcmp sigma (ex, rt cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x" by (rule CMP_SOUND[OF comb])
    qed
    show ?case by (rule combine_case_cmp_sound[OF caller callee bound])
  next
    case (5 tr s' ctx) then show ?case using DG_INTRA by blast
  next
    case (6 tau rho) then show ?case using DG_RETURN by blast
  next
    case (7 tau rho) then show ?case using DG_CALLEE by blast
  next
    case (8 ctx cl s) then show ?case using ENTER_MONO by (simp add: context_domain.route_def)
  qed
  show ?thesis by (rule L.collect_sound)
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
  "tau \<noteq> [] \<Longrightarrow> head_digest f (tau @ tl rho @ [<last tau|last rho>]) = head_digest f tau"
  by (simp add: head_digest_def)

lemma head_digest_DG_CALLEE:
  "rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau)
     \<Longrightarrow> head_digest f rho = (f \<circ> enter_state) (last tau)"
  by (simp add: head_digest_def)

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
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, route cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp sigma (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
  by (rule side_cfg_T_eff_cmp_collect_ctx_sound_semantic
        [where rt = route and entdg = entdg and cmp = cmp and gcmp = gcmp and dg = dg,
         OF ENTRY PROC_ENTRY EDGE LOCAL_POST CMP_SOUND DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO])

end

section \<open>Instance: the semantic entry-store route (\<open>prep = id\<close> shim)\<close>

text \<open>
  \<^locale>\<open>context_domain\<close> is instantiable.  The semantic entry-store route
  (\<open>TD_Side_Eff_Ctx_Sound\<close>) is the call-site-agnostic \<open>prep = id\<close> shim: its digest
  order is \<open>(\<subseteq>)\<close> and its global pot is a single \<^typ>\<open>unit\<close> slot, so \<open>route\<close>
  collapses to \<^const>\<open>entry_store_ec\<close>.  This is the backward-compatible instance
  that leaves \<open>semantic_entry_store_ctx_analysis_sound\<close> unchanged --- it certifies
  that the richer interface subsumes the prior cc-free routing helper.
\<close>

interpretation entry_store_ctx:
  context_domain "UNIV :: store set" "\<lambda>cc. id" "\<lambda>cc ctx a. entry_store_ec ctx a"
    entry_store_entdg "(\<subseteq>)" .

lemma entry_store_route_eq:
  "entry_store_ctx.route cc ctx a = entry_store_ec ctx a"
  by (simp add: entry_store_ctx.route_def)

end

