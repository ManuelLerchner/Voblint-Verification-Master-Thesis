theory Call_Spec
  imports TD_Side_Eff_Cmp_Sound
begin

section \<open>First-class Goblint-style call and routing contracts (Stage 0)\<close>

text \<open>
  Stage 0 of the Goblint-aligned analysis specification (see
  \<^file>\<open>../../../../../docs/GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md\<close>, section 6): a
  first-class, analysis-provided call contract over the \<^emph>\<open>current\<close> single-value
  state \<^typ>\<open>'a abs_state\<close>.  No state, tree, equation-system, or solver type changes;
  the locales only \<^emph>\<open>consume\<close> existing constants.

  Four locales, split by concern:
  \<^item> \<open>call_spec\<close> --- executable call configuration: the context-keyed entry
    frame \<open>enter_seed\<close> and the caller/callee merge \<open>combine\<close>, with the sole
    sigma-free semantic law \<open>combine_sound\<close>.
  \<^item> \<open>global_routing_spec\<close> --- executable global-store routing: \<open>gkey\<close> (write key)
    and \<open>gcmp\<close> (which keyed slots a context reads).
  \<^item> \<open>trace_context_compatibility\<close> --- proof-only: the trace digest \<open>dg\<close> and its
    stability laws \<open>dg_intra\<close> / \<open>dg_return\<close> / \<open>dg_callee\<close>.
  \<^item> \<open>goblint_analysis_spec\<close> --- the analysis configuration (call + routing).

  The candidate-solution-dependent premises of
  \<^const>\<open>cfg_collect_ctx\<close> soundness (ENTRY / PROC_ENTRY / EDGE / LOCAL_POST /
  CMP_SOUND / ENTER_MONO) stay theorem-level, out of the reusable locales: they
  mention a concrete solution \<open>sigma\<close>, and ENTER_MONO is not always dischargeable.
\<close>

subsection \<open>Call configuration: entry frame and caller/callee merge\<close>

locale call_spec =
  fixes enter_seed :: "'c \<Rightarrow> 'a::sound_domain abs_state"
    and combine :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes combine_sound:
    "\<And>sc se s t. s \<in> \<lbrakk>sc\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>se\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>combine sc se\<rbrakk>"

subsection \<open>Global-store routing\<close>

locale global_routing_spec =
  fixes gkey :: "'c \<Rightarrow> 'g::finite"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"

subsection \<open>Trace/context compatibility (proof-only)\<close>

locale trace_context_compatibility =
  fixes dg :: "store list \<Rightarrow> 'c"
    and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and entdg :: "store \<Rightarrow> 'c"
  assumes dg_intra: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and dg_return: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and dg_callee: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau)
                       \<Longrightarrow> dg rho = entdg (last tau)"

subsection \<open>The analysis specification: call configuration + routing\<close>

locale goblint_analysis_spec = context_domain + call_spec + global_routing_spec

subsection \<open>Soundness assembly\<close>

text \<open>
  The composed corollary.  \<^locale>\<open>call_spec\<close> supplies the context routing (\<open>route\<close>)
  and \<open>trace_context_compatibility\<close> supplies the digest laws; the six
  solution-dependent premises stay hypotheses.  The proof is a wrapper around the
  existing \<open>context_domain.collect_ctx_sound_route\<close> --- no mathematics is
  reproved.
\<close>

locale cmp_generator_soundness = goblint_analysis_spec + trace_context_compatibility
begin

theorem cmp_generator_sound:
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and CMP_SOUND: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global x
        \<Longrightarrow> side_env_cmp gcmp sigma (ex, route cl ctx (route_read_cmp sigma (cl, ctx))) x
              \<le> side_env_cmp gcmp sigma (v, ctx) x"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (route cl ctx (route_read_cmp sigma (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
  by (rule collect_ctx_sound_route
        [OF ENTRY PROC_ENTRY EDGE LOCAL_POST CMP_SOUND dg_intra dg_return dg_callee ENTER_MONO])

end

end
