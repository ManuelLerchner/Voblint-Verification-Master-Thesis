theory Call_Spec
  imports TD_Side_Eff_Cmp_Sound
begin

section \<open>A Goblint-inspired analysis specification (Stage 0)\<close>

text \<open>
  Stage 0 of the Goblint-aligned direction (see
  \<^file>\<open>../../../../../../../docs/GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md\<close>, sections 6-7):
  a first-class, analysis-provided call and routing contract over the \<^emph>\<open>current\<close>
  single-value state \<^typ>\<open>'a abs_state\<close>.  No state, tree, equation-system, or solver
  type changes.  This theory is \<^emph>\<open>purely semantic\<close>: it imports only the soundness layer
  \<^theory>\<open>Voblint_Analysis.TD_Side_Eff_Cmp_Sound\<close>; the wiring to the concrete generator
  lives in the descendant theory \<open>Call_Spec_Generator\<close>.

  This is a \<^emph>\<open>Goblint-inspired\<close> specification for the current formalization, not a copy
  of Goblint's \<^verbatim>\<open>Spec\<close> (analyses.ml):
  \<^item> \<open>entry_seed\<close> models the current CMP frame initialisation (the generator's
    \<open>frame_seed\<close> argument).  It is \<^emph>\<open>not\<close> Goblint's \<^verbatim>\<open>enter\<close>.
  \<^item> \<open>gkey\<close> / \<open>gcmp\<close> is this formalization's routing abstraction, inspired by Goblint's
    \<^verbatim>\<open>V\<close> / \<^verbatim>\<open>sideg\<close> / \<^verbatim>\<open>global\<close> but not a direct copy of any \<^verbatim>\<open>Spec\<close> field.

  The caller/callee merge is \<^emph>\<open>fixed\<close> in Stage 0 to \<^const>\<open>combine_abs\<close> (locals from
  caller, globals from callee).  An analysis-varied \<open>return_merge\<close> is deferred to
  Stage 0.5: the current generator combine builder is derived from the transfer's
  \<^const>\<open>etf_combine\<close>, so a \<open>return_merge\<close> parameter would not determine the generated
  equations.  Its soundness as a merge is the existing \<open>combine_states_sound\<close>.
\<close>

lemma fixed_merge_sound:
  fixes sc se :: "'a::sound_domain abs_state"
  assumes "s \<in> \<lbrakk>sc\<rbrakk>" and "t \<in> \<lbrakk>se\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>combine_abs sc se\<rbrakk>"
  using assms by (rule combine_states_sound)

subsection \<open>Call configuration: the entry frame\<close>

locale call_spec =
  fixes entry_seed :: "'c \<Rightarrow> 'a::sound_domain abs_state"

subsection \<open>Global-store routing\<close>

text \<open>
  \<open>reads_own_slot\<close> is the \<^emph>\<open>weakest\<close> routing law: a context reads \<^emph>\<open>at least\<close> its own
  written slot.  It does not force reading exactly one slot (Goblint analyses may read
  arbitrary global information), leaving room for richer read policies while still
  proving the current keyed implementation.
\<close>

locale global_routing_spec =
  fixes gkey :: "'c \<Rightarrow> 'g::finite"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
  assumes reads_own_slot: "\<And>ctx. gcmp ctx (gkey ctx)"
begin

text \<open>
  Bridge (\<open>gkey\<close> writes \<open>\<leftrightarrow>\<close> \<open>gcmp\<close> reads): the slot a context writes is included in the
  slots it reads, so the written value is below the keyed read.
\<close>

lemma own_slot_le_read:
  "sigma (Inr (gkey ctx)) \<le> side_env_cmp gcmp sigma (v, ctx)"
proof -
  have "sigma (Inr (gkey ctx)) \<le> glob_env_cmp gcmp ctx sigma"
    by (simp add: glob_env_cmp_upper reads_own_slot)
  thus ?thesis unfolding side_env_cmp_def by (simp add: le_supI2)
qed

end

subsection \<open>Trace/context compatibility (proof-only)\<close>

locale trace_context_compatibility =
  fixes dg :: "store list \<Rightarrow> 'c"
    and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and entdg :: "store \<Rightarrow> 'c"
  assumes dg_intra: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and dg_return: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and dg_callee: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau)
                       \<Longrightarrow> dg rho = entdg (last tau)"

subsection \<open>The analysis specification: context + call + routing\<close>

text \<open>
  Composing three independent locales does not identify their type variables by name, so
  the \<^bold>\<open>for\<close>-clause pins one context type \<open>'c\<close>, one value type \<open>'a\<close>, and one global-key
  type \<open>'g\<close> across \<^locale>\<open>context_domain\<close>, \<^locale>\<open>call_spec\<close>, and
  \<^locale>\<open>global_routing_spec\<close>.
\<close>

locale goblint_analysis_spec =
  context_domain start_context prep ctx_sel entdg cmp +
  call_spec entry_seed +
  global_routing_spec gkey gcmp
  for start_context :: "'c"
    and prep :: "pp \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and ctx_sel :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
    and entdg :: "store \<Rightarrow> 'c"
    and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and entry_seed :: "'c \<Rightarrow> 'a abs_state"
    and gkey :: "'c \<Rightarrow> 'g::finite"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"

subsection \<open>Soundness assembly\<close>

text \<open>
  \<open>context_collecting_soundness\<close> packages \<^emph>\<open>collecting-semantics soundness\<close>, not
  generator soundness: it wraps the existing \<open>context_domain.collect_ctx_sound_route\<close>,
  with \<^locale>\<open>trace_context_compatibility\<close> supplying the digest laws.  The six
  solution-dependent premises (\<open>ENTRY\<close> \<dots> \<open>ENTER_MONO\<close>, \<open>CMP_SOUND\<close> among them) stay
  hypotheses on the candidate solution; the theorem does not produce that solution and
  reproves no mathematics.

  Honest scope: this theorem consumes \<open>cmp\<close> / \<open>entdg\<close> / \<open>dg\<close> / \<open>gcmp\<close> / \<open>route\<close>; it does
  \<^emph>\<open>not\<close> consume \<open>entry_seed\<close>, which configures the generator (\<open>spec_generator\<close> in
  \<open>Call_Spec_Generator\<close>) that produces the candidate solution and enters soundness only
  through the \<open>PROC_ENTRY\<close> / \<open>CMP_SOUND\<close> hypotheses.  Stage 0 declares the contract and
  bridges its fields (\<open>own_slot_le_read\<close> here; \<open>spec_generator\<close> and
  \<open>spec_cmb_realizes_combine\<close> in \<open>Call_Spec_Generator\<close>); discharging the solution
  premises from the generated system is Stage 0.5.
\<close>

locale context_collecting_soundness =
  goblint_analysis_spec start_context prep ctx_sel entdg cmp entry_seed gkey gcmp +
  trace_context_compatibility dg cmp entdg
  for start_context :: "'c"
    and prep :: "pp \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and ctx_sel :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
    and entdg :: "store \<Rightarrow> 'c"
    and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and entry_seed :: "'c \<Rightarrow> 'a abs_state"
    and gkey :: "'c \<Rightarrow> 'g::finite"
    and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
    and dg :: "store list \<Rightarrow> 'c"
begin

theorem context_collecting_sound:
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
