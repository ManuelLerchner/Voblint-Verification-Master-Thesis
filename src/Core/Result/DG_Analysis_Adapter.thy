theory DG_Analysis_Adapter
  imports Routed_Context Abstract_Checks Analysis_Result Activation_Backbone
begin

section \<open>Generic public result and check-report adapter for a routed DG analysis\<close>

text \<open>
  Both Sign's and Interval's routed-context analyses build their public
  \<^type>\<open>analysis_result\<close>/check report/soundness triple through hand-rolled,
  near-duplicate adapter code, each following the identical shape once a
  routed D/G equation system is solved: read the local unknown at every
  covered \<open>(node, context)\<close> pair into an \<^type>\<open>analysis_result\<close>, classify
  every compiled check against it via \<^const>\<open>classify_checks_verdicts\<close>, and
  discharge that report's own soundness from the activation-indexed
  collecting semantics (\<^theory>\<open>Voblint_Core.Activation_Backbone\<close>) already
  available once EDGE/CALL/COMB are in hand from \<^locale>\<open>routed_context_hetero\<close>.
  \<open>dg_analysis_adapter\<close> derives that whole triple once, generic in a domain
  instance (a \<open>classify\<close> function with its own soundness obligations) and a
  context instance (an interpretation of \<^locale>\<open>routed_context_hetero\<close>),
  leaving solver choice orthogonal: which concrete solver produced
  \<open>sigma\<close>/\<open>sg\<close> is an interpretation-site argument, never a locale parameter,
  matching how Interval's own Warrow/join/per-origin solver choice is already
  orthogonal to its context.
\<close>

locale dg_analysis_adapter =
  routed_context_hetero S gs g gk0 route bot0 s0d s0g sigma vars x0 sg seed_key
    "static_resolve g"
  for S :: "('a::sound_domain abs_state lifted, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d s0g
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('a abs_state lifted, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and sg :: "pp \<times> 'c + 'k \<Rightarrow> 'a abs_state lifted"
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k" +
  fixes classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes classify_proved:
    "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> truthy (aval c s)"
    and classify_refuted:
    "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> truthy (aval c s)"
begin

subsection \<open>An entry-local bound in the shape \<open>pp_entry_s0g_bound\<close> gives for globals\<close>

text \<open>
  The local-carrier twin of \<open>pp_entry_s0g_bound\<close> (\<^theory>\<open>Voblint_Core.DG_Ctx_Activation\<close>),
  proved the same way: \<open>Gen\<close>'s own entry accumulator starts at \<open>bot0 \<squnion> s0d\<close>,
  \<open>side_acc_dg_ge_acc\<close> only grows it, and \<open>pp_eq_bound\<close> transports the
  bound across a covered point's post-solution equation. Every concrete routed
  instance so far (e.g. Interval's entry-state and call-string contexts)
  proves this same fact once per instance; stating it here lets every
  interpretation of this locale reuse it instead.
\<close>

lemma locals_ge_s0d:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0d \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
proof -
  have "s0d \<le> locals (eq Gen (cfg_entry g, ctx) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

subsection \<open>The public result table\<close>

text \<open>
  Built from the locale's own solved \<open>vars\<close>/\<open>sigma\<close> pair, mirroring how
  \<open>monovariant_analysis_result_for\<close> and \<open>analyse_interval_entry_state_result_for\<close>
  build an \<^type>\<open>analysis_result\<close> from an already-solved key set and reader.
  \<^locale>\<open>routed_context_hetero\<close>'s own local unknown is already the abstract
  \<^typ>\<open>'a abs_state lifted\<close> carrier, not an executable substrate, so no
  \<open>is_bot_pred\<close>/\<open>resolved_st_q\<close> projection applies here (unlike
  \<open>normalize_point\<close>, which reads that executable representation): the one
  collapse this table needs is \<^const>\<open>canonicalize_lift\<close> against
  \<^const>\<open>is_bot_state\<close>, so a witness-bottom \<^const>\<open>Lifted\<close> payload --- a solved
  value that is pointwise \<^const>\<open>bot\<close> without the solver's own \<^const>\<open>Bot\<close> tag
  --- reads as \<^const>\<open>Unreachable\<close> here, matching \<^const>\<open>classify_point\<close>'s
  documented discipline of never fabricating a vacuous \<^const>\<open>Check_Proved\<close>
  off an empty state.
\<close>

definition analyse_result :: "('c, 'a abs_state) analysis_result" where
  "analyse_result = Analysis_Result vars
     (\<lambda>v ctx. case canonicalize_lift is_bot_state (locals (sigma (Inl (v, ctx)))) of
                Bot \<Rightarrow> Unreachable | Lifted a \<Rightarrow> Reachable a)"

lemma lookup_context_analyse_result:
  "lookup_context analyse_result v ctx =
     (if (v, ctx) \<in> vars
      then (case canonicalize_lift is_bot_state (locals (sigma (Inl (v, ctx)))) of
              Bot \<Rightarrow> Unreachable | Lifted a \<Rightarrow> Reachable a)
      else Unreachable)"
  unfolding lookup_context_def analyse_result_def by simp

text \<open>
  The soundness bridge \<open>gammaM (sg (Inl (v, ctx)))\<close> steps need: a covered
  point's guarded reading agrees exactly with \<open>analyse_result\<close>'s own
  \<^const>\<open>lookup_context\<close> answer at the same key, \<^const>\<open>Unreachable\<close>
  concretizing to the empty set and \<^const>\<open>Reachable\<close> to \<^const>\<open>gamma_state\<close> of
  its payload. This is the un-projected special case of
  \<open>gamma_point_normalize_point_canonicalize_lift\<close> (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>):
  that lemma bridges a resolved_st_q-backed report across the same
  \<^const>\<open>canonicalize_lift\<close> collapse composed with a reader projection, while
  this locale's \<open>sigma\<close> is already at the abstract carrier, so no projection
  is threaded here.
\<close>

lemma gammaM_sg_eq_lookup_context:
  assumes cov: "(v, ctx) \<in> vars"
  shows "gamma_state_lift (sg (Inl (v, ctx))) =
           (case lookup_context analyse_result v ctx of
              Unreachable \<Rightarrow> {} | Reachable st \<Rightarrow> gamma_state st)"
proof -
  have "gamma_state_lift (sg (Inl (v, ctx))) = gamma_dg_base (locals (sigma (Inl (v, ctx))))
          (globs (sigma (Inr gk0)))"
    using cov by (simp add: sg_cov)
  also have "\<dots> = gamma_state_lift (locals (sigma (Inl (v, ctx))))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> = (case canonicalize_lift is_bot_state (locals (sigma (Inl (v, ctx)))) of
                      Bot \<Rightarrow> {} | Lifted a \<Rightarrow> gamma_state a)"
  proof (cases "locals (sigma (Inl (v, ctx)))")
    case Bot
    then show ?thesis by simp
  next
    case (Lifted st0)
    show ?thesis
    proof (cases "is_bot_state st0")
      case True
      with Lifted have "gamma_state st0 = {}" using is_bot_state_gamma_state_empty by blast
      with Lifted True show ?thesis by simp
    next
      case False
      with Lifted show ?thesis by simp
    qed
  qed
  also have "\<dots> = (case lookup_context analyse_result v ctx of
                      Unreachable \<Rightarrow> {} | Reachable st \<Rightarrow> gamma_state st)"
    using cov unfolding lookup_context_analyse_result by (simp split: lifted.splits)
  finally show ?thesis .
qed

subsection \<open>Activation-collect soundness against the routed local unknown\<close>

text \<open>
  The shared soundness step both report-soundness theorems below need: every
  activation-collected store at any \<open>(v, ctx)\<close> pair is concretized by the
  solved local unknown's own \<^const>\<open>gamma_state_lift\<close>, independent of
  \<open>classify\<close>. Factored out once so both theorems cite it instead of
  re-deriving the same six-obligation \<open>activation_collect_sound_gen\<close>
  argument twice within this locale.
\<close>

lemma activation_collect_dg_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c
  assumes entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gamma_dg_base s0d s0g"
  shows "activation_collect gs enterc initial_ctx g S0 v ctx
           \<subseteq> gamma_state_lift (sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen)
  fix s0 assume s0mem: "s0 \<in> S0"
  have le_local: "s0d \<le> locals (sigma (Inl (cfg_entry g, initial_ctx)))"
    by (rule locals_ge_s0d[OF entry_cov])
  have le_global: "s0g \<le> globs (sigma (Inr gk0))"
    by (rule pp_entry_s0g_bound[OF entry_cov])
  have "gamma_dg_base s0d s0g
        \<subseteq> gamma_dg_base (locals (sigma (Inl (cfg_entry g, initial_ctx)))) (globs (sigma (Inr gk0)))"
    by (rule gamma_dg_base_mono[OF le_local le_global])
  with s0mem s0_sound have "s0 \<in> gamma_dg_base (locals (sigma (Inl (cfg_entry g, initial_ctx))))
                                   (globs (sigma (Inr gk0)))" by blast
  thus "s0 \<in> gamma_state_lift (sg (Inl (cfg_entry g, initial_ctx)))"
    using entry_cov by (simp add: sg_cov)
next
  fix u a v' c' s' s''
  assume "(u, a, v') \<in> intra g" "s' \<in> gamma_state_lift (sg (Inl (u, c')))" "s'' \<in> edge_step a s'"
  thus "s'' \<in> gamma_state_lift (sg (Inl (v', c')))" by (rule dg_ctx_act_edge)
next
  fix u dst pars args p cont c' s'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gamma_state_lift (sg (Inl (u, c')))"
  show "call_enter gs (CallEdge dst pars args) s'
          \<in> gamma_state_lift
              (sg (Inl (FunctionEntry p, enterc u c' (call_enter gs (CallEdge dst pars args) s'))))"
    using routed_context_call[OF ce sm] .
next
  fix cl dst pars args p cont c1 s' t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sm: "s' \<in> gamma_state_lift (sg (Inl (cl, c1)))"
    and tm: "t \<in> gamma_state_lift (sg (Inl (FunctionResult p, enterc cl c1 es)))"
    and ces: "call_enter_store gs g cl s' es"
  show "combine_collect gs dst s' t \<in> gamma_state_lift (sg (Inl (cont, c1)))"
    using tm routed_context_comb[OF ce sm _ ces] by blast
qed

text \<open>
  The node-soundness bridge a concrete instance's own report-soundness proof
  needs, phrased directly against \<^const>\<open>analyse_result\<close> rather than against
  \<open>analyse_report_ctx\<close> (defined below): every activation-collected store at \<open>v\<close> is
  concretized by \<^const>\<open>analyse_result\<close>'s own reading, \<^const>\<open>bot\<close> when
  uncovered or witness-bottom, its \<^const>\<open>Reachable\<close> payload otherwise ---
  composing \<open>activation_collect_dg_sound\<close> with \<open>gammaM_sg_eq_lookup_context\<close>,
  case-split on coverage. A concrete instance whose own public result reads
  through this same \<open>analyse_result\<close> (up to a proved value equality) gets its
  own node-soundness bridge from this lemma directly, instead of re-deriving
  it from \<open>routed_context_hetero\<close>'s primitives by hand.
\<close>

lemma analyse_result_node_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c
  assumes entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gamma_dg_base s0d s0g"
  shows "activation_collect gs enterc initial_ctx g S0 v ctx
           \<subseteq> gamma_state (case lookup_context analyse_result v ctx of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  have "activation_collect gs enterc initial_ctx g S0 v ctx
          \<subseteq> gamma_state_lift (sg (Inl (v, ctx)))"
    by (rule activation_collect_dg_sound[OF entry_cov s0_sound])
  also have "\<dots> = gamma_point (lookup_context analyse_result v ctx)"
  proof (cases "(v, ctx) \<in> vars")
    case True
    show ?thesis
      unfolding gamma_point_def by (rule gammaM_sg_eq_lookup_context[OF True])
  next
    case False
    hence "gamma_state_lift (sg (Inl (v, ctx))) = {}" by (simp add: sg_uncov)
    moreover from False have "lookup_context analyse_result v ctx = Unreachable"
      unfolding lookup_context_analyse_result by simp
    ultimately show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

subsection \<open>The context-indexed and source-level check reports\<close>

definition analyse_report_ctx :: "(pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_report_ctx = classify_checks_verdicts g analyse_result classify"

definition analyse_report :: "check_report_entry list" where
  "analyse_report = map (\<lambda>(u, c, v). (u, c, verdict_check_result v)) analyse_report_ctx"

subsection \<open>Report soundness\<close>

text \<open>
  \<open>S0\<close> and \<open>initial_ctx\<close> are the two facts genuinely external to this
  locale: which concrete stores the analysis actually starts from, and which
  context the solved system covers the entry point under. Every existing
  concrete instance (e.g. Interval's entry-state and call-string contexts)
  discharges both as per-instance facts about its own solved system, not as
  locale theorems, since they depend on which keys a terminated solve
  actually reached --- \<open>entry_cov\<close> mirrors those instances' own \<open>entry_cov\<close>
  context assumption, and \<open>s0_sound\<close> mirrors the \<open>sound0\<close>/\<open>collect_exit\<close>
  premises every LTR-level soundness theorem in this development already
  takes.
\<close>

theorem analyse_report_ctx_proved_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c and v :: cfg_node and c :: exp
  assumes mem: "(v, c, Decided Check_Proved) \<in> set analyse_report_ctx"
    and entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gamma_dg_base s0d s0g"
  shows "\<And>ctx s. s \<in> activation_collect gs enterc initial_ctx g S0 v ctx
           \<Longrightarrow> truthy (aval c s)"
proof -
  fix ctx s
  assume smem: "s \<in> activation_collect gs enterc initial_ctx g S0 v ctx"
  have node_sound: "activation_collect gs enterc initial_ctx g S0 v ctx
      \<subseteq> gamma_state (case lookup_context analyse_result v ctx of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_result_node_sound[OF entry_cov s0_sound])
  obtain st where reach: "lookup_context analyse_result v ctx = Reachable st"
    and sst: "s \<in> gamma_state st"
    using smem node_sound by (cases "lookup_context analyse_result v ctx") (auto simp: gamma_state_bot)
  have mem_unfold: "(v, c, Decided Check_Proved) \<in> set (classify_checks_verdicts g analyse_result classify)"
    using mem unfolding analyse_report_ctx_def .
  have "classify c st = Check_Proved"
    using classify_checks_ctx_proved_sound[OF finE mem_unfold reach] .
  thus "truthy (aval c s)" using classify_proved[OF _ sst] by blast
qed

theorem analyse_report_ctx_refuted_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c and v :: cfg_node and c :: exp
  assumes mem: "(v, c, Decided Check_Refuted) \<in> set analyse_report_ctx"
    and entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gamma_dg_base s0d s0g"
  shows "\<And>ctx s. s \<in> activation_collect gs enterc initial_ctx g S0 v ctx
           \<Longrightarrow> \<not> truthy (aval c s)"
proof -
  fix ctx s
  assume smem: "s \<in> activation_collect gs enterc initial_ctx g S0 v ctx"
  have node_sound: "activation_collect gs enterc initial_ctx g S0 v ctx
      \<subseteq> gamma_state (case lookup_context analyse_result v ctx of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_result_node_sound[OF entry_cov s0_sound])
  obtain st where reach: "lookup_context analyse_result v ctx = Reachable st"
    and sst: "s \<in> gamma_state st"
    using smem node_sound by (cases "lookup_context analyse_result v ctx") (auto simp: gamma_state_bot)
  have mem_unfold: "(v, c, Decided Check_Refuted) \<in> set (classify_checks_verdicts g analyse_result classify)"
    using mem unfolding analyse_report_ctx_def .
  have "classify c st = Check_Refuted"
    using classify_checks_ctx_refuted_sound[OF finE mem_unfold reach] .
  thus "\<not> truthy (aval c s)" using classify_refuted[OF _ sst] by blast
qed

end

end
