theory DG_Analysis_Adapter
  imports Routed_Context Contextual_Check_Report Analysis_Result Activation_Backbone
begin

section \<open>Public result and check-report adapter for a local-state routed DG analysis\<close>

text \<open>
  Every concrete routed-context analysis needs the same public
  \<^type>\<open>analysis_result\<close>/check report/soundness triple, and each one follows
  the identical shape once a routed D/G equation system is solved: read the
  local unknown at every covered \<open>(node, context)\<close> pair into an
  \<^type>\<open>analysis_result\<close>, classify every compiled check against it via
  \<^const>\<open>classify_checks_verdicts\<close>, and discharge that report's own soundness
  from the activation-indexed collecting semantics
  (\<^theory>\<open>Voblint_Framework.Activation_Backbone\<close>) already available once
  EDGE/CALL/COMB are in hand from \<^locale>\<open>routed_context_base_hetero\<close>.
  \<open>dg_analysis_adapter\<close> derives that whole triple once, generic in a domain
  instance (a \<open>classify\<close> function with its own soundness obligations), a
  context instance (an interpretation of \<^locale>\<open>routed_context_base_hetero\<close>),
  and the carrier the solved table is stored at (a readback \<open>rd\<close> into the abstract
  state, the identity when the table already holds abstract states),
  leaving solver choice orthogonal: which concrete solver produced
  \<open>sigma\<close>/\<open>sg\<close> is an interpretation-site argument, never a locale parameter,
  matching how Interval's own Warrow/join/per-origin solver choice is already
  orthogonal to its context.

  It is not generic over the D/G split, and \<open>gammaDG_rd\<close> is where that shows:
  requiring \<open>gammaDG d g' = gamma_state_lift (rd d)\<close> for every \<open>g'\<close> says the
  concretization ignores the global component entirely, so the published table
  can be read off the local unknown alone. That holds of every analysis
  currently routed through here, and it is what makes \<open>analyse_result\<close> a
  function of \<open>sigma\<close> at \<open>Inl\<close> keys only. A concretization that genuinely
  reads both components --- an ownership split, say --- does not interpret this
  locale as it stands; admitting one means widening \<open>rd\<close> to
  \<^typ>\<open>'D \<Rightarrow> 'G \<Rightarrow> 'a abs_state lifted\<close> and reading the global unknown at
  \<open>Inr gk0\<close> alongside the local one, which every present instance would
  instantiate at a constant function.
\<close>

locale dg_analysis_adapter =
  routed_context_base_hetero S gammaDG gs g gk0 route bot0 s0d s0g sigma vars x0 sg seed_key
    "static_resolve g" is_bot gammaM enterc
  for S :: "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and sg :: "pp \<times> 'c + 'k \<Rightarrow> 'M"
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and gammaM :: "'M \<Rightarrow> store set"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" +
  fixes rd :: "'D \<Rightarrow> 'a::sound_domain abs_state lifted"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes gammaDG_rd: "\<And>d g'. gammaDG d g' = gamma_state_lift (rd d)"
    and classify_proved:
    "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c s)"
    and classify_refuted:
    "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> \<not> truthy (aval c s)"
    and vars_finite: "finite vars"
begin


subsection \<open>The public result table\<close>

text \<open>
  Built from the locale's own solved \<open>vars\<close>/\<open>sigma\<close> pair, mirroring how
  \<open>analyse_interval_entry_state_result_for\<close> builds an
  \<^type>\<open>analysis_result\<close> from an already-solved key set and reader.
  The solved local unknown is read back into \<^typ>\<open>'a abs_state lifted\<close> by \<open>rd\<close> ---
  the identity when the framework was instantiated at that carrier, the executable
  readback when it was instantiated at the solver's own --- and the one
  collapse this table then needs is \<^const>\<open>canonicalize_lift\<close> against
  \<^const>\<open>is_empty_state\<close>, so a witness-bottom \<^const>\<open>Lifted\<close> payload --- a solved
  value that is pointwise \<^const>\<open>bot\<close> without the solver's own \<^const>\<open>Bot\<close> tag
  --- reads as \<^const>\<open>Bot\<close> here, matching \<^const>\<open>classify_point\<close>'s
  documented discipline of never fabricating a vacuous \<^const>\<open>Check_Proved\<close>
  off an empty state.
\<close>

definition analyse_result :: "('c, 'a abs_state) analysis_result" where
  "analyse_result = Analysis_Result vars
     (\<lambda>v ctx. canonicalize_lift is_empty_state (rd (locals (sigma (Inl (v, ctx))))))"

lemma lookup_context_analyse_result:
  "lookup_context analyse_result v ctx =
     (if (v, ctx) \<in> vars
      then canonicalize_lift is_empty_state (rd (locals (sigma (Inl (v, ctx)))))
      else Bot)"
  unfolding lookup_context_def analyse_result_def by simp

text \<open>Canonicality holds unconditionally here: \<^const>\<open>canonicalize_lift\<close> is
  exactly what rules out a \<^const>\<open>Lifted\<close> payload that is secretly empty, and
  it runs on every entry the table publishes.

  Finiteness cannot be proved here, because \<open>vars\<close> is a fixed arbitrary set and
  this locale deliberately does not know which solver produced it --- that is
  what keeps it independent of solver choice. It is therefore an assumption,
  \<open>vars_finite\<close>, and an interpretation discharges it from the solver it actually
  ran: \<open>finite_stabl_solve\<close> says a terminating solve stabilizes finitely many
  unknowns, and the interpretation site is the only place that knows \<open>vars\<close> is
  that stable set.

  Nothing about the context type enters, which is why entry-state contexts are
  covered as readily as monovariant ones despite their context space being
  unbounded.\<close>

lemma analyse_result_canonical:
  assumes "lookup_context analyse_result v ctx = Lifted st"  shows "\<not> is_empty_state st"
  using assms
  unfolding lookup_context_analyse_result
  by (cases "rd (locals (sigma (Inl (v, ctx))))")
     (auto simp: normalize_lift_def split: if_splits)

theorem wf_analyse_result: "wf_analysis_result is_empty_state analyse_result"
  unfolding wf_analysis_result_def finite_analysis_result_def
  using vars_finite analyse_result_canonical by (simp add: analyse_result_def)

text \<open>
  The soundness bridge \<open>gammaM (sg (Inl (v, ctx)))\<close> steps need: a covered
  point's guarded reading agrees exactly with \<open>analyse_result\<close>'s own
  \<^const>\<open>lookup_context\<close> answer at the same key, \<^const>\<open>Bot\<close>
  concretizing to the empty set and \<^const>\<open>Lifted\<close> to \<^const>\<open>gamma_state\<close> of
  its payload. This is the un-projected special case of the general
  executable-carrier bridge that composes the same \<^const>\<open>canonicalize_lift\<close>
  collapse with a reader projection over a resolved_st_q-backed report,
  while this locale's \<open>sigma\<close> is already at the abstract carrier, so no
  projection is threaded here.
\<close>

lemma gammaM_sg_eq_lookup_context:
  assumes cov: "(v, ctx) \<in> vars"
  shows "gammaM (sg (Inl (v, ctx))) =
           (case lookup_context analyse_result v ctx of
              Bot \<Rightarrow> {} | Lifted st \<Rightarrow> \<lbrakk>st\<rbrakk>)"
proof -
  have "gammaM (sg (Inl (v, ctx))) = gammaDG (locals (sigma (Inl (v, ctx))))
          (globs (sigma (Inr gk0)))"
    using cov by simp
  also have "\<dots> = gamma_state_lift (rd (locals (sigma (Inl (v, ctx)))))"
    by (rule gammaDG_rd)
  also have "\<dots> = gamma_state_lift (lookup_context analyse_result v ctx)"
    using cov unfolding lookup_context_analyse_result by simp
  finally show ?thesis by (simp split: lifted.splits)
qed


text \<open>
  The node-soundness bridge a concrete instance's own report-soundness proof
  needs, phrased directly against \<^const>\<open>analyse_result\<close> rather than against
  \<open>analyse_report_ctx\<close> (defined below): every activation-collected store at \<open>v\<close> is
  concretized by \<^const>\<open>analyse_result\<close>'s own reading, \<^const>\<open>bot\<close> when
  uncovered or witness-bottom, its \<^const>\<open>Lifted\<close> payload otherwise ---
  composing \<open>activation_collect_dg_sound\<close> with \<open>gammaM_sg_eq_lookup_context\<close>,
  case-split on coverage. A concrete instance whose own public result reads
  through this same \<open>analyse_result\<close> (up to a proved value equality) gets its
  own node-soundness bridge from this lemma directly, instead of re-deriving
  it from \<open>routed_context_base_hetero\<close>'s primitives by hand.
\<close>

lemma analyse_result_node_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c
  assumes entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "activation_collect gs enterc initial_ctx g S0 v ctx
           \<subseteq> \<lbrakk>case lookup_context analyse_result v ctx of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have "activation_collect gs enterc initial_ctx g S0 v ctx
          \<subseteq> gammaM (sg (Inl (v, ctx)))"
    by (rule activation_collect_dg_sound[OF entry_cov s0_sound])
  also have "\<dots> = gamma_point (lookup_context analyse_result v ctx)"
  proof (cases "(v, ctx) \<in> vars")
    case True
    show ?thesis
      unfolding gamma_point_def by (rule gammaM_sg_eq_lookup_context[OF True])
  next
    case False
    hence "gammaM (sg (Inl (v, ctx))) = {}" by simp
    moreover from False have "lookup_context analyse_result v ctx = Bot"
      unfolding lookup_context_analyse_result by simp
    ultimately show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

subsection \<open>The context-indexed check report\<close>

definition analyse_report_ctx :: "(pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_report_ctx = classify_checks_verdicts g analyse_result classify"

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
text \<open>Both endpoints below reach their classifier obligation the same way, and
  that route is this lemma: a collected store at a decided check sits inside
  some reachable state the report classified, and the report's verdict is what
  the classifier said about that very state. Only the appeal to
  \<open>classify_proved\<close> or \<open>classify_refuted\<close> afterwards differs.\<close>

lemma analyse_report_ctx_decided:
  fixes S0 :: "store set" and initial_ctx :: 'c and v :: cfg_node and c :: exp
  assumes mem: "(v, c, Decided r) \<in> set analyse_report_ctx"
    and entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
    and smem: "s \<in> activation_collect gs enterc initial_ctx g S0 v ctx"
    and known: "r \<noteq> Check_Unknown"
  obtains st where "s \<in> \<lbrakk>st\<rbrakk>" and "classify c st = r"
proof -
  have node_sound: "activation_collect gs enterc initial_ctx g S0 v ctx
      \<subseteq> \<lbrakk>case lookup_context analyse_result v ctx of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_result_node_sound[OF entry_cov s0_sound])
  obtain st where reach: "lookup_context analyse_result v ctx = Lifted st"
    and sst: "s \<in> \<lbrakk>st\<rbrakk>"
    using smem node_sound by (cases "lookup_context analyse_result v ctx") auto
  have "classify c st = r"
    using classify_checks_ctx_decided_sound[OF finE
            mem[unfolded analyse_report_ctx_def] reach known] .
  with sst show ?thesis by (rule that)
qed

theorem analyse_report_ctx_proved_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c and v :: cfg_node and c :: exp
  assumes mem: "(v, c, Decided Check_Proved) \<in> set analyse_report_ctx"
    and entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "\<And>ctx s. s \<in> activation_collect gs enterc initial_ctx g S0 v ctx
           \<Longrightarrow> truthy (aval c s)"
proof -
  fix ctx s
  assume smem: "s \<in> activation_collect gs enterc initial_ctx g S0 v ctx"
  obtain st where sst: "s \<in> \<lbrakk>st\<rbrakk>" and "classify c st = Check_Proved"
    by (rule analyse_report_ctx_decided[OF mem entry_cov s0_sound smem]) simp
  thus "truthy (aval c s)" using classify_proved[OF _ sst] by blast
qed

theorem analyse_report_ctx_refuted_sound:
  fixes S0 :: "store set" and initial_ctx :: 'c and v :: cfg_node and c :: exp
  assumes mem: "(v, c, Decided Check_Refuted) \<in> set analyse_report_ctx"
    and entry_cov: "(cfg_entry g, initial_ctx) \<in> vars"
    and s0_sound: "S0 \<subseteq> gammaDG s0d s0g"
  shows "\<And>ctx s. s \<in> activation_collect gs enterc initial_ctx g S0 v ctx
           \<Longrightarrow> \<not> truthy (aval c s)"
proof -
  fix ctx s
  assume smem: "s \<in> activation_collect gs enterc initial_ctx g S0 v ctx"
  obtain st where sst: "s \<in> \<lbrakk>st\<rbrakk>" and "classify c st = Check_Refuted"
    by (rule analyse_report_ctx_decided[OF mem entry_cov s0_sound smem]) simp
  thus "\<not> truthy (aval c s)" using classify_refuted[OF _ sst] by blast
qed

end

end
