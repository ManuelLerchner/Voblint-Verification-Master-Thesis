theory MCP_Analyses
  imports MCP_Carrier "Voblint_Framework.MCP_Registry"
begin

section \<open>The registered analyses, run as one\<close>

text \<open>
  \<^theory>\<open>Voblint_CLI.MCP_Carrier\<close> lays out one field per registered analysis
  and states how each field runs, describes, reads back and answers. This theory
  runs the active fields as one component, proves the combination sound whatever
  analyses are registered, and registers it at every context policy. Every proof
  here goes by cases over the registered analyses, so a new analysis in the
  manifest needs nothing new here.
\<close>

subsection \<open>Each analysis on its own field\<close>

lemma field_spec_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (field_spec (registration_of a) \<G> p) (part_gamma \<G> b)"
  by (cases a rule: analysis_domain_cases; cases b rule: analysis_domain_cases;
      simp only: part_gamma.simps registration_of.simps analysis_registration.simps;
      rule field_frame; simp add: lift_get_put_other)

lemma part_gamma_rd: "part_gamma \<G> a x = gamma_lift (val_gamma a) (map_lift (mcp_rd \<G>) x)"
  by (cases a rule: analysis_domain_cases; cases x)
    (simp_all add: mcp_rd_def gamma_lift_default_st_gamma_to_fun)

lemma part_gamma_Bot [simp]: "part_gamma \<G> a Bot = {}"
  by (cases a rule: analysis_domain_cases) simp_all

lemma part_gamma_dead:
  "\<not> field_live (registration_of a) r \<Longrightarrow> part_gamma \<G> a (Lifted r) = {}"
  by (cases a rule: analysis_domain_cases) simp_all

lemma field_empty_rd:
  "field_empty (registration_of a) (declared_global_vars p) r
     = val_empty a (mcp_rd (declared_global p) r)"
  by (cases a rule: analysis_domain_cases)
     (simp_all add: mcp_rd_def
        default_st_is_bot_for_iff[where \<G> = "declared_global p", OF declared_global_iff]
        split: lifted.split)

lemma val_empty_gamma: "val_empty a v \<Longrightarrow> val_gamma a v = {}"
  by (cases a rule: analysis_domain_cases)
    (auto split: lifted.splits dest: is_empty_state_gamma_state_empty)

subsection \<open>The registry of the untyped analyses\<close>

text \<open>
  The registered analyses form a \<^locale>\<open>mcp_registry\<close> over the untyped language:
  every field answers queries as its published value does, the active fields run as
  one component, and a check is decided from the meet of their answers. The
  constants keep the names this theory always gave them.
\<close>

global_interpretation umcp: mcp_registry aval ret_var "\<lambda>_ _ n. n" declared_global check_truth_exp
    "\<lambda>\<G> p a. field_spec (registration_of a) \<G> p" "\<lambda>a. field_live (registration_of a)"
    mcp_rd val_gamma val_empty "\<lambda>p a. field_empty (registration_of a) (declared_global_vars p)"
    "\<lambda>a v ch. value_answer (registration_of a) v"
  defines part_answer = umcp.part_answer and mcp_field = umcp.mcp_field
    and mcp_norm = umcp.mcp_norm and mcp_comp = umcp.mcp_comp and mcp_emp = umcp.mcp_emp
    and mcp_empty_v = umcp.mcp_empty_v and mcp_answer = umcp.mcp_answer
    and mcp_ask = umcp.mcp_ask and mcp_classify = umcp.mcp_classify
proof (unfold_locales, goal_cases Truth FieldSound Frame Single Dead EmptyRd EmptyGamma Bot Answer)
  case (Truth c s) show ?case by (rule aval_check_truth_exp)
next
  case (FieldSound p a) show ?case
    using field_spec_sound[of p a] by (simp add: sound_local_spec_inst part_gamma_rd[abs_def])
next
  case (Frame a b \<G> p) then show ?case
    using field_spec_frame[of a b \<G> p] by (simp add: part_gamma_rd[abs_def])
next
  case (Single \<G> p a) show ?case by (rule single_entry_field_spec)
next
  case (Dead a r \<G>) then show ?case
    using part_gamma_dead[of a r \<G>] by (simp add: part_gamma_rd)
next
  case (EmptyRd p a r) show ?case by (rule field_empty_rd)
next
  case (EmptyGamma a v) then show ?case by (rule val_empty_gamma)
next
  case (Bot a) show ?case by (cases a rule: analysis_domain_cases) simp_all
next
  case (Answer s a v q) then show ?case using value_answer_sound by simp
qed

lemma umcp_act_gamma [simp]: "umcp.act_gamma = mcp_gamma_v"
  by (simp add: fun_eq_iff umcp.act_gamma_def mcp_gamma_v_def)

text \<open>The registry's facts, stated over the carrier's own field concretization.\<close>

theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "sound_local_spec (declared_global p)
           (mcp_gamma (map (part_gamma (declared_global p)) as))
           (mcp_comp as (declared_global p) p)"
  using umcp.mcp_comp_sound[OF assms, of p]
  by (simp add: sound_local_spec_inst part_gamma_rd[abs_def])

lemmas single_entry_mcp_comp = umcp.single_entry_mcp_comp

lemma mcp_gamma_rd:
  "as \<noteq> [] \<Longrightarrow> mcp_gamma (map (part_gamma \<G>) as) x
                  = gamma_lift (mcp_gamma_v as) (map_lift (mcp_rd \<G>) x)"
  using umcp.mcp_gamma_rd[of as \<G> x] by (simp add: part_gamma_rd[abs_def])

lemma mcp_gamma_v_bot: "as \<noteq> [] \<Longrightarrow> mcp_gamma_v as \<bottom> = {}"
  using umcp.act_gamma_bot by simp

lemma mcp_emp_rd: "mcp_emp as p r = mcp_empty_v as (mcp_rd (declared_global p) r)"
  by (rule umcp.mcp_emp_rd)

lemma mcp_empty_v_gamma: "mcp_empty_v as v \<Longrightarrow> mcp_gamma_v as v = {}"
  using umcp.mcp_empty_v_gamma by simp

lemma sound_emptiness_mcp: "sound_emptiness (mcp_empty_v as) (mcp_gamma_v as)"
  using umcp.sound_emptiness_mcp by simp

lemma mcp_classify_proved:
  "mcp_classify as e v = Check_Proved \<Longrightarrow> s \<in> mcp_gamma_v as v \<Longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using umcp.mcp_classify_proved[of s as v e] by simp

lemma mcp_classify_refuted:
  "mcp_classify as e v = Check_Refuted \<Longrightarrow> s \<in> mcp_gamma_v as v
   \<Longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using umcp.mcp_classify_refuted[of s as v e] by simp

text \<open>
  The combined test is not exact. Interval says \<open>x = 2\<close> and Parity says \<open>x\<close> is odd:
  neither field is empty, so the test does not fire, yet no store satisfies both.
\<close>

definition mcp_contradiction :: mcp_val where
  "mcp_contradiction =
     set_slot3 (set_slot2 (\<bottom> :: mcp_val) (Lifted ((\<top> :: ivl abs_state)(STR ''x'' := Ivl (Fin 2) (Fin 2)))))
       (Lifted ((\<top> :: parity abs_state)(STR ''x'' := POdd)))"

lemma mcp_contradiction_not_empty:
  "\<not> mcp_empty_v [Interval_Analysis, Parity_Analysis] mcp_contradiction"
proof -
  have "(\<lambda>_. 2) \<in> \<gamma> ((\<top> :: ivl abs_state)(STR ''x'' := Ivl (Fin 2) (Fin 2)))"
    by (auto simp: gamma_state_def top_ivl_def gamma_ivl_top)
  moreover have "(\<lambda>_. 1) \<in> \<gamma> ((\<top> :: parity abs_state)(STR ''x'' := POdd))"
    by (auto simp: gamma_state_def gamma_parity_top)
  ultimately show ?thesis
    by (auto simp: umcp.mcp_empty_v_def mcp_contradiction_def is_empty_state_iff_gamma_state_empty)
qed

lemma mcp_contradiction_no_store:
  "mcp_gamma_v [Interval_Analysis, Parity_Analysis] mcp_contradiction = {}"
proof (rule equals0I)
  fix s
  assume "s \<in> mcp_gamma_v [Interval_Analysis, Parity_Analysis] mcp_contradiction"
  then have "s (STR ''x'') \<in> gamma_ivl (Ivl (Fin 2) (Fin 2))"
    and "s (STR ''x'') \<in> gamma_parity POdd"
    by (auto simp: mcp_gamma_v_def mcp_contradiction_def gamma_state_def
             dest: spec[of _ "STR ''x''"])
  then show False by (simp, presburger)
qed

lemma mcp_empty_v_not_exact:
  "\<not> exact_emptiness (mcp_empty_v [Interval_Analysis, Parity_Analysis])
       (mcp_gamma_v [Interval_Analysis, Parity_Analysis])"
  using exact_emptinessD [of _ _ mcp_contradiction] mcp_contradiction_not_empty
    mcp_contradiction_no_store
  by blast


text \<open>
  A caller activates a distinct, nonempty list of analyses. The registrations
  below take any list and run it as \<open>activation\<close> normalizes it, so they hold
  unconditionally; \<open>activation\<close> is the identity on every list a caller may
  pass.
\<close>

definition activation :: "analysis_domain list \<Rightarrow> analysis_domain list" where
  "activation as = (if as = [] then [Int_Analysis Refine_Fixpoint] else remdups as)"

lemma activation_ne [simp]: "activation as \<noteq> []"
  by (simp add: activation_def)

lemma distinct_activation [simp]: "distinct (activation as)"
  by (simp add: activation_def)

lemma activation_id: "distinct as \<Longrightarrow> as \<noteq> [] \<Longrightarrow> activation as = as"
  by (simp add: activation_def)

section \<open>Registering the active analyses\<close>

text \<open>
  The active analyses run through the shared pipeline once per context
  policy, as one registered analysis does. What they owe the pipeline does not
  depend on the policy, beyond its seeds being apart from the analysis-wide
  global, so it is proved once here. Each registration leaves the activation
  list and the global update rule as parameters.
\<close>

lemma mcp_routed_dg_analysis:
  fixes buffer_key :: 'k and global_of :: "'n \<Rightarrow> 'k"
  assumes seed_ne: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and seed_ne_global: "\<And>v ctx n. seed v ctx \<noteq> global_of n"
  shows "dg_analysis (mcp_comp (activation as)) (mcp_emp (activation as)) mcp_rd
    (mcp_init (activation as)) buffer_key global_of seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE('k) TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify (activation as)) (mcp_gamma_v (activation as))
    (mcp_empty_v (activation as)) (TD_side_rule_Interp_solve_c r)
    (\<lambda>\<G> c. dg_spec_of c) (\<lambda>\<G> d e. d) (\<lambda>\<G> d. d) (\<lambda>\<G> d. Bot)
    (\<lambda>\<G> p. []) (\<lambda>p ci d e. d)"
proof (rule dg_analysis_whole_stateI[OF td_certified_solver],
    goal_cases CompSound EnterSingle EmptyRd EmptyVSound SeedNe ClProved ClRefuted BotState
    Init SeedNeGlobal)
  case (CompSound p)
  have eq: "mcp_gamma (map (part_gamma (declared_global p)) (activation as))
      = (\<lambda>d. gamma_lift (mcp_gamma_v (activation as)) (map_lift (mcp_rd (declared_global p)) d))"
    by (rule ext) (rule mcp_gamma_rd[OF activation_ne])
  show ?case using mcp_comp_sound[of "activation as" p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF single_entry_mcp_comp[OF activation_ne],
        of as "declared_global p" p
          "ls_channel (mcp_comp (activation as) (declared_global p) p) d" ci "(d, d)"]
    by (simp add: dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (rule mcp_emp_rd)
next
  case EmptyVSound show ?case by (rule sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by (rule seed_ne)
next
  case (ClProved e d s) then show ?case by (rule mcp_classify_proved)
next
  case (ClRefuted e d s) then show ?case by (rule mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp_gamma_v_bot[OF activation_ne])
next
  case (Init p) show ?case by (rule mcp_init_sound)
next
  case (SeedNeGlobal v ctx n) show ?case by (rule seed_ne_global)
qed

subsection \<open>At the unit context\<close>

text \<open>
  \<open>mcp_rule\<close>: the analysis with one context \<open>()\<close>, routed by \<open>route_unit\<close>. Each
  registration names a solver key per program global, which this placement
  never publishes at: every global lives in a point's own state.
\<close>

global_interpretation mcp_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, unit) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. dg_spec_of c" "\<lambda>\<G> d e. d" "\<lambda>\<G> d. d" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. []" "\<lambda>p ci d e. d"
  for as r
  by (rule mcp_routed_dg_analysis) simp_all

subsection \<open>At the entry-state context\<close>

text \<open>
  An activation is keyed by the values the active analyses give its formals
  on entry. The context has a list per field; a field no active analysis
  runs keys nothing.
\<close>

global_interpretation mcp_es_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "mcp_formals_route (activation as)"
      mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, mcp_ctx) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. dg_spec_of c" "\<lambda>\<G> d e. d" "\<lambda>\<G> d. d" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. []" "\<lambda>p ci d e. d"
  for as r
  by (rule mcp_routed_dg_analysis) simp_all

subsection \<open>At the call-string context\<close>

text \<open>
  \<open>mcp_cs_rule\<close>: an activation is keyed by its last \<open>k\<close> call sites, routed by
  \<open>cs_route k\<close> from the empty root string.
\<close>

global_interpretation mcp_cs_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, cfg_node list) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. dg_spec_of c" "\<lambda>\<G> d e. d" "\<lambda>\<G> d. d" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. []" "\<lambda>p ci d e. d"
  for as k r
  by (rule mcp_routed_dg_analysis) simp_all

end
