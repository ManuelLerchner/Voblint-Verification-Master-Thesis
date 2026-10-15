theory MCP
  imports MCP_Carrier
begin

section \<open>The active typed analyses, run through the pipeline\<close>

text \<open>
  A caller activates a list of typed analyses, as Goblint's \<^verbatim>\<open>ana.activated\<close>. The
  registry runs the distinct ones as one component; the pipeline solves it on the typed
  CFG at call-string contexts of bound \<open>k\<close>, exactly as it solves one analysis.
\<close>

definition activation_of :: "analysis list \<Rightarrow> analysis list" where
  "activation_of as = (if as = [] then [Interval] else remdups as)"

lemma activation_of_ne [simp]: "activation_of as \<noteq> []"
  by (simp add: activation_of_def)

lemma distinct_activation_of [simp]: "distinct (activation_of as)"
  by (simp add: activation_of_def)

text \<open>Every active field starts at its analysis's own entry state, every other at bottom.\<close>

definition mcp_init :: "kind_decls \<Rightarrow> analysis list \<Rightarrow> mcp_st" where
  "mcp_init ds as =
     Product (if Interval \<in> set as then Lifted (nonrel_init_st ds) else Bot)
     (Product (if Congruence \<in> set as then Lifted (nonrel_init_st ds) else Bot)
     (Product (Product (if Ana_Int Refine_Never \<in> set as then Lifted (nonrel_init_st ds) else Bot)
        (Product (if Ana_Int Refine_Once \<in> set as then Lifted (nonrel_init_st ds) else Bot)
                 (if Ana_Int Refine_Fixpoint \<in> set as then Lifted (nonrel_init_st ds) else Bot)))
     (Product (if Sign \<in> set as then Lifted (nonrel_init_st ds) else Bot)
     (Product (if Parity \<in> set as then Lifted (nonrel_init_st ds) else Bot)
              (if Order \<in> set as then Lifted (OFacts True {}) else Bot)))))"

lemma mcp_init_sound:
  "init_stores (kenv_of ds) \<subseteq> mcp.act_gamma ds as (mcp_rd is_global (mcp_init ds as))"
proof
  fix t assume t: "t \<in> init_stores (kenv_of ds)"
  have "t \<in> val_gamma (kenv_of ds) a (mcp_rd is_global (mcp_init ds as))" if m: "a \<in> set as" for a
  proof (cases a rule: analysis_cases)
    case Order with m show ?thesis
      by (simp add: mcp_init_def mcp_rd_def init_stores_in_kinds[OF t])
  qed (use m in \<open>simp_all add: mcp_init_def mcp_rd_def subsetD[OF nonrel_init_sound t]\<close>)
  then show "t \<in> mcp.act_gamma ds as (mcp_rd is_global (mcp_init ds as))"
    by (simp add: mcp.act_gamma_def)
qed

text \<open>What the combination owes the pipeline does not depend on the context policy, so
  it is proved once, for any route and root context, as for the untyped analyses
  (\<open>mcp_routed_dg_analysis\<close>).\<close>

lemma mcp_cs_routed:
  "gdg_analysis
    eval ReturnVar (\<lambda>_. kind_conv (kenv_of ds)) (\<lambda>_. is_global) (\<lambda>_. init_stores (kenv_of ds))
    (mcp_comp sem ds (activation_of as)) (mcp_emp (activation_of as)) mcp_rd
    (mcp_init ds (activation_of as))
    Analysis_Buffer Analysis_Global Activation_Seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE((var_id, 'c) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify sem ds (activation_of as)) (mcp.act_gamma ds (activation_of as))
    (mcp_empty_v (activation_of as))
    (TD_side_rule_Interp_solve_c r)
    (\<lambda>_ c. dg_spec_of c) (\<lambda>p d e. d) (\<lambda>_ d. d) (\<lambda>_ d. Bot) (\<lambda>_ p. []) (\<lambda>p ci d e. d)
    (\<lambda>p. elab_cfg p ds) (\<lambda>_. FunctionEntry prog_main_name)"
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p)
  have eq: "mcp_gamma (map (mcp.part_gamma ds is_global) (activation_of as))
      = (\<lambda>d. gamma_lift (mcp.act_gamma ds (activation_of as)) (map_lift (mcp_rd is_global) d))"
    by (rule ext) (rule mcp.mcp_gamma_rd[OF activation_of_ne])
  show ?case
    using mcp.mcp_comp_sound[OF distinct_activation_of activation_of_ne, where sem = sem and ds = ds and p = p,
        of as]
    unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF mcp.single_entry_mcp_comp[OF activation_of_ne],
        of sem ds as is_global p
          "ls_channel (mcp_comp sem ds (activation_of as) is_global p) d" ci "(d, d)"]
    by (simp add: dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (rule mcp.mcp_emp_rd)
next
  case EmptyV show ?case by (rule mcp.sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro mcp.mcp_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro mcp.mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp.act_gamma_bot[OF activation_of_ne])
next
  case (InitSound p) show ?case by (rule mcp_init_sound)
next
  case (SeedNeGlobal v ctx n) show ?case by simp
next
  case (PEntry p) show ?case by (simp add: elab_cfg_def)
next
  case (FinIntra p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (FinCalls p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (CallsUnique p) show ?case by (rule elab_cfg_calls_source_unique)
qed

subsection \<open>At call-string contexts\<close>

global_interpretation mcp_cs: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "mcp_comp sem ds (activation_of as)" "mcp_emp (activation_of as)" mcp_rd
    "mcp_init ds (activation_of as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((var_id, cfg_node list) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify sem ds (activation_of as)" "mcp.act_gamma ds (activation_of as)"
    "mcp_empty_v (activation_of as)"
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds as r k
  by (rule mcp_cs_routed)

subsection \<open>At entry-state contexts\<close>

text \<open>
  A call is keyed by what each active field gives the callee's formals on entry, as the
  untyped analyses key it (\<open>mcp_formals_route\<close>); a field no active analysis runs keys
  nothing, and the order field keys nothing.
\<close>

type_synonym mcp_ctx =
  "(ivl kd list, (congruence kd list,
    ((int_never int_tuple kd list, (int_once int_tuple kd list, int_fixpoint int_tuple kd list)
      analysis_product) analysis_product,
    (sign kd list, (parity kd list, unit list) analysis_product) analysis_product)
    analysis_product) analysis_product) analysis_product"

definition mcp_route ::
    "analysis list \<Rightarrow> (var_id \<Rightarrow> bool) \<Rightarrow> cfg_node \<Rightarrow> mcp_ctx \<Rightarrow> mcp_st lifted
       \<Rightarrow> (var_id, exp) gcall_action \<Rightarrow> mcp_ctx" where
  "mcp_route as \<G> u ctx d ca =
     Product (if Interval \<in> set as then nonrel_es_ctx \<G> (lift_get slot1 d) ca else [])
     (Product (if Congruence \<in> set as then nonrel_es_ctx \<G> (lift_get slot2 d) ca else [])
     (Product (Product (if Ana_Int Refine_Never \<in> set as then nonrel_es_ctx \<G> (lift_get slot3n d) ca else [])
        (Product (if Ana_Int Refine_Once \<in> set as then nonrel_es_ctx \<G> (lift_get slot3o d) ca else [])
                 (if Ana_Int Refine_Fixpoint \<in> set as then nonrel_es_ctx \<G> (lift_get slot3f d) ca else [])))
     (Product (if Sign \<in> set as then nonrel_es_ctx \<G> (lift_get slot4 d) ca else [])
     (Product (if Parity \<in> set as then nonrel_es_ctx \<G> (lift_get slot5 d) ca else []) []))))"

definition mcp_root_ctx :: mcp_ctx where
  "mcp_root_ctx = Product [] (Product [] (Product (Product [] (Product [] []))
     (Product [] (Product [] []))))"

global_interpretation mcp_es: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "mcp_comp sem ds (activation_of as)" "mcp_emp (activation_of as)" mcp_rd
    "mcp_init ds (activation_of as)"
    Analysis_Buffer Analysis_Global Activation_Seed "mcp_route (activation_of as)" mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((var_id, mcp_ctx) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify sem ds (activation_of as)" "mcp.act_gamma ds (activation_of as)"
    "mcp_empty_v (activation_of as)"
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds as r
  by (rule mcp_cs_routed)

subsection \<open>End-to-end soundness\<close>

context
  fixes sem :: sem_conf and ds :: kind_decls and as :: "analysis list" and r :: globals_rule and k :: nat
begin

lemma mcp_cs_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_cs.terminates sem ds as k r is_global p"
  shows "(reaching ds p v)
           \<subseteq> (\<Union>ctx. mcp.act_gamma ds (activation_of as) (mcp_cs.state_at sem ds as k r is_global p ctx v))"
  using mcp_cs.gfun_route_result_node_sound
      [OF elab_cfg_def _ elab_wf_compile_input[OF wf] solves, of "cs_context k" v]
  by (simp add: node_collect_def cs_route_def cs_context_def)

theorem mcp_cs_verdict_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_cs.terminates sem ds as k r is_global p"
    and mem: "(v, c, Decided res) \<in> set (mcp_cs.verdict_report sem ds as k r is_global p)"
    and s: "s \<in> (reaching ds p v)"
  shows "res = Check_Proved \<Longrightarrow> truthy (eval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
proof -
  obtain ctx where sc: "s \<in> mcp.act_gamma ds (activation_of as) (mcp_cs.state_at sem ds as k r is_global p ctx v)"
    using mcp_cs_node_sound[OF wf solves] s by blast
  have decided:
    "mcp_classify sem ds (activation_of as) c (mcp_cs.state_at sem ds as k r is_global p ctx v) = res"
    if known: "res \<noteq> Check_Unknown"
  proof (cases "lookup_table (mcp_cs.result sem ds as k r is_global p) v ctx")
    case Bot
    then show ?thesis using sc by (simp add: mcp_cs.state_at_unfold mcp.act_gamma_bot)
  next
    case (Lifted st)
    have fin: "finite (intra (elab_cfg p ds))" by (simp add: elab_cfg_def compile_prog_finite)
    show ?thesis
      using classify_checks_ctx_decided_sound[OF fin
          mem[unfolded mcp_cs.verdict_report_def] Lifted known] Lifted
      by (simp add: mcp_cs.state_at_unfold)
  qed
  show "res = Check_Proved \<Longrightarrow> truthy (eval c s)"
    using decided mcp.mcp_classify_proved[OF sc] by auto
  show "res = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
    using decided mcp.mcp_classify_refuted[OF sc] by auto
qed

lemma mcp_es_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_es.terminates sem ds as r is_global p"
  shows "(reaching ds p v)
           \<subseteq> (\<Union>ctx. mcp.act_gamma ds (activation_of as) (mcp_es.state_at sem ds as r is_global p ctx v))"
proof
  fix s assume "s \<in> (reaching ds p v)"
  then obtain ctx :: mcp_ctx where "s \<in> ctx_sem.gactivation_collect eval ReturnVar (kind_conv (kenv_of ds))
      is_global (mcp_es.admitted_contexts sem ds as r is_global p) mcp_root_ctx (elab_cfg p ds)
      (init_stores (kenv_of ds)) v ctx"
    using mcp_es.gentry_state_node_collect_eq_Union_of_terminates
        [OF elab_cfg_def elab_wf_compile_input[OF wf] solves, of v]
    by (auto simp: node_collect_def)
  then have "s \<in> gamma_lift (mcp.act_gamma ds (activation_of as))
      (lookup_table (mcp_es.result sem ds as r is_global p) v ctx)"
    using mcp_es.gentry_state_lookup_sound_of_terminates
        [OF elab_cfg_def elab_wf_compile_input[OF wf] solves, of v ctx]
    by blast
  then have "s \<in> mcp.act_gamma ds (activation_of as) (mcp_es.state_at sem ds as r is_global p ctx v)"
    by (auto simp: mcp_es.state_at_unfold split: lifted.splits)
  then show "s \<in> (\<Union>ctx. mcp.act_gamma ds (activation_of as) (mcp_es.state_at sem ds as r is_global p ctx v))"
    by blast
qed

theorem mcp_es_verdict_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_es.terminates sem ds as r is_global p"
    and mem: "(v, c, Decided res) \<in> set (mcp_es.verdict_report sem ds as r is_global p)"
    and s: "s \<in> (reaching ds p v)"
  shows "res = Check_Proved \<Longrightarrow> truthy (eval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
proof -
  obtain ctx where sc: "s \<in> mcp.act_gamma ds (activation_of as) (mcp_es.state_at sem ds as r is_global p ctx v)"
    using mcp_es_node_sound[OF wf solves] s by blast
  have decided:
    "mcp_classify sem ds (activation_of as) c (mcp_es.state_at sem ds as r is_global p ctx v) = res"
    if known: "res \<noteq> Check_Unknown"
  proof (cases "lookup_table (mcp_es.result sem ds as r is_global p) v ctx")
    case Bot
    then show ?thesis using sc by (simp add: mcp_es.state_at_unfold mcp.act_gamma_bot)
  next
    case (Lifted st)
    have fin: "finite (intra (elab_cfg p ds))" by (simp add: elab_cfg_def compile_prog_finite)
    show ?thesis
      using classify_checks_ctx_decided_sound[OF fin
          mem[unfolded mcp_es.verdict_report_def] Lifted known] Lifted
      by (simp add: mcp_es.state_at_unfold)
  qed
  show "res = Check_Proved \<Longrightarrow> truthy (eval c s)"
    using decided mcp.mcp_classify_proved[OF sc] by auto
  show "res = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
    using decided mcp.mcp_classify_refuted[OF sc] by auto
qed

end

end
