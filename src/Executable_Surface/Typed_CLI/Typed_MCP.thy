theory Typed_MCP
  imports Typed_Carrier
begin

section \<open>The active typed analyses, run through the pipeline\<close>

text \<open>
  A caller activates a list of typed analyses, as Goblint's \<^verbatim>\<open>ana.activated\<close>. The
  registry runs the distinct ones as one component; the pipeline solves it on the typed
  CFG at call-string contexts of bound \<open>k\<close>, exactly as it solves one analysis.
\<close>

definition tactivation :: "typed_domain list \<Rightarrow> typed_domain list" where
  "tactivation as = (if as = [] then [Typed_Interval] else remdups as)"

lemma tactivation_ne [simp]: "tactivation as \<noteq> []"
  by (simp add: tactivation_def)

lemma distinct_tactivation [simp]: "distinct (tactivation as)"
  by (simp add: tactivation_def)

text \<open>Every active field starts at its analysis's own entry state, every other at bottom.\<close>

definition tmcp_init :: "kind_decls \<Rightarrow> typed_domain list \<Rightarrow> tmcp_st" where
  "tmcp_init ds as =
     Product (if Typed_Interval \<in> set as then Lifted (tinit_st ds) else Bot)
     (Product (if Typed_Congruence \<in> set as then Lifted (tinit_st ds) else Bot)
     (Product (if Typed_Int \<in> set as then Lifted (tinit_st ds) else Bot)
     (Product (if Typed_Sign \<in> set as then Lifted (tinit_st ds) else Bot)
     (Product (if Typed_Parity \<in> set as then Lifted (tinit_st ds) else Bot)
              (if Typed_Order \<in> set as then Lifted top else Bot)))))"

lemma tmcp_init_sound:
  "tinit_stores (kenv_of ds) \<subseteq> tmcp.act_gamma ds as (tmcp_rd tglobal (tmcp_init ds as))"
proof
  fix t assume t: "t \<in> tinit_stores (kenv_of ds)"
  have "t \<in> tval_gamma (kenv_of ds) a (tmcp_rd tglobal (tmcp_init ds as))" if "a \<in> set as" for a
  proof (cases a)
    case Typed_Interval with that have m: "Typed_Interval \<in> set as" by simp
    show ?thesis by (simp add: Typed_Interval m tmcp_init_def tmcp_rd_def subsetD[OF tinit_sound t])
  next
    case Typed_Congruence with that have m: "Typed_Congruence \<in> set as" by simp
    show ?thesis by (simp add: Typed_Congruence m tmcp_init_def tmcp_rd_def subsetD[OF tinit_sound t])
  next
    case Typed_Int with that have m: "Typed_Int \<in> set as" by simp
    show ?thesis by (simp add: Typed_Int m tmcp_init_def tmcp_rd_def subsetD[OF tinit_sound t])
  next
    case Typed_Sign with that have m: "Typed_Sign \<in> set as" by simp
    show ?thesis by (simp add: Typed_Sign m tmcp_init_def tmcp_rd_def subsetD[OF tinit_sound t])
  next
    case Typed_Parity with that have m: "Typed_Parity \<in> set as" by simp
    show ?thesis by (simp add: Typed_Parity m tmcp_init_def tmcp_rd_def subsetD[OF tinit_sound t])
  next
    case Typed_Order with that have m: "Typed_Order \<in> set as" by simp
    show ?thesis by (simp add: Typed_Order m tmcp_init_def tmcp_rd_def)
  qed
  then show "t \<in> tmcp.act_gamma ds as (tmcp_rd tglobal (tmcp_init ds as))"
    by (simp add: tmcp.act_gamma_def)
qed

global_interpretation typed_mcp: gdg_analysis
    teval ReturnVar "\<lambda>_. tconv (kenv_of ds)" "\<lambda>_. tglobal" "\<lambda>_. tinit_stores (kenv_of ds)"
    "tmcp.mcp_comp ds (tactivation as)" "tmcp.mcp_emp (tactivation as)" tmcp_rd
    "tmcp_init ds (tactivation as)"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ u ctx d ca. typed_cs k u ctx d" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, cfg_node list) global_unknown)
       TYPE((tmcp_st lifted, tmcp_st lifted) dg_state) r"
    \<bottom> "tmcp.mcp_classify ds (tactivation as)" "tmcp.act_gamma ds (tactivation as)"
    "tmcp.mcp_empty_v (tactivation as)"
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. typed_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for ds as r k
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p)
  have eq: "mcp_gamma (map (tmcp.part_gamma ds tglobal) (tactivation as))
      = (\<lambda>d. gamma_lift (tmcp.act_gamma ds (tactivation as)) (map_lift (tmcp_rd tglobal) d))"
    by (rule ext) (rule tmcp.mcp_gamma_rd[OF tactivation_ne])
  show ?case
    using tmcp.mcp_comp_sound[OF distinct_tactivation tactivation_ne, of ds as p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF tmcp.single_entry_mcp_comp[OF tactivation_ne],
        of ds as tglobal p
          "ls_channel (tmcp.mcp_comp ds (tactivation as) tglobal p) d" ci "(d, d)"]
    by (simp add: dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (rule tmcp.mcp_emp_rd)
next
  case EmptyV show ?case by (rule tmcp.sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro tmcp.mcp_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro tmcp.mcp_classify_refuted)
next
  case BotState show ?case by (rule tmcp.act_gamma_bot[OF tactivation_ne])
next
  case (InitSound p) show ?case by (rule tmcp_init_sound)
next
  case (SeedNeGlobal v ctx n) show ?case by simp
next
  case (PEntry p) show ?case by (simp add: typed_cfg_def)
next
  case (FinIntra p) show ?case by (simp add: typed_cfg_def compile_prog_finite)
next
  case (FinCalls p) show ?case by (simp add: typed_cfg_def compile_prog_finite)
next
  case (CallsUnique p) show ?case by (rule typed_cfg_calls_source_unique)
qed

end
