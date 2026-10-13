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
    "tmcp_comp ds (tactivation as)" "tmcp_emp (tactivation as)" tmcp_rd
    "tmcp_init ds (tactivation as)"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ u ctx d ca. typed_cs k u ctx d" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, cfg_node list) global_unknown)
       TYPE((tmcp_st lifted, tmcp_st lifted) dg_state) r"
    \<bottom> "tmcp_classify ds (tactivation as)" "tmcp.act_gamma ds (tactivation as)"
    "tmcp_empty_v (tactivation as)"
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
          "ls_channel (tmcp_comp ds (tactivation as) tglobal p) d" ci "(d, d)"]
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

subsection \<open>End-to-end soundness\<close>

context
  fixes ds :: kind_decls and as :: "typed_domain list" and r :: globals_rule and k :: nat
begin

lemma typed_mcp_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_mcp.terminates ds as k r tglobal p"
  shows "tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v
           \<subseteq> (\<Union>ctx. tmcp.act_gamma ds (tactivation as) (typed_mcp.state_at ds as k r tglobal p ctx v))"
  using typed_mcp.gfun_route_result_node_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves, of "typed_cs k" v]
  by (simp add: tnode_collect_def)

theorem typed_mcp_verdict_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_mcp.terminates ds as k r tglobal p"
    and mem: "(v, c, Decided res) \<in> set (typed_mcp.verdict_report ds as k r tglobal p)"
    and s: "s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v"
  shows "res = Check_Proved \<Longrightarrow> truthy (teval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
proof -
  obtain ctx where sc: "s \<in> tmcp.act_gamma ds (tactivation as) (typed_mcp.state_at ds as k r tglobal p ctx v)"
    using typed_mcp_node_sound[OF wf solves] s by blast
  have decided:
    "tmcp_classify ds (tactivation as) c (typed_mcp.state_at ds as k r tglobal p ctx v) = res"
    if known: "res \<noteq> Check_Unknown"
  proof (cases "lookup_table (typed_mcp.result ds as k r tglobal p) v ctx")
    case Bot
    then show ?thesis using sc by (simp add: typed_mcp.state_at_unfold tmcp.act_gamma_bot)
  next
    case (Lifted st)
    have fin: "finite (intra (typed_cfg p ds))" by (simp add: typed_cfg_def compile_prog_finite)
    show ?thesis
      using classify_checks_ctx_decided_sound[OF fin
          mem[unfolded typed_mcp.verdict_report_def] Lifted known] Lifted
      by (simp add: typed_mcp.state_at_unfold)
  qed
  show "res = Check_Proved \<Longrightarrow> truthy (teval c s)"
    using decided tmcp.mcp_classify_proved[OF sc] by auto
  show "res = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
    using decided tmcp.mcp_classify_refuted[OF sc] by auto
qed

end

section \<open>The typed entry point\<close>

text \<open>
  The experimental typed counterpart of \<open>run_voblint\<close>: it analyzes a program under its
  kind declarations with the activated typed analyses, as Goblint's \<^verbatim>\<open>ana.activated\<close>
  selects them, and answers the verdicts of the program's checks. At call-string contexts
  the active analyses run as one through the registry, each asking the others through
  \<open>EvalInt\<close>. At entry-state contexts one non-relational analysis runs alone; the
  registry's entry-state route is not there yet. The entry point sits beside the untyped
  one, which analyzes the lowered program, so the two can be compared on the same input.
\<close>

definition mcp_run ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_answer" where
  "mcp_run as r k ds p =
     (if TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
           (cfg_exit (typed_cfg p ds), []) = None
      then Typed_No_Answer
      else Typed_Analysed (map (\<lambda>(u, c, v). (u, c, verdict_result v))
             (typed_mcp.verdict_report ds as k r tglobal p)))"

definition run_typed ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> typed_context \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_answer" where
  "run_typed as r cx ds p =
     (if \<not> wf_program_compile_input_exec p then Typed_Malformed
      else case cx of
        Typed_Call_String k \<Rightarrow> mcp_run as r k ds p
      | Typed_Entry_State \<Rightarrow> (case as of [d] \<Rightarrow> run_one d r cx ds p | _ \<Rightarrow> Typed_Unsupported))"

lemma mcp_run_sound:
  assumes wf: "wf_program_compile_input p"
  shows "run_sound (mcp_run as r k ds p) ds p"
proof (intro allI impI)
  fix rs v c res
  assume run: "mcp_run as r k ds p = Typed_Analysed rs" and mem: "(v, c, res) \<in> set rs"
  have solved: "TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
      (cfg_exit (typed_cfg p ds), []) \<noteq> None"
    and rs: "rs = map (\<lambda>(u, c, v). (u, c, verdict_result v)) (typed_mcp.verdict_report ds as k r tglobal p)"
    using run by (simp_all add: mcp_run_def split: if_splits)
  have stops: "typed_mcp.terminates ds as k r tglobal p"
    unfolding typed_mcp.terminates_code
    using TD_side_rule_Interp.solve_dom_of_solve_c[OF solved] by simp
  obtain w where w: "(v, c, w) \<in> set (typed_mcp.verdict_report ds as k r tglobal p)"
    and res: "res = verdict_result w"
    using mem rs by auto
  show "(res = Check_Proved \<longrightarrow> (\<forall>s \<in> reaching ds p v. truthy (teval c s)))
       \<and> (res = Check_Refuted \<longrightarrow> (\<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)))"
  proof (cases w)
    case (Lifted r')
    then show ?thesis
      using typed_mcp_verdict_sound[OF wf stops, of v c r'] w res
      by (auto simp: verdict_result_def)
  qed (simp add: res verdict_result_def)
qed

theorem run_typed_sound:
  assumes run: "run_typed as r cx ds p = Typed_Analysed rs"
    and mem: "(v, c, res) \<in> set rs"
  shows run_typed_proved_sound:
      "res = Check_Proved \<Longrightarrow> \<forall>s \<in> reaching ds p v. truthy (teval c s)"
    and run_typed_refuted_sound:
      "res = Check_Refuted \<Longrightarrow> \<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)"
proof -
  have exec: "wf_program_compile_input_exec p"
    using run by (simp add: run_typed_def split: if_splits)
  note wf = wf_program_compile_input_exec_sound[OF exec]
  have "run_sound (run_typed as r cx ds p) ds p"
    using run_one_sound[OF wf] mcp_run_sound[OF wf] exec
    by (simp add: run_typed_def split: list.splits typed_context.splits)
  then show "res = Check_Proved \<Longrightarrow> \<forall>s \<in> reaching ds p v. truthy (teval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)"
    using run mem by blast+
qed

end
