theory Nonrel_Order_Product
  imports Typed_Order_Analysis "Voblint_Typed_Nonrel.Spec_Product"
begin

section \<open>A non-relational domain and the order domain in one solve\<close>

text \<open>
  The two components run as Goblint's \<^verbatim>\<open>MCP2\<close> runs \<^verbatim>\<open>base\<close> beside a relational
  analysis: one state per program point holds both, and each component's transfer asks
  the product's channel. The non-relational component asks \<open>EvalInt\<close> for every operand it
  evaluates; the order component answers comparisons between variables from its facts.
\<close>

type_synonym 'a no_state = "('a tst toplift, var_id order_rel) pstate"

definition no_spec :: "kenv \<Rightarrow> (var_id, texp, 'a::kind_int_domain no_state) glocal_spec" where
  "no_spec \<kappa> = spec_product (typed_exec_spec \<kappa>) ord_spec"

subsection \<open>Verdicts\<close>

text \<open>
  A check is decided by asking the product, as Goblint's \<^verbatim>\<open>assert\<close> analysis asks
  \<^verbatim>\<open>man.ask (EvalInt e)\<close>. The question is put to the state the solver's result is read
  back to, through the same handlers: the non-relational one on the read-back
  function and the order one on its facts. Their met answer is read in the
  non-relational domain, whose truth test decides the check.
\<close>

type_synonym 'a no_rd = "('a tabs toplift lifted, var_id order_rel lifted) analysis_product"

fun no_rd_query :: "kenv \<Rightarrow> texp gchannel \<Rightarrow> 'a::kind_int_domain no_rd \<Rightarrow> texp gchannel" where
  "no_rd_query \<kappa> ch (Product a b) q =
     (case a of Lifted x \<Rightarrow> tquery \<kappa> ch x q | Bot \<Rightarrow> \<top>) \<sqinter> ord_query ch b q"

fun no_gamma :: "kenv \<Rightarrow> 'a::kind_int_domain no_rd \<Rightarrow> tstore set" where
  "no_gamma \<kappa> (Product a b) = gamma_lift (gamma_tt \<kappa>) a \<inter> gamma_ord_lift b"

definition no_classify :: "kenv \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain no_rd \<Rightarrow> check_result" where
  "no_classify \<kappa> c d =
     (case truth_ik (of_answer_ik None (ask_rec (no_rd_query \<kappa>) query_depth {} d (EvalInt c)) :: 'a) of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"

lemma no_rd_query_sound:
  assumes "s \<in> no_gamma \<kappa> d" and "geval_query.channel_holds teval ch s"
  shows "geval_holds teval q (no_rd_query \<kappa> ch d q) s"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  obtain a b where d: "d = Product a b" by (cases d)
  obtain x y where a: "a = Lifted x" and b: "b = Lifted y"
    and sx: "s \<in> gamma_tt \<kappa> x" and sy: "s \<in> gamma_ord y"
    using assms(1) by (cases a; cases b) (simp_all add: d)
  have "geval_holds teval q (tquery \<kappa> ch x q) s"
    using T.sound_local_spec_queryD[OF typed_spec_sound[of \<kappa>, where 'a = 'a],
        unfolded T.gsound_query_def, rule_format, OF sx assms(2)]
    by (simp add: typed_spec_def)
  moreover have "geval_holds teval q (ord_query ch (Lifted y) q) s"
    by (rule ord_query_sound[OF sy])
  ultimately show ?thesis
    by (simp add: d a b geval_query.inf_sound)
qed

lemma no_classify_sound:
  assumes s: "s \<in> no_gamma \<kappa> d"
  shows no_classify_proved: "no_classify \<kappa> c d = Check_Proved \<Longrightarrow> truthy (teval c s)"
    and no_classify_refuted: "no_classify \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  let ?a = "ask_rec (no_rd_query \<kappa>) query_depth {} d (EvalInt c)"
  have "geval_query.channel_holds teval (ask_rec (no_rd_query \<kappa>) query_depth {} d) s"
    by (rule T.ask_rec_sound) (rule no_rd_query_sound[OF s])
  then have "teval c s \<in> gamma_answer ?a"
    using geval_query.channel_holdsD[of teval _ s "EvalInt c"] by simp
  then have v: "teval c s \<in> numeric_domain_class.gamma (of_answer_ik None ?a :: 'a)"
    by (rule of_answer_ik_sound[rotated]) simp
  have truth: "truthy (teval c s) = b" if "truth_ik (of_answer_ik None ?a :: 'a) = Some b" for b
    by (rule truth_ik_sound[OF that v])
  show "no_classify \<kappa> c d = Check_Proved \<Longrightarrow> truthy (teval c s)"
    using truth by (auto simp: no_classify_def split: option.splits bool.splits)
  show "no_classify \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
    using truth by (auto simp: no_classify_def split: option.splits bool.splits)
qed

subsection \<open>Reading back and emptiness\<close>

fun no_readback :: "(var_id \<Rightarrow> bool) \<Rightarrow> ('a::kind_int_domain tst toplift lifted, var_id order_rel lifted) analysis_product
    \<Rightarrow> 'a no_rd" where
  "no_readback \<G> (Product a b) = Product (map_lift (map_toplift (default_st_to_fun \<G>)) a) b"

fun no_empty :: "('a lifted, 'b lifted) analysis_product \<Rightarrow> bool" where
  "no_empty (Product a b) \<longleftrightarrow> a = Bot \<or> b = Bot"

lemma no_empty_readback: "no_empty s \<longleftrightarrow> no_empty (no_readback \<G> s)"
proof (cases s)
  case (Product a b) then show ?thesis by (cases a) (simp_all add: map_lift_def)
qed

lemma no_empty_sound: "sound_emptiness no_empty (no_gamma \<kappa>)"
proof (rule sound_emptinessI)
  fix d :: "'a::kind_int_domain no_rd" assume "no_empty d"
  then show "no_gamma \<kappa> d = {}" by (cases d) auto
qed

lemma no_spec_sound_rd:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal
     (\<lambda>d. gamma_lift (no_gamma \<kappa>) (map_lift (no_readback tglobal) d))
     (no_spec \<kappa> :: (var_id, texp, 'a::kind_int_domain no_state) glocal_spec)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  have G: "gamma_lift (no_gamma \<kappa>) (map_lift (no_readback tglobal) d)
      = pgamma (gamma_exec \<kappa>) gamma_ord_lift d" for d :: "'a no_state"
  proof (cases d)
    case (Lifted p) then show ?thesis by (cases p) (simp add: gamma_exec_def)
  qed simp
  show ?thesis
    unfolding G no_spec_def
    by (rule T.spec_product_sound[OF typed_exec_spec_sound ord_spec_sound])
qed

subsection \<open>The pipeline instance\<close>

definition no_init :: "kind_decls \<Rightarrow> ('a::kind_int_domain tst toplift lifted, var_id order_rel lifted) analysis_product" where
  "no_init ds = Product (Lifted (tinit_st ds)) (Lifted top)"

global_interpretation nonrel_order: gdg_analysis
    teval ReturnVar "\<lambda>_. tconv (kenv_of ds)" "\<lambda>_. tglobal" "\<lambda>_. tinit_stores (kenv_of ds)"
    "\<lambda>_ _. no_spec (kenv_of ds) :: (var_id, texp, 'a::kind_int_domain no_state) glocal_spec"
    "\<lambda>_. no_empty" no_readback "no_init ds"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ u ctx d ca. typed_cs k u ctx d" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, cfg_node list) global_unknown)
       TYPE(('a no_state, 'a no_state) dg_state) r"
    "Product Bot Bot" "no_classify (kenv_of ds)" "no_gamma (kenv_of ds)" no_empty
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. typed_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for ds r k
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p) show ?case by (rule no_spec_sound_rd)
next
  case (EnterSingle p ci d) show ?case
  proof (cases d)
    case (Lifted q) then show ?thesis
      by (cases q)
         (simp add: no_spec_def spec_product_def typed_exec_spec_def ord_spec_def penter_def
           dg_pipeline.comp_entry_def)
  qed (simp add: no_spec_def spec_product_def dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (rule no_empty_readback)
next
  case EmptyV show ?case by (rule no_empty_sound)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro no_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro no_classify_refuted)
next
  case BotState show ?case by simp
next
  case (InitSound p) show ?case
    using tinit_sound[of ds, where 'a = 'a] by (simp add: no_init_def)
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

text \<open>As for one typed analysis: a terminating solve bounds every typed store reaching a
  node by the node's state under some context, and a decided verdict, aggregated over the
  contexts, holds at every such store. Neither verdict says the node is reached.\<close>

context
  fixes ds :: kind_decls and r :: globals_rule and k :: nat
begin

lemma nonrel_order_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "nonrel_order.terminates TYPE('a::kind_int_domain) ds k r tglobal p"
  shows "tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v
           \<subseteq> (\<Union>ctx. no_gamma (kenv_of ds)
                 (nonrel_order.state_at ds k r tglobal p ctx v :: 'a no_rd))"
  using nonrel_order.gfun_route_result_node_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves, of "typed_cs k" v]
  by (simp add: tnode_collect_def)

theorem nonrel_order_verdict_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "nonrel_order.terminates TYPE('a::kind_int_domain) ds k r tglobal p"
    and mem: "(v, c, Decided res) \<in> set (nonrel_order.verdict_report TYPE('a) ds k r tglobal p)"
    and s: "s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v"
  shows "res = Check_Proved \<Longrightarrow> truthy (teval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
proof -
  obtain ctx where sc:
    "s \<in> no_gamma (kenv_of ds) (nonrel_order.state_at ds k r tglobal p ctx v :: 'a no_rd)"
    using nonrel_order_node_sound[OF wf solves] s by blast
  have decided: "no_classify (kenv_of ds) c (nonrel_order.state_at ds k r tglobal p ctx v :: 'a no_rd) = res"
    if known: "res \<noteq> Check_Unknown"
  proof (cases "lookup_table (nonrel_order.result ds k r tglobal p :: (_, 'a no_rd) solved_table) v ctx")
    case Bot
    then show ?thesis using sc by (simp add: nonrel_order.state_at_unfold)
  next
    case (Lifted st)
    have fin: "finite (intra (typed_cfg p ds))" by (simp add: typed_cfg_def compile_prog_finite)
    show ?thesis
      using classify_checks_ctx_decided_sound[OF fin
          mem[unfolded nonrel_order.verdict_report_def] Lifted known] Lifted
      by (simp add: nonrel_order.state_at_unfold)
  qed
  show "res = Check_Proved \<Longrightarrow> truthy (teval c s)"
    using decided no_classify_proved[OF sc] by auto
  show "res = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
    using decided no_classify_refuted[OF sc] by auto
qed

end

end
