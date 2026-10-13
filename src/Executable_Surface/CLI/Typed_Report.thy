theory Typed_Report
  imports Analysis_Report "Voblint_Typed_CLI.Typed_MCP"
begin

section \<open>The report of a typed run\<close>

text \<open>
  A typed run is reported by the builder a VIMP run uses (\<^const>\<open>report_of\<close>): the typed
  graph, the declared variables, no global name kept at its own unknown, since the typed
  analyses keep every variable in a point's own state, the division obligations of the
  typed expressions, and the program's procedures.
\<close>

fun tarith_obligations :: "texp \<Rightarrow> texp arithmetic_obligation list" where
  "tarith_obligations (TN _ _) = []"
| "tarith_obligations (TVar _ _) = []"
| "tarith_obligations (TArith k op a b) =
     tarith_obligations a @ tarith_obligations b
     @ (if op = ADiv \<or> op = AMod then [Arithmetic_Obligation (TArith k op a b) b] else [])"
| "tarith_obligations (TCast _ a) = tarith_obligations a"
| "tarith_obligations (TCmp _ a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TNot a) = tarith_obligations a"
| "tarith_obligations (TAnd a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TOr a b) = tarith_obligations a @ tarith_obligations b"

text \<open>An obligation is safe when its divisor is not zero, compared at the divisor's kind.\<close>

definition tarith_condition :: "texp arithmetic_obligation \<Rightarrow> texp" where
  "tarith_condition ob =
     TCmp CNe (arithmetic_divisor ob) (TN (texp_kind (arithmetic_divisor ob)) 0)"

type_synonym typed_report =
  "(typed_domain list \<times> globals_rule \<times> typed_context, tmcp_ctx report_context,
    var_id, texp, unit, tmcp_val) analysis_report"

definition typed_cs_report ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> cfg_node list) set
          \<times> (pp \<times> cfg_node list + (unit, cfg_node list) global_unknown
              \<Rightarrow> (tmcp_st lifted, tmcp_st lifted) dg_state)
       \<Rightarrow> typed_report" where
  "typed_cs_report as r k ds p sol =
     report_of (as, r, Typed_Call_String k) (map fst ds) (typed_cfg p ds) []
       (obligation_sites tarith_obligations (typed_cfg p ds)) tarith_condition
       (prog_main_name # prog_procs p) (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
       (tmcp_classify ds (tactivation as)) (typed_mcp.solved_run_of ds as k tglobal p sol)"

subsection \<open>At entry-state contexts\<close>

text \<open>
  An entry-state context is listed in the order of an injective key, as a VIMP entry
  state is (\<^const>\<open>entry_ctx_key\<close>): each field's formal values, a kind-tagged value
  keyed by its tag, its kind and its value.
\<close>

fun ikind_key :: "ikind \<Rightarrow> order_key" where
  "ikind_key I8 = Key_Int 0"
| "ikind_key U8 = Key_Int 1"
| "ikind_key I16 = Key_Int 2"
| "ikind_key U16 = Key_Int 3"
| "ikind_key I32 = Key_Int 4"
| "ikind_key U32 = Key_Int 5"
| "ikind_key I64 = Key_Int 6"
| "ikind_key U64 = Key_Int 7"

lemma ikind_key_inject [simp]: "ikind_key a = ikind_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

fun kd_key :: "('a \<Rightarrow> order_key) \<Rightarrow> 'a kd \<Rightarrow> order_key" where
  "kd_key f KBot = Key_List [Key_Int 0]"
| "kd_key f (KD k a) = Key_List [Key_Int 1, ikind_key k, f a]"
| "kd_key f KTop = Key_List [Key_Int 2]"

lemma kd_key_inject:
  assumes "\<And>a b. f a = f b \<Longrightarrow> a = b"
  shows "kd_key f x = kd_key f y \<Longrightarrow> x = y"
  using assms by (cases x; cases y) auto

lemma map_kd_key_inject:
  assumes "\<And>a b. f a = f b \<Longrightarrow> a = b"
  shows "map (kd_key f) xs = map (kd_key f) ys \<Longrightarrow> xs = ys"
  using kd_key_inject[OF assms] by (auto dest: list.inj_map_strong[rotated])

definition int_tuple_key :: "int_tuple \<Rightarrow> order_key" where
  "int_tuple_key a = Key_List [ivl_key (it_ivl a), congruence_key (it_cong a)]"

lemma int_tuple_key_inject [simp]: "int_tuple_key a = int_tuple_key b \<longleftrightarrow> a = b"
  unfolding int_tuple_key_def by (cases a; cases b) simp

fun tmcp_ctx_key :: "tmcp_ctx \<Rightarrow> order_key" where
  "tmcp_ctx_key (Product i (Product c (Product t (Product s (Product q u))))) =
     Key_List [Key_List (map (kd_key ivl_key) i), Key_List (map (kd_key congruence_key) c),
               Key_List (map (kd_key int_tuple_key) t), Key_List (map (kd_key sign_key) s),
               Key_List (map (kd_key parity_key) q), Key_List (map (\<lambda>_. Key_List []) u)]"

lemma inj_tmcp_ctx_key: "inj tmcp_ctx_key"
proof (rule injI)
  fix a b :: tmcp_ctx
  assume eq: "tmcp_ctx_key a = tmcp_ctx_key b"
  obtain i c t s q u where a: "a = Product i (Product c (Product t (Product s (Product q u))))"
    by (metis analysis_product.exhaust)
  obtain i' c' t' s' q' u'
    where b: "b = Product i' (Product c' (Product t' (Product s' (Product q' u'))))"
    by (metis analysis_product.exhaust)
  from eq have keys:
    "map (kd_key ivl_key) i = map (kd_key ivl_key) i'"
    "map (kd_key congruence_key) c = map (kd_key congruence_key) c'"
    "map (kd_key int_tuple_key) t = map (kd_key int_tuple_key) t'"
    "map (kd_key sign_key) s = map (kd_key sign_key) s'"
    "map (kd_key parity_key) q = map (kd_key parity_key) q'"
    "map (\<lambda>_. Key_List []) u = map (\<lambda>_. Key_List []) u'"
    by (simp_all add: a b)
  have "length u = length u'" using keys(6) by (metis length_map)
  then have "u = u'" by (simp add: list_eq_iff_nth_eq)
  moreover have "i = i'" by (rule map_kd_key_inject[OF _ keys(1)]) simp
  moreover have "c = c'" by (rule map_kd_key_inject[OF _ keys(2)]) simp
  moreover have "t = t'" by (rule map_kd_key_inject[OF _ keys(3)]) simp
  moreover have "s = s'" by (rule map_kd_key_inject[OF _ keys(4)]) simp
  moreover have "q = q'" by (rule map_kd_key_inject[OF _ keys(5)]) simp
  ultimately show "a = b" by (simp add: a b)
qed

definition typed_es_report ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> tmcp_ctx) set
          \<times> (pp \<times> tmcp_ctx + (unit, tmcp_ctx) global_unknown
              \<Rightarrow> (tmcp_st lifted, tmcp_st lifted) dg_state)
       \<Rightarrow> typed_report" where
  "typed_es_report as r ds p sol =
     report_of (as, r, Typed_Entry_State) (map fst ds) (typed_cfg p ds) []
       (obligation_sites tarith_obligations (typed_cfg p ds)) tarith_condition
       (prog_main_name # prog_procs p) tmcp_ctx_key Report_Entry
       (tmcp_classify ds (tactivation as)) (typed_mcp_es.solved_run_of ds as tglobal p sol)"

subsection \<open>The run\<close>

text \<open>A typed run solves the equations of the chosen context policy and reports the
  answer; the logical \<open>None\<close> branch of the executable solve has no report.\<close>

definition typed_report_run ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> typed_context \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> typed_report option" where
  "typed_report_run as r cx ds p =
     (case cx of
        Typed_Call_String k \<Rightarrow>
          map_option (typed_cs_report as r k ds p)
            (TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
               (cfg_exit (typed_cfg p ds), []))
      | Typed_Entry_State \<Rightarrow>
          map_option (typed_es_report as r ds p)
            (TD_side_rule_Interp_solve_c r (typed_mcp_es.equations ds as tglobal p)
               (cfg_exit (typed_cfg p ds), tmcp_root_ctx)))"

subsection \<open>What the builder keeps\<close>

text \<open>A check row is a row of the solve's verdict report, and every state the solved
  table covers is listed, whatever the language.\<close>

lemma report_of_check_mem:
  assumes "chk \<in> set (report_checks
             (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr))"
  shows "(check_point chk, check_exp chk, check_verdict chk)
           \<in> set (classify_checks_verdicts g (run_table sr) classify)"
proof -
  from assms have "chk \<in> set (result_checks_of g (run_table sr) classify)"
    by (simp add: report_of_def Let_def)
  then have "(check_point chk, check_exp chk, check_verdict chk)
      \<in> set (map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk))
                 (result_checks_of g (run_table sr) classify))"
    by (simp only: set_map) (rule imageI)
  then show ?thesis by (simp only: result_checks_of_verdicts)
qed

lemma report_of_state_mem:
  assumes fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
    and look: "lookup_table (run_table sr) v ctx = Lifted d"
  shows "Lifted d \<in> report_states_at
           (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr) v"
proof -
  have "lookup_table (run_table sr) v ctx
          \<in> lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
    by (rule imageI[OF lookup_table_LiftedD[OF look]])
  then show ?thesis by (simp only: report_states_at_report_of[OF fin inj] look)
qed

subsection \<open>Soundness\<close>

text \<open>
  A typed report is sound for every typed store that reaches a node from a store whose
  globals are zero at their kinds. A proved check holds there and a refuted one fails,
  and the store lies in one of the states the report lists at the node. The executable
  solve's answer is the run the typed theorems are about (\<open>solve_c_run\<close>); the check
  column is that run's verdict report, and the listed states are every entry of its
  table.
\<close>

theorem typed_report_check_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run as r cx ds p = Some res"
    and chk: "chk \<in> set (report_checks res)"
    and s: "s \<in> reaching ds p (check_point chk)"
  shows "check_verdict chk = Decided Check_Proved \<Longrightarrow> truthy (teval (check_exp chk) s)"
    and "check_verdict chk = Decided Check_Refuted \<Longrightarrow> \<not> truthy (teval (check_exp chk) s)"
proof -
  have "(check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (teval (check_exp chk) s))
      \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval (check_exp chk) s))"
  proof (cases cx)
    case (Typed_Call_String k)
    from run obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
              (typed_mcp.root_query ds p) = Some sol"
      and res: "res = typed_cs_report as r k ds p sol"
      by (auto simp: typed_report_run_def Typed_Call_String dg_pipeline.root_query_def)
    note solved = typed_mcp.solve_c_run[OF sol]
    have "(check_point chk, check_exp chk, check_verdict chk)
            \<in> set (typed_mcp.verdict_report ds as k r tglobal p)"
      using report_of_check_mem[OF chk[unfolded res typed_cs_report_def]] solved(2)
      by (simp add: typed_mcp.verdict_report_def)
    then show ?thesis
      using typed_mcp_verdict_sound[OF wf solved(1) _ s] by auto
  next
    case Typed_Entry_State
    from run obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (typed_mcp_es.equations ds as tglobal p)
              (typed_mcp_es.root_query ds p) = Some sol"
      and res: "res = typed_es_report as r ds p sol"
      by (auto simp: typed_report_run_def Typed_Entry_State dg_pipeline.root_query_def)
    note solved = typed_mcp_es.solve_c_run[OF sol]
    have "(check_point chk, check_exp chk, check_verdict chk)
            \<in> set (typed_mcp_es.verdict_report ds as r tglobal p)"
      using report_of_check_mem[OF chk[unfolded res typed_es_report_def]] solved(2)
      by (simp add: typed_mcp_es.verdict_report_def)
    then show ?thesis
      using typed_mcp_es_verdict_sound[OF wf solved(1) _ s] by auto
  qed
  then show "check_verdict chk = Decided Check_Proved \<Longrightarrow> truthy (teval (check_exp chk) s)"
    and "check_verdict chk = Decided Check_Refuted \<Longrightarrow> \<not> truthy (teval (check_exp chk) s)"
    by blast+
qed

theorem typed_report_state_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run as r cx ds p = Some res"
    and s: "s \<in> reaching ds p v"
  obtains d where "Lifted d \<in> report_states_at res v"
    and "s \<in> tmcp.act_gamma ds (tactivation as) d"
proof -
  have "\<exists>d. Lifted d \<in> report_states_at res v \<and> s \<in> tmcp.act_gamma ds (tactivation as) d"
  proof (cases cx)
    case (Typed_Call_String k)
    from run obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
              (typed_mcp.root_query ds p) = Some sol"
      and res: "res = typed_cs_report as r k ds p sol"
      by (auto simp: typed_report_run_def Typed_Call_String dg_pipeline.root_query_def)
    note solved = typed_mcp.solve_c_run[OF sol]
    let ?r = "typed_mcp.result ds as k r tglobal p"
    from typed_mcp_node_sound[OF wf solved(1)] s obtain ctx where
      sc: "s \<in> tmcp.act_gamma ds (tactivation as) (typed_mcp.state_at ds as k r tglobal p ctx v)"
      by blast
    obtain d where look: "lookup_table ?r v ctx = Lifted d"
      and sd: "s \<in> tmcp.act_gamma ds (tactivation as) d"
    proof (cases "lookup_table ?r v ctx")
      case Bot
      with sc show ?thesis by (simp add: typed_mcp.state_at_unfold tmcp.act_gamma_bot)
    next
      case (Lifted d)
      with sc that show ?thesis by (simp add: typed_mcp.state_at_unfold)
    qed
    have fin: "finite (covered_keys ?r)"
      using typed_mcp.vars_finite_of_terminates[OF solved(1)]
      by (simp add: dg_pipeline.result_def dg_pipeline.sol_vars_def)
    have tbl: "run_table (typed_mcp.solved_run_of ds as k tglobal p sol) = ?r"
      using solved(2) by simp
    have "Lifted d \<in> report_states_at res v"
      unfolding res typed_cs_report_def
      by (rule report_of_state_mem[OF _ inj_call_string_key look[folded tbl]]) (simp only: tbl fin)
    with sd show ?thesis by blast
  next
    case Typed_Entry_State
    from run obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (typed_mcp_es.equations ds as tglobal p)
              (typed_mcp_es.root_query ds p) = Some sol"
      and res: "res = typed_es_report as r ds p sol"
      by (auto simp: typed_report_run_def Typed_Entry_State dg_pipeline.root_query_def)
    note solved = typed_mcp_es.solve_c_run[OF sol]
    let ?r = "typed_mcp_es.result ds as r tglobal p"
    from typed_mcp_es_node_sound[OF wf solved(1)] s obtain ctx where
      sc: "s \<in> tmcp.act_gamma ds (tactivation as) (typed_mcp_es.state_at ds as r tglobal p ctx v)"
      by blast
    obtain d where look: "lookup_table ?r v ctx = Lifted d"
      and sd: "s \<in> tmcp.act_gamma ds (tactivation as) d"
    proof (cases "lookup_table ?r v ctx")
      case Bot
      with sc show ?thesis by (simp add: typed_mcp_es.state_at_unfold tmcp.act_gamma_bot)
    next
      case (Lifted d)
      with sc that show ?thesis by (simp add: typed_mcp_es.state_at_unfold)
    qed
    have fin: "finite (covered_keys ?r)"
      using typed_mcp_es.vars_finite_of_terminates[OF solved(1)]
      by (simp add: dg_pipeline.result_def dg_pipeline.sol_vars_def)
    have tbl: "run_table (typed_mcp_es.solved_run_of ds as tglobal p sol) = ?r"
      using solved(2) by simp
    have "Lifted d \<in> report_states_at res v"
      unfolding res typed_es_report_def
      by (rule report_of_state_mem[OF _ inj_tmcp_ctx_key look[folded tbl]]) (simp only: tbl fin)
    with sd show ?thesis by blast
  qed
  then show ?thesis using that by blast
qed

subsection \<open>Rendering a typed report\<close>

text \<open>
  A typed report is rendered by \<^const>\<open>render_report\<close> with a renderer of its own: each
  active analysis shows a kind-tagged value per variable, the order analysis its facts,
  and an entry-state context the formal values of its active fields. Typed analyses keep
  every variable in a point's own state, so no edge reads or writes a global unknown.
\<close>

instantiation toplift :: (join_val) join_val
begin
fun vjoin_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "vjoin_toplift (TL a) (TL b) = TL (vjoin a b)"
| "vjoin_toplift _ _ = TTop"
instance ..
end

instantiation order_rel :: (type) join_val
begin
definition vjoin_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "vjoin_order_rel = sup"
instance ..
end

datatype typed_value =
    Typed_Interval_Value "ivl kd"
  | Typed_Congruence_Value "congruence kd"
  | Typed_Int_Value "int_tuple kd"
  | Typed_Sign_Value "sign kd"
  | Typed_Parity_Value "parity kd"
  | Typed_Order_Value "(vname \<times> vname) list option"

fun string_of_typed_value :: "typed_value \<Rightarrow> String.literal" where
  "string_of_typed_value (Typed_Interval_Value v) = to_string v"
| "string_of_typed_value (Typed_Congruence_Value v) = to_string v"
| "string_of_typed_value (Typed_Int_Value v) = to_string v"
| "string_of_typed_value (Typed_Sign_Value v) = to_string v"
| "string_of_typed_value (Typed_Parity_Value v) = to_string v"
| "string_of_typed_value (Typed_Order_Value v) = order_view_string v"

text \<open>A variable is shown by its name, qualified by its procedure when it is local.\<close>

fun var_label :: "var_id \<Rightarrow> vname" where
  "var_label (GlobalId x) = x"
| "var_label (ScopedId f x) = f + STR ''::'' + x"
| "var_label (ReturnId f) = f + STR ''::return''"
| "var_label ReturnVar = STR ''return''"

definition tfield_view ::
    "('a kd \<Rightarrow> typed_value) \<Rightarrow> var_id list \<Rightarrow> 'a tabs toplift lifted \<Rightarrow> typed_value field_state" where
  "tfield_view mk vars d =
     Field_Store (map (\<lambda>x. (var_label x, mk (case d of Bot \<Rightarrow> KBot | Lifted TTop \<Rightarrow> KTop
                                                  | Lifted (TL \<sigma>) \<Rightarrow> \<sigma> x))) vars)"

definition order_field_view :: "var_id order_rel lifted \<Rightarrow> typed_value field_state" where
  "order_field_view d =
     Field_Whole (Typed_Order_Value (case d of
        Lifted (OFacts ps) \<Rightarrow> Some (map (\<lambda>(a, b). (var_label a, var_label b)) (sorted_list_of_set ps))
      | _ \<Rightarrow> None))"

definition typed_render ::
    "typed_domain list \<Rightarrow> var_id list \<Rightarrow> tmcp_val \<Rightarrow> (typed_domain, typed_value) analysis_view" where
  "typed_render as vars v = map (\<lambda>a. (a, case a of
       Typed_Interval \<Rightarrow> tfield_view Typed_Interval_Value vars (tslot1 v)
     | Typed_Congruence \<Rightarrow> tfield_view Typed_Congruence_Value vars (tslot2 v)
     | Typed_Int \<Rightarrow> tfield_view Typed_Int_Value vars (tslot3 v)
     | Typed_Sign \<Rightarrow> tfield_view Typed_Sign_Value vars (tslot4 v)
     | Typed_Parity \<Rightarrow> tfield_view Typed_Parity_Value vars (tslot5 v)
     | Typed_Order \<Rightarrow> order_field_view (tslot6 v))) as"

fun typed_ctx_values :: "typed_domain list \<Rightarrow> tmcp_ctx \<Rightarrow> typed_value list" where
  "typed_ctx_values as (Product i (Product c (Product t (Product s (Product q u))))) =
     concat (map (\<lambda>a. case a of
         Typed_Interval \<Rightarrow> map Typed_Interval_Value i
       | Typed_Congruence \<Rightarrow> map Typed_Congruence_Value c
       | Typed_Int \<Rightarrow> map Typed_Int_Value t
       | Typed_Sign \<Rightarrow> map Typed_Sign_Value s
       | Typed_Parity \<Rightarrow> map Typed_Parity_Value q
       | Typed_Order \<Rightarrow> []) as)"

definition typed_renderer ::
    "(typed_domain list \<times> globals_rule \<times> typed_context, tmcp_ctx, tmcp_val, var_id, texp, unit,
      typed_domain, typed_value) report_renderer" where
  "typed_renderer =
     \<lparr> rr_view = (\<lambda>(as, _, _). typed_render (tactivation as)),
       rr_context = (\<lambda>(as, _, _). typed_ctx_values (tactivation as)),
       rr_footprints = \<lparr> fp_edge_reads = (\<lambda>_ _. []), fp_edge_writes = (\<lambda>_ _. []),
                         fp_call_reads = (\<lambda>_ _. []), fp_call_writes = (\<lambda>_ _. []) \<rparr> \<rparr>"


definition typed_render_report ::
    "(typed_value \<Rightarrow> 'v) \<Rightarrow> typed_report \<Rightarrow> (var_id, texp, unit, typed_domain, 'v) run_result" where
  "typed_render_report = render_report typed_renderer"

end
