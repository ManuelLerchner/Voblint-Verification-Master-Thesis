theory MCP_Carrier
  imports
    "Voblint_CLI.Analysis_Config"
    "Voblint_CLI.Dispatch_Carrier"
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_Analysis_Parity.Parity_Analyses"
    "Voblint_Analysis_Int.Int_Analyses"
    "Voblint_Analysis_Congruence.Congruence_Analyses"
    "Voblint_Analysis_Relational.Rel_Order_Local"
    "Voblint_CLI.MCP_Field"
begin

section \<open>The combined state of the registered analyses\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Every registered analysis owns one field of the combined state, in manifest order.
  This theory names the analyses, lays out the fields, and states for each analysis
  how its field runs, what it describes, how it reads back and answers queries, and
  where it starts. Nothing here is proved beyond citing each analysis's own
  registration; the combination and its soundness are in \<open>MCP_Analyses\<close>.
\<close>

datatype analysis_domain =
    Sign_Analysis
  | Interval_Analysis
  | Parity_Analysis
  | Int_Analysis
  | Congruence_Analysis
  | Order_Analysis

subsection \<open>One value type wide enough for every analysis\<close>

text \<open>
  A run result crosses the dispatcher without its caller knowing which analysis
  produced it, so every published value in it has one type: a tagged union with one
  constructor per registered analysis. Each is rendered by its own analysis and listed
  by an injective key, so no printer decides which contexts are listed.
\<close>

datatype abstract_value =
    SignValue "sign"
  | IntervalValue "ivl"
  | ParityValue "parity"
  | IntDomValue "int_dom"
  | CongruenceValue "congruence"
  | OrderValue "(vname \<times> vname) list option"

fun string_of_abstract_value :: "abstract_value \<Rightarrow> String.literal" where
  "string_of_abstract_value (SignValue v) =
     to_string v"
| "string_of_abstract_value (IntervalValue v) =
     to_string v"
| "string_of_abstract_value (ParityValue v) =
     to_string v"
| "string_of_abstract_value (IntDomValue v) =
     to_string v"
| "string_of_abstract_value (CongruenceValue v) =
     to_string v"
| "string_of_abstract_value (OrderValue v) =
     order_view_string v"

fun abstract_value_key :: "abstract_value \<Rightarrow> order_key" where
  "abstract_value_key (SignValue v) =
     Key_List [Key_Int 0, sign_key v]"
| "abstract_value_key (IntervalValue v) =
     Key_List [Key_Int 1, ivl_key v]"
| "abstract_value_key (ParityValue v) =
     Key_List [Key_Int 2, parity_key v]"
| "abstract_value_key (IntDomValue v) =
     Key_List [Key_Int 3, int_dom_key v]"
| "abstract_value_key (CongruenceValue v) =
     Key_List [Key_Int 4, congruence_key v]"
| "abstract_value_key (OrderValue v) =
     Key_List [Key_Int 5, order_view_key v]"

lemma abstract_value_key_inject [simp]:
  "abstract_value_key a = abstract_value_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma inj_abstract_value_key: "inj abstract_value_key"
  by (rule injI) simp

subsection \<open>Fields\<close>

definition slot1 where
  "slot1 r = pleft r"

definition slot2 where
  "slot2 r = pleft (pright r)"

definition slot3 where
  "slot3 r = pleft (pright (pright r))"

definition slot4 where
  "slot4 r = pleft (pright (pright (pright r)))"

definition slot5 where
  "slot5 r = pleft (pright (pright (pright (pright r))))"

definition slot6 where
  "slot6 r = pright (pright (pright (pright (pright r))))"

definition set_slot1 where
  "set_slot1 r v = Product v (pright r)"

definition set_slot2 where
  "set_slot2 r v = Product (pleft r) (Product v (pright (pright r)))"

definition set_slot3 where
  "set_slot3 r v = Product (pleft r) (Product (pleft (pright r)) (Product v (pright
    (pright (pright r)))))"

definition set_slot4 where
  "set_slot4 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright
    (pright r))) (Product v (pright (pright (pright (pright r)))))))"

definition set_slot5 where
  "set_slot5 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright
    (pright r))) (Product (pleft (pright (pright (pright r)))) (Product v (pright (pright
    (pright (pright (pright r)))))))))"

definition set_slot6 where
  "set_slot6 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright
    (pright r))) (Product (pleft (pright (pright (pright r)))) (Product (pleft (pright
    (pright (pright (pright r))))) v))))"

lemmas slot_defs [simp] = slot1_def slot2_def slot3_def slot4_def slot5_def slot6_def
  set_slot1_def set_slot2_def set_slot3_def set_slot4_def set_slot5_def set_slot6_def

type_synonym mcp_st =
  "(sign exec_dg_st lifted, (ivl exec_dg_st lifted, (parity exec_dg_st lifted, (int_dom
    exec_dg_st lifted, (congruence exec_dg_st lifted, relc) analysis_product)
    analysis_product) analysis_product) analysis_product) analysis_product"

type_synonym mcp_val =
  "(sign abs_state lifted, (ivl abs_state lifted, (parity abs_state lifted, (int_dom
    abs_state lifted, (congruence abs_state lifted, relc) analysis_product)
    analysis_product) analysis_product) analysis_product) analysis_product"

type_synonym mcp_ctx =
  "(sign list, (ivl list, (parity list, (int_dom list, (congruence list, unit list)
    analysis_product) analysis_product) analysis_product) analysis_product)
    analysis_product"

subsection \<open>Each analysis on its own field\<close>

fun mcp_component_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_component_of \<G> p Sign_Analysis =
     lens_of (lift_get slot1) (lift_put set_slot1) (ask_assign (exec_component \<G>
       (resolved_st_q_is_bot_for (declared_global_vars p)) (sign_tf_st_for \<G>)
       (sign_enter_st_for \<G>)))"
| "mcp_component_of \<G> p Interval_Analysis =
     lens_of (lift_get slot2) (lift_put set_slot2) (ask_assign (exec_component \<G>
       (resolved_st_q_is_bot_for (declared_global_vars p)) (ivl_tf_st_for \<G>)
       (ivl_enter_st_for \<G>)))"
| "mcp_component_of \<G> p Parity_Analysis =
     lens_of (lift_get slot3) (lift_put set_slot3) (ask_assign (exec_component \<G>
       (resolved_st_q_is_bot_for (declared_global_vars p)) (parity_tf_st_for \<G>)
       (parity_enter_st_for \<G>)))"
| "mcp_component_of \<G> p Int_Analysis =
     lens_of (lift_get slot4) (lift_put set_slot4) (ask_assign (exec_component \<G>
       (resolved_st_q_is_bot_for (declared_global_vars p)) (int_tf_st_for Refine_Fixpoint
       \<G>) (int_dom_enter_st_for Refine_Fixpoint \<G>)))"
| "mcp_component_of \<G> p Congruence_Analysis =
     lens_of (lift_get slot5) (lift_put set_slot5) (ask_assign (exec_component \<G>
       (resolved_st_q_is_bot_for (declared_global_vars p)) (congruence_tf_st_for \<G>)
       (congruence_enter_st_for \<G>)))"
| "mcp_component_of \<G> p Order_Analysis =
     lens_of (lift_get slot6) (lift_put set_slot6) (order_component (program_vars p))"

fun part_gamma :: "(vname \<Rightarrow> bool) \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted \<Rightarrow> store set" where
  "part_gamma \<G> Sign_Analysis =
     (\<lambda>x. \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot1 x)\<rbrakk>\<^sub>\<bottom>)"
| "part_gamma \<G> Interval_Analysis =
     (\<lambda>x. \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot2 x)\<rbrakk>\<^sub>\<bottom>)"
| "part_gamma \<G> Parity_Analysis =
     (\<lambda>x. \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot3 x)\<rbrakk>\<^sub>\<bottom>)"
| "part_gamma \<G> Int_Analysis =
     (\<lambda>x. \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot4 x)\<rbrakk>\<^sub>\<bottom>)"
| "part_gamma \<G> Congruence_Analysis =
     (\<lambda>x. \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot5 x)\<rbrakk>\<^sub>\<bottom>)"
| "part_gamma \<G> Order_Analysis =
     (\<lambda>x. \<lbrakk>(lift_get slot6 x)\<rbrakk>)"

fun part_live :: "analysis_domain \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "part_live Sign_Analysis r =
     (slot1 r \<noteq> \<bottom>)"
| "part_live Interval_Analysis r =
     (slot2 r \<noteq> \<bottom>)"
| "part_live Parity_Analysis r =
     (slot3 r \<noteq> \<bottom>)"
| "part_live Int_Analysis r =
     (slot4 r \<noteq> \<bottom>)"
| "part_live Congruence_Analysis r =
     (slot5 r \<noteq> \<bottom>)"
| "part_live Order_Analysis r =
     (slot6 r \<noteq> \<bottom>)"

fun part_empty :: "vname list \<Rightarrow> analysis_domain \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "part_empty gs Sign_Analysis r =
     (case (slot1 r) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Interval_Analysis r =
     (case (slot2 r) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Parity_Analysis r =
     (case (slot3 r) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Int_Analysis r =
     (case (slot4 r) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Congruence_Analysis r =
     (case (slot5 r) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Order_Analysis r =
     ((slot6 r) = RelBot)"

subsection \<open>What each field publishes\<close>

definition mcp_rd :: "(vname \<Rightarrow> bool) \<Rightarrow> mcp_st \<Rightarrow> mcp_val" where
  "mcp_rd \<G> r = Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot1 r)) (Product
    (map_lift (fun_of_resolved_st_q_for \<G>) (slot2 r)) (Product (map_lift
    (fun_of_resolved_st_q_for \<G>) (slot3 r)) (Product (map_lift (fun_of_resolved_st_q_for
    \<G>) (slot4 r)) (Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot5 r)) (slot6
    r)))))"

fun val_gamma :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "val_gamma Sign_Analysis v =
     \<lbrakk>(slot1 v)\<rbrakk>\<^sub>\<bottom>"
| "val_gamma Interval_Analysis v =
     \<lbrakk>(slot2 v)\<rbrakk>\<^sub>\<bottom>"
| "val_gamma Parity_Analysis v =
     \<lbrakk>(slot3 v)\<rbrakk>\<^sub>\<bottom>"
| "val_gamma Int_Analysis v =
     \<lbrakk>(slot4 v)\<rbrakk>\<^sub>\<bottom>"
| "val_gamma Congruence_Analysis v =
     \<lbrakk>(slot5 v)\<rbrakk>\<^sub>\<bottom>"
| "val_gamma Order_Analysis v =
     \<lbrakk>(slot6 v)\<rbrakk>"

definition mcp_gamma_v :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "mcp_gamma_v as v = (\<Inter>a \<in> set as. val_gamma a v)"

fun val_empty :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> bool" where
  "val_empty Sign_Analysis v =
     (case (slot1 v) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Interval_Analysis v =
     (case (slot2 v) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Parity_Analysis v =
     (case (slot3 v) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Int_Analysis v =
     (case (slot4 v) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Congruence_Analysis v =
     (case (slot5 v) of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Order_Analysis v =
     ((slot6 v) = RelBot)"

fun val_answer :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> query \<Rightarrow> answer" where
  "val_answer Sign_Analysis v q =
     (case (slot1 v) of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> sign_eval_answer st q)"
| "val_answer Interval_Analysis v q =
     (case (slot2 v) of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> interval_eval_answer st q)"
| "val_answer Parity_Analysis v q =
     (case (slot3 v) of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> parity_eval_answer st q)"
| "val_answer Int_Analysis v q =
     (case (slot4 v) of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> int_eval_answer st q)"
| "val_answer Congruence_Analysis v q =
     (case (slot5 v) of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> congruence_eval_answer st q)"
| "val_answer Order_Analysis v q =
     rel_qry (slot6 v) q"

fun field_of ::
  "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> vname list \<Rightarrow> abstract_value field_state" where
  "field_of Sign_Analysis v vars =
     Field_Store (map (\<lambda>x. (x, SignValue (case (slot1 v) of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st x)))
       vars)"
| "field_of Interval_Analysis v vars =
     Field_Store (map (\<lambda>x. (x, IntervalValue (case (slot2 v) of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st
       x))) vars)"
| "field_of Parity_Analysis v vars =
     Field_Store (map (\<lambda>x. (x, ParityValue (case (slot3 v) of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st
       x))) vars)"
| "field_of Int_Analysis v vars =
     Field_Store (map (\<lambda>x. (x, IntDomValue (case (slot4 v) of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st
       x))) vars)"
| "field_of Congruence_Analysis v vars =
     Field_Store (map (\<lambda>x. (x, CongruenceValue (case (slot5 v) of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st
       x))) vars)"
| "field_of Order_Analysis v vars =
     Field_Whole (OrderValue (order_pairs (slot6 v)))"

subsection \<open>Where each field starts, and what it keys a callee by\<close>

text \<open>
  The entry state starts every active field at its analysis's own entry state and
  every other field at its bottom. A field no active analysis runs is never read, and
  keeping it at bottom makes the solver's joins, widenings and comparisons on it
  constant-time. Under the entry-state policy a callee is keyed by what the active
  fields key it by; a field no active analysis runs keys nothing.
\<close>

definition mcp_init :: "analysis_domain list \<Rightarrow> mcp_st" where
  "mcp_init as = Product (if Sign_Analysis \<in> set as then (Lifted cinit_sign_st) else \<bottom>)
    (Product (if Interval_Analysis \<in> set as then (Lifted cinit_ivl_st) else \<bottom>) (Product
    (if Parity_Analysis \<in> set as then (Lifted cinit_parity_st) else \<bottom>) (Product (if
    Int_Analysis \<in> set as then (Lifted cinit_int_dom_st) else \<bottom>) (Product (if
    Congruence_Analysis \<in> set as then (Lifted cinit_congruence_st) else \<bottom>) (if
    Order_Analysis \<in> set as then top_relc else \<bottom>)))))"

definition mcp_formals_route ::
  "analysis_domain list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> mcp_ctx \<Rightarrow> mcp_st lifted
     \<Rightarrow> call_action \<Rightarrow> mcp_ctx" where
  "mcp_formals_route as \<G> u ctx d ca = Product (if Sign_Analysis \<in> set as then
    exec_formals_route \<G> u [] (lift_get slot1 d) ca else []) (Product (if
    Interval_Analysis \<in> set as then exec_formals_route \<G> u [] (lift_get slot2 d) ca else
    []) (Product (if Parity_Analysis \<in> set as then exec_formals_route \<G> u [] (lift_get
    slot3 d) ca else []) (Product (if Int_Analysis \<in> set as then exec_formals_route \<G> u []
    (lift_get slot4 d) ca else []) (Product (if Congruence_Analysis \<in> set as then
    exec_formals_route \<G> u [] (lift_get slot5 d) ca else []) (if Order_Analysis \<in> set as
    then [] else [])))))"

definition mcp_root_ctx :: mcp_ctx where
  "mcp_root_ctx = Product [] (Product [] (Product [] (Product [] (Product [] []))))"

fun ctx_values :: "analysis_domain \<Rightarrow> mcp_ctx \<Rightarrow> abstract_value list" where
  "ctx_values Sign_Analysis ctx =
     map SignValue (slot1 ctx)"
| "ctx_values Interval_Analysis ctx =
     map IntervalValue (slot2 ctx)"
| "ctx_values Parity_Analysis ctx =
     map ParityValue (slot3 ctx)"
| "ctx_values Int_Analysis ctx =
     map IntDomValue (slot4 ctx)"
| "ctx_values Congruence_Analysis ctx =
     map CongruenceValue (slot5 ctx)"
| "ctx_values Order_Analysis ctx =
     []"

subsection \<open>What each analysis's registration supplies\<close>

lemma mcp_component_of_sound:
  "mcp_component_sound (declared_global p) (part_gamma (declared_global p) a)
     (mcp_component_of (declared_global p) p a)"
  by (cases a; simp only: part_gamma.simps mcp_component_of.simps;
      rule field_component_sound[OF ask_assign_sound[OF sign_rule.comp_sound]]
        field_component_sound[OF ask_assign_sound[OF interval_rule.comp_sound]]
        field_component_sound[OF ask_assign_sound[OF parity_rule.comp_sound]]
        field_component_sound[OF ask_assign_sound[OF int_rule.comp_sound]]
        field_component_sound[OF ask_assign_sound[OF congruence_rule.comp_sound]]
        field_component_sound[OF order_component_sound];
      auto simp: less_eq_analysis_product_def)

lemma single_entry_mcp_component_of: "single_entry (mcp_component_of \<G> p a)"
  by (cases a) (auto intro!: single_entry_lens_of lift_put_get single_entry_ask_assign[OF
    single_entry_exec_component] single_entry_order_component)

lemma mcp_component_of_silent:
  "a \<in> {Sign_Analysis, Interval_Analysis, Parity_Analysis, Int_Analysis, Congruence_Analysis}
     \<Longrightarrow> mc_query (mcp_component_of \<G> p a) A x q = \<top>"
  by (cases a) (simp_all add: lens_of_def ask_assign_def exec_component_def lens_component_def)

lemma mcp_init_sound:
  "cinit_stores (declared_global p)
     \<subseteq> mcp_gamma_v as (mcp_rd (declared_global p) (mcp_init as))"
proof -
  have "cinit_stores (declared_global p)
          \<subseteq> val_gamma a (mcp_rd (declared_global p) (mcp_init as))"
    if "a \<in> set as" for a
    by (cases a)
       (use that sign_rule.init_sound interval_rule.init_sound parity_rule.init_sound
         int_rule.init_sound congruence_rule.init_sound in \<open>simp_all add: mcp_init_def
         mcp_rd_def\<close>)
  then show ?thesis by (auto simp: mcp_gamma_v_def)
qed

lemma val_answer_sound: "s \<in> val_gamma a v \<Longrightarrow> eval_holds q (val_answer a v q) s"
  by (cases a)
     (auto split: lifted.splits intro: sign_eval_answer_sound interval_eval_answer_sound
       parity_eval_answer_sound int_eval_answer_sound congruence_eval_answer_sound
       rel_qry_sound)

end
