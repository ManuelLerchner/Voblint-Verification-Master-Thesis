theory MCP_Analyses
  imports
    Analysis_Config
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_Analysis_Int.Int_Analyses"
    "Voblint_Analysis_Parity.Parity_Analyses"
    "Voblint_Analysis_Congruence.Congruence_Analyses"
    "Voblint_Framework.Local_Spec_Product"
    "Voblint_Framework.Check_Answer"
begin

section \<open>The state every registered analysis runs on\<close>

text \<open>
  Goblint's \<open>MCP\<close> keeps one state per activated analysis side by side. Voblint
  fixes the combined state once, with a field for every registered analysis,
  and lets the activation list choose which fields run. The fields sit in
  nested \<^typ>\<open>('a, 'b) analysis_product\<close>s, whose order, join, widening and
  narrowing are componentwise, so a field no active analysis touches stays
  what it started as and changes nothing the solver compares.

  A slot names the position of a field; the same five positions serve the
  solver's state and the published value.
\<close>

definition slot1 :: "('a, 'r) analysis_product \<Rightarrow> 'a" where
  "slot1 r = pleft r"

definition slot2 :: "('x, ('a, 'r) analysis_product) analysis_product \<Rightarrow> 'a" where
  "slot2 r = pleft (pright r)"

definition slot3 ::
  "('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product \<Rightarrow> 'a" where
  "slot3 r = pleft (pright (pright r))"

definition slot4 ::
  "('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a" where
  "slot4 r = pleft (pright (pright (pright r)))"

definition slot5 ::
  "('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a" where
  "slot5 r = pright (pright (pright (pright r)))"

definition set_slot1 :: "('a, 'r) analysis_product \<Rightarrow> 'a \<Rightarrow> ('a, 'r) analysis_product" where
  "set_slot1 r v = Product v (pright r)"

definition set_slot2 ::
  "('x, ('a, 'r) analysis_product) analysis_product \<Rightarrow> 'a
     \<Rightarrow> ('x, ('a, 'r) analysis_product) analysis_product" where
  "set_slot2 r v = Product (pleft r) (Product v (pright (pright r)))"

definition set_slot3 ::
  "('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product \<Rightarrow> 'a
     \<Rightarrow> ('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product" where
  "set_slot3 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product v (pright (pright (pright r)))))"

definition set_slot4 ::
  "('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a
   \<Rightarrow> ('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product" where
  "set_slot4 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
       (Product v (pright (pright (pright (pright r)))))))"

definition set_slot5 ::
  "('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a
   \<Rightarrow> ('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product" where
  "set_slot5 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
       (Product (pleft (pright (pright (pright r)))) v)))"

lemmas slot_defs [simp] = slot1_def slot2_def slot3_def slot4_def slot5_def
  set_slot1_def set_slot2_def set_slot3_def set_slot4_def set_slot5_def

lemma pleft_pright_bot [simp]:
  "pleft (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  "pright (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  by (simp_all add: bot_analysis_product_def)

lemma pleft_pright_mono:
  "p \<le> q \<Longrightarrow> pleft p \<le> pleft q" "p \<le> q \<Longrightarrow> pright p \<le> pright q"
  by (simp_all add: less_eq_analysis_product_def)

type_synonym mcp_st =
  "(sign exec_dg_st lifted,
    (ivl exec_dg_st lifted,
     (int_dom exec_dg_st lifted,
      (parity exec_dg_st lifted, congruence exec_dg_st lifted) analysis_product)
     analysis_product) analysis_product) analysis_product"

type_synonym mcp_val =
  "(sign abs_state lifted,
    (ivl abs_state lifted,
     (int_dom abs_state lifted,
      (parity abs_state lifted, congruence abs_state lifted) analysis_product)
     analysis_product) analysis_product) analysis_product"

subsection \<open>Each analysis on its own field\<close>

text \<open>
  An analysis runs as its executable component on its own field, through the
  lens of \<^const>\<open>lift_get\<close> and \<^const>\<open>lift_put\<close>.
\<close>

fun mcp_component_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_component_of \<G> p Sign_Analysis = lens_of (lift_get slot1) (lift_put set_slot1)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (sign_tf_st_for \<G>) (sign_enter_st_for \<G>))"
| "mcp_component_of \<G> p Interval_Analysis = lens_of (lift_get slot2) (lift_put set_slot2)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (ivl_tf_st_for \<G>) (ivl_enter_st_for \<G>))"
| "mcp_component_of \<G> p Int_Analysis = lens_of (lift_get slot3) (lift_put set_slot3)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (int_tf_st_for Refine_Fixpoint \<G>) (int_dom_enter_st_for Refine_Fixpoint \<G>))"
| "mcp_component_of \<G> p Parity_Analysis = lens_of (lift_get slot4) (lift_put set_slot4)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (parity_tf_st_for \<G>) (parity_enter_st_for \<G>))"
| "mcp_component_of \<G> p Congruence_Analysis = lens_of (lift_get slot5) (lift_put set_slot5)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (congruence_tf_st_for \<G>) (congruence_enter_st_for \<G>))"

text \<open>What each field describes, read through the analysis's own readback.\<close>

fun part_gamma :: "(vname \<Rightarrow> bool) \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted \<Rightarrow> store set" where
  "part_gamma \<G> Sign_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot1 x)))"
| "part_gamma \<G> Interval_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot2 x)))"
| "part_gamma \<G> Int_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot3 x)))"
| "part_gamma \<G> Parity_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot4 x)))"
| "part_gamma \<G> Congruence_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot5 x)))"

lemma field_component_sound:
  fixes f :: "'r::{semilattice_sup, order_bot} \<Rightarrow> 'c::semilattice_sup lifted"
  assumes sound: "mcp_component_sound \<G> (\<lambda>d. gamma_point (map_lift R d)) cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = Bot"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "mcp_component_sound \<G> (\<lambda>x. gamma_point (map_lift R (lift_get f x)))
           (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule lens_of_sound[OF sound, where get = "lift_get f"])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])


lemma mcp_component_of_sound:
  "mcp_component_sound (declared_global p) (part_gamma (declared_global p) a)
     (mcp_component_of (declared_global p) p a)"
  by (cases a; simp only: part_gamma.simps mcp_component_of.simps;
      rule field_component_sound[OF sign_rule.comp_sound]
        field_component_sound[OF interval_rule.comp_sound]
        field_component_sound[OF int_rule.comp_sound]
        field_component_sound[OF parity_rule.comp_sound]
        field_component_sound[OF congruence_rule.comp_sound];
      auto simp: less_eq_analysis_product_def)

lemma field_frame:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = Bot"
  shows "mcp_frame (lens_of (lift_get f1) (lift_put u1) cmp)
           (\<lambda>x. gamma_point (map_lift R (lift_get f2 x)))"
  unfolding mcp_frame_def lens_of_def by (auto simp: lift_get_put_other[OF assms])

lemma mcp_component_of_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (mcp_component_of \<G> p a) (part_gamma \<G> b)"
  by (cases a; cases b; simp only: part_gamma.simps mcp_component_of.simps;
      simp; rule field_frame; simp)

lemma single_entry_exec_component:
  "single_entry (exec_component \<G> empty_pred tf_st enter_st)"
  by (simp add: single_entry_def exec_component_def lens_component_def)

lemma single_entry_mcp_component_of: "single_entry (mcp_component_of \<G> p a)"
  by (cases a) (auto intro!: single_entry_lens_of single_entry_exec_component lift_put_get)

subsection \<open>The active analyses, run as one\<close>

text \<open>
  The combined state is unreachable as soon as one active analysis says its
  field is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close> when one component does. The
  normalization changes no concretization: a field that describes nothing
  empties the intersection already.
\<close>

fun part_live :: "analysis_domain \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "part_live Sign_Analysis r = (slot1 r \<noteq> Bot)"
| "part_live Interval_Analysis r = (slot2 r \<noteq> Bot)"
| "part_live Int_Analysis r = (slot3 r \<noteq> Bot)"
| "part_live Parity_Analysis r = (slot4 r \<noteq> Bot)"
| "part_live Congruence_Analysis r = (slot5 r \<noteq> Bot)"

definition mcp_norm :: "analysis_domain list \<Rightarrow> mcp_st lifted \<Rightarrow> mcp_st lifted" where
  "mcp_norm as x =
     (case x of Bot \<Rightarrow> Bot | Lifted r \<Rightarrow> if list_all (\<lambda>a. part_live a r) as then x else Bot)"

lemma part_gamma_Bot [simp]: "part_gamma \<G> a Bot = {}"
  by (cases a) simp_all

lemma part_gamma_dead: "\<not> part_live a r \<Longrightarrow> part_gamma \<G> a (Lifted r) = {}"
  by (cases a) simp_all

lemma mcp_gamma_norm:
  "mcp_gamma (map (part_gamma \<G>) as) (mcp_norm as x) = mcp_gamma (map (part_gamma \<G>) as) x"
  by (cases x) (auto simp: mcp_norm_def mcp_gamma_def list_all_iff dest: part_gamma_dead)

definition mcp_comp ::
  "analysis_domain list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_comp as \<G> p = map_component (mcp_norm as) (mcp_combine (map (mcp_component_of \<G> p) as))"

theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "mcp_component_sound (declared_global p)
           (mcp_gamma (map (part_gamma (declared_global p)) as))
           (mcp_comp as (declared_global p) p)"
proof -
  let ?gcs = "map (\<lambda>a. (part_gamma (declared_global p) a,
                         mcp_component_of (declared_global p) p a)) as"
  have "mcp_component_sound (declared_global p) (mcp_gamma (map fst ?gcs))
          (mcp_combine (map snd ?gcs))"
    by (rule mcp_combine_sound)
       (auto simp: mcp_component_of_sound assms
         intro!: mcp_independent_map mcp_component_of_frame)
  then show ?thesis
    unfolding mcp_comp_def
    by (intro map_component_sound) (simp_all add: comp_def mcp_gamma_norm)
qed

lemma single_entry_mcp_comp: "as \<noteq> [] \<Longrightarrow> single_entry (mcp_comp as \<G> p)"
  unfolding mcp_comp_def
  by (intro single_entry_map_component single_entry_mcp_combine)
     (auto simp: single_entry_mcp_component_of)

subsection \<open>What the combined state publishes\<close>

text \<open>
  A solved combined state is published field by field, each through its
  analysis's own readback. Its concretization is the intersection over the
  active fields, and a check is decided from the meet of the active analyses'
  answers.
\<close>

definition mcp_rd :: "(vname \<Rightarrow> bool) \<Rightarrow> mcp_st \<Rightarrow> mcp_val" where
  "mcp_rd \<G> r =
     Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot1 r))
       (Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot2 r))
         (Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot3 r))
           (Product (map_lift (fun_of_resolved_st_q_for \<G>) (slot4 r))
             (map_lift (fun_of_resolved_st_q_for \<G>) (slot5 r)))))"

fun val_gamma :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "val_gamma Sign_Analysis v = gamma_point (slot1 v)"
| "val_gamma Interval_Analysis v = gamma_point (slot2 v)"
| "val_gamma Int_Analysis v = gamma_point (slot3 v)"
| "val_gamma Parity_Analysis v = gamma_point (slot4 v)"
| "val_gamma Congruence_Analysis v = gamma_point (slot5 v)"

definition mcp_gamma_v :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "mcp_gamma_v as v = (\<Inter>a \<in> set as. val_gamma a v)"

lemma part_gamma_rd: "part_gamma \<G> a x = gamma_lift (val_gamma a) (map_lift (mcp_rd \<G>) x)"
  by (cases a; cases x) (simp_all add: mcp_rd_def)

lemma mcp_gamma_rd:
  "as \<noteq> [] \<Longrightarrow> mcp_gamma (map (part_gamma \<G>) as) x
                  = gamma_lift (mcp_gamma_v as) (map_lift (mcp_rd \<G>) x)"
  by (cases x) (auto simp: mcp_gamma_def mcp_gamma_v_def part_gamma_rd)

lemma mcp_gamma_v_bot: "as \<noteq> [] \<Longrightarrow> mcp_gamma_v as \<bottom> = {}"
proof -
  have "val_gamma a \<bottom> = {}" for a by (cases a) simp_all
  then show "as \<noteq> [] \<Longrightarrow> ?thesis" by (auto simp: mcp_gamma_v_def)
qed

fun part_empty :: "vname list \<Rightarrow> analysis_domain \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "part_empty gs Sign_Analysis r =
     (case slot1 r of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Interval_Analysis r =
     (case slot2 r of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Int_Analysis r =
     (case slot3 r of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Parity_Analysis r =
     (case slot4 r of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"
| "part_empty gs Congruence_Analysis r =
     (case slot5 r of Bot \<Rightarrow> True | Lifted st \<Rightarrow> resolved_st_q_is_bot_for gs st)"

definition mcp_emp :: "analysis_domain list \<Rightarrow> imp_prog \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "mcp_emp as p r = list_ex (\<lambda>a. part_empty (declared_global_vars p) a r) as"

fun val_empty :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> bool" where
  "val_empty Sign_Analysis v = (case slot1 v of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Interval_Analysis v =
     (case slot2 v of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Int_Analysis v = (case slot3 v of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Parity_Analysis v = (case slot4 v of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"
| "val_empty Congruence_Analysis v =
     (case slot5 v of Bot \<Rightarrow> True | Lifted st \<Rightarrow> is_empty_state st)"

definition mcp_empty_v :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> bool" where
  "mcp_empty_v as v = list_ex (\<lambda>a. val_empty a v) as"

lemma part_empty_rd:
  "part_empty (declared_global_vars p) a r = val_empty a (mcp_rd (declared_global p) r)"
  by (cases a)
     (simp_all add: mcp_rd_def
        resolved_st_q_is_bot_for_iff[where \<G> = "declared_global p", OF declared_global_iff]
        split: lifted.split)

lemma mcp_emp_rd: "mcp_emp as p r = mcp_empty_v as (mcp_rd (declared_global p) r)"
  by (simp add: mcp_emp_def mcp_empty_v_def part_empty_rd)

lemma val_empty_gamma: "val_empty a v \<Longrightarrow> val_gamma a v = {}"
  by (cases a) (auto split: lifted.splits dest: is_empty_state_gamma_state_empty)

lemma mcp_empty_v_gamma: "mcp_empty_v as v \<Longrightarrow> mcp_gamma_v as v = {}"
  by (auto simp: mcp_empty_v_def mcp_gamma_v_def list_ex_iff dest: val_empty_gamma)

fun val_answer :: "analysis_domain \<Rightarrow> mcp_val \<Rightarrow> query \<Rightarrow> answer" where
  "val_answer Sign_Analysis v q =
     (case slot1 v of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> sign_eval_answer st q)"
| "val_answer Interval_Analysis v q =
     (case slot2 v of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> interval_eval_answer st q)"
| "val_answer Int_Analysis v q =
     (case slot3 v of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> int_eval_answer st q)"
| "val_answer Parity_Analysis v q =
     (case slot4 v of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> parity_eval_answer st q)"
| "val_answer Congruence_Analysis v q =
     (case slot5 v of Bot \<Rightarrow> \<top> | Lifted st \<Rightarrow> congruence_eval_answer st q)"

definition mcp_answer :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> query \<Rightarrow> answer" where
  "mcp_answer as v q = fold (\<lambda>a r. r \<sqinter> val_answer a v q) as \<top>"

lemma val_answer_sound: "s \<in> val_gamma a v \<Longrightarrow> eval_holds q (val_answer a v q) s"
  by (cases a)
     (auto split: lifted.splits intro: sign_eval_answer_sound interval_eval_answer_sound
        int_eval_answer_sound parity_eval_answer_sound congruence_eval_answer_sound)

lemma mcp_answer_fold_sound:
  "\<forall>a \<in> set as. s \<in> val_gamma a v \<Longrightarrow> eval_holds q r s
   \<Longrightarrow> eval_holds q (fold (\<lambda>a r. r \<sqinter> val_answer a v q) as r) s"
  by (induction as arbitrary: r) (auto intro: eval_query.inf_sound val_answer_sound)

lemma mcp_answer_sound: "s \<in> mcp_gamma_v as v \<Longrightarrow> eval_holds q (mcp_answer as v q) s"
  unfolding mcp_answer_def mcp_gamma_v_def by (rule mcp_answer_fold_sound) auto

definition mcp_classify :: "analysis_domain list \<Rightarrow> exp \<Rightarrow> mcp_val \<Rightarrow> check_result" where
  "mcp_classify as = answer_check (mcp_answer as)"

lemma mcp_classify_proved:
  "mcp_classify as e v = Check_Proved \<Longrightarrow> s \<in> mcp_gamma_v as v \<Longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  unfolding mcp_classify_def by (erule answer_check_proved) (rule mcp_answer_sound)

lemma mcp_classify_refuted:
  "mcp_classify as e v = Check_Refuted \<Longrightarrow> s \<in> mcp_gamma_v as v
   \<Longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  unfolding mcp_classify_def by (erule answer_check_refuted) (rule mcp_answer_sound)

definition mcp_init :: mcp_st where
  "mcp_init =
     Product (Lifted cinit_sign_st) (Product (Lifted cinit_ivl_st)
       (Product (Lifted cinit_int_dom_st)
         (Product (Lifted cinit_parity_st) (Lifted cinit_congruence_st))))"

lemma mcp_init_sound:
  "cinit_stores (declared_global p) \<subseteq> mcp_gamma_v as (mcp_rd (declared_global p) mcp_init)"
proof -
  have "cinit_stores (declared_global p) \<subseteq> val_gamma a (mcp_rd (declared_global p) mcp_init)"
    for a
    using sign_rule.init_sound interval_rule.init_sound int_rule.init_sound
      parity_rule.init_sound congruence_rule.init_sound
    by (cases a) (simp_all add: mcp_init_def mcp_rd_def)
  then show ?thesis by (auto simp: mcp_gamma_v_def)
qed

text \<open>
  A caller activates a distinct, nonempty list of analyses. The registrations
  below take any list and run it as \<open>activation\<close> normalizes it, so they hold
  unconditionally; \<open>activation\<close> is the identity on every list a caller may
  pass.
\<close>

definition activation :: "analysis_domain list \<Rightarrow> analysis_domain list" where
  "activation as = (if as = [] then [Int_Analysis] else remdups as)"

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
  assumes "\<And>v ctx. seed v ctx \<noteq> gk0"
  shows "routed_dg_analysis (mcp_comp (activation as)) (mcp_emp (activation as)) mcp_rd mcp_init
    gk0 seed (TD_side_rule_Interp_solve r)
    (TD_side_upd_rule.solve_dom init_basic_ug_state (update_global_of r))
    \<bottom> (mcp_classify (activation as)) (mcp_gamma_v (activation as))
    (mcp_empty_v (activation as)) (TD_side_rule_Interp_solve_c r)"
proof (unfold_locales, goal_cases CompSound EnterSingle EmptyRd EmptyVSound SeedNe
    SolvePP SolveFin ClProved ClRefuted BotState Init DomC)
  case (CompSound p)
  have eq: "mcp_gamma (map (part_gamma (declared_global p)) (activation as))
      = (\<lambda>d. gamma_lift (mcp_gamma_v (activation as)) (map_lift (mcp_rd (declared_global p)) d))"
    by (rule ext) (rule mcp_gamma_rd[OF activation_ne])
  show ?case using mcp_comp_sound[of "activation as" p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF single_entry_mcp_comp[OF activation_ne],
        of as "declared_global p" p ci "(d, d)"]
    by (simp add: routed_dg_pipeline.entry_of_def)
next
  case (EmptyRd p s) show ?case by (rule mcp_emp_rd)
next
  case (EmptyVSound v) then show ?case by (rule mcp_empty_v_gamma)
next
  case (SeedNe v ctx) show ?case by (rule assms)
next
  case (SolvePP eqs x) then show ?case
    by (rule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (SolveFin eqs x) then show ?case by (rule TD_side_rule_Interp.finite_stabl_solve)
next
  case (ClProved e d s) then show ?case by (rule mcp_classify_proved)
next
  case (ClRefuted e d s) then show ?case by (rule mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp_gamma_v_bot[OF activation_ne])
next
  case (Init p) show ?case by (rule mcp_init_sound)
next
  case (DomC eqs x) then show ?case by (rule TD_side_rule_Interp.solve_dom_of_solve_c)
qed

subsection \<open>At the unit context\<close>

global_interpretation mcp_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd mcp_init
    "Analysis_Global ()" Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_upd_rule.solve_dom init_basic_ug_state (update_global_of r)"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as r
  by (rule mcp_routed_dg_analysis) simp

subsection \<open>At the entry-state context\<close>

text \<open>
  An activation is keyed by the values the active analyses give its formals
  on entry. The context has a list per field; a field no active analysis
  runs keys nothing.
\<close>

type_synonym mcp_ctx =
  "(sign list, (ivl list, (int_dom list, (parity list, congruence list) analysis_product)
     analysis_product) analysis_product) analysis_product"

definition mcp_formals_route ::
  "analysis_domain list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> mcp_ctx \<Rightarrow> mcp_st lifted
     \<Rightarrow> call_action \<Rightarrow> mcp_ctx" where
  "mcp_formals_route as \<G> u ctx d ca =
     Product
       (if Sign_Analysis \<in> set as then exec_formals_route \<G> u [] (lift_get slot1 d) ca else [])
       (Product
         (if Interval_Analysis \<in> set as
          then exec_formals_route \<G> u [] (lift_get slot2 d) ca else [])
         (Product
           (if Int_Analysis \<in> set as
            then exec_formals_route \<G> u [] (lift_get slot3 d) ca else [])
           (Product
             (if Parity_Analysis \<in> set as
              then exec_formals_route \<G> u [] (lift_get slot4 d) ca else [])
             (if Congruence_Analysis \<in> set as
              then exec_formals_route \<G> u [] (lift_get slot5 d) ca else []))))"

definition mcp_root_ctx :: mcp_ctx where
  "mcp_root_ctx = Product [] (Product [] (Product [] (Product [] [])))"

global_interpretation mcp_es_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd mcp_init
    "Analysis_Global ()" Activation_Seed "mcp_formals_route (activation as)" mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_upd_rule.solve_dom init_basic_ug_state (update_global_of r)"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as r
  by (rule mcp_routed_dg_analysis) simp

subsection \<open>At the call-string context\<close>

global_interpretation mcp_cs_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd mcp_init
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_upd_rule.solve_dom init_basic_ug_state (update_global_of r)"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as k r
  by (rule mcp_routed_dg_analysis) simp

end
