theory MCP_Carrier
  imports Analysis_Config "Voblint_Framework.MCP_Registry" "Voblint_Framework.Local_Spec_Product"
begin

section \<open>The combined state of the typed analyses\<close>

text \<open>
  Every typed analysis owns one field of the combined state, as in Goblint's MCP, and
  the typed analyses form a \<^locale>\<open>mcp_registry\<close> over the
  typed language. A non-relational field runs the typed component and answers through
  its evaluator, which may ask the channel about operands; the order field runs the
  order component and answers comparisons from its facts.
\<close>

subsection \<open>Fields\<close>

text \<open>Int has one field per refinement mode, each holding the product at that mode.\<close>

type_synonym mcp_st =
  "(ivl tst lifted, (congruence tst lifted,
    ((int_never int_tuple tst lifted, (int_once int_tuple tst lifted,
      int_fixpoint int_tuple tst lifted) analysis_product) analysis_product,
    (sign tst lifted, (parity tst lifted, var_id order_rel lifted)
    analysis_product) analysis_product) analysis_product) analysis_product) analysis_product"

type_synonym mcp_val =
  "(ivl tabs lifted, (congruence tabs lifted,
    ((int_never int_tuple tabs lifted, (int_once int_tuple tabs lifted,
      int_fixpoint int_tuple tabs lifted) analysis_product) analysis_product,
    (sign tabs lifted, (parity tabs lifted, var_id order_rel lifted)
    analysis_product) analysis_product) analysis_product) analysis_product) analysis_product"

definition slot1 where "slot1 r = pleft r"
definition slot2 where "slot2 r = pleft (pright r)"
definition slot3 where "slot3 r = pleft (pright (pright r))"
definition slot4 where "slot4 r = pleft (pright (pright (pright r)))"
definition slot5 where "slot5 r = pleft (pright (pright (pright (pright r))))"
definition slot6 where "slot6 r = pright (pright (pright (pright (pright r))))"
definition slot3n where "slot3n r = pleft (slot3 r)"
definition slot3o where "slot3o r = pleft (pright (slot3 r))"
definition slot3f where "slot3f r = pright (pright (slot3 r))"

definition set_slot1 where "set_slot1 r v = Product v (pright r)"
definition set_slot2 where "set_slot2 r v = Product (pleft r) (Product v (pright (pright r)))"
definition set_slot3 where
  "set_slot3 r v = Product (pleft r) (Product (pleft (pright r))
     (Product v (pright (pright (pright r)))))"
definition set_slot4 where
  "set_slot4 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product v (pright (pright (pright (pright r)))))))"
definition set_slot5 where
  "set_slot5 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product (pleft (pright (pright (pright r)))) (Product v (pright (pright (pright (pright (pright r)))))))))"
definition set_slot6 where
  "set_slot6 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product (pleft (pright (pright (pright r)))) (Product (pleft (pright (pright (pright (pright r))))) v))))"
definition set_slot3n where "set_slot3n r v = set_slot3 r (Product v (pright (slot3 r)))"
definition set_slot3o where
  "set_slot3o r v = set_slot3 r (Product (slot3n r) (Product v (slot3f r)))"
definition set_slot3f where
  "set_slot3f r v = set_slot3 r (Product (slot3n r) (Product (slot3o r) v))"

lemmas slot_defs [simp] = slot1_def slot2_def slot3_def slot4_def slot5_def slot6_def
  slot3n_def slot3o_def slot3f_def
  set_slot1_def set_slot2_def set_slot3_def set_slot4_def set_slot5_def set_slot6_def
  set_slot3n_def set_slot3o_def set_slot3f_def

definition mcp_rd :: "(var_id \<Rightarrow> bool) \<Rightarrow> mcp_st \<Rightarrow> mcp_val" where
  "mcp_rd \<G> r =
     Product (map_lift (default_st_to_fun \<G>) (slot1 r))
     (Product (map_lift (default_st_to_fun \<G>) (slot2 r))
     (Product (Product (map_lift (default_st_to_fun \<G>) (slot3n r))
        (Product (map_lift (default_st_to_fun \<G>) (slot3o r))
                 (map_lift (default_st_to_fun \<G>) (slot3f r))))
     (Product (map_lift (default_st_to_fun \<G>) (slot4 r))
     (Product (map_lift (default_st_to_fun \<G>) (slot5 r)) (slot6 r)))))"

subsection \<open>Each analysis on its own field\<close>

text \<open>Each selectable analysis runs its own specification on one slot of the carrier,
  through a lens that reads and writes that slot alone; \<open>val_gamma\<close> reads the
  stores the slot denotes.\<close>

definition field ::
  "sem_conf \<Rightarrow> kenv \<Rightarrow> imp_prog \<Rightarrow> analysis \<Rightarrow> mcp_st lifted local_spec" where
  "field sem \<kappa> p a = (case a of
      Interval \<Rightarrow> lens_of (lift_get slot1) (lift_put set_slot1) (nonrel_exec_spec sem \<kappa>)
    | Congruence \<Rightarrow> lens_of (lift_get slot2) (lift_put set_slot2) (nonrel_exec_spec sem \<kappa>)
    | Ana_Int Refine_Never \<Rightarrow> lens_of (lift_get slot3n) (lift_put set_slot3n) (nonrel_exec_spec sem \<kappa>)
    | Ana_Int Refine_Once \<Rightarrow> lens_of (lift_get slot3o) (lift_put set_slot3o) (nonrel_exec_spec sem \<kappa>)
    | Ana_Int Refine_Fixpoint \<Rightarrow> lens_of (lift_get slot3f) (lift_put set_slot3f) (nonrel_exec_spec sem \<kappa>)
    | Sign \<Rightarrow> lens_of (lift_get slot4) (lift_put set_slot4) (nonrel_exec_spec sem \<kappa>)
    | Parity \<Rightarrow> lens_of (lift_get slot5) (lift_put set_slot5) (nonrel_exec_spec sem \<kappa>)
    | Order \<Rightarrow> lens_of (lift_get slot6) (lift_put set_slot6) (ord_spec \<kappa> (ord_vars p)))"

fun val_gamma :: "kenv \<Rightarrow> analysis \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "val_gamma \<kappa> Interval v = gamma_lift (gamma_tabs \<kappa>) (slot1 v)"
| "val_gamma \<kappa> Congruence v = gamma_lift (gamma_tabs \<kappa>) (slot2 v)"
| "val_gamma \<kappa> (Ana_Int Refine_Never) v = gamma_lift (gamma_tabs \<kappa>) (slot3n v)"
| "val_gamma \<kappa> (Ana_Int Refine_Once) v = gamma_lift (gamma_tabs \<kappa>) (slot3o v)"
| "val_gamma \<kappa> (Ana_Int Refine_Fixpoint) v = gamma_lift (gamma_tabs \<kappa>) (slot3f v)"
| "val_gamma \<kappa> Sign v = gamma_lift (gamma_tabs \<kappa>) (slot4 v)"
| "val_gamma \<kappa> Parity v = gamma_lift (gamma_tabs \<kappa>) (slot5 v)"
| "val_gamma \<kappa> Order v = gamma_ord_lift \<kappa> (slot6 v)"

fun live :: "analysis \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "live Interval r = (slot1 r \<noteq> Bot)"
| "live Congruence r = (slot2 r \<noteq> Bot)"
| "live (Ana_Int Refine_Never) r = (slot3n r \<noteq> Bot)"
| "live (Ana_Int Refine_Once) r = (slot3o r \<noteq> Bot)"
| "live (Ana_Int Refine_Fixpoint) r = (slot3f r \<noteq> Bot)"
| "live Sign r = (slot4 r \<noteq> Bot)"
| "live Parity r = (slot5 r \<noteq> Bot)"
| "live Order r = (slot6 r \<noteq> Bot)"

definition t_lift_empty :: "'a::kind_int_domain tabs lifted \<Rightarrow> bool" where
  "t_lift_empty x = (case x of Bot \<Rightarrow> True | Lifted d \<Rightarrow> t_empty d)"

fun val_empty :: "analysis \<Rightarrow> mcp_val \<Rightarrow> bool" where
  "val_empty Interval v = t_lift_empty (slot1 v)"
| "val_empty Congruence v = t_lift_empty (slot2 v)"
| "val_empty (Ana_Int Refine_Never) v = t_lift_empty (slot3n v)"
| "val_empty (Ana_Int Refine_Once) v = t_lift_empty (slot3o v)"
| "val_empty (Ana_Int Refine_Fixpoint) v = t_lift_empty (slot3f v)"
| "val_empty Sign v = t_lift_empty (slot4 v)"
| "val_empty Parity v = t_lift_empty (slot5 v)"
| "val_empty Order v = (slot6 v = Bot)"

definition st_lift_empty :: "'a::kind_int_domain tst lifted \<Rightarrow> bool" where
  "st_lift_empty x = (case x of Bot \<Rightarrow> True | Lifted d \<Rightarrow> st_is_bot d)"

fun field_empty :: "analysis \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "field_empty Interval r = st_lift_empty (slot1 r)"
| "field_empty Congruence r = st_lift_empty (slot2 r)"
| "field_empty (Ana_Int Refine_Never) r = st_lift_empty (slot3n r)"
| "field_empty (Ana_Int Refine_Once) r = st_lift_empty (slot3o r)"
| "field_empty (Ana_Int Refine_Fixpoint) r = st_lift_empty (slot3f r)"
| "field_empty Sign r = st_lift_empty (slot4 r)"
| "field_empty Parity r = st_lift_empty (slot5 r)"
| "field_empty Order r = (slot6 r = Bot)"

definition t_answer ::
  "sem_conf \<Rightarrow> kenv \<Rightarrow> 'a::kind_int_domain tabs lifted \<Rightarrow> channel \<Rightarrow> channel" where
  "t_answer sem \<kappa> x ch q = (case x of Bot \<Rightarrow> \<top> | Lifted d \<Rightarrow> nonrel_query sem \<kappa> ch d q)"

fun answer :: "sem_conf \<Rightarrow> kenv \<Rightarrow> analysis \<Rightarrow> mcp_val \<Rightarrow> channel \<Rightarrow> channel" where
  "answer sem \<kappa> Interval v ch = t_answer sem \<kappa> (slot1 v) ch"
| "answer sem \<kappa> Congruence v ch = t_answer sem \<kappa> (slot2 v) ch"
| "answer sem \<kappa> (Ana_Int Refine_Never) v ch = t_answer sem \<kappa> (slot3n v) ch"
| "answer sem \<kappa> (Ana_Int Refine_Once) v ch = t_answer sem \<kappa> (slot3o v) ch"
| "answer sem \<kappa> (Ana_Int Refine_Fixpoint) v ch = t_answer sem \<kappa> (slot3f v) ch"
| "answer sem \<kappa> Sign v ch = t_answer sem \<kappa> (slot4 v) ch"
| "answer sem \<kappa> Parity v ch = t_answer sem \<kappa> (slot5 v) ch"
| "answer sem \<kappa> Order v ch = ord_query ch (slot6 v)"

text \<open>A check asks for the truth value of its condition: a comparison or a logical
  operator is that value already, and any other condition is compared with zero.\<close>

fun truth_exp :: "exp \<Rightarrow> exp" where
  "truth_exp (TCmp op a b) = TCmp op a b"
| "truth_exp (TNot a) = TNot a"
| "truth_exp (TAnd a b) = TAnd a b"
| "truth_exp (TOr a b) = TOr a b"
| "truth_exp c = TCmp CNe c (TN I32 0)"

lemma eval_truth_exp: "eval (truth_exp c) s = (if truthy (eval c s) then 1 else 0)"
  by (cases c) (simp_all add: truthy_def ik_norm_def ik_min_def ik_max_def)

subsection \<open>The registry\<close>

text \<open>Each field is sound for its own slot and leaves every other slot's stores in
  place, so the fields together interpret the registry locale
  \<^locale>\<open>mcp_registry\<close>.\<close>

lemma t_answer_sound:
  assumes "s \<in> gamma_lift (gamma_tabs \<kappa>) x" and "eval_query.channel_holds ch s"
  shows "eval_holds q (t_answer sem \<kappa> (x :: 'a::kind_int_domain tabs lifted) ch q) s"
proof (cases x)
  case (Lifted d)
  from assms Lifted have "s \<in> gamma_tabs \<kappa> d" by simp
  from sound_local_spec_queryD[OF nonrel_spec_sound[of \<kappa>, where 'a = 'a],
      unfolded sound_query_def, rule_format, OF this assms(2)]
  show ?thesis by (simp add: t_answer_def Lifted nonrel_spec_def)
qed (simp add: t_answer_def)

lemma lens_lift_sound:
  fixes f :: "mcp_st \<Rightarrow> 'c::{semilattice_sup, order_bot}"
  assumes sound: "sound_local_spec \<kappa> g cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = \<bottom>"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "sound_local_spec \<kappa>
           (\<lambda>x. g (lift_get f x)) (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule lens_of_sound[OF sound])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])

lemma lens_lift_frame:
  assumes "\<And>x v. g (lift_put u x v) = g x"
  shows "mcp_frame (lens_of get (lift_put u) cmp) g"
  unfolding mcp_frame_def lens_of_def by (auto simp: assms)

lemma lens_lift_sound_eq:
  fixes f :: "mcp_st \<Rightarrow> 'c::{semilattice_sup, order_bot}"
  assumes sound: "sound_local_spec \<kappa> gm cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = \<bottom>"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
    and eq: "\<And>x. g x = gm (lift_get f x)"
  shows "sound_local_spec \<kappa> g
           (lens_of (lift_get f) (lift_put u) cmp)"
proof -
  have "g = (\<lambda>x. gm (lift_get f x))" by (rule ext) (rule eq)
  then show ?thesis using lens_lift_sound[OF sound get_put get_bot mono] by simp
qed

lemma mcp_bot_slots [simp]:
  "slot1 (\<bottom> :: mcp_st) = Bot" "slot2 (\<bottom> :: mcp_st) = Bot" "slot3n (\<bottom> :: mcp_st) = Bot"
  "slot3o (\<bottom> :: mcp_st) = Bot" "slot3f (\<bottom> :: mcp_st) = Bot"
  "slot4 (\<bottom> :: mcp_st) = Bot" "slot5 (\<bottom> :: mcp_st) = Bot" "slot6 (\<bottom> :: mcp_st) = Bot"
  "slot1 (\<bottom> :: mcp_val) = Bot" "slot2 (\<bottom> :: mcp_val) = Bot" "slot3n (\<bottom> :: mcp_val) = Bot"
  "slot3o (\<bottom> :: mcp_val) = Bot" "slot3f (\<bottom> :: mcp_val) = Bot"
  "slot4 (\<bottom> :: mcp_val) = Bot" "slot5 (\<bottom> :: mcp_val) = Bot" "slot6 (\<bottom> :: mcp_val) = Bot"
  by (simp_all add: bot_analysis_product_def bot_lifted_def)

lemma field_sound:
  "sound_local_spec \<kappa>
     (\<lambda>x. gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global) x)) (field sem \<kappa> p a)"
proof -
  note nonrel = lens_lift_sound_eq[OF nonrel_exec_spec_sound]
  note simps = less_eq_analysis_product_def lift_get_def mcp_rd_def gamma_exec_def
    bot_analysis_product_def bot_lifted_def
  show ?thesis
  proof (cases a rule: analysis_cases)
    case Order then show ?thesis
      by (simp add: field_def)
         (rule lens_lift_sound_eq[OF ord_spec_sound]; auto simp: simps split: lifted.splits)
  qed (simp add: field_def; rule nonrel; auto simp: simps split: lifted.splits)+
qed

lemma field_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (field sem \<kappa> p a)
     (\<lambda>x. gamma_lift (val_gamma \<kappa> b) (map_lift (mcp_rd \<G>) x))"
  by (cases a rule: analysis_cases; cases b rule: analysis_cases; simp add: field_def;
      rule lens_lift_frame;
      auto simp: lift_put_def mcp_rd_def bot_analysis_product_def bot_lifted_def
        split: lifted.splits)

lemma ord_answer_sound:
  "s \<in> gamma_ord_lift \<kappa> x \<Longrightarrow> eval_holds q (ord_query ch x q) s"
  by (cases x) (simp_all add: ord_query_sound)

lemma single_entry_nonrel_exec_spec: "single_entry (nonrel_exec_spec sem \<kappa>)"
  by (simp add: single_entry_def nonrel_exec_spec_def)

lemma single_entry_ord_spec: "single_entry (ord_spec \<kappa> ys)"
  by (simp add: single_entry_def ord_spec_def)

lemma single_entry_field: "single_entry (field sem \<kappa> p a)"
  by (cases a rule: analysis_cases) (auto simp: field_def intro!: single_entry_lens_of lift_put_get
      single_entry_nonrel_exec_spec single_entry_ord_spec)

global_interpretation mcp: mcp_registry "kenv_of ds"
    truth_exp "\<lambda>\<G> p a. field sem (kenv_of ds) p a" live mcp_rd "val_gamma (kenv_of ds)" val_empty
    "\<lambda>p. field_empty" "answer sem (kenv_of ds)"
  for sem ds
  defines part_answer = mcp.part_answer and mcp_field = mcp.mcp_field
    and mcp_norm = mcp.mcp_norm and mcp_comp = mcp.mcp_comp and mcp_emp = mcp.mcp_emp
    and mcp_empty_v = mcp.mcp_empty_v and mcp_answer = mcp.mcp_answer
    and mcp_ask = mcp.mcp_ask and mcp_classify = mcp.mcp_classify
proof (unfold_locales, goal_cases Truth FieldSound Frame Single Dead EmptyRd EmptyGamma Bot Answer)
  case (Truth c s) show ?case by (rule eval_truth_exp)
next
  case (FieldSound p a) show ?case by (rule field_sound)
next
  case (Frame a b \<G> p) then show ?case by (rule field_frame)
next
  case (Single \<G> p a) show ?case by (rule single_entry_field)
next
  case (Dead a r \<G>) then show ?case by (cases a rule: analysis_cases) (simp_all add: mcp_rd_def)
next
  case (EmptyRd p a r) show ?case
    by (cases a rule: analysis_cases)
       (simp_all add: mcp_rd_def st_lift_empty_def t_lift_empty_def st_is_bot_iff t_empty_def split:
         lifted.splits)
next
  case (EmptyGamma a v) then show ?case
    by (cases a rule: analysis_cases)
      (auto simp: t_lift_empty_def dest: t_empty_sound split: lifted.splits)
next
  case (Bot a) show ?case
    by (cases a rule: analysis_cases) (simp_all add: bot_analysis_product_def bot_lifted_def)
next
  case (Answer s a v ch q) then show ?case
    by (cases a rule: analysis_cases) (auto intro: t_answer_sound ord_answer_sound)
qed

end
