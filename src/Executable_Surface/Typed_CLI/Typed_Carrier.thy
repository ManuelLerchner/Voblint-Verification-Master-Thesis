theory Typed_Carrier
  imports Typed_Run "Voblint_Framework.MCP_Registry"
begin

section \<open>The combined state of the typed analyses\<close>

text \<open>
  Every typed analysis owns one field of the combined state, as in the untyped carrier
  (\<^verbatim>\<open>MCP_Carrier\<close>), and the typed analyses form a \<^locale>\<open>mcp_registry\<close> over the
  typed language. A non-relational field runs the typed component and answers through
  its evaluator, which may ask the channel about operands; the order field runs the
  order component and answers comparisons from its facts.
\<close>

subsection \<open>Fields\<close>

type_synonym tmcp_st =
  "(ivl tst toplift lifted, (congruence tst toplift lifted, (int_tuple tst toplift lifted,
    (sign tst toplift lifted, (parity tst toplift lifted, var_id order_rel lifted)
    analysis_product) analysis_product) analysis_product) analysis_product) analysis_product"

type_synonym tmcp_val =
  "(ivl tabs toplift lifted, (congruence tabs toplift lifted, (int_tuple tabs toplift lifted,
    (sign tabs toplift lifted, (parity tabs toplift lifted, var_id order_rel lifted)
    analysis_product) analysis_product) analysis_product) analysis_product) analysis_product"

definition tslot1 where "tslot1 r = pleft r"
definition tslot2 where "tslot2 r = pleft (pright r)"
definition tslot3 where "tslot3 r = pleft (pright (pright r))"
definition tslot4 where "tslot4 r = pleft (pright (pright (pright r)))"
definition tslot5 where "tslot5 r = pleft (pright (pright (pright (pright r))))"
definition tslot6 where "tslot6 r = pright (pright (pright (pright (pright r))))"

definition set_tslot1 where "set_tslot1 r v = Product v (pright r)"
definition set_tslot2 where "set_tslot2 r v = Product (pleft r) (Product v (pright (pright r)))"
definition set_tslot3 where
  "set_tslot3 r v = Product (pleft r) (Product (pleft (pright r))
     (Product v (pright (pright (pright r)))))"
definition set_tslot4 where
  "set_tslot4 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product v (pright (pright (pright (pright r)))))))"
definition set_tslot5 where
  "set_tslot5 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product (pleft (pright (pright (pright r)))) (Product v (pright (pright (pright (pright (pright r)))))))))"
definition set_tslot6 where
  "set_tslot6 r v = Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
     (Product (pleft (pright (pright (pright r)))) (Product (pleft (pright (pright (pright (pright r))))) v))))"

lemmas tslot_defs [simp] = tslot1_def tslot2_def tslot3_def tslot4_def tslot5_def tslot6_def
  set_tslot1_def set_tslot2_def set_tslot3_def set_tslot4_def set_tslot5_def set_tslot6_def

definition tmcp_rd :: "(var_id \<Rightarrow> bool) \<Rightarrow> tmcp_st \<Rightarrow> tmcp_val" where
  "tmcp_rd \<G> r =
     Product (map_lift (map_toplift (default_st_to_fun \<G>)) (tslot1 r))
     (Product (map_lift (map_toplift (default_st_to_fun \<G>)) (tslot2 r))
     (Product (map_lift (map_toplift (default_st_to_fun \<G>)) (tslot3 r))
     (Product (map_lift (map_toplift (default_st_to_fun \<G>)) (tslot4 r))
     (Product (map_lift (map_toplift (default_st_to_fun \<G>)) (tslot5 r)) (tslot6 r)))))"

subsection \<open>Each analysis on its own field\<close>

definition tfield :: "kenv \<Rightarrow> typed_domain \<Rightarrow> (var_id, texp, tmcp_st lifted) glocal_spec" where
  "tfield \<kappa> a = (case a of
      Typed_Interval \<Rightarrow> lens_of (lift_get tslot1) (lift_put set_tslot1) (typed_exec_spec \<kappa>)
    | Typed_Congruence \<Rightarrow> lens_of (lift_get tslot2) (lift_put set_tslot2) (typed_exec_spec \<kappa>)
    | Typed_Int \<Rightarrow> lens_of (lift_get tslot3) (lift_put set_tslot3) (typed_exec_spec \<kappa>)
    | Typed_Sign \<Rightarrow> lens_of (lift_get tslot4) (lift_put set_tslot4) (typed_exec_spec \<kappa>)
    | Typed_Parity \<Rightarrow> lens_of (lift_get tslot5) (lift_put set_tslot5) (typed_exec_spec \<kappa>)
    | Typed_Order \<Rightarrow> lens_of (lift_get tslot6) (lift_put set_tslot6) ord_spec)"

fun tval_gamma :: "kenv \<Rightarrow> typed_domain \<Rightarrow> tmcp_val \<Rightarrow> tstore set" where
  "tval_gamma \<kappa> Typed_Interval v = gamma_lift (gamma_tt \<kappa>) (tslot1 v)"
| "tval_gamma \<kappa> Typed_Congruence v = gamma_lift (gamma_tt \<kappa>) (tslot2 v)"
| "tval_gamma \<kappa> Typed_Int v = gamma_lift (gamma_tt \<kappa>) (tslot3 v)"
| "tval_gamma \<kappa> Typed_Sign v = gamma_lift (gamma_tt \<kappa>) (tslot4 v)"
| "tval_gamma \<kappa> Typed_Parity v = gamma_lift (gamma_tt \<kappa>) (tslot5 v)"
| "tval_gamma \<kappa> Typed_Order v = gamma_ord_lift (tslot6 v)"

fun tlive :: "typed_domain \<Rightarrow> tmcp_st \<Rightarrow> bool" where
  "tlive Typed_Interval r = (tslot1 r \<noteq> Bot)"
| "tlive Typed_Congruence r = (tslot2 r \<noteq> Bot)"
| "tlive Typed_Int r = (tslot3 r \<noteq> Bot)"
| "tlive Typed_Sign r = (tslot4 r \<noteq> Bot)"
| "tlive Typed_Parity r = (tslot5 r \<noteq> Bot)"
| "tlive Typed_Order r = (tslot6 r \<noteq> Bot)"

definition tt_lift_empty :: "'a::kind_int_domain tabs toplift lifted \<Rightarrow> bool" where
  "tt_lift_empty x = (case x of Bot \<Rightarrow> True | Lifted d \<Rightarrow> tt_empty d)"

fun tval_empty :: "typed_domain \<Rightarrow> tmcp_val \<Rightarrow> bool" where
  "tval_empty Typed_Interval v = tt_lift_empty (tslot1 v)"
| "tval_empty Typed_Congruence v = tt_lift_empty (tslot2 v)"
| "tval_empty Typed_Int v = tt_lift_empty (tslot3 v)"
| "tval_empty Typed_Sign v = tt_lift_empty (tslot4 v)"
| "tval_empty Typed_Parity v = tt_lift_empty (tslot5 v)"
| "tval_empty Typed_Order v = (tslot6 v = Bot)"

definition tst_lift_empty :: "'a::kind_int_domain tst toplift lifted \<Rightarrow> bool" where
  "tst_lift_empty x = (case x of Bot \<Rightarrow> True | Lifted d \<Rightarrow> tst_empty d)"

fun tfield_empty :: "typed_domain \<Rightarrow> tmcp_st \<Rightarrow> bool" where
  "tfield_empty Typed_Interval r = tst_lift_empty (tslot1 r)"
| "tfield_empty Typed_Congruence r = tst_lift_empty (tslot2 r)"
| "tfield_empty Typed_Int r = tst_lift_empty (tslot3 r)"
| "tfield_empty Typed_Sign r = tst_lift_empty (tslot4 r)"
| "tfield_empty Typed_Parity r = tst_lift_empty (tslot5 r)"
| "tfield_empty Typed_Order r = (tslot6 r = Bot)"

definition tt_answer :: "kenv \<Rightarrow> 'a::kind_int_domain tabs toplift lifted \<Rightarrow> texp gchannel \<Rightarrow> texp gchannel" where
  "tt_answer \<kappa> x ch q = (case x of Bot \<Rightarrow> \<top> | Lifted d \<Rightarrow> tquery \<kappa> ch d q)"

fun tanswer :: "kenv \<Rightarrow> typed_domain \<Rightarrow> tmcp_val \<Rightarrow> texp gchannel \<Rightarrow> texp gchannel" where
  "tanswer \<kappa> Typed_Interval v ch = tt_answer \<kappa> (tslot1 v) ch"
| "tanswer \<kappa> Typed_Congruence v ch = tt_answer \<kappa> (tslot2 v) ch"
| "tanswer \<kappa> Typed_Int v ch = tt_answer \<kappa> (tslot3 v) ch"
| "tanswer \<kappa> Typed_Sign v ch = tt_answer \<kappa> (tslot4 v) ch"
| "tanswer \<kappa> Typed_Parity v ch = tt_answer \<kappa> (tslot5 v) ch"
| "tanswer \<kappa> Typed_Order v ch = ord_query ch (tslot6 v)"

text \<open>A check asks whether its condition differs from zero.\<close>

definition truth_texp :: "texp \<Rightarrow> texp" where
  "truth_texp c = TCmp CNe c (TN I32 0)"

lemma teval_truth_texp: "teval (truth_texp c) s = (if truthy (teval c s) then 1 else 0)"
  by (simp add: truth_texp_def truthy_def ik_norm_def ik_min_def ik_max_def)

subsection \<open>The registry\<close>

lemma tt_answer_sound:
  assumes "s \<in> gamma_lift (gamma_tt \<kappa>) x" and "geval_query.channel_holds teval ch s"
  shows "geval_holds teval q (tt_answer \<kappa> (x :: 'a::kind_int_domain tabs toplift lifted) ch q) s"
proof (cases x)
  case (Lifted d)
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  from assms Lifted have "s \<in> gamma_tt \<kappa> d" by simp
  from T.sound_local_spec_queryD[OF typed_spec_sound[of \<kappa>, where 'a = 'a],
      unfolded T.gsound_query_def, rule_format, OF this assms(2)]
  show ?thesis by (simp add: tt_answer_def Lifted typed_spec_def)
qed (simp add: tt_answer_def)

lemma lens_lift_sound:
  fixes f :: "tmcp_st \<Rightarrow> 'c::{semilattice_sup, order_bot}"
  assumes sound: "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal g cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = \<bottom>"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal
           (\<lambda>x. g (lift_get f x)) (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule mcp_sem.lens_of_sound[OF sound])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])

lemma lens_lift_frame:
  assumes "\<And>x v. g (lift_put u x v) = g x"
  shows "mcp_frame (lens_of get (lift_put u) cmp) g"
  unfolding mcp_frame_def lens_of_def by (auto simp: assms)

lemma lens_lift_sound_eq:
  fixes f :: "tmcp_st \<Rightarrow> 'c::{semilattice_sup, order_bot}"
  assumes sound: "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal gm cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = \<bottom>"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
    and eq: "\<And>x. g x = gm (lift_get f x)"
  shows "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal g
           (lens_of (lift_get f) (lift_put u) cmp)"
proof -
  have "g = (\<lambda>x. gm (lift_get f x))" by (rule ext) (rule eq)
  then show ?thesis using lens_lift_sound[OF sound get_put get_bot mono] by simp
qed

lemma tmcp_bot_slots [simp]:
  "tslot1 (\<bottom> :: tmcp_st) = Bot" "tslot2 (\<bottom> :: tmcp_st) = Bot" "tslot3 (\<bottom> :: tmcp_st) = Bot"
  "tslot4 (\<bottom> :: tmcp_st) = Bot" "tslot5 (\<bottom> :: tmcp_st) = Bot" "tslot6 (\<bottom> :: tmcp_st) = Bot"
  "tslot1 (\<bottom> :: tmcp_val) = Bot" "tslot2 (\<bottom> :: tmcp_val) = Bot" "tslot3 (\<bottom> :: tmcp_val) = Bot"
  "tslot4 (\<bottom> :: tmcp_val) = Bot" "tslot5 (\<bottom> :: tmcp_val) = Bot" "tslot6 (\<bottom> :: tmcp_val) = Bot"
  by (simp_all add: bot_analysis_product_def bot_lifted_def)

lemma tslot_mono:
  fixes r r' :: tmcp_st
  assumes "r \<le> r'"
  shows "tslot1 r \<le> tslot1 r'" "tslot2 r \<le> tslot2 r'" "tslot3 r \<le> tslot3 r'"
    "tslot4 r \<le> tslot4 r'" "tslot5 r \<le> tslot5 r'" "tslot6 r \<le> tslot6 r'"
  using assms by (simp_all add: less_eq_analysis_product_def)

lemma tfield_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal
     (\<lambda>x. gamma_lift (tval_gamma \<kappa> a) (map_lift (tmcp_rd tglobal) x)) (tfield \<kappa> a)"
proof -
  note nonrel = lens_lift_sound_eq[OF typed_exec_spec_sound]
  note simps = less_eq_analysis_product_def lift_get_def tmcp_rd_def gamma_exec_def
    bot_analysis_product_def bot_lifted_def
  show ?thesis
  proof (cases a)
    case Typed_Interval then show ?thesis
      by (simp add: tfield_def) (rule nonrel; auto simp: simps split: lifted.splits)
  next
    case Typed_Congruence then show ?thesis
      by (simp add: tfield_def) (rule nonrel; auto simp: simps split: lifted.splits)
  next
    case Typed_Int then show ?thesis
      by (simp add: tfield_def) (rule nonrel; auto simp: simps split: lifted.splits)
  next
    case Typed_Sign then show ?thesis
      by (simp add: tfield_def) (rule nonrel; auto simp: simps split: lifted.splits)
  next
    case Typed_Parity then show ?thesis
      by (simp add: tfield_def) (rule nonrel; auto simp: simps split: lifted.splits)
  next
    case Typed_Order then show ?thesis
      by (simp add: tfield_def)
         (rule lens_lift_sound_eq[OF ord_spec_sound]; auto simp: simps split: lifted.splits)
  qed
qed

lemma tfield_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (tfield \<kappa> a)
     (\<lambda>x. gamma_lift (tval_gamma \<kappa> b) (map_lift (tmcp_rd \<G>) x))"
  by (cases a; cases b; simp add: tfield_def; rule lens_lift_frame;
      auto simp: lift_put_def tmcp_rd_def bot_analysis_product_def bot_lifted_def
        split: lifted.splits)

lemma ord_answer_sound:
  "s \<in> gamma_ord_lift x \<Longrightarrow> geval_holds teval q (ord_query ch x q) s"
  by (cases x) (simp_all add: ord_query_sound)

lemma single_entry_typed_exec_spec: "single_entry (typed_exec_spec \<kappa>)"
  by (simp add: single_entry_def typed_exec_spec_def)

lemma single_entry_ord_spec: "single_entry ord_spec"
  by (simp add: single_entry_def ord_spec_def)

lemma single_entry_tfield: "single_entry (tfield \<kappa> a)"
  by (cases a) (auto simp: tfield_def intro!: single_entry_lens_of lift_put_get
      single_entry_typed_exec_spec single_entry_ord_spec)

global_interpretation tmcp: mcp_registry teval ReturnVar "\<lambda>_. tconv (kenv_of ds)" "\<lambda>_. tglobal"
    truth_texp "\<lambda>\<G> p a. tfield (kenv_of ds) a" tlive tmcp_rd "tval_gamma (kenv_of ds)" tval_empty
    "\<lambda>p. tfield_empty" "tanswer (kenv_of ds)"
  for ds
proof (unfold_locales, goal_cases Truth FieldSound Frame Single Dead EmptyRd EmptyGamma Bot Answer)
  case (Truth c s) show ?case by (rule teval_truth_texp)
next
  case (FieldSound p a) show ?case by (rule tfield_sound)
next
  case (Frame a b \<G> p) then show ?case by (rule tfield_frame)
next
  case (Single \<G> p a) show ?case by (rule single_entry_tfield)
next
  case (Dead a r \<G>) then show ?case by (cases a) (simp_all add: tmcp_rd_def)
next
  case (EmptyRd p a r) show ?case
    by (cases a) (simp_all add: tmcp_rd_def tst_lift_empty_def tt_lift_empty_def tst_empty_iff
        split: lifted.splits)
next
  case (EmptyGamma a v) then show ?case
    by (cases a) (auto simp: tt_lift_empty_def dest: tt_empty_sound split: lifted.splits)
next
  case (Bot a) show ?case
    by (cases a) (simp_all add: bot_analysis_product_def bot_lifted_def)
next
  case (Answer s a v ch q) then show ?case
    by (cases a) (auto intro: tt_answer_sound ord_answer_sound)
qed

end
