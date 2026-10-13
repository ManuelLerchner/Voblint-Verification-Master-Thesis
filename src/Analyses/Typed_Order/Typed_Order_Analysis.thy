theory Typed_Order_Analysis
  imports "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis"
begin

section \<open>The order domain at typed variables\<close>

text \<open>
  The relational carrier of the untyped order analysis (\<open>relc\<close>) over any variable
  type: a finite set of pairs \<open>(x, y)\<close>, each meaning that \<open>x\<close>'s value is at most
  \<open>y\<close>'s. Stored values are already normalized to their kinds, so the facts compare the
  values a typed run holds; a guard adds a fact only when it compares two variable
  reads, whose values the comparison sees unconverted.
\<close>

datatype 'v order_rel = OBot | OFacts "('v \<times> 'v) set"

instantiation order_rel :: (type) "{bounded_semilattice_sup_bot, order_top}"
begin

fun less_eq_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> bool" where
  "less_eq_order_rel OBot _ = True"
| "less_eq_order_rel (OFacts _) OBot = False"
| "less_eq_order_rel (OFacts a) (OFacts b) = (b \<subseteq> a)"

definition less_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> bool" where
  "less_order_rel a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

fun sup_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "sup_order_rel OBot b = b"
| "sup_order_rel a OBot = a"
| "sup_order_rel (OFacts a) (OFacts b) = OFacts (a \<inter> b)"

definition bot_order_rel :: "'v order_rel" where "bot_order_rel = OBot"

definition top_order_rel :: "'v order_rel" where "top_order_rel = OFacts {}"

instance proof
  fix x y z :: "'v order_rel"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_order_rel_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
  show "x \<le> x \<squnion> y" "y \<le> x \<squnion> y" by (cases x; cases y; auto)+
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) auto
  show "bot \<le> x" by (simp add: bot_order_rel_def)
  show "x \<le> top" by (cases x) (simp_all add: top_order_rel_def)
qed

end

instantiation order_rel :: (type) warrowing
begin

definition widen_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "widen_order_rel a b = a \<squnion> b"

definition narrow_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "narrow_order_rel a b = b"

instance proof
  fix x y :: "'v order_rel"
  show "x \<le> x \<nabla> y" "y \<le> x \<nabla> y" by (simp_all add: widen_order_rel_def)
  show "y \<le> x \<Longrightarrow> y \<le> x \<Delta> y" "y \<le> x \<Longrightarrow> x \<Delta> y \<le> x"
    by (simp_all add: narrow_order_rel_def)
qed

end

fun gamma_ord :: "'v order_rel \<Rightarrow> ('v \<Rightarrow> int) set" where
  "gamma_ord OBot = {}"
| "gamma_ord (OFacts ps) = {s. \<forall>(x, y) \<in> ps. s x \<le> s y}"

lemma gamma_ord_mono: "a \<le> b \<Longrightarrow> gamma_ord a \<subseteq> gamma_ord b"
  by (cases a; cases b) auto

lemma gamma_ord_top [simp]: "gamma_ord top = UNIV"
  by (simp add: top_order_rel_def)

fun ord_forget :: "'v \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "ord_forget x OBot = OBot"
| "ord_forget x (OFacts ps) = OFacts {(a, b) \<in> ps. a \<noteq> x \<and> b \<noteq> x}"

lemma ord_forget_sound: "s \<in> gamma_ord d \<Longrightarrow> s(x := v) \<in> gamma_ord (ord_forget x d)"
  by (cases d) auto

subsection \<open>Guards\<close>

text \<open>The orders a comparison between \<open>x\<close> and \<open>y\<close> fixes when it has the truth value
  \<open>pol\<close>. A disequality fixes none: the carrier holds only weak orders.\<close>

fun cmp_facts :: "cop \<Rightarrow> bool \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v) set" where
  "cmp_facts CLt True x y = {(x, y)}"
| "cmp_facts CLe True x y = {(x, y)}"
| "cmp_facts CGt True x y = {(y, x)}"
| "cmp_facts CGe True x y = {(y, x)}"
| "cmp_facts CEq True x y = {(x, y), (y, x)}"
| "cmp_facts CNe True x y = {}"
| "cmp_facts CLt False x y = {(y, x)}"
| "cmp_facts CLe False x y = {(y, x)}"
| "cmp_facts CGt False x y = {(x, y)}"
| "cmp_facts CGe False x y = {(x, y)}"
| "cmp_facts CEq False x y = {}"
| "cmp_facts CNe False x y = {(x, y), (y, x)}"

lemma cmp_facts_sound:
  "cop_eval c (s x) (s y) = pol \<Longrightarrow> (a, b) \<in> cmp_facts c pol x y \<Longrightarrow> s a \<le> s b"
  by (cases c; cases pol) auto

fun ord_branch :: "texp \<Rightarrow> bool \<Rightarrow> var_id order_rel \<Rightarrow> var_id order_rel" where
  "ord_branch (TCmp c (TVar k x) (TVar k' y)) pol (OFacts ps) = OFacts (ps \<union> cmp_facts c pol x y)"
| "ord_branch (TNot b) pol d = ord_branch b (\<not> pol) d"
| "ord_branch _ _ d = d"

lemma ord_branch_sound:
  "s \<in> gamma_ord d \<Longrightarrow> truthy (teval b s) = pol \<Longrightarrow> s \<in> gamma_ord (ord_branch b pol d)"
proof (induction b pol d rule: ord_branch.induct)
  case (1 c k x k' y pol ps)
  then show ?case using cmp_facts_sound[of c s x y pol] by (auto split: if_splits)
next
  case (2 b pol d)
  then show ?case by (auto split: if_splits)
qed simp_all

subsection \<open>Verdicts\<close>

text \<open>A pair \<open>(x, y)\<close> decides \<open>x \<le> y\<close> as true and \<open>y < x\<close> as false; with the reverse
  pair it also decides equality.\<close>

definition ord_le :: "var_id order_rel \<Rightarrow> var_id \<Rightarrow> var_id \<Rightarrow> bool" where
  "ord_le d x y = (case d of OBot \<Rightarrow> False | OFacts ps \<Rightarrow> x = y \<or> (x, y) \<in> ps)"

lemma ord_le_sound: "ord_le d x y \<Longrightarrow> s \<in> gamma_ord d \<Longrightarrow> s x \<le> s y"
  by (cases d) (auto simp: ord_le_def)

fun ord_decide :: "cop \<Rightarrow> var_id order_rel \<Rightarrow> var_id \<Rightarrow> var_id \<Rightarrow> bool option" where
  "ord_decide CLe d x y = (if ord_le d x y then Some True else None)"
| "ord_decide CGe d x y = (if ord_le d y x then Some True else None)"
| "ord_decide CLt d x y = (if ord_le d y x then Some False else None)"
| "ord_decide CGt d x y = (if ord_le d x y then Some False else None)"
| "ord_decide CEq d x y = (if ord_le d x y \<and> ord_le d y x then Some True else None)"
| "ord_decide CNe d x y = (if ord_le d x y \<and> ord_le d y x then Some False else None)"

lemma ord_decide_sound:
  "ord_decide c d x y = Some r \<Longrightarrow> s \<in> gamma_ord d \<Longrightarrow> cop_eval c (s x) (s y) = r"
  using ord_le_sound[of d x y s] ord_le_sound[of d y x s]
  by (cases c) (auto split: if_splits)

fun ord_classify :: "texp \<Rightarrow> var_id order_rel \<Rightarrow> check_result" where
  "ord_classify (TCmp c (TVar k x) (TVar k' y)) d =
     (case ord_decide c d x y of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"
| "ord_classify _ d = Check_Unknown"

lemma ord_classify_sound:
  assumes "s \<in> gamma_ord d"
  shows ord_classify_proved: "ord_classify c d = Check_Proved \<Longrightarrow> truthy (teval c s)"
    and ord_classify_refuted: "ord_classify c d = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
  using assms ord_decide_sound
  by (induction c d rule: ord_classify.induct;
      fastforce split: option.splits bool.splits if_splits)+

subsection \<open>The component\<close>

text \<open>
  Assignments and library calls forget their destination; a return forgets the
  return slot. At a call the callee starts from no facts and the caller learns
  nothing back, as in the untyped order analysis: a callee may change globals, so
  no fact survives the call.
\<close>

definition ord_spec :: "(var_id, texp, var_id order_rel lifted) glocal_spec" where
  "ord_spec =
     \<lparr> ls_query = query_unknown,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. map_lift (ord_forget x)),
       ls_special = (\<lambda>ch sc x. map_lift (ord_forget x)),
       ls_branch = (\<lambda>ch b pol. map_lift (ord_branch b pol)),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p d. case r of None \<Rightarrow> d | Some a \<Rightarrow> map_lift (ord_forget ReturnVar) d),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p. [(fst p, Lifted top)]),
       ls_combine_env = combine_env_identity,
       ls_combine_assign = (\<lambda>ch ci d de. Lifted top) \<rparr>"

abbreviation gamma_ord_lift :: "var_id order_rel lifted \<Rightarrow> tstore set" where
  "gamma_ord_lift d \<equiv> gamma_lift gamma_ord (map_lift (\<lambda>d. d) d)"

lemma gamma_ord_lift_simps [simp]:
  "gamma_ord_lift Bot = {}"
  "gamma_ord_lift (Lifted x) = gamma_ord x"
  "gamma_ord_lift (map_lift f (Lifted x)) = gamma_ord (f x)"
  by (simp_all add: map_lift_def)

lemma gamma_ord_lift_mono: "x \<le> y \<Longrightarrow> gamma_ord_lift x \<subseteq> gamma_ord_lift y"
  by (cases x; cases y) (auto dest: gamma_ord_mono)

theorem ord_spec_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal gamma_ord_lift ord_spec"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  have L: "\<exists>x. d = Lifted x \<and> s \<in> gamma_ord x" if "s \<in> gamma_ord_lift d" for s d
    using that by (cases d) simp_all
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_ord_lift x \<subseteq> gamma_ord_lift y" by (rule gamma_ord_lift_mono)
    show "T.gsound_query gamma_ord_lift (ls_query ord_spec)"
      by (simp add: ord_spec_def T.sound_query_unknown)
    show "T.gsound_skip gamma_ord_lift (ls_skip ord_spec)"
      by (simp add: ord_spec_def T.gsound_skip_def)
    show "T.gsound_body gamma_ord_lift (ls_body ord_spec)"
      by (simp add: ord_spec_def T.gsound_body_def)
    show "T.gsound_event gamma_ord_lift (ls_event ord_spec)"
      by (simp add: ord_spec_def T.gsound_event_def)
    show "T.gsound_assign gamma_ord_lift (ls_assign ord_spec)"
      by (auto simp: ord_spec_def T.gsound_assign_def dest!: L intro: ord_forget_sound)
    show "T.gsound_special gamma_ord_lift (ls_special ord_spec)"
      by (auto simp: ord_spec_def T.gsound_special_def dest!: L intro: ord_forget_sound)
    show "T.gsound_branch gamma_ord_lift (ls_branch ord_spec)"
      using ord_branch_sound by (fastforce simp: ord_spec_def T.gsound_branch_def dest!: L)
    show "T.gsound_return gamma_ord_lift (ls_return ord_spec)"
      by (auto simp: ord_spec_def T.gsound_return_def dest!: L intro: ord_forget_sound
          split: option.splits)
    show "T.gsound_enter gamma_ord_lift (ls_enter ord_spec)"
      by (simp add: ord_spec_def T.gsound_enter_def)
    show "T.gsound_combine gamma_ord_lift (ls_combine_env ord_spec) (ls_combine_assign ord_spec)"
      by (simp add: ord_spec_def T.sound_combine_env_identity)
  qed
qed

subsection \<open>The pipeline instance\<close>

text \<open>The same unit-context instance as the non-relational typed analyses, with the
  order component in place of a per-variable state. The concretization does not depend
  on the kind declarations, but the program's runs and initial stores do.\<close>

global_interpretation typed_order: gdg_analysis
    teval ReturnVar "\<lambda>_. tconv (kenv_of ds)" "\<lambda>_. tglobal" "\<lambda>_. tinit_stores (kenv_of ds)"
    "\<lambda>_ _. ord_spec" "\<lambda>_ d. d = OBot" "\<lambda>_ d. d" "top :: var_id order_rel"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ _ _ _ _. ()" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((var_id order_rel lifted, var_id order_rel lifted) dg_state) r"
    OBot ord_classify gamma_ord "\<lambda>d. d = OBot"
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. typed_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for ds r
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p) show ?case by (rule ord_spec_sound)
next
  case (EnterSingle p ci d) show ?case
    by (simp add: ord_spec_def dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by simp
next
  case EmptyV show ?case by (rule sound_emptinessI) simp
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro ord_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro ord_classify_refuted)
next
  case BotState show ?case by simp
next
  case (InitSound p) show ?case by simp
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
  fixes ds :: kind_decls and r :: globals_rule
begin

lemma typed_order_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_order.terminates r ds tglobal p"
  shows "tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v
           \<subseteq> gamma_ord (typed_order.state_at r ds tglobal p () v)"
  using typed_order.gfun_route_result_node_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves, of "\<lambda>_ _ _. ()" v]
  by (simp add: tnode_collect_def UNIV_unit)

text \<open>A proved order check holds at every typed store reaching its node; a refuted one
  fails at every such store. Neither verdict says the node is reached.\<close>

theorem typed_order_report_proved_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_order.terminates r ds tglobal p"
    and mem: "(v, c, Check_Proved) \<in> set (typed_order.report r ds tglobal p ())"
  shows "\<forall>s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v.
           truthy (teval c s)"
  using typed_order.gfun_route_report_proved_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves mem, of "\<lambda>_ _ _. ()"]
    typed_order.fun_route_node_collect_eq_Union[of ds p v "\<lambda>_ _ _. ()"]
  by (simp add: tnode_collect_def)

theorem typed_order_report_refuted_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_order.terminates r ds tglobal p"
    and mem: "(v, c, Check_Refuted) \<in> set (typed_order.report r ds tglobal p ())"
  shows "\<forall>s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v.
           \<not> truthy (teval c s)"
  using typed_order.gfun_route_report_refuted_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves mem, of "\<lambda>_ _ _. ()"]
    typed_order.fun_route_node_collect_eq_Union[of ds p v "\<lambda>_ _ _. ()"]
  by (simp add: tnode_collect_def)

end
end
