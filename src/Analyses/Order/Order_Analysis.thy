theory Order_Analysis
  imports "Voblint_Nonrelational.Nonrelational_Analysis"
begin

section \<open>The order domain at typed variables\<close>

text \<open>
  A relational carrier over any variable type: a finite set of pairs \<open>(x, y)\<close>, each
  meaning that \<open>x\<close>'s value is at most \<open>y\<close>'s. Stored values are already normalized to
  their kinds, so the facts compare the values a run holds; a guard adds a fact only
  when it compares two variable reads, whose values the comparison sees unconverted.
  The flag records that every variable other than the return slot holds a value of its
  kind (@{const in_kinds}): a copy between two variables of one kind then passes the
  conversion unchanged.
\<close>

datatype 'v order_rel = OBot | OFacts bool "('v \<times> 'v) set"

instantiation order_rel :: (type) "{bounded_semilattice_sup_bot, order_top}"
begin

fun less_eq_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> bool" where
  "less_eq_order_rel OBot _ = True"
| "less_eq_order_rel (OFacts _ _) OBot = False"
| "less_eq_order_rel (OFacts t a) (OFacts u b) = (b \<subseteq> a \<and> (u \<longrightarrow> t))"

definition less_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> bool" where
  "less_order_rel a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

fun sup_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "sup_order_rel OBot b = b"
| "sup_order_rel a OBot = a"
| "sup_order_rel (OFacts t a) (OFacts u b) = OFacts (t \<and> u) (a \<inter> b)"

definition bot_order_rel :: "'v order_rel" where "bot_order_rel = OBot"

definition top_order_rel :: "'v order_rel" where "top_order_rel = OFacts False {}"

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

fun gamma_ord :: "kenv \<Rightarrow> var_id order_rel \<Rightarrow> store set" where
  "gamma_ord \<kappa> OBot = {}"
| "gamma_ord \<kappa> (OFacts t ps) = {s. (t \<longrightarrow> in_kinds \<kappa> s) \<and> (\<forall>(x, y) \<in> ps. s x \<le> s y)}"

lemma gamma_ord_mono: "a \<le> b \<Longrightarrow> gamma_ord \<kappa> a \<subseteq> gamma_ord \<kappa> b"
  by (cases a; cases b) auto

lemma gamma_ord_top [simp]: "gamma_ord \<kappa> top = UNIV"
  by (simp add: top_order_rel_def)

fun ord_forget :: "'v \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "ord_forget x OBot = OBot"
| "ord_forget x (OFacts t ps) = OFacts t {(a, b) \<in> ps. a \<noteq> x \<and> b \<noteq> x}"

text \<open>Every write converts to its destination's kind except the return slot's, which no
  kind constrains, so a forgotten destination keeps the stores typed.\<close>

lemma ord_forget_sound:
  "s \<in> gamma_ord \<kappa> d \<Longrightarrow> v = ik_norm (\<kappa> x) n \<or> x = ReturnVar
     \<Longrightarrow> s(x := v) \<in> gamma_ord \<kappa> (ord_forget x d)"
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

fun ord_branch :: "exp \<Rightarrow> bool \<Rightarrow> var_id order_rel \<Rightarrow> var_id order_rel" where
  "ord_branch (TCmp c (TVar k x) (TVar k' y)) pol (OFacts t ps) = OFacts t (ps \<union> cmp_facts c pol x y)"
| "ord_branch (TNot b) pol d = ord_branch b (\<not> pol) d"
| "ord_branch _ _ d = d"

lemma ord_branch_sound:
  "s \<in> gamma_ord \<kappa> d \<Longrightarrow> truthy (eval b s) = pol \<Longrightarrow> s \<in> gamma_ord \<kappa> (ord_branch b pol d)"
proof (induction b pol d rule: ord_branch.induct)
  case (1 c k x k' y pol t ps)
  then show ?case using cmp_facts_sound[of c s x y pol] by (auto split: if_splits)
next
  case (2 b pol d)
  then show ?case by (auto split: if_splits)
qed simp_all

subsection \<open>Verdicts\<close>

text \<open>A pair \<open>(x, y)\<close> decides \<open>x \<le> y\<close> as true and \<open>y < x\<close> as false; with the reverse
  pair it also decides equality.\<close>

definition ord_le :: "var_id order_rel \<Rightarrow> var_id \<Rightarrow> var_id \<Rightarrow> bool" where
  "ord_le d x y = (case d of OBot \<Rightarrow> False | OFacts _ ps \<Rightarrow> x = y \<or> (x, y) \<in> ps)"

lemma ord_le_sound: "ord_le d x y \<Longrightarrow> s \<in> gamma_ord \<kappa> d \<Longrightarrow> s x \<le> s y"
  by (cases d) (auto simp: ord_le_def)

fun ord_decide :: "cop \<Rightarrow> var_id order_rel \<Rightarrow> var_id \<Rightarrow> var_id \<Rightarrow> bool option" where
  "ord_decide CLe d x y = (if ord_le d x y then Some True else None)"
| "ord_decide CGe d x y = (if ord_le d y x then Some True else None)"
| "ord_decide CLt d x y = (if ord_le d y x then Some False else None)"
| "ord_decide CGt d x y = (if ord_le d x y then Some False else None)"
| "ord_decide CEq d x y = (if ord_le d x y \<and> ord_le d y x then Some True else None)"
| "ord_decide CNe d x y = (if ord_le d x y \<and> ord_le d y x then Some False else None)"

lemma ord_decide_sound:
  "ord_decide c d x y = Some r \<Longrightarrow> s \<in> gamma_ord \<kappa> d \<Longrightarrow> cop_eval c (s x) (s y) = r"
  using ord_le_sound[of d x y s \<kappa>] ord_le_sound[of d y x s \<kappa>]
  by (cases c) (auto split: if_splits)

fun ord_classify :: "exp \<Rightarrow> var_id order_rel \<Rightarrow> check_result" where
  "ord_classify (TCmp c (TVar k x) (TVar k' y)) d =
     (case ord_decide c d x y of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"
| "ord_classify _ d = Check_Unknown"

lemma ord_classify_sound:
  assumes "s \<in> gamma_ord \<kappa> d"
  shows ord_classify_proved: "ord_classify c d = Check_Proved \<Longrightarrow> truthy (eval c s)"
    and ord_classify_refuted: "ord_classify c d = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
  using assms ord_decide_sound
  by (induction c d rule: ord_classify.induct;
      fastforce split: option.splits bool.splits if_splits)+

subsection \<open>The query\<close>

text \<open>
  The component answers \<open>EvalInt\<close> for a comparison between two variables from its own
  facts, as Goblint's \<^verbatim>\<open>varEq\<close> and \<^verbatim>\<open>expRelation\<close> do
  (\<^verbatim>\<open>varEq.ml\<close> line 595, \<^verbatim>\<open>expRelation.ml\<close> lines 53 to 70 at \<^verbatim>\<open>0dc12d355\<close>):
  a decided comparison is the exact truth value, anything else is \<open>\<top>\<close>. It asks
  nobody, as those analyses do not.
\<close>

fun ord_query :: "exp gchannel \<Rightarrow> var_id order_rel lifted \<Rightarrow> exp gchannel" where
  "ord_query ch (Lifted d) (EvalInt (TCmp c (TVar k x) (TVar k' y))) =
     (case ord_decide c d x y of Some b \<Rightarrow> answer_of_int (if b then 1 else 0) | None \<Rightarrow> \<top>)"
| "ord_query ch d q = \<top>"

lemma ord_query_sound:
  "s \<in> gamma_ord \<kappa> d \<Longrightarrow> geval_holds eval q (ord_query ch (Lifted d) q) s"
  using ord_decide_sound
  by (cases "(ch, Lifted d, q)" rule: ord_query.cases) (auto split: option.splits)

subsection \<open>Assignments\<close>

text \<open>
  At \<open>x = e\<close> the component asks about the state before the assignment, where
  \<open>(\<kappa> x) e\<close> evaluates to the new value of \<open>x\<close> and every other variable keeps
  its value. The exact answer \<open>1\<close> to \<open>(\<kappa> x) e \<le> y\<close> makes \<open>(x, y)\<close> true
  afterwards, and \<open>y \<le> (\<kappa> x) e\<close> makes \<open>(y, x)\<close> true. The candidate partners are
  the variables in \<open>ys\<close>. A copy from a variable of the same kind records both orders
  when the stores are typed and gives the destination the source's facts, as Goblint's
  \<^verbatim>\<open>varEq\<close> records an equality for an assignment between variables of one type
  (\<^verbatim>\<open>varEq.ml\<close> at \<^verbatim>\<open>0dc12d355\<close>).
\<close>

definition ord_copy ::
    "kenv \<Rightarrow> var_id \<Rightarrow> exp \<Rightarrow> (var_id \<times> var_id) set \<Rightarrow> (var_id \<times> var_id) set" where
  "ord_copy \<kappa> x e ps = (case e of
     TVar k y \<Rightarrow> if y \<noteq> x \<and> y \<noteq> ReturnVar \<and> \<kappa> y = \<kappa> x
       then {(x, y), (y, x)} \<union> (\<lambda>(a, b). (x, b)) ` Set.filter (\<lambda>(a, b). a = y) ps
            \<union> (\<lambda>(a, b). (a, x)) ` Set.filter (\<lambda>(a, b). b = y) ps
       else {}
   | _ \<Rightarrow> {})"

definition ord_learn ::
    "kenv \<Rightarrow> var_id list \<Rightarrow> exp gchannel \<Rightarrow> var_id \<Rightarrow> exp \<Rightarrow> var_id order_rel \<Rightarrow> var_id order_rel" where
  "ord_learn \<kappa> ys ch x e d =
     (case d of
        OBot \<Rightarrow> OBot
      | OFacts t ps \<Rightarrow> OFacts t (ps
          \<union> (if t then ord_copy \<kappa> x e ps else {})
          \<union> set (map (\<lambda>y. (x, y)) (filter (\<lambda>y. y \<noteq> x
                \<and> answer_const (ch (EvalInt (TCmp CLe (TCast (\<kappa> x) e) (TVar (\<kappa> y) y)))) = Some 1) ys))
          \<union> set (map (\<lambda>y. (y, x)) (filter (\<lambda>y. y \<noteq> x
                \<and> answer_const (ch (EvalInt (TCmp CLe (TVar (\<kappa> y) y) (TCast (\<kappa> x) e)))) = Some 1) ys))))"

lemma geval_holds_constD:
  "geval_holds ev (EvalInt e) a s \<Longrightarrow> answer_const a = Some n \<Longrightarrow> ev e s = n"
  using gamma_int_dom_constant_subset by (cases a rule: answer_const.cases) auto

lemma ord_learn_sound:
  assumes post: "s(x := ik_norm (\<kappa> x) (eval e s)) \<in> gamma_ord \<kappa> d"
    and ch: "geval_query.channel_holds eval ch s"
  shows "s(x := ik_norm (\<kappa> x) (eval e s)) \<in> gamma_ord \<kappa> (ord_learn \<kappa> ys ch x e d)"
proof (cases d)
  case OBot with post show ?thesis by simp
next
  case (OFacts t ps)
  define s' where "s' = s(x := ik_norm (\<kappa> x) (eval e s))"
  have up: "s' x \<le> s' y"
    if "y \<noteq> x" "answer_const (ch (EvalInt (TCmp CLe (TCast (\<kappa> x) e) (TVar (\<kappa> y) y)))) = Some 1" for
      y
    using that geval_holds_constD[OF geval_query.channel_holdsD[OF ch] that(2)]
    by (simp add: s'_def split: if_splits)
  have down: "s' y \<le> s' x"
    if "y \<noteq> x" "answer_const (ch (EvalInt (TCmp CLe (TVar (\<kappa> y) y) (TCast (\<kappa> x) e)))) = Some 1" for
      y
    using that geval_holds_constD[OF geval_query.channel_holdsD[OF ch] that(2)]
    by (simp add: s'_def split: if_splits)
  have mem: "s' \<in> gamma_ord \<kappa> (OFacts t ps)" using post OFacts by (simp add: s'_def)
  have copy: "s' a \<le> s' b" if t: "t" and ab: "(a, b) \<in> ord_copy \<kappa> x e ps" for a b
  proof -
    from ab obtain k y where e: "e = TVar k y" and y: "y \<noteq> x" "y \<noteq> ReturnVar" "\<kappa> y = \<kappa> x"
      and ab': "(a, b) = (x, y) \<or> (a, b) = (y, x) \<or> (a = x \<and> (y, b) \<in> ps) \<or> (b = x \<and> (a, y) \<in> ps)"
      by (auto simp: ord_copy_def split: exp.splits if_splits)
    from post OFacts t have "in_kinds \<kappa> s'" by (simp add: s'_def)
    then have "s' y \<in> ik_range (\<kappa> x)" using y unfolding in_kinds_def by metis
    then have "s' x = s' y" using y by (simp add: s'_def e del: ik_range_iff)
    then show ?thesis using ab' mem by auto
  qed
  show ?thesis
    using mem up down copy unfolding s'_def[symmetric] by (auto simp: ord_learn_def OFacts)
qed

subsection \<open>Calls\<close>

text \<open>The callee starts from no facts and the caller learns none back. The callee's
  stores are typed when the caller's are, since a call converts each actual to its
  formal's kind; the caller's after the call when both sides' are, as the result
  converts to its destination's kind.\<close>

definition ord_in_kinds :: "var_id order_rel lifted \<Rightarrow> bool" where
  "ord_in_kinds d = (case d of Lifted (OFacts t _) \<Rightarrow> t | _ \<Rightarrow> False)"

definition ord_enter :: "var_id list \<Rightarrow> exp list \<Rightarrow> var_id order_rel lifted \<Rightarrow> var_id order_rel" where
  "ord_enter ps es d = OFacts (ord_in_kinds d) {}"

subsection \<open>The component\<close>

text \<open>
  Assignments forget their destination and learn, library calls forget it, and a
  return forgets the return slot. The caller learns nothing back from a call: a callee
  may change globals, so no fact survives it.
\<close>

definition ord_spec :: "kenv \<Rightarrow> var_id list \<Rightarrow> (var_id, exp, var_id order_rel lifted) glocal_spec"
  where
  "ord_spec \<kappa> ys =
     \<lparr> ls_query = ord_query,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. map_lift (ord_learn \<kappa> ys ch x e \<circ> ord_forget x)),
       ls_special = (\<lambda>ch sc x. map_lift (ord_forget x)),
       ls_branch = (\<lambda>ch b pol. map_lift (ord_branch b pol)),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p d. case r of None \<Rightarrow> d | Some a \<Rightarrow> map_lift (ord_forget ReturnVar) d),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p. [(fst p, Lifted (ord_enter (ci_formals ci) (ci_args ci) (fst p)))]),
       ls_combine_env = combine_env_identity,
       ls_combine_assign = (\<lambda>ch ci d de. Lifted (OFacts (ord_in_kinds d \<and> ord_in_kinds de) {})) \<rparr>"

abbreviation gamma_ord_lift :: "kenv \<Rightarrow> var_id order_rel lifted \<Rightarrow> store set" where
  "gamma_ord_lift \<kappa> d \<equiv> gamma_lift (gamma_ord \<kappa>) (map_lift (\<lambda>d. d) d)"

lemma gamma_ord_lift_simps [simp]:
  "gamma_ord_lift \<kappa> Bot = {}"
  "gamma_ord_lift \<kappa> (Lifted x) = gamma_ord \<kappa> x"
  "gamma_ord_lift \<kappa> (map_lift f (Lifted x)) = gamma_ord \<kappa> (f x)"
  by (simp_all add: map_lift_def)

lemma gamma_ord_lift_mono: "x \<le> y \<Longrightarrow> gamma_ord_lift \<kappa> x \<subseteq> gamma_ord_lift \<kappa> y"
  by (cases x; cases y) (auto dest: gamma_ord_mono)

lemma ord_enter_sound:
  assumes "s \<in> gamma_ord_lift \<kappa> d"
  shows "bind_formals ps (map2 (\<lambda>x. ik_norm (\<kappa> x)) ps (map (\<lambda>e. eval e s) es))
           (enter_state is_global s)
           \<in> gamma_ord \<kappa> (ord_enter ps es d)"
proof -
  have "in_kinds \<kappa> (vimp.gcall_enter \<kappa> (CallEdge dst ps es) s)" if "ord_in_kinds d" for dst
    using assms that by (intro in_kinds_call_enter)
      (auto simp: ord_in_kinds_def split: lifted.splits order_rel.splits)
  then show ?thesis
    by (auto simp: ord_enter_def vimp.call_enter_CallEdge)
qed

lemma ord_in_kinds_in_kinds: "s \<in> gamma_ord_lift \<kappa> d \<Longrightarrow> ord_in_kinds d \<Longrightarrow> in_kinds \<kappa> s"
  by (auto simp: ord_in_kinds_def split: lifted.splits order_rel.splits)

lemma in_kinds_gcombine:
  "in_kinds \<kappa> s \<Longrightarrow> in_kinds \<kappa> t
     \<Longrightarrow> in_kinds \<kappa> (combine_assign dst (kind_conv \<kappa> dst (t ReturnVar)) (combine_env is_global s t))"
  by (cases dst) (auto simp: in_kinds_combine_env)

theorem ord_spec_sound:
  "mcp_sem.gsound_local_spec eval ReturnVar (kind_conv \<kappa>) is_global (gamma_ord_lift \<kappa>) (ord_spec \<kappa> ys)"
proof -
  interpret T: mcp_sem eval ReturnVar "kind_conv \<kappa>" is_global .
  have L: "\<exists>x. d = Lifted x \<and> s \<in> gamma_ord \<kappa> x" if "s \<in> gamma_ord_lift \<kappa> d" for s d
    using that by (cases d) simp_all
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_ord_lift \<kappa> x \<subseteq> gamma_ord_lift \<kappa> y" by (rule gamma_ord_lift_mono)
    show "T.gsound_query (gamma_ord_lift \<kappa>) (ls_query (ord_spec \<kappa> ys))"
      by (auto simp: ord_spec_def T.gsound_query_def ord_query_sound dest!: L)
    show "T.gsound_skip (gamma_ord_lift \<kappa>) (ls_skip (ord_spec \<kappa> ys))"
      by (simp add: ord_spec_def T.gsound_skip_def)
    show "T.gsound_body (gamma_ord_lift \<kappa>) (ls_body (ord_spec \<kappa> ys))"
      by (simp add: ord_spec_def T.gsound_body_def)
    show "T.gsound_event (gamma_ord_lift \<kappa>) (ls_event (ord_spec \<kappa> ys))"
      by (simp add: ord_spec_def T.gsound_event_def)
    show "T.gsound_assign (gamma_ord_lift \<kappa>) (ls_assign (ord_spec \<kappa> ys))"
      by (auto dest!: L simp: ord_spec_def T.gsound_assign_def
          intro!: ord_learn_sound ord_forget_sound)
    show "T.gsound_special (gamma_ord_lift \<kappa>) (ls_special (ord_spec \<kappa> ys))"
      by (auto simp: ord_spec_def T.gsound_special_def dest!: L intro: ord_forget_sound)
    show "T.gsound_branch (gamma_ord_lift \<kappa>) (ls_branch (ord_spec \<kappa> ys))"
      using ord_branch_sound by (fastforce simp: ord_spec_def T.gsound_branch_def dest!: L)
    show "T.gsound_return (gamma_ord_lift \<kappa>) (ls_return (ord_spec \<kappa> ys))"
      by (auto simp: ord_spec_def T.gsound_return_def dest!: L intro: ord_forget_sound
          split: option.splits)
    show "T.gsound_enter (gamma_ord_lift \<kappa>) (ls_enter (ord_spec \<kappa> ys))"
      by (auto simp: ord_spec_def T.gsound_enter_def cfg_transfer_sem.call_enter_CallEdge
          intro: ord_enter_sound)
    show "T.gsound_combine (gamma_ord_lift \<kappa>) (ls_combine_env (ord_spec \<kappa> ys))
        (ls_combine_assign (ord_spec \<kappa> ys))"
      by (auto simp: ord_spec_def T.gsound_combine_def combine_env_identity_def
          cfg_transfer_sem.gcombine_collect_def intro!: in_kinds_gcombine dest:
            ord_in_kinds_in_kinds)
  qed
qed

text \<open>The candidate partners: every variable some procedure of the program declares
  (@{const program_vars}).\<close>

definition ord_vars :: "imp_prog \<Rightarrow> var_id list" where
  "ord_vars p = remdups (concat (map (\<lambda>q. map (resolve_var (declared_global p) q)
     (filter (\<lambda>x. x \<noteq> ret_var) (scope_vnames_list p q))) (prog_main_name # prog_procs p)))"

subsection \<open>The pipeline instance\<close>

text \<open>The same unit-context instance as the non-relational typed analyses, with the
  order component in place of a per-variable state. The concretization does not depend
  on the kind declarations, but the program's runs and initial stores do.\<close>

global_interpretation order_analysis: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "\<lambda>_ p. ord_spec (kenv_of ds) (ord_vars p)" "\<lambda>_ d. d = OBot" "\<lambda>_ d. d" "OFacts True {}"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ _ _ _ _. ()" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((var_id order_rel lifted, var_id order_rel lifted) dg_state) r"
    OBot ord_classify "gamma_ord (kenv_of ds)" "\<lambda>d. d = OBot"
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
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
  case (InitSound p) show ?case by (auto dest: init_stores_in_kinds)
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

end
