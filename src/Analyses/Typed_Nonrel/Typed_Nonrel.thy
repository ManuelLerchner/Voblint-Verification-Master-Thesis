theory Typed_Nonrel
  imports "Voblint_Typed_CFG.Typed_Invariants" "Voblint_Domain.Kind_Lifted"
    "Voblint_Domain.Top_Lift"
    "Voblint_Framework.Analysis_Query"
begin

text \<open>Values here are per variable, so \<open>\<gamma>\<close> is the class concretization alone.\<close>

no_notation gamma_S ("\<gamma>")

section \<open>Comparisons from two queries\<close>

text \<open>A domain that decides \<open><\<close> and \<open>=\<close> decides every comparison: the others swap or
  negate those two answers.\<close>

fun cop_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool option) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool option) \<Rightarrow> cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool option"
where
  "cop_of lt eq CLt a b = lt a b"
| "cop_of lt eq CGt a b = lt b a"
| "cop_of lt eq CLe a b = map_option HOL.Not (lt b a)"
| "cop_of lt eq CGe a b = map_option HOL.Not (lt a b)"
| "cop_of lt eq CEq a b = eq a b"
| "cop_of lt eq CNe a b = map_option HOL.Not (eq a b)"

lemma cop_of_sound:
  fixes conc :: "'a \<Rightarrow> int set"
  assumes lt: "\<And>a b r i j. lt a b = Some r \<Longrightarrow> i \<in> conc a \<Longrightarrow> j \<in> conc b \<Longrightarrow> (i < j) = r"
    and eq: "\<And>a b r i j. eq a b = Some r \<Longrightarrow> i \<in> conc a \<Longrightarrow> j \<in> conc b \<Longrightarrow> (i = j) = r"
  shows "cop_of lt eq c a b = Some r \<Longrightarrow> m \<in> conc a \<Longrightarrow> n \<in> conc b \<Longrightarrow> cop_eval c m n = r"
  by (cases c) (auto dest: lt eq)

section \<open>Kind-aware integer domains\<close>

text \<open>
  The operations a typed transfer needs from an integer domain, after Goblint's
  \<^verbatim>\<open>IntDomain.S\<close>: every operation that produces a value takes the kind it computes
  at. \<open>top_ik k\<close> is Goblint's \<open>top_of ik\<close>, \<open>of_int_ik\<close> its \<open>of_int ik\<close>, \<open>cast_ik sk k\<close> its
  \<open>cast_to ?from_ik:sk k\<close>, where \<open>sk\<close> is the operand's kind when it is known, and \<open>arith_ik k op\<close> the binary operation at kind \<open>k\<close>, whose concrete
  result is normalized to \<open>k\<close>. A comparison answers \<open>Some b\<close> only when every pair of
  operands agrees on \<open>b\<close>. \<open>refine_ik c a b\<close> narrows both operands of a comparison
  known to hold, as \<^verbatim>\<open>inv_bin_int\<close> in Goblint's \<^verbatim>\<open>baseInvariant.ml\<close> does for a guard. \<open>raw_aop_ik\<close> is
  the operation on mathematical integers, which a backward step inverts, and
  \<open>fits_ik k a\<close> says that every value of \<open>a\<close> lies in \<open>k\<close>'s range, so that
  normalizing to \<open>k\<close> changes none of them.

  \<open>answer_ik\<close> and \<open>of_answer_ik\<close> translate between a value and an answer to Goblint's
  \<open>EvalInt\<close> query, as Goblint's \<^verbatim>\<open>IntDomTuple\<close> is both the base value and the
  query result. \<open>of_answer_ik sk\<close> may use the kind \<open>sk\<close> of the queried expression,
  when it is known, to bound an answer that claims nothing.
\<close>

class kind_int_domain = ik_domain +
  fixes top_ik :: "ikind \<Rightarrow> 'a::{bounded_semilattice_sup_bot, order_top}"
    and of_int_ik :: "ikind \<Rightarrow> int \<Rightarrow> 'a"
    and cast_ik :: "ikind option \<Rightarrow> ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and arith_ik :: "ikind \<Rightarrow> aop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and cmp_ik :: "cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and meet_ik :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and refine_ik :: "cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
    and raw_aop_ik :: "aop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and fits_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> bool"
    and answer_ik :: "'a \<Rightarrow> answer"
    and of_answer_ik :: "ikind option \<Rightarrow> answer \<Rightarrow> 'a"
  assumes top_ik_sound: "n \<in> ik_range k \<Longrightarrow> n \<in> \<gamma> (top_ik k)"
    and of_int_ik_sound: "ik_norm k n \<in> \<gamma> (of_int_ik k n)"
    and cast_ik_sound:
      "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> \<gamma> a
         \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik sk k a)"
    and arith_ik_sound:
      "m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> \<gamma> (arith_ik k op a b)"
    and cmp_ik_sound:
      "cmp_ik c a b = Some r \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> cop_eval c m n = r"
    and meet_ik_sound: "m \<in> \<gamma> a \<Longrightarrow> m \<in> \<gamma> b \<Longrightarrow> m \<in> \<gamma> (meet_ik a b)"
    and refine_ik_sound:
      "cop_eval c m n \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b
         \<Longrightarrow> m \<in> \<gamma> (fst (refine_ik c a b)) \<and> n \<in> \<gamma> (snd (refine_ik c a b))"
    and raw_aop_ik_sound: "m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> aop_eval op m n \<in> \<gamma> (raw_aop_ik op a b)"
    and fits_ik_sound: "fits_ik k a \<Longrightarrow> n \<in> \<gamma> a \<Longrightarrow> n \<in> ik_range k"
    and answer_ik_sound: "n \<in> \<gamma> a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    and of_answer_ik_sound:
      "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
         \<Longrightarrow> n \<in> \<gamma> (of_answer_ik sk q)"

text \<open>A single-component domain answers with its component of \<^typ>\<open>int_dom\<close> and
  leaves the others at top, so its answer claims exactly what its value does.\<close>

abbreviation answer_with :: "(int_dom \<Rightarrow> int_dom) \<Rightarrow> answer" where
  "answer_with f \<equiv> QLifted (f \<top>)"

section \<open>Typed abstract states\<close>

text \<open>
  A typed abstract state maps every variable identity to a kind-tagged value. It
  describes the typed stores whose values lie in the state's values: \<^const>\<open>tstyped\<close>
  is part of the description, so a value the state does not constrain still stays in
  its variable's range. \<^const>\<open>TTop\<close> above the typed states describes every store,
  typed or not; a transfer answers it for an action no typed program contains.
\<close>

type_synonym 'a tabs = "var_id \<Rightarrow> 'a kd"

definition gamma_tabs :: "kenv \<Rightarrow> 'a::ik_domain tabs \<Rightarrow> tstore set" where
  "gamma_tabs \<kappa> \<sigma> = {t. tstyped \<kappa> t \<and> (\<forall>v. t v \<in> \<gamma> (\<sigma> v))}"

fun gamma_tt :: "kenv \<Rightarrow> 'a::ik_domain tabs toplift \<Rightarrow> tstore set" where
  "gamma_tt \<kappa> TTop = UNIV"
| "gamma_tt \<kappa> (TL \<sigma>) = gamma_tabs \<kappa> \<sigma>"

lemma gamma_tabsD:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "tstyped \<kappa> t" and "t v \<in> \<gamma> (\<sigma> v)"
  using assms by (simp_all add: gamma_tabs_def)

lemma gamma_tabsI:
  "tstyped \<kappa> t \<Longrightarrow> (\<And>v. t v \<in> \<gamma> (\<sigma> v)) \<Longrightarrow> t \<in> gamma_tabs \<kappa> \<sigma>"
  by (simp add: gamma_tabs_def)

lemma gamma_tabs_mono:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  shows "gamma_tabs \<kappa> \<sigma>\<^sub>1 \<subseteq> gamma_tabs \<kappa> \<sigma>\<^sub>2"
proof -
  have "x v \<in> \<gamma> (\<sigma>\<^sub>2 v)" if "x v \<in> \<gamma> (\<sigma>\<^sub>1 v)" for x v
    using that gamma_mono[OF le_funD[OF assms, of v]] by blast
  then show ?thesis by (auto simp: gamma_tabs_def simp del: gamma_kd.simps)
qed

lemma gamma_tt_mono: "d\<^sub>1 \<le> d\<^sub>2 \<Longrightarrow> gamma_tt \<kappa> d\<^sub>1 \<subseteq> gamma_tt \<kappa> d\<^sub>2"
  by (cases d\<^sub>1; cases d\<^sub>2) (simp_all add: gamma_tabs_mono)

lemma gamma_tabs_bot [simp]: "gamma_tabs \<kappa> \<bottom> = {}"
  by (simp add: gamma_tabs_def bot_fun_def bot_kd_def)

section \<open>Reading and evaluating\<close>

text \<open>
  Reading a variable gives its value without the tag. An untagged top is the
  variable's whole range, as Goblint reads an unconstrained local at \<open>top_of ik\<close>; the
  return slot has no declared kind and reads as top.
\<close>

fun kd_val :: "'a::kind_int_domain kd \<Rightarrow> 'a" where
  "kd_val KBot = \<bottom>"
| "kd_val (KD k a) = a"
| "kd_val KTop = \<top>"

definition read_var :: "kenv \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> var_id \<Rightarrow> 'a" where
  "read_var \<kappa> \<sigma> v =
     (case \<sigma> v of KTop \<Rightarrow> if v = ReturnVar then \<top> else top_ik (\<kappa> v) | d \<Rightarrow> kd_val d)"

lemma kd_val_sound: "n \<in> \<gamma> d \<Longrightarrow> n \<in> \<gamma> (kd_val d)"
  by (cases d) simp_all

lemma read_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "t v \<in> \<gamma> (read_var \<kappa> \<sigma> v)"
proof -
  have ty: "tstyped \<kappa> t" and tv: "t v \<in> \<gamma> (\<sigma> v)"
    using gamma_tabsD[OF assms] by blast+
  show ?thesis
  proof (cases "\<sigma> v")
    case KTop
    show ?thesis
    proof (cases "v = ReturnVar")
      case False
      then have "t v \<in> ik_range (\<kappa> v)" using ty by (simp add: tstyped_def)
      with KTop False show ?thesis by (simp add: read_var_def top_ik_sound)
    qed (use KTop in \<open>simp add: read_var_def\<close>)
  qed (use tv in \<open>simp_all add: read_var_def\<close>)
qed

text \<open>A truth value is \<open>0\<close> or \<open>1\<close>; an undecided one is both.\<close>

definition bool_val :: "bool option \<Rightarrow> 'a::kind_int_domain" where
  "bool_val r =
     (case r of Some True \<Rightarrow> of_int_ik I32 1 | Some False \<Rightarrow> of_int_ik I32 0
      | None \<Rightarrow> of_int_ik I32 0 \<squnion> of_int_ik I32 1)"

definition truth_ik :: "'a::kind_int_domain \<Rightarrow> bool option" where
  "truth_ik a = cmp_ik CNe a (of_int_ik I32 0)"

lemma of_int_ik_I32_01:
  "0 \<in> \<gamma> (of_int_ik I32 0 :: 'a::kind_int_domain)"
  "1 \<in> \<gamma> (of_int_ik I32 1 :: 'a::kind_int_domain)"
  using of_int_ik_sound[of I32 0] of_int_ik_sound[of I32 1]
  by (simp_all add: ik_norm_def ik_min_def ik_max_def)

lemma bool_val_sound:
  assumes "\<And>b. r = Some b \<Longrightarrow> P = b"
  shows "(if P then 1 else 0) \<in> \<gamma> (bool_val r :: 'a::kind_int_domain)"
proof (cases r)
  case None
  have "0 \<in> \<gamma> (of_int_ik I32 0 \<squnion> of_int_ik I32 1 :: 'a)"
    "1 \<in> \<gamma> (of_int_ik I32 0 \<squnion> of_int_ik I32 1 :: 'a)"
    using of_int_ik_I32_01 gamma_mono[OF sup.cobounded1] gamma_mono[OF sup.cobounded2]
    by blast+
  with None show ?thesis by (simp add: bool_val_def)
next
  case (Some b)
  with assms show ?thesis by (cases b) (simp_all add: bool_val_def of_int_ik_I32_01)
qed

lemma truth_ik_sound:
  "truth_ik a = Some b \<Longrightarrow> n \<in> \<gamma> a \<Longrightarrow> truthy n = b"
  unfolding truth_ik_def
  using cmp_ik_sound[of CNe a "of_int_ik I32 0" b n 0] of_int_ik_I32_01(1)
  by (simp add: truthy_def)

text \<open>A conversion knows its operand's kind when the operand produces values of that
  kind: an operation always does, and a variable does when it is read at its declared
  kind.\<close>

definition src_kind :: "kenv \<Rightarrow> texp \<Rightarrow> ikind option" where
  "src_kind \<kappa> e =
     (case e of TVar ik v \<Rightarrow> if v \<noteq> ReturnVar \<and> ik = \<kappa> v then Some ik else None
      | _ \<Rightarrow> Some (texp_kind e))"

lemma src_kind_sound:
  assumes "tstyped \<kappa> t" and "src_kind \<kappa> e = Some k"
  shows "teval e t \<in> ik_range k"
  using assms by (cases e) (auto simp: src_kind_def tstyped_def split: if_splits)

lemma cast_ik_None_sound: "n \<in> \<gamma> a \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik None k a)"
  by (rule cast_ik_sound) simp_all

text \<open>
  Evaluation consults the other analyses, as Goblint's \<^verbatim>\<open>base\<close> does
  (\<^verbatim>\<open>eval_rv_ask_evalint\<close> in \<^verbatim>\<open>src/analyses/base.ml\<close> at \<^verbatim>\<open>0dc12d355\<close>): every
  operand that is not a constant is asked about through the channel \<open>ch\<close>, and its
  answer replaces the value. Since this analysis answers the query too, the answer
  already includes its own evaluation, and nothing is evaluated twice. \<open>taeval\<close> asks
  about the operands but not about the expression itself, which is how the analysis
  answers a query without asking it back; \<open>taeval_ask\<close> also asks about the
  expression. An answer that claims nothing, such as the one a query cycle gets,
  falls back to the analysis's own evaluation, where Goblint takes the kind's top.
  Under the channel that answers every query with \<open>\<top>\<close>, both are the plain
  evaluation.
\<close>

fun taeval :: "kenv \<Rightarrow> (texp gquery \<Rightarrow> answer) \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a"
  and taeval_ask :: "kenv \<Rightarrow> (texp gquery \<Rightarrow> answer) \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "taeval \<kappa> ch (TN ik n) \<sigma> = of_int_ik ik n"
| "taeval \<kappa> ch (TVar ik v) \<sigma> = read_var \<kappa> \<sigma> v"
| "taeval \<kappa> ch (TArith ik op a b) \<sigma> = arith_ik ik op (taeval_ask \<kappa> ch a \<sigma>) (taeval_ask \<kappa> ch b \<sigma>)"
| "taeval \<kappa> ch (TCast ik a) \<sigma> = cast_ik (src_kind \<kappa> a) ik (taeval_ask \<kappa> ch a \<sigma>)"
| "taeval \<kappa> ch (TCmp op a b) \<sigma> =
     bool_val (cmp_ik op (taeval_ask \<kappa> ch a \<sigma>) (taeval_ask \<kappa> ch b \<sigma>))"
| "taeval \<kappa> ch (TNot a) \<sigma> = bool_val (map_option HOL.Not (truth_ik (taeval_ask \<kappa> ch a \<sigma>)))"
| "taeval \<kappa> ch (TAnd a b) \<sigma> =
     bool_val (case (truth_ik (taeval_ask \<kappa> ch a \<sigma>), truth_ik (taeval_ask \<kappa> ch b \<sigma>)) of
                 (Some False, _) \<Rightarrow> Some False | (_, Some False) \<Rightarrow> Some False
               | (Some True, Some True) \<Rightarrow> Some True | _ \<Rightarrow> None)"
| "taeval \<kappa> ch (TOr a b) \<sigma> =
     bool_val (case (truth_ik (taeval_ask \<kappa> ch a \<sigma>), truth_ik (taeval_ask \<kappa> ch b \<sigma>)) of
                 (Some True, _) \<Rightarrow> Some True | (_, Some True) \<Rightarrow> Some True
               | (Some False, Some False) \<Rightarrow> Some False | _ \<Rightarrow> None)"
| "taeval_ask \<kappa> ch e \<sigma> =
     (case e of TN ik n \<Rightarrow> of_int_ik ik n
      | _ \<Rightarrow> (case ch (EvalInt e) of QTop \<Rightarrow> taeval \<kappa> ch e \<sigma> | q \<Rightarrow> of_answer_ik (src_kind \<kappa> e) q))"

lemma taeval_ask_of_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds teval ch t"
    and "teval e t \<in> \<gamma> (taeval \<kappa> ch e \<sigma>)"
  shows "teval e t \<in> \<gamma> (taeval_ask \<kappa> ch e \<sigma>)"
proof -
  have ans: "teval e t \<in> gamma_answer (ch (EvalInt e))"
    using geval_query.channel_holdsD[OF assms(2), of "EvalInt e"] by simp
  have rng: "\<And>k. src_kind \<kappa> e = Some k \<Longrightarrow> teval e t \<in> ik_range k"
    using src_kind_sound[OF gamma_tabsD(1)[OF assms(1)]] .
  show ?thesis
    using assms(3) of_answer_ik_sound[OF rng ans]
    by (cases e; cases "ch (EvalInt e)") auto
qed

theorem taeval_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds teval ch t"
  shows "teval e t \<in> \<gamma> (taeval \<kappa> ch e \<sigma>)"
proof (induction e)
  case (TN ik n) show ?case by (simp add: of_int_ik_sound)
next
  case (TVar ik v) show ?case by (simp add: read_var_sound[OF assms(1)])
next
  case (TArith ik op a b) then show ?case
    using taeval_ask_of_sound[OF assms] by (simp add: arith_ik_sound)
next
  case (TCast ik a)
  have "teval a t \<in> ik_range k" if "src_kind \<kappa> a = Some k" for k
    using src_kind_sound[OF gamma_tabsD(1)[OF assms(1)] that] .
  with TCast taeval_ask_of_sound[OF assms] show ?case by (simp add: cast_ik_sound)
next
  case (TCmp op a b) then show ?case
    using taeval_ask_of_sound[OF assms] by (simp add: bool_val_sound cmp_ik_sound)
next
  case (TNot a)
  have a: "teval a t \<in> \<gamma> (taeval_ask \<kappa> ch a \<sigma>)"
    by (rule taeval_ask_of_sound[OF assms TNot])
  have "(if \<not> truthy (teval a t) then 1 else 0)
      \<in> \<gamma> (bool_val (map_option HOL.Not (truth_ik (taeval_ask \<kappa> ch a \<sigma>))) :: 'a)"
    by (rule bool_val_sound) (use a truth_ik_sound in auto)
  moreover have "teval (TNot a) t = (if \<not> truthy (teval a t) then 1 else 0)"
    by simp
  ultimately show ?case by (simp only: taeval.simps)
next
  case (TAnd a b)
  have a: "teval a t \<in> \<gamma> (taeval_ask \<kappa> ch a \<sigma>)" and b: "teval b t \<in> \<gamma> (taeval_ask \<kappa> ch b \<sigma>)"
    using taeval_ask_of_sound[OF assms] TAnd by blast+
  show ?case
    unfolding teval.simps taeval.simps
    by (rule bool_val_sound)
       (use a b truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
next
  case (TOr a b)
  have a: "teval a t \<in> \<gamma> (taeval_ask \<kappa> ch a \<sigma>)" and b: "teval b t \<in> \<gamma> (taeval_ask \<kappa> ch b \<sigma>)"
    using taeval_ask_of_sound[OF assms] TOr by blast+
  show ?case
    unfolding teval.simps taeval.simps
    by (rule bool_val_sound)
       (use a b truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
qed

corollary taeval_ask_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds teval ch t"
  shows "teval e t \<in> \<gamma> (taeval_ask \<kappa> ch e \<sigma>)"
  by (rule taeval_ask_of_sound[OF assms taeval_sound[OF assms]])

end
