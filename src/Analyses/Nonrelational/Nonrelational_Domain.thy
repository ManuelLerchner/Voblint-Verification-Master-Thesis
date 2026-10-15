theory Nonrelational_Domain
  imports "Voblint_Compile.Kind_Invariants" "Voblint_Domain.Kind_Lifted"
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
  The concrete semantics wraps every result, signed or not. How an abstract domain treats
  a possible signed overflow is a separate choice, Goblint's
  \<^verbatim>\<open>sem.int.signed_overflow\<close>: \<open>Assume_Top\<close>, its default, answers the kind's top,
  and \<open>Assume_Wraparound\<close> wraps as the concrete semantics does. Both are sound here. An
  unsigned kind always wraps (\<^verbatim>\<open>should_wrap\<close> in \<^verbatim>\<open>intDomain0.ml\<close>).
\<close>

datatype signed_overflow_policy = Assume_Top | Assume_Wraparound

definition should_wrap :: "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> bool" where
  "should_wrap ovp k \<longleftrightarrow> \<not> ik_signed k \<or> ovp = Assume_Wraparound"

text \<open>
  The options of Goblint's \<^verbatim>\<open>sem.int\<close> group that the domains read. Goblint reads
  them from its global configuration at every use; here one value is a parameter of
  the evaluator and the transfers, and every soundness theorem holds for each value.
  A further option is a further field.
\<close>

record sem_conf =
  sem_int_signed_overflow :: signed_overflow_policy

definition default_sem_conf :: sem_conf where
  "default_sem_conf = \<lparr> sem_int_signed_overflow = Assume_Top \<rparr>"

text \<open>A remainder of in-range operands, and a quotient unless the divisor is \<open>-1\<close>, stays
  in the kind's range: no policy applies to them.\<close>

lemma c_mod_between: "min 0 a \<le> c_mod a b \<and> c_mod a b \<le> max 0 a"
proof (cases "b = 0")
  case False
  have "c_mod a b = sgn a * (\<bar>a\<bar> mod \<bar>b\<bar>)"
    using False by (simp add: c_mod_def c_div_def algebra_simps abs_mult_sgn
        minus_div_mult_eq_mod[symmetric] sgn_mult_abs; metis abs_sgn)
  moreover have "0 \<le> \<bar>a\<bar> mod \<bar>b\<bar>" "\<bar>a\<bar> mod \<bar>b\<bar> \<le> \<bar>a\<bar>"
    using False by (simp_all add: zmod_le_nonneg_dividend)
  ultimately show ?thesis by (cases "0 \<le> a") (auto simp: sgn_if)
qed (simp add: c_mod_def)

lemma c_mod_in_range: "m \<in> ik_range k \<Longrightarrow> c_mod m n \<in> ik_range k"
  using c_mod_between[of m n] ik_min_le_zero[of k] zero_le_ik_max[of k]
  by (cases "0 \<le> m") (auto simp: min_def max_def simp del: ik_min_le_zero zero_le_ik_max)

lemma c_div_in_range:
  assumes m: "m \<in> ik_range k" and n: "n \<in> ik_range k" and n1: "n \<noteq> -1"
  shows "c_div m n \<in> ik_range k"
proof (cases "n = 0")
  case False
  define q where "q = \<bar>m\<bar> div \<bar>n\<bar>"
  have q0: "0 \<le> q" using False by (simp add: q_def pos_imp_zdiv_nonneg_iff)
  have "q * \<bar>n\<bar> = \<bar>m\<bar> - \<bar>m\<bar> mod \<bar>n\<bar>" by (simp add: q_def minus_mod_eq_div_mult)
  moreover have "0 \<le> \<bar>m\<bar> mod \<bar>n\<bar>" using False by simp
  ultimately have qn: "q * \<bar>n\<bar> \<le> \<bar>m\<bar>" by linarith
  have cd: "c_div m n = sgn m * sgn n * q" using False by (simp add: c_div_def q_def)
  have lo: "ik_min k = (if ik_signed k then - ik_max k - 1 else 0)"
    by (simp add: ik_min_def ik_max_def)
  have one: "1 \<le> ik_max k" by (cases k) (simp_all add: ik_max_def ik_half_def ik_mod_def)
  have mk: "ik_min k \<le> m" "m \<le> ik_max k" "ik_min k \<le> n" "n \<le> ik_max k" using m n by simp_all
  show ?thesis
  proof (cases "n = 1")
    case True
    then show ?thesis using m by simp
  next
    case n2: False
    with False n1 have "2 \<le> \<bar>n\<bar>" by linarith
    then have "2 * q \<le> \<bar>m\<bar>" using qn mult_left_mono[of 2 "\<bar>n\<bar>" q] q0 by (simp add: mult.commute)
    then show ?thesis using cd lo one mk q0 by (auto simp: sgn_if split: if_splits)
  qed
qed simp

text \<open>
  The operations a typed transfer needs from an integer domain, after Goblint's
  \<^verbatim>\<open>IntDomain.S\<close>: every operation that produces a value takes the kind it computes
  at. \<open>top_ik k\<close> is Goblint's \<open>top_of ik\<close>, \<open>of_int_ik\<close> its \<open>of_int ik\<close>, \<open>cast_ik ovp sk k\<close> its
  \<open>cast_to ?from_ik:sk k\<close>, where \<open>sk\<close> is the operand's kind when it is known, and
  \<open>arith_ik ovp k op operands_fit\<close> the binary operation at kind \<open>k\<close>, whose concrete result
  is normalized to \<open>k\<close>; \<open>operands_fit\<close> says that both operands lie in \<open>k\<close>'s range, as
  they do when each operand has kind \<open>k\<close>. It does not say that the result does. A
  comparison answers \<open>Some b\<close> only when every pair of
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
    and cast_ik :: "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and arith_ik :: "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
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
         \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik ovp sk k a)"
    and arith_ik_sound:
      "(operands_fit \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b
         \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> \<gamma> (arith_ik ovp k op operands_fit a b)"
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
  describes the typed stores whose values lie in the state's values: \<^const>\<open>in_kinds\<close>
  is part of the description, so a value the state does not constrain still stays in
  its variable's range.
\<close>

type_synonym 'a tabs = "var_id \<Rightarrow> 'a kd"

definition gamma_tabs :: "kenv \<Rightarrow> 'a::ik_domain tabs \<Rightarrow> store set" where
  "gamma_tabs \<kappa> \<sigma> = {t. in_kinds \<kappa> t \<and> (\<forall>v. t v \<in> \<gamma> (\<sigma> v))}"

lemma gamma_tabsD:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "in_kinds \<kappa> t" and "t v \<in> \<gamma> (\<sigma> v)"
  using assms by (simp_all add: gamma_tabs_def)

lemma gamma_tabsI:
  "in_kinds \<kappa> t \<Longrightarrow> (\<And>v. t v \<in> \<gamma> (\<sigma> v)) \<Longrightarrow> t \<in> gamma_tabs \<kappa> \<sigma>"
  by (simp add: gamma_tabs_def)

lemma gamma_tabs_mono:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  shows "gamma_tabs \<kappa> \<sigma>\<^sub>1 \<subseteq> gamma_tabs \<kappa> \<sigma>\<^sub>2"
proof -
  have "x v \<in> \<gamma> (\<sigma>\<^sub>2 v)" if "x v \<in> \<gamma> (\<sigma>\<^sub>1 v)" for x v
    using that gamma_mono[OF le_funD[OF assms, of v]] by blast
  then show ?thesis by (auto simp: gamma_tabs_def simp del: gamma_kd.simps)
qed

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

text \<open>A tagged value lies in its tag's range, so a conversion from it knows its source.\<close>

definition kd_kind :: "'a kd \<Rightarrow> ikind option" where
  "kd_kind d = (case d of KD k a \<Rightarrow> Some k | _ \<Rightarrow> None)"

lemma kd_kind_range: "n \<in> \<gamma> d \<Longrightarrow> kd_kind d = Some k \<Longrightarrow> n \<in> ik_range k"
  by (cases d) (auto simp: kd_kind_def)

lemma read_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "t v \<in> \<gamma> (read_var \<kappa> \<sigma> v)"
proof -
  have ty: "in_kinds \<kappa> t" and tv: "t v \<in> \<gamma> (\<sigma> v)"
    using gamma_tabsD[OF assms] by blast+
  show ?thesis
  proof (cases "\<sigma> v")
    case KTop
    show ?thesis
    proof (cases "v = ReturnVar")
      case False
      then have "t v \<in> ik_range (\<kappa> v)" using ty by (simp add: in_kinds_def)
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

definition src_kind :: "kenv \<Rightarrow> exp \<Rightarrow> ikind option" where
  "src_kind \<kappa> e =
     (case e of TVar ik v \<Rightarrow> if v \<noteq> ReturnVar \<and> ik = \<kappa> v then Some ik else None
      | _ \<Rightarrow> Some (exp_kind e))"

lemma src_kind_sound:
  assumes "in_kinds \<kappa> t" and "src_kind \<kappa> e = Some k"
  shows "eval e t \<in> ik_range k"
  using assms by (cases e) (auto simp: src_kind_def in_kinds_def split: if_splits)

lemma cast_ik_None_sound: "n \<in> \<gamma> a \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik ovp None k a)"
  by (rule cast_ik_sound) simp_all

text \<open>A conversion may name the kind of the expression it converts, as Goblint's
  \<^verbatim>\<open>cast_to ?from_ik\<close> does: a typed store gives that expression a value in its kind's range.\<close>

lemma cast_ik_src_sound:
  assumes "in_kinds \<kappa> t" and "eval e t \<in> \<gamma> a"
  shows "ik_norm k (eval e t) \<in> \<gamma> (cast_ik ovp (src_kind \<kappa> e) k a)"
  using assms(2) src_kind_sound[OF assms(1)] by (intro cast_ik_sound) auto

text \<open>
  Evaluation consults the other analyses, as Goblint's \<^verbatim>\<open>base\<close> does
  (\<^verbatim>\<open>eval_rv_ask_evalint\<close> in \<^verbatim>\<open>src/analyses/base.ml\<close> at \<^verbatim>\<open>0dc12d355\<close>): every
  operand that is not a constant is asked about through the channel \<open>ch\<close>, and its
  answer is met with the analysis's own evaluation. Goblint takes the answer alone:
  there the evaluated state is the one the channel answers about, since CIL splits a
  conjunction into one guard per conjunct. A VIMP guard refines a whole conjunction in
  one state, so the second conjunct is evaluated in a state the first has already
  narrowed, finer than the channel's. \<open>aeval\<close> asks
  about the operands but not about the expression itself, which is how the analysis
  answers a query without asking it back; \<open>aeval_ask\<close> also asks about the
  expression. An answer that claims nothing, such as the one a query cycle gets,
  falls back to the analysis's own evaluation, where Goblint takes the kind's top.
  Under the channel that answers every query with \<open>\<top>\<close>, both are the plain
  evaluation.
\<close>

context
  fixes sem :: sem_conf
begin

fun aeval :: "kenv \<Rightarrow> (exp gquery \<Rightarrow> answer) \<Rightarrow> exp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a"
  and aeval_ask :: "kenv \<Rightarrow> (exp gquery \<Rightarrow> answer) \<Rightarrow> exp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "aeval \<kappa> ch (TN ik n) \<sigma> = of_int_ik ik n"
| "aeval \<kappa> ch (TVar ik v) \<sigma> = read_var \<kappa> \<sigma> v"
| "aeval \<kappa> ch (TArith ik op a b) \<sigma> =
     arith_ik (sem_int_signed_overflow sem) ik op (src_kind \<kappa> a = Some ik \<and> src_kind \<kappa> b = Some ik)
       (aeval_ask \<kappa> ch a \<sigma>) (aeval_ask \<kappa> ch b \<sigma>)"
| "aeval \<kappa> ch (TCast ik a) \<sigma> =
     cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> a) ik (aeval_ask \<kappa> ch a \<sigma>)"
| "aeval \<kappa> ch (TCmp op a b) \<sigma> =
     bool_val (cmp_ik op (aeval_ask \<kappa> ch a \<sigma>) (aeval_ask \<kappa> ch b \<sigma>))"
| "aeval \<kappa> ch (TNot a) \<sigma> = bool_val (map_option HOL.Not (truth_ik (aeval_ask \<kappa> ch a \<sigma>)))"
| "aeval \<kappa> ch (TAnd a b) \<sigma> =
     bool_val (case (truth_ik (aeval_ask \<kappa> ch a \<sigma>), truth_ik (aeval_ask \<kappa> ch b \<sigma>)) of
                 (Some False, _) \<Rightarrow> Some False | (_, Some False) \<Rightarrow> Some False
               | (Some True, Some True) \<Rightarrow> Some True | _ \<Rightarrow> None)"
| "aeval \<kappa> ch (TOr a b) \<sigma> =
     bool_val (case (truth_ik (aeval_ask \<kappa> ch a \<sigma>), truth_ik (aeval_ask \<kappa> ch b \<sigma>)) of
                 (Some True, _) \<Rightarrow> Some True | (_, Some True) \<Rightarrow> Some True
               | (Some False, Some False) \<Rightarrow> Some False | _ \<Rightarrow> None)"
| "aeval_ask \<kappa> ch e \<sigma> =
     (case e of TN ik n \<Rightarrow> of_int_ik ik n
      | _ \<Rightarrow> (case ch (EvalInt e) of QTop \<Rightarrow> aeval \<kappa> ch e \<sigma>
              | q \<Rightarrow> meet_ik (aeval \<kappa> ch e \<sigma>) (of_answer_ik (src_kind \<kappa> e) q)))"

lemma aeval_ask_of_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds eval ch t"
    and "eval e t \<in> \<gamma> (aeval \<kappa> ch e \<sigma>)"
  shows "eval e t \<in> \<gamma> (aeval_ask \<kappa> ch e \<sigma>)"
proof -
  have ans: "eval e t \<in> gamma_answer (ch (EvalInt e))"
    using geval_query.channel_holdsD[OF assms(2), of "EvalInt e"] by simp
  have rng: "\<And>k. src_kind \<kappa> e = Some k \<Longrightarrow> eval e t \<in> ik_range k"
    using src_kind_sound[OF gamma_tabsD(1)[OF assms(1)]] .
  show ?thesis
    using assms(3) of_answer_ik_sound[OF rng ans] meet_ik_sound
    by (cases e; cases "ch (EvalInt e)") auto
qed

theorem aeval_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds eval ch t"
  shows "eval e t \<in> \<gamma> (aeval \<kappa> ch e \<sigma>)"
proof (induction e)
  case (TN ik n) show ?case by (simp add: of_int_ik_sound)
next
  case (TVar ik v) show ?case by (simp add: read_var_sound[OF assms(1)])
next
  case (TArith ik op a b)
  have "src_kind \<kappa> e = Some ik \<Longrightarrow> eval e t \<in> ik_range ik" for e
    using src_kind_sound[OF gamma_tabsD(1)[OF assms(1)]] .
  with TArith show ?case
    using aeval_ask_of_sound[OF assms] by (simp add: arith_ik_sound)
next
  case (TCast ik a)
  have "eval a t \<in> ik_range k" if "src_kind \<kappa> a = Some k" for k
    using src_kind_sound[OF gamma_tabsD(1)[OF assms(1)] that] .
  with TCast aeval_ask_of_sound[OF assms] show ?case by (simp add: cast_ik_sound)
next
  case (TCmp op a b) then show ?case
    using aeval_ask_of_sound[OF assms] by (simp add: bool_val_sound cmp_ik_sound)
next
  case (TNot a)
  have a: "eval a t \<in> \<gamma> (aeval_ask \<kappa> ch a \<sigma>)"
    by (rule aeval_ask_of_sound[OF assms TNot])
  have "(if \<not> truthy (eval a t) then 1 else 0)
      \<in> \<gamma> (bool_val (map_option HOL.Not (truth_ik (aeval_ask \<kappa> ch a \<sigma>))) :: 'a)"
    by (rule bool_val_sound) (use a truth_ik_sound in auto)
  moreover have "eval (TNot a) t = (if \<not> truthy (eval a t) then 1 else 0)"
    by simp
  ultimately show ?case by (simp only: aeval.simps)
next
  case (TAnd a b)
  have a: "eval a t \<in> \<gamma> (aeval_ask \<kappa> ch a \<sigma>)" and b: "eval b t \<in> \<gamma> (aeval_ask \<kappa> ch b \<sigma>)"
    using aeval_ask_of_sound[OF assms] TAnd by blast+
  show ?case
    unfolding eval.simps aeval.simps
    by (rule bool_val_sound)
       (use a b truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
next
  case (TOr a b)
  have a: "eval a t \<in> \<gamma> (aeval_ask \<kappa> ch a \<sigma>)" and b: "eval b t \<in> \<gamma> (aeval_ask \<kappa> ch b \<sigma>)"
    using aeval_ask_of_sound[OF assms] TOr by blast+
  show ?case
    unfolding eval.simps aeval.simps
    by (rule bool_val_sound)
       (use a b truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
qed

corollary aeval_ask_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "geval_query.channel_holds eval ch t"
  shows "eval e t \<in> \<gamma> (aeval_ask \<kappa> ch e \<sigma>)"
  by (rule aeval_ask_of_sound[OF assms aeval_sound[OF assms]])

end

end