theory Typed_Nonrel
  imports "Voblint_Typed_CFG.Typed_Invariants" "Voblint_Domain.Kind_Lifted"
begin

section \<open>Kind-aware integer domains\<close>

text \<open>
  The operations a typed transfer needs from an integer domain, after Goblint's
  \<^verbatim>\<open>IntDomain.S\<close>: every operation that produces a value takes the kind it computes
  at. \<open>top_ik k\<close> is Goblint's \<open>top_of ik\<close>, \<open>of_int_ik\<close> its \<open>of_int ik\<close>, \<open>cast_ik\<close> its
  \<open>cast_to ik\<close>, and \<open>arith_ik k op\<close> the binary operation at kind \<open>k\<close>, whose concrete
  result is normalized to \<open>k\<close>. A comparison answers \<open>Some b\<close> only when every pair of
  operands agrees on \<open>b\<close>.
\<close>

class kind_int_domain = ik_domain +
  fixes top_ik :: "ikind \<Rightarrow> 'a::{bounded_semilattice_sup_bot, order_top}"
    and of_int_ik :: "ikind \<Rightarrow> int \<Rightarrow> 'a"
    and cast_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and arith_ik :: "ikind \<Rightarrow> aop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and cmp_ik :: "cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool option"
  assumes top_ik_sound: "n \<in> ik_range k \<Longrightarrow> n \<in> \<gamma> (top_ik k)"
    and of_int_ik_sound: "ik_norm k n \<in> \<gamma> (of_int_ik k n)"
    and cast_ik_sound: "n \<in> \<gamma> a \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik k a)"
    and arith_ik_sound:
      "m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> \<gamma> (arith_ik k op a b)"
    and cmp_ik_sound:
      "cmp_ik c a b = Some r \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> cop_eval c m n = r"

section \<open>Typed abstract states\<close>

text \<open>
  A typed abstract state maps every variable identity to a kind-tagged value. It
  describes the typed stores whose values lie in the state's values: \<^const>\<open>tstyped\<close>
  is part of the description, so a value the state does not constrain still stays in
  its variable's range. The top state is the one exception and describes every store,
  untyped or not; a transfer answers it for an action no typed program contains.
\<close>

type_synonym 'a tabs = "var_id \<Rightarrow> 'a kd"

definition gamma_tabs :: "kenv \<Rightarrow> 'a::ik_domain tabs \<Rightarrow> tstore set" where
  "gamma_tabs \<kappa> \<sigma> =
     (if \<sigma> = \<top> then UNIV else {t. tstyped \<kappa> t \<and> (\<forall>v. t v \<in> \<gamma> (\<sigma> v))})"

lemma gamma_tabs_top [simp]: "gamma_tabs \<kappa> \<top> = UNIV"
  by (simp add: gamma_tabs_def)

lemma gamma_tabsD:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>"
  shows "tstyped \<kappa> t" and "t v \<in> \<gamma> (\<sigma> v)"
  using assms by (simp_all add: gamma_tabs_def)

lemma gamma_tabsI:
  "tstyped \<kappa> t \<Longrightarrow> (\<And>v. t v \<in> \<gamma> (\<sigma> v)) \<Longrightarrow> t \<in> gamma_tabs \<kappa> \<sigma>"
  by (simp add: gamma_tabs_def)

lemma gamma_tabs_mono:
  assumes "\<sigma>\<^sub>1 \<le> \<sigma>\<^sub>2"
  shows "gamma_tabs \<kappa> \<sigma>\<^sub>1 \<subseteq> gamma_tabs \<kappa> \<sigma>\<^sub>2"
proof (cases "\<sigma>\<^sub>2 = \<top>")
  case False
  then have "\<sigma>\<^sub>1 \<noteq> \<top>" using assms top.extremum_uniqueI by blast
  have "x v \<in> \<gamma> (\<sigma>\<^sub>2 v)" if "x v \<in> \<gamma> (\<sigma>\<^sub>1 v)" for x v
    using that gamma_mono[OF le_funD[OF assms, of v]] by blast
  with False \<open>\<sigma>\<^sub>1 \<noteq> \<top>\<close> show ?thesis
    by (auto simp: gamma_tabs_def simp del: gamma_kd.simps)
qed simp

lemma gamma_tabs_bot [simp]: "gamma_tabs \<kappa> \<bottom> = {}"
proof -
  have "(\<bottom> :: 'a::ik_domain tabs) \<noteq> \<top>"
    by (simp add: fun_eq_iff bot_kd_def top_kd_def)
  then show ?thesis by (simp add: gamma_tabs_def bot_fun_def bot_kd_def)
qed

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
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>"
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

fun taeval :: "kenv \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "taeval \<kappa> (TN ik n) \<sigma> = of_int_ik ik n"
| "taeval \<kappa> (TVar ik v) \<sigma> = read_var \<kappa> \<sigma> v"
| "taeval \<kappa> (TArith ik op a b) \<sigma> = arith_ik ik op (taeval \<kappa> a \<sigma>) (taeval \<kappa> b \<sigma>)"
| "taeval \<kappa> (TCast ik a) \<sigma> = cast_ik ik (taeval \<kappa> a \<sigma>)"
| "taeval \<kappa> (TCmp op a b) \<sigma> = bool_val (cmp_ik op (taeval \<kappa> a \<sigma>) (taeval \<kappa> b \<sigma>))"
| "taeval \<kappa> (TNot a) \<sigma> = bool_val (map_option HOL.Not (truth_ik (taeval \<kappa> a \<sigma>)))"
| "taeval \<kappa> (TAnd a b) \<sigma> =
     bool_val (case (truth_ik (taeval \<kappa> a \<sigma>), truth_ik (taeval \<kappa> b \<sigma>)) of
                 (Some False, _) \<Rightarrow> Some False | (_, Some False) \<Rightarrow> Some False
               | (Some True, Some True) \<Rightarrow> Some True | _ \<Rightarrow> None)"
| "taeval \<kappa> (TOr a b) \<sigma> =
     bool_val (case (truth_ik (taeval \<kappa> a \<sigma>), truth_ik (taeval \<kappa> b \<sigma>)) of
                 (Some True, _) \<Rightarrow> Some True | (_, Some True) \<Rightarrow> Some True
               | (Some False, Some False) \<Rightarrow> Some False | _ \<Rightarrow> None)"

theorem taeval_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>"
  shows "teval e t \<in> \<gamma> (taeval \<kappa> e \<sigma>)"
proof (induction e)
  case (TN ik n) show ?case by (simp add: of_int_ik_sound)
next
  case (TVar ik v) show ?case by (simp add: read_var_sound[OF assms])
next
  case (TArith ik op a b) then show ?case by (simp add: arith_ik_sound)
next
  case (TCast ik a) then show ?case by (simp add: cast_ik_sound)
next
  case (TCmp op a b) then show ?case
    by (simp add: bool_val_sound cmp_ik_sound)
next
  case (TNot a)
  have "(if \<not> truthy (teval a t) then 1 else 0)
      \<in> \<gamma> (bool_val (map_option HOL.Not (truth_ik (taeval \<kappa> a \<sigma>))) :: 'a)"
    by (rule bool_val_sound) (use TNot truth_ik_sound in auto)
  moreover have "teval (TNot a) t = (if \<not> truthy (teval a t) then 1 else 0)"
    by simp
  ultimately show ?case by (simp only: taeval.simps)
next
  case (TAnd a b)
  show ?case
    unfolding teval.simps taeval.simps
    by (rule bool_val_sound)
       (use TAnd truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
next
  case (TOr a b)
  show ?case
    unfolding teval.simps taeval.simps
    by (rule bool_val_sound)
       (use TOr truth_ik_sound in \<open>auto split: option.splits bool.splits\<close>)
qed

end
