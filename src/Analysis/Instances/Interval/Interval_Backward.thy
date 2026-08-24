theory Interval_Backward
  imports Interval_Arithmetic Voblint_Core.Exec_Backward "Voblint_VIMP.VIMP_Expr"
    "Voblint_VIMP.VIMP_Elaborated" Voblint_Core.Abstract_Arithmetic Interval_Numeric_Queries
begin

section \<open>Interval backward filtering\<close>

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>interval_lt\<close>/\<open>interval_eqb\<close>/\<open>interval_tobool\<close> restate
  \<open>Interval_Numeric_Queries\<close>'s \<open>interval_less_true\<close>/\<open>interval_less_false\<close>/
  \<open>interval_eq_true\<close>/\<open>interval_eq_false\<close> as the three-valued \<open>bool option\<close>
  queries \<open>Voblint_Core.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale expects: \<open>Some True\<close>/\<open>Some False\<close> when the bound-based table decides
  it, \<open>None\<close> otherwise. \<open>interval_tobool\<close> is truthiness against the point
  interval \<open>[0,0]\<close>.
\<close>

definition interval_lt :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_lt a b =
     (if interval_less_true a b then Some True
      else if interval_less_false a b then Some False
      else None)"

definition interval_eqb :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_eqb a b =
     (if interval_eq_true a b then Some True
      else if interval_eq_false a b then Some False
      else None)"

definition interval_tobool :: "ivl \<Rightarrow> bool option" where
  "interval_tobool a =
     (if interval_eq_false a (Ivl (Fin 0) (Fin 0)) then Some True
      else if interval_eq_true a (Ivl (Fin 0) (Fin 0)) then Some False
      else None)"

lemma interval_lt_sound:
  assumes "interval_lt p q = Some b" and "i \<in> gamma_ivl p" and "j \<in> gamma_ivl q"
  shows "(i < j) = b"
  using assms unfolding interval_lt_def
  by (auto split: if_splits dest: interval_less_true_sound interval_less_false_sound)

lemma interval_eqb_sound:
  assumes "interval_eqb p q = Some b" and "i \<in> gamma_ivl p" and "j \<in> gamma_ivl q"
  shows "(i = j) = b"
  using assms unfolding interval_eqb_def
  by (auto split: if_splits dest: interval_eq_true_sound interval_eq_false_sound)

lemma interval_tobool_sound:
  assumes "interval_tobool p = Some b" and "i \<in> gamma_ivl p"
  shows "truthy i = b"
proof -
  have z: "(0::int) \<in> gamma_ivl (Ivl (Fin 0) (Fin 0))" by simp
  show ?thesis
    using assms z
    unfolding interval_tobool_def truthy_def
    by (auto split: if_splits dest: interval_eq_false_sound interval_eq_true_sound)
qed

lemma interval_lt_mono:
  assumes hp: "\<not> is_bot (p1::ivl)" and hq: "\<not> is_bot q1"
      and hpm: "p1 \<le> p2" and hqm: "q1 \<le> q2"
      and hwide: "interval_lt p2 q2 = Some b"
  shows "interval_lt p1 q1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  obtain l2 u2 where q1_def: "q1 = Ivl l2 u2" by (cases q1)
  obtain l2' u2' where q2_def: "q2 = Ivl l2' u2'" by (cases q2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_bot_ivl is_bottom_ivl_def by auto
  have ne_q1: "l2 \<le> u2" using hq unfolding q1_def is_bot_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'" "l2' \<le> l2" "u2 \<le> u2'"
    using hpm hqm unfolding p1_def p2_def q1_def q2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" and ne_q2: "l2' \<le> u2'"
    using bnds ne_p1 ne_q1 by order+
  show ?thesis
  proof (cases "interval_less_true p2 q2")
    case True
    then have "u1' < l2'" using p2_def q2_def ne_p2 ne_q2 by simp
    then have "u1 < l2" using bnds by order
    then have p1q1: "interval_less_true p1 q1" using p1_def q1_def ne_p1 ne_q1 by simp
    have "interval_lt p2 q2 = Some True" using True unfolding interval_lt_def by simp
    with hwide have "b = True" by simp
    then show ?thesis using p1q1 unfolding interval_lt_def by simp
  next
    case False
    then have hlf: "interval_less_false p2 q2"
      using hwide unfolding interval_lt_def by (auto split: if_splits)
    then have "u2' \<le> l1'" using p2_def q2_def ne_p2 ne_q2 by simp
    then have hle: "u2 \<le> l1" using bnds by order
    then have p1q1f: "interval_less_false p1 q1" using p1_def q1_def ne_p1 ne_q1 by simp
    have p1q1nt: "\<not> interval_less_true p1 q1"
    proof
      assume "interval_less_true p1 q1"
      then have "u1 < l2" using p1_def q1_def ne_p1 ne_q1 by simp
      with hle ne_p1 ne_q1 show False by order
    qed
    have "interval_lt p2 q2 = Some False" using False hlf unfolding interval_lt_def by simp
    with hwide have "b = False" by simp
    then show ?thesis using p1q1f p1q1nt unfolding interval_lt_def by simp
  qed
qed


lemma interval_eqb_mono:
  assumes hp: "\<not> is_bot (p1::ivl)" and hq: "\<not> is_bot q1"
      and hpm: "p1 \<le> p2" and hqm: "q1 \<le> q2"
      and hwide: "interval_eqb p2 q2 = Some b"
  shows "interval_eqb p1 q1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  obtain l2 u2 where q1_def: "q1 = Ivl l2 u2" by (cases q1)
  obtain l2' u2' where q2_def: "q2 = Ivl l2' u2'" by (cases q2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_bot_ivl is_bottom_ivl_def by auto
  have ne_q1: "l2 \<le> u2" using hq unfolding q1_def is_bot_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'" "l2' \<le> l2" "u2 \<le> u2'"
    using hpm hqm unfolding p1_def p2_def q1_def q2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" and ne_q2: "l2' \<le> u2'"
    using bnds ne_p1 ne_q1 by order+
  show ?thesis
    using hwide ne_p1 ne_q1 ne_p2 ne_q2 bnds
    unfolding interval_eqb_def p1_def p2_def q1_def q2_def
    by (auto split: if_splits; order)
qed

lemma interval_tobool_mono:
  assumes hp: "\<not> is_bot (p1::ivl)" and hpm: "p1 \<le> p2"
      and hwide: "interval_tobool p2 = Some b"
  shows "interval_tobool p1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_bot_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'"
    using hpm unfolding p1_def p2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" using bnds ne_p1 by order
  show ?thesis
    using hwide ne_p1 ne_p2 bnds
    unfolding interval_tobool_def p1_def p2_def
    by (auto split: if_splits; order)
qed

subsection \<open>Ikind-aware casting\<close>

text \<open>
  \<open>ivl_cast\<close> mirrors Goblint's own \<open>IntervalDomain.norm ~cast:true\<close> exactly
  (source-checked 2026-08-25 against \<open>intervalDomain.ml\<close>): an unbounded side
  cannot be wrapped at all (\<open>top\<close>); a finite range already inside \<open>ik\<close>'s
  bounds is untouched; a finite range wider than \<open>ik\<close>'s own representable
  width cannot wrap as one connected interval (\<open>top\<close>, matching Goblint's
  \<open>resdiff > diff\<close> check); otherwise each bound wraps via \<open>ik_norm\<close>, and if
  the wrapped bounds come out disordered the wrapped range is disconnected
  and unrepresentable (\<open>top\<close>, matching Goblint's post-wrap \<open>l \<le> u\<close> check).
\<close>

definition ivl_cast :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_cast ik a =
     (if is_bottom_ivl a then bot
      else case a of Ivl lo hi \<Rightarrow>
        (case (lo, hi) of
           (Fin l, Fin h) \<Rightarrow>
             (if ik_min ik \<le> l \<and> h \<le> ik_max ik then a
              else if h - l > ik_max ik - ik_min ik then top
              else let l' = ik_norm ik l; h' = ik_norm ik h
                   in if l' \<le> h' then Ivl (Fin l') (Fin h') else top)
         | _ \<Rightarrow> top))"

subsection \<open>Abstract expression evaluation\<close>

text \<open>
  \<open>aval_ivl_t\<close> is the sole evaluator for intervals: it operates directly on
  an already-elaborated \<^typ>\<open>texp\<close>, so it needs no \<open>\<Gamma>\<close>/\<open>ik\<close> parameter of
  its own -- every node already carries the kind it should be cast/normed
  at. Every arithmetic node is normed once through \<^const>\<open>ivl_cast\<close> at
  its own kind, matching Goblint's own \<open>norm ~cast:true\<close> wraparound-or-widen
  behavior exactly -- a bespoke cast against the interval's own bounds,
  not a generic boundary-conservative fallback -- and \<open>TLess\<close>/\<open>TEq\<close>/\<open>TNot\<close>/\<open>TAnd\<close>/\<open>TOr\<close> never
  norm their own 0/1-shaped result, matching \<^const>\<open>teval\<close>. \<open>aval_ivl\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale this interprets below) is a thin wrapper elaborating its argument
  once and handing it to \<open>aval_ivl_t\<close>, not a second, independent recursion
  to keep in sync: both \<open>Interval_Transfer\<close>'s forward obligations and the
  \<open>backward_domain_refined\<close> interpretation below target it.
\<close>
fun aval_ivl_t :: "texp => (vname => ivl) => ivl" where
    "aval_ivl_t (TN ik n)        \<sigma> = ivl_cast ik (Ivl (Fin n) (Fin n))"
  | "aval_ivl_t (TV ik x)        \<sigma> = ivl_cast ik (\<sigma> x)"
  | "aval_ivl_t (TPlus  ik a b)  \<sigma> = ivl_cast ik (aval_ivl_t a \<sigma> + aval_ivl_t b \<sigma>)"
  | "aval_ivl_t (TMinus ik a b)  \<sigma> = ivl_cast ik (aval_ivl_t a \<sigma> - aval_ivl_t b \<sigma>)"
  | "aval_ivl_t (TTimes ik a b)  \<sigma> = ivl_cast ik (aval_ivl_t a \<sigma> * aval_ivl_t b \<sigma>)"
  | "aval_ivl_t (TLess a b) \<sigma> =
       (if is_bot (aval_ivl_t a \<sigma>) \<or> is_bot (aval_ivl_t b \<sigma>) then bot
        else if interval_lt (aval_ivl_t a \<sigma>) (aval_ivl_t b \<sigma>) = Some True then Ivl (Fin 1) (Fin 1)
        else if interval_lt (aval_ivl_t a \<sigma>) (aval_ivl_t b \<sigma>) = Some False then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl_t (TEq a b) \<sigma> =
       (if is_bot (aval_ivl_t a \<sigma>) \<or> is_bot (aval_ivl_t b \<sigma>) then bot
        else if interval_eqb (aval_ivl_t a \<sigma>) (aval_ivl_t b \<sigma>) = Some True then Ivl (Fin 1) (Fin 1)
        else if interval_eqb (aval_ivl_t a \<sigma>) (aval_ivl_t b \<sigma>) = Some False then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl_t (TNot a) \<sigma> =
       (if is_bot (aval_ivl_t a \<sigma>) then bot
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some True then Ivl (Fin 0) (Fin 0)
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some False then Ivl (Fin 1) (Fin 1)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl_t (TAnd a b) \<sigma> =
       (if is_bot (aval_ivl_t a \<sigma>) \<or> is_bot (aval_ivl_t b \<sigma>) then bot
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some False
                \<or> interval_tobool (aval_ivl_t b \<sigma>) = Some False
        then Ivl (Fin 0) (Fin 0)
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some True
                \<and> interval_tobool (aval_ivl_t b \<sigma>) = Some True
        then Ivl (Fin 1) (Fin 1)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl_t (TOr a b) \<sigma> =
       (if is_bot (aval_ivl_t a \<sigma>) \<or> is_bot (aval_ivl_t b \<sigma>) then bot
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some True
                \<or> interval_tobool (aval_ivl_t b \<sigma>) = Some True
        then Ivl (Fin 1) (Fin 1)
        else if interval_tobool (aval_ivl_t a \<sigma>) = Some False
                \<and> interval_tobool (aval_ivl_t b \<sigma>) = Some False
        then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"

definition aval_ivl :: "tyenv => ikind => exp => (vname => ivl) => ivl" where
  "aval_ivl \<Gamma> ik a \<sigma> = aval_ivl_t (elaborate \<Gamma> ik a) \<sigma>"

lemma ivl_cast_sound:
  assumes v: "v \<in> gamma_ivl a"
  shows "ik_norm ik v \<in> gamma_ivl (ivl_cast ik a)"
proof -
  have notbot: "\<not> is_bottom_ivl a"
    using v is_bottom_ivl_correct by (metis empty_iff)
  show ?thesis
  proof (cases a)
    case (Ivl lo hi)
    show ?thesis
    proof (cases "\<exists>l h. lo = Fin l \<and> hi = Fin h")
      case False
      with notbot Ivl show ?thesis
        by (cases lo; cases hi) (simp_all add: ivl_cast_def top_ivl_def gamma_ivl_top)
    next
      case True
      then obtain l h where lo_eq: "lo = Fin l" and hi_eq: "hi = Fin h" by blast
      have lv: "l \<le> v" and vh: "v \<le> h"
        using v Ivl lo_eq hi_eq by (auto simp: eint_le.simps)
      have cast_eq: "ivl_cast ik a =
          (if ik_min ik \<le> l \<and> h \<le> ik_max ik then a
           else if h - l > ik_max ik - ik_min ik then top
           else let l' = ik_norm ik l; h' = ik_norm ik h
                in if l' \<le> h' then Ivl (Fin l') (Fin h') else top)"
        using notbot Ivl lo_eq hi_eq by (simp add: ivl_cast_def)
      show ?thesis
      proof (cases "ik_min ik \<le> l \<and> h \<le> ik_max ik")
        case True
        then have "v \<in> ik_range ik" using lv vh by simp
        then have "ik_norm ik v = v" by (rule ik_norm_id)
        with True cast_eq v show ?thesis
          by simp
      next
        case not_inrange: False
        show ?thesis
        proof (cases "h - l > ik_max ik - ik_min ik")
          case True
          have "ivl_cast ik a = top"
            using cast_eq not_inrange True by simp
          then show ?thesis by (simp add: top_ivl_def gamma_ivl_top)
        next
          case width_ok: False
          show ?thesis
          proof (cases "ik_norm ik l \<le> ik_norm ik h")
            case ordered: True
            have wrap: "ik_norm ik l \<le> ik_norm ik v \<and> ik_norm ik v \<le> ik_norm ik h"
              using ik_norm_interval_wrap[of h l ik, OF _ ordered lv vh] width_ok by simp
            have "ivl_cast ik a = Ivl (Fin (ik_norm ik l)) (Fin (ik_norm ik h))"
              using cast_eq not_inrange width_ok ordered by (simp add: Let_def)
            with wrap show ?thesis by (simp add: eint_le.simps)
          next
            case False
            have "ivl_cast ik a = top"
              using cast_eq not_inrange width_ok False by (simp add: Let_def)
            then show ?thesis by (simp add: top_ivl_def gamma_ivl_top)
          qed
        qed
      qed
    qed
  qed
qed

lemma ivl_cast_mono:
  assumes le: "a1 \<le> a2"
  shows "ivl_cast ik a1 \<le> ivl_cast ik a2"
proof (cases "is_bottom_ivl a1")
  case True
  then have "ivl_cast ik a1 = bot" by (simp add: ivl_cast_def)
  then show ?thesis by (simp add: bot_least)
next
  case notbot1: False
  show ?thesis
  proof (cases "ivl_cast ik a2 = top")
    case True
    then show ?thesis by (simp add: top_greatest)
  next
    case a2_not_top: False
    have notbot2: "\<not> is_bottom_ivl a2"
    proof
      assume bot2: "is_bottom_ivl a2"
      then have "gamma_ivl a2 = {}" using is_bottom_ivl_correct by simp
      moreover have "gamma_ivl a1 \<subseteq> gamma_ivl a2" using le gamma_ivl_mono by simp
      moreover have "gamma_ivl a1 \<noteq> {}" using notbot1 is_bottom_ivl_correct by simp
      ultimately show False by blast
    qed
    obtain lo2 hi2 where a2_eq: "a2 = Ivl lo2 hi2" by (cases a2)
    obtain l2 h2 where lo2_eq: "lo2 = Fin l2" and hi2_eq: "hi2 = Fin h2"
      using a2_not_top notbot2 a2_eq
      by (cases lo2; cases hi2) (simp_all add: ivl_cast_def is_bottom_ivl_def)
    obtain lo1 hi1 where a1_eq: "a1 = Ivl lo1 hi1" by (cases a1)
    obtain l1 h1 where lo1_eq: "lo1 = Fin l1" and hi1_eq: "hi1 = Fin h1"
      using le notbot1 a1_eq a2_eq lo2_eq hi2_eq
      by (cases lo1; cases hi1) (auto simp: less_eq_ivl_def eint_le.simps is_bottom_ivl_def)
    have l1h1: "l1 \<le> h1"
      using notbot1 a1_eq lo1_eq hi1_eq by (simp add: is_bottom_ivl_def)
    have cast1_eq: "ivl_cast ik a1 =
        (if ik_min ik \<le> l1 \<and> h1 \<le> ik_max ik then a1
         else if h1 - l1 > ik_max ik - ik_min ik then top
         else let l' = ik_norm ik l1; h' = ik_norm ik h1
              in if l' \<le> h' then Ivl (Fin l') (Fin h') else top)"
      using notbot1 a1_eq lo1_eq hi1_eq by (simp add: ivl_cast_def)
    have cast2_eq: "ivl_cast ik a2 =
        (if ik_min ik \<le> l2 \<and> h2 \<le> ik_max ik then a2
         else if h2 - l2 > ik_max ik - ik_min ik then top
         else let l' = ik_norm ik l2; h' = ik_norm ik h2
              in if l' \<le> h' then Ivl (Fin l') (Fin h') else top)"
      using notbot2 a2_eq lo2_eq hi2_eq by (simp add: ivl_cast_def)
    have le12: "l2 \<le> l1" "h1 \<le> h2"
      using le a1_eq a2_eq lo1_eq hi1_eq lo2_eq hi2_eq by (auto simp: less_eq_ivl_def eint_le.simps)
    have l1h2: "l1 \<le> h2" and l2h1: "l2 \<le> h1"
      using l1h1 le12 by simp_all
    show ?thesis
    proof (cases "ik_min ik \<le> l2 \<and> h2 \<le> ik_max ik")
      case True
      then have cast2_val: "ivl_cast ik a2 = a2" using cast2_eq by simp
      have inrange1: "ik_min ik \<le> l1 \<and> h1 \<le> ik_max ik" using True le12 by simp
      have l1_id: "ik_norm ik l1 = l1"
        using inrange1 l1h1 by (intro ik_norm_id) simp
      have h1_id: "ik_norm ik h1 = h1"
        using inrange1 l1h1 by (intro ik_norm_id) simp
      have "ivl_cast ik a1 = a1" using inrange1 cast1_eq by simp
      with cast2_val le show ?thesis by simp
    next
      case not_inrange2: False
      have not_too_wide2: "\<not> h2 - l2 > ik_max ik - ik_min ik"
        using a2_not_top cast2_eq not_inrange2
        by (cases "h2 - l2 > ik_max ik - ik_min ik") simp_all
      have ordered2: "ik_norm ik l2 \<le> ik_norm ik h2"
        using a2_not_top cast2_eq not_inrange2 not_too_wide2
        by (cases "ik_norm ik l2 \<le> ik_norm ik h2") (simp_all add: Let_def)
      have wrap1: "ik_norm ik l2 \<le> ik_norm ik l1 \<and> ik_norm ik l1 \<le> ik_norm ik h2"
        using ik_norm_interval_wrap[of h2 l2 ik, OF _ ordered2 le12(1) l1h2] not_too_wide2 by simp
      have wrap2: "ik_norm ik l2 \<le> ik_norm ik h1 \<and> ik_norm ik h1 \<le> ik_norm ik h2"
        using ik_norm_interval_wrap[of h2 l2 ik, OF _ ordered2 l2h1 le12(2)] not_too_wide2 by simp
      have cast2_val: "ivl_cast ik a2 = Ivl (Fin (ik_norm ik l2)) (Fin (ik_norm ik h2))"
        using cast2_eq not_inrange2 not_too_wide2 ordered2 by (simp add: Let_def)
      show ?thesis
      proof (cases "ik_min ik \<le> l1 \<and> h1 \<le> ik_max ik")
        case True
        have l1_id: "ik_norm ik l1 = l1" using True l1h1 by (intro ik_norm_id) simp
        have h1_id: "ik_norm ik h1 = h1" using True l1h1 by (intro ik_norm_id) simp
        have "ivl_cast ik a1 = a1" using True cast1_eq by simp
        with cast2_val wrap1 wrap2 l1_id h1_id a1_eq lo1_eq hi1_eq show ?thesis
          by (simp add: less_eq_ivl_def eint_le.simps)
      next
        case not_inrange1: False
        have not_too_wide1: "\<not> h1 - l1 > ik_max ik - ik_min ik"
          using le12 not_too_wide2 by simp
        have width_l1h2: "h2 - l1 \<le> ik_max ik - ik_min ik"
          using le12 not_too_wide2 by simp
        have ord_l1h2: "ik_norm ik l1 \<le> ik_norm ik h2" using wrap1 by simp
        have wrap1h1: "ik_norm ik l1 \<le> ik_norm ik h1 \<and> ik_norm ik h1 \<le> ik_norm ik h2"
          using ik_norm_interval_wrap[of h2 l1 ik, OF width_l1h2 ord_l1h2 l1h1 le12(2)] by simp
        have ordered1: "ik_norm ik l1 \<le> ik_norm ik h1"
          using wrap1h1 by simp
        have "ivl_cast ik a1 = Ivl (Fin (ik_norm ik l1)) (Fin (ik_norm ik h1))"
          using cast1_eq not_inrange1 not_too_wide1 ordered1 by (simp add: Let_def)
        with cast2_val wrap1 wrap2 show ?thesis
          by (simp add: less_eq_ivl_def eint_le.simps)
      qed
    qed
  qed
qed

interpretation ivl_arith: expression_domain_sound
    aval_ivl ivl_cast "\<lambda>n. Ivl (Fin n) (Fin n)" interval_lt interval_eqb interval_tobool
  by unfold_locales
     (simp_all add: aval_ivl_def ivl_plus_sound ivl_minus_sound ivl_times_sound
                     ivl_plus_mono ivl_minus_mono ivl_times_mono
                     interval_lt_sound interval_eqb_sound
                     interval_tobool_sound[unfolded truthy_def]
                     interval_lt_mono interval_eqb_mono interval_tobool_mono
                     sup_ivl_def join_ivl.simps truthy_def top_ivl_def gamma_ivl_top Let_def
                     ivl_cast_sound ivl_cast_mono)

lemmas aval_ivl_sound = ivl_arith.aval_dom_sound[unfolded gamma_abs_ivl]
lemmas aval_ivl_mono = ivl_arith.aval_dom_mono

text \<open>
  \<open>aval_ivl_t (elaborate \<Gamma> ik a) = aval_ivl \<Gamma> ik a\<close> is immediate from
  \<open>aval_ivl\<close>'s own definition -- no induction needed, since \<open>aval_ivl_t\<close>
  is the primitive recursion and \<open>aval_ivl\<close> is defined in terms of it.
\<close>

lemma aval_ivl_t_elaborate [simp]:
  "aval_ivl_t (elaborate \<Gamma> ik a) \<sigma> = aval_ivl \<Gamma> ik a \<sigma>"
  by (simp add: aval_ivl_def)

lemma aval_ivl_t_elaborate_syn [simp]:
  "aval_ivl_t (elaborate_syn \<Gamma> a) \<sigma> = aval_ivl \<Gamma> (opk (esyn \<Gamma> a)) a \<sigma>"
  by (simp add: elaborate_syn_def)

lemma aval_ivl_t_sound:
  assumes "\<forall>x. s x \<in> gamma_ivl (sigma x)"
  shows "taval \<Gamma> ik a s \<in> gamma_ivl (aval_ivl_t (elaborate \<Gamma> ik a) sigma)"
  using aval_ivl_sound[OF assms] by simp

lemma aval_ivl_t_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_ivl_t (elaborate \<Gamma> ik a) sigma1 \<le> aval_ivl_t (elaborate \<Gamma> ik a) sigma2"
  using aval_ivl_mono by simp

lemma aval_ivl_t_sound_syn:
  assumes "\<forall>x. s x \<in> gamma_ivl (sigma x)"
  shows "taval_syn \<Gamma> a s \<in> gamma_ivl (aval_ivl_t (elaborate_syn \<Gamma> a) sigma)"
  unfolding taval_syn_def elaborate_syn_def using aval_ivl_t_sound[OF assms] .

lemma aval_ivl_t_mono_syn:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_ivl_t (elaborate_syn \<Gamma> a) sigma1 \<le> aval_ivl_t (elaborate_syn \<Gamma> a) sigma2"
  unfolding elaborate_syn_def using aval_ivl_t_mono .


subsection \<open>Backward inverse operators\<close>

text \<open>
  Inverse operators for backward analysis over intervals.
  @{text inv_less_ivl} performs precise interval narrowing: on the true branch
  of @{text "n1 < n2"}, the upper bound of @{text n1} tightens to one below
  the upper bound of @{text n2}, and the lower bound of @{text n2} tightens to
  one above the lower bound of @{text n1}.  On the false branch (@{text "n1 \<ge> n2"}),
  @{text n1}\<open>s\<close> lower bound tightens to the lower bound of @{text n2}, and @{text n2}\<open>s\<close>
  upper bound tightens to the upper bound of @{text n1}.  Plus/minus/times
  instantiate the shared @{const inv_conservative} (identity) instead of a
  per-domain no-op.
\<close>

fun inv_less_ivl :: "bool => ivl => ivl => ivl * ivl" where
    "inv_less_ivl True  (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl MinInf (u2 - Fin 1),
        Ivl l2 u2 \<sqinter> Ivl (l1 + Fin 1) PlusInf)"
  | "inv_less_ivl False (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl l2 PlusInf,
        Ivl l2 u2 \<sqinter> Ivl MinInf u1)"

lemma inv_less_ivl_n1_ub:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl MinInf (u2 - Fin 1))"
  by (cases u2; auto; linarith)

lemma inv_less_ivl_n2_lb:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl (l1 + Fin 1) PlusInf)"
  by (cases l1; auto; linarith)

lemma inv_less_ivl_n1_ge_lb:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl l2 PlusInf)"
  by (cases l2; auto; linarith)

lemma inv_less_ivl_n2_le_ub:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl MinInf u1)"
  by (cases u1; auto; linarith)

lemma inv_less_ivl_sound:
  assumes g1: "n1 \<in> gamma_ivl a1" and g2: "n2 \<in> gamma_ivl a2" and eq: "(n1 < n2) = res"
  shows "n1 \<in> gamma_ivl (fst (inv_less_ivl res a1 a2))
       \<and> n2 \<in> gamma_ivl (snd (inv_less_ivl res a1 a2))"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (rule ivl_exhaustE)
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (rule ivl_exhaustE)
  show ?thesis
  proof (cases res)
    case True
    have lt: "n1 < n2" using eq True by simp
    have p1: "n1 \<in> gamma_ivl (Ivl l1 u1 \<sqinter> Ivl MinInf (u2 - Fin 1))"
      by (rule meet_ivl_gamma[OF g1[unfolded ha1] inv_less_ivl_n1_ub[OF g2[unfolded ha2] lt]])
    have p2: "n2 \<in> gamma_ivl (Ivl l2 u2 \<sqinter> Ivl (l1 + Fin 1) PlusInf)"
      by (rule meet_ivl_gamma[OF g2[unfolded ha2] inv_less_ivl_n2_lb[OF g1[unfolded ha1] lt]])
    show ?thesis using p1 p2 by (simp add: True ha1 ha2)
  next
    case False
    have nlt: "\<not> n1 < n2" using eq False by simp
    have p1: "n1 \<in> gamma_ivl (Ivl l1 u1 \<sqinter> Ivl l2 PlusInf)"
      by (rule meet_ivl_gamma[OF g1[unfolded ha1] inv_less_ivl_n1_ge_lb[OF g2[unfolded ha2] nlt]])
    have p2: "n2 \<in> gamma_ivl (Ivl l2 u2 \<sqinter> Ivl MinInf u1)"
      by (rule meet_ivl_gamma[OF g2[unfolded ha2] inv_less_ivl_n2_le_ub[OF g1[unfolded ha1] nlt]])
    show ?thesis using p1 p2 by (simp add: False ha1 ha2)
  qed
qed

subsection \<open>Backward inverse operator for equality\<close>

text \<open>
  @{text inv_eq_ivl} narrows on a guard @{text \<open>e1 = e2\<close>} known true or false.
  The true branch narrows both operands to their intersection, the same
  argument as the sign instance via \<open>meet_ivl_gamma\<close>. The false
  branch is the sound identity: a precise refinement is possible in specific
  cases (e.g. excluding a known point value from one bound of the other
  operand when that point sits exactly at that bound), but @{typ ivl}'s
  infinite domain makes proving that refinement's monotonicity
  disproportionately more expensive than for the finite sign lattice ---
  attempted and abandoned; the guard conditions needed access the interval's
  own bound values, and a boundary-matching guard is not compatible with the
  order-based case-split technique that closed the sign proof. This is a
  documented precision gap, not a soundness one: \<open>bfilter\<close>'s @{text
  \<open>Eq _ _ False\<close>} case under this instance narrows exactly as much for
  Interval as it already does today (not at all), while Sign gains real
  precision from its own instance.
\<close>

fun inv_eq_ivl :: "bool => ivl => ivl => ivl * ivl" where
    "inv_eq_ivl True  a1 a2 = (meet_ivl a1 a2, meet_ivl a1 a2)"
  | "inv_eq_ivl False a1 a2 = (a1, a2)"

lemma inv_eq_ivl_sound:
  assumes "n1 \<in> gamma_ivl a1" and "n2 \<in> gamma_ivl a2" and "(n1 = n2) = res"
  shows "n1 \<in> gamma_ivl (fst (inv_eq_ivl res a1 a2))
       \<and> n2 \<in> gamma_ivl (snd (inv_eq_ivl res a1 a2))"
proof (cases res)
  case True
  then have "n1 = n2" using assms(3) by simp
  then have "n1 \<in> gamma_ivl a2" using assms(2) by simp
  then have "n1 \<in> gamma_ivl (meet_ivl a1 a2)" using meet_ivl_gamma[OF assms(1)] by simp
  then show ?thesis using True \<open>n1 = n2\<close> by simp
next
  case False
  then show ?thesis using assms(1,2) by simp
qed

lemma inv_eq_ivl_mono:
  assumes A1: "a1 \<le> (a1' :: ivl)" and A2: "a2 \<le> a2'"
  shows
    "fst (inv_eq_ivl r a1 a2) \<le> fst (inv_eq_ivl r a1' a2') \<and>
     snd (inv_eq_ivl r a1 a2) \<le> snd (inv_eq_ivl r a1' a2')"
proof (cases r)
  case True
  have "a1 \<sqinter> a2 \<le> a1' \<sqinter> a2'" by (rule inf_mono[OF A1 A2])
  then show ?thesis using True by (simp add: inf_ivl_def)
next
  case False
  then show ?thesis using A1 A2 by simp
qed

lemma inv_less_ivl_mono:
  assumes a1: "(a1 :: ivl) \<le> a1'" and a2: "(a2 :: ivl) \<le> a2'"
  shows "fst (inv_less_ivl res a1 a2) \<le> fst (inv_less_ivl res a1' a2')
       \<and> snd (inv_less_ivl res a1 a2) \<le> snd (inv_less_ivl res a1' a2')"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (rule ivl_exhaustE)
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (rule ivl_exhaustE)
  obtain l1' u1' where ha1': "a1' = Ivl l1' u1'" by (rule ivl_exhaustE)
  obtain l2' u2' where ha2': "a2' = Ivl l2' u2'" by (rule ivl_exhaustE)
  from a1[unfolded ha1 ha1' less_eq_ivl_def] have ord1: "eint_le l1' l1" "eint_le u1 u1'" by auto
  from a2[unfolded ha2 ha2' less_eq_ivl_def] have ord2: "eint_le l2' l2" "eint_le u2 u2'" by auto
  show ?thesis
  proof (cases res)
    case True
    then have r: "res = True" by simp
    have aux1: "Ivl MinInf (u2 - Fin 1) \<le> Ivl MinInf (u2' - Fin (1::int))"
      by (simp add: less_eq_ivl_def eint_minus_mono[OF ord2(2) eint_le_refl])
    have aux2: "Ivl (l1 + Fin 1) PlusInf \<le> Ivl (l1' + Fin (1::int)) PlusInf"
      by (simp add: less_eq_ivl_def eint_plus_mono[OF ord1(1) eint_le_refl])
    show ?thesis
      unfolding r ha1 ha2 ha1' ha2' inv_less_ivl.simps fst_conv snd_conv
    proof (intro conjI)
      show "Ivl l1 u1 \<sqinter> Ivl MinInf (u2 - Fin 1) \<le> Ivl l1' u1' \<sqinter> Ivl MinInf (u2' - Fin 1)"
        by (intro inf_mono a1[unfolded ha1 ha1'] aux1)
      show "Ivl l2 u2 \<sqinter> Ivl (l1 + Fin 1) PlusInf \<le> Ivl l2' u2' \<sqinter> Ivl (l1' + Fin 1) PlusInf"
        by (intro inf_mono a2[unfolded ha2 ha2'] aux2)
    qed
  next
    case False
    then have r: "res = False" by simp
    have aux3: "Ivl l2 PlusInf \<le> Ivl l2' PlusInf"
      by (simp add: less_eq_ivl_def ord2(1) eint_le_refl)
    have aux4: "Ivl MinInf u1 \<le> Ivl MinInf u1'"
      by (simp add: less_eq_ivl_def ord1(2) eint_le_refl)
    show ?thesis
      unfolding r ha1 ha2 ha1' ha2' inv_less_ivl.simps fst_conv snd_conv
    proof (intro conjI)
      show "Ivl l1 u1 \<sqinter> Ivl l2 PlusInf \<le> Ivl l1' u1' \<sqinter> Ivl l2' PlusInf"
        by (intro inf_mono a1[unfolded ha1 ha1'] aux3)
      show "Ivl l2 u2 \<sqinter> Ivl MinInf u1 \<le> Ivl l2' u2' \<sqinter> Ivl MinInf u1'"
        by (intro inf_mono a2[unfolded ha2 ha2'] aux4)
    qed
  qed
qed

text \<open>
  Reductiveness: @{const inv_less_ivl}/@{const inv_eq_ivl} only ever narrow an
  operand via @{const meet_ivl} or pass it through unchanged. \<open>meet_ivl_le_lb1\<close>/
  \<open>meet_ivl_le_lb2\<close> are stated via \<open>(\<sqinter>)\<close>, not \<open>meet_ivl\<close> itself, so restate them
  directly in terms of \<open>meet_ivl\<close> here (matching the case-split style already
  used in the @{class semilattice_inf} instance proof) for direct use below.
\<close>

lemma meet_ivl_le1: "meet_ivl a b \<le> a"
  by (cases a; cases b;
      simp add: less_eq_ivl_def;
      metis eint_le_linear eint_le_trans eint_le_refl)

lemma meet_ivl_le2: "meet_ivl a b \<le> b"
  by (cases a; cases b;
      auto simp: less_eq_ivl_def split: if_splits intro: eint_le_trans eint_le_refl)

lemma inv_less_ivl_reductive1: "fst (inv_less_ivl res a1 a2) \<le> a1"
  apply (cases res; cases a1; cases a2)
  using eint_le_linear less_eq_ivl_def by(auto)

lemma inv_less_ivl_reductive2: "snd (inv_less_ivl res a1 a2) \<le> a2"
  apply (cases res; cases a1; cases a2)
  using eint_le_linear less_eq_ivl_def by(auto)

lemma inv_eq_ivl_reductive1: "fst (inv_eq_ivl res a1 a2) \<le> a1"
  by (cases res; simp add: meet_ivl_le1)

lemma inv_eq_ivl_reductive2: "snd (inv_eq_ivl res a1 a2) \<le> a2"
  by (cases res; simp add: meet_ivl_le2)


subsection \<open>Backward-domain interpretation\<close>

text \<open>
  One interpretation discharges soundness, monotonicity, and reductiveness
  together against @{locale backward_domain_refined} -- each \<open>inv_*\<close>'s
  mono/reductive obligation is one @{const le_pair} fact, built from the
  componentwise per-operator lemmas above.

  The \<open>intersect\<close> parameter is instantiated with \<^const>\<open>intersect_ivl\<close>, not with the
  lattice \<^const>\<open>inf\<close>. The locale only requires \<open>intersect\<close> to preserve
  concretizations, to be reductive in both arguments, and to be monotone --- never
  that it is the greatest lower bound of the representation order --- and the
  normalising variant additionally keeps every filtered state canonical, so an
  infeasible guard stores \<^const>\<open>bot\<close> instead of a reversed bound pair.
  \<^const>\<open>inf\<close> itself cannot be normalised without losing the greatest-lower-bound
  law; @{thm [source] meet_ivl_normalized_breaks_greatest} is that counterexample.
\<close>

global_interpretation ivl_backward_domain:
    backward_domain_refined intersect_ivl aval_ivl interval_tobool
                    inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative
  defines
    afilter_ivl = ivl_backward_domain.afilter
    and feasible_ivl = ivl_backward_domain.feasible
    and bfilter_ivl = ivl_backward_domain.bfilter
    and branch_ivl = ivl_backward_domain.branch
    and branch_lifted_ivl = ivl_backward_domain.branch_lifted
    and afilter_ivl_st = ivl_backward_domain.afilter_st
    and bfilter_ivl_st = ivl_backward_domain.bfilter_st
    and branch_ivl_st = ivl_backward_domain.branch_st
proof unfold_locales
  fix n :: int and a b :: ivl
  assume H1: "n \<in> gamma a" and H2: "n \<in> gamma b"
  have h1: "n \<in> gamma_ivl a" using H1 by simp
  have h2: "n \<in> gamma_ivl b" using H2 by simp
  show "n \<in> gamma (intersect_ivl a b)"
    using intersect_ivl_gamma[OF h1 h2] by simp
next
  fix s :: store and e :: exp and \<Gamma> :: tyenv and ik :: ikind and \<sigma> :: "vname \<Rightarrow> ivl"
  assume H: "\<forall>x. s x \<in> gamma (\<sigma> x)"
  have h: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" using H by simp
  show "taval \<Gamma> ik e s \<in> gamma (aval_ivl \<Gamma> ik e \<sigma>)"
    using aval_ivl_sound[of s \<sigma> \<Gamma> ik e] h by simp
next
  fix n1 n2 :: int and a1 a2 :: ivl and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 < n2) = res"
  have h1: "n1 \<in> gamma_ivl a1" using H1 by simp
  have h2: "n2 \<in> gamma_ivl a2" using H2 by simp
  show "n1 \<in> gamma (fst (inv_less_ivl res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less_ivl res a1 a2))"
    using inv_less_ivl_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 :: ivl and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 = n2) = res"
  have h1: "n1 \<in> gamma_ivl a1" using H1 by simp
  have h2: "n2 \<in> gamma_ivl a2" using H2 by simp
  show "n1 \<in> gamma (fst (inv_eq_ivl res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq_ivl res a1 a2))"
    using inv_eq_ivl_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 :: ivl and ik :: ikind and r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "ik_norm ik (n1 + n2) \<in> gamma r"
  show
    "n1 \<in> gamma (fst (inv_conservative ik r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_conservative ik r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 :: ivl and ik :: ikind and r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "ik_norm ik (n1 - n2) \<in> gamma r"
  show
    "n1 \<in> gamma (fst (inv_conservative ik r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_conservative ik r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 :: ivl and ik :: ikind and r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "ik_norm ik (n1 * n2) \<in> gamma r"
  show
    "n1 \<in> gamma (fst (inv_conservative ik r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_conservative ik r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix p :: ivl and b :: bool and i :: int
  assume "interval_tobool p = Some b" and "i \<in> gamma p"
  then show "truthy i = b" using interval_tobool_sound by simp
next
  fix a1 a2 b1 b2 :: ivl
  assume "a1 \<le> a2" and "b1 \<le> b2"
  thus "intersect_ivl a1 b1 \<le> intersect_ivl a2 b2" by (rule intersect_ivl_mono)
next
  fix e :: exp and \<Gamma> :: tyenv and ik :: ikind and \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> ivl"
  assume "\<sigma>1 \<le> \<sigma>2"
  thus "aval_ivl \<Gamma> ik e \<sigma>1 \<le> aval_ivl \<Gamma> ik e \<sigma>2" by (rule aval_ivl_mono)
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_less_ivl res x1 y1) (inv_less_ivl res x2 y2)"
    using inv_less_ivl_mono[OF A B] by (simp add: le_pair_def)
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_eq_ivl res x1 y1) (inv_eq_ivl res x2 y2)"
    using inv_eq_ivl_mono[OF A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: ivl and ik :: ikind
  assume "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_conservative ik r1 x1 y1) (inv_conservative ik r2 x2 y2)"
    using A B by (simp add: inv_conservative_def le_pair_def)
next
  fix a b :: ivl
  show "intersect_ivl a b \<le> a" by (rule intersect_ivl_le1)
next
  fix a b :: ivl
  show "intersect_ivl a b \<le> b" by (rule intersect_ivl_le2)
next
  fix res :: bool and a1 a2 :: ivl
  show "le_pair (inv_less_ivl res a1 a2) (a1, a2)"
    using inv_less_ivl_reductive1 inv_less_ivl_reductive2 by (simp add: le_pair_def)
next
  fix res :: bool and a1 a2 :: ivl
  show "le_pair (inv_eq_ivl res a1 a2) (a1, a2)"
    using inv_eq_ivl_reductive1 inv_eq_ivl_reductive2 by (simp add: le_pair_def)
next
  fix r a1 a2 :: ivl and ik :: ikind
  show "le_pair (inv_conservative ik r a1 a2) (a1, a2)"
    by (simp add: inv_conservative_def le_pair_def)
next
  fix p1 p2 :: ivl and bv :: bool
  assume "\<not> is_bot p1" and "p1 \<le> p2" and "interval_tobool p2 = Some bv"
  then show "interval_tobool p1 = Some bv" using interval_tobool_mono by simp
qed

text \<open>
  Executable @{typ "ivl resolved_st_q"} mirror of \<open>afilter_ivl\<close> /
  \<open>bfilter_ivl\<close>, and its commutation with the abstract filters through
  @{const fun_of_resolved_st_q_for}. Both come from the generic
  @{locale backward_domain} executable mirror (\<open>Exec_Backward\<close>).
\<close>

lemmas afilter_ivl_st_commute = ivl_backward_domain.afilter_st_commute
lemmas bfilter_ivl_st_commute = ivl_backward_domain.bfilter_st_commute
lemmas branch_ivl_st_commute = ivl_backward_domain.branch_st_commute

lemma afilter_ivl_mono:
  "a1 \<le> (a2 :: ivl) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_ivl \<Gamma> ik e a1 sigma1 \<le> afilter_ivl \<Gamma> ik e a2 sigma2"
  using ivl_backward_domain.afilter_mono by (simp add: afilter_ivl_def)

lemma bfilter_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_ivl \<Gamma> b res sigma1 \<le> bfilter_ivl \<Gamma> b res sigma2"
  using ivl_backward_domain.bfilter_mono by (simp add: bfilter_ivl_def)

lemma branch_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_ivl \<Gamma> b res sigma1 \<le> branch_ivl \<Gamma> b res sigma2"
  using ivl_backward_domain.branch_mono by (simp add: branch_ivl_def)

lemma branch_ivl_le_bfilter_ivl: "branch_ivl \<Gamma> e pol \<sigma> \<le> bfilter_ivl \<Gamma> e pol \<sigma>"
  using ivl_backward_domain.branch_le_bfilter by (simp add: branch_ivl_def bfilter_ivl_def)

end

