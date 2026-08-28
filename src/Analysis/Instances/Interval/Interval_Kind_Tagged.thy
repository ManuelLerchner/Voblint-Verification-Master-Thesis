theory Interval_Kind_Tagged
  imports Interval_Backward Interval_Warrowing Voblint_Core.Kind_Tagged
begin

section \<open>Intervals as a kind-clampable component\<close>

text \<open>
  \<^const>\<open>widen_ivl_core\<close> sends a moved bound to \<^const>\<open>MinInf\<close> or
  \<^const>\<open>PlusInf\<close>, which is outside every kind's range, so the conversion at
  the next node has an operand it cannot represent and answers
  \<^const>\<open>ivl_top_of\<close> -- discarding the bound the widening kept. Goblint's own
  interval widening saturates at \<open>min_int_of ik\<close>/\<open>max_int_of ik\<close> instead, so
  its normalization is the identity on a widened value.

  \<^class>\<open>kind_clamp\<close> is what a tagged cell needs of its component to do the
  same: the kind's greatest element, and a cut-down against it.
\<close>

subsection \<open>Pointwise extrema on the bound type\<close>

fun eint_max :: "eint \<Rightarrow> eint \<Rightarrow> eint" where
  "eint_max a b = (if a \<le> b then b else a)"

fun eint_min :: "eint \<Rightarrow> eint \<Rightarrow> eint" where
  "eint_min a b = (if a \<le> b then a else b)"

text \<open>\<^const>\<open>eint_le\<close> is total, which is the one fact every bound comparison
  below turns on.\<close>

lemma eint_not_le [dest]: "\<not> eint_le a b \<Longrightarrow> eint_le b a"
  using eint_le_linear[of a b] by blast

lemma eint_max_ge1 [simp]: "a \<le> eint_max a b"
  by (simp add: eint_le_refl)

lemma eint_max_ge2 [simp]: "b \<le> eint_max a b"
  using eint_le_linear[of a b] by (auto simp: eint_le_refl less_eq_eint_def)

lemma eint_min_le1 [simp]: "eint_min a b \<le> a"
  by (auto simp: eint_le_refl less_eq_eint_def)

lemma eint_min_le2 [simp]: "eint_min a b \<le> b"
  using eint_le_linear[of a b] by (auto simp: eint_le_refl less_eq_eint_def)

lemma eint_max_least: "a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> eint_max a b \<le> c"
  by simp

lemma eint_min_greatest: "c \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> eint_min a b"
  by simp

subsection \<open>The clamp\<close>

text \<open>
  The clamp raises the lower bound to the kind's minimum and lowers the upper
  bound to its maximum. It does \<^emph>\<open>not\<close> collapse an empty result to
  \<^const>\<open>bot\<close>, and that is deliberate: the interval order compares bounds
  syntactically, so \<^term>\<open>bot :: ivl\<close> is one particular empty interval rather
  than every empty one. Collapsing would break \<open>a_clamp_greatest\<close> -- take
  \<^term>\<open>Ivl (Fin 200) (Fin 40)\<close> below \<^term>\<open>Ivl (Fin 100) (Fin 50)\<close>, both
  inside \<^const>\<open>I32\<close>'s range and both empty, where the clamped result is empty
  but the operand is not below \<^const>\<open>bot\<close>. Leaving the clamped pair as it
  falls keeps all three laws unconditional, and \<^const>\<open>is_bottom_ivl\<close> already
  recognizes an empty interval wherever emptiness is what matters.
\<close>

definition ivl_clamp :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_clamp ik i =
     (case i of Ivl l u \<Rightarrow>
        Ivl (eint_max l (Fin (ik_min ik))) (eint_min u (Fin (ik_max ik))))"

lemma ivl_clamp_simp [simp]:
  "ivl_clamp ik (Ivl l u) = Ivl (eint_max l (Fin (ik_min ik))) (eint_min u (Fin (ik_max ik)))"
  by (simp add: ivl_clamp_def)

instantiation ivl :: kind_clamp
begin

definition "a_top_of_ivl = ivl_top_of"
definition "a_clamp_ivl = ivl_clamp"

instance
proof intro_classes
  fix k :: ikind and a c :: ivl
  show "a_clamp k c \<le> c"
    by (cases c)
       (auto simp: a_clamp_ivl_def less_eq_ivl_def less_eq_eint_def eint_le_refl
             dest: eint_le_linear[THEN disjE])
  show "a_clamp k c \<le> a_top_of k"
    by (cases c)
       (auto simp: a_clamp_ivl_def a_top_of_ivl_def ivl_top_of_def less_eq_ivl_def
                   less_eq_eint_def eint_le_refl
             dest: eint_le_linear[THEN disjE])
  show "a \<le> c \<Longrightarrow> a \<le> a_top_of k \<Longrightarrow> a \<le> a_clamp k c"
    by (cases a; cases c)
       (auto simp: a_clamp_ivl_def a_top_of_ivl_def ivl_top_of_def less_eq_ivl_def
             intro: eint_max_least eint_min_greatest)
qed

end

text \<open>
  The clamp is exact on values the kind can already hold, so cutting an
  in-range interval down changes nothing. This is what makes the tagged
  widening lose no precision it would otherwise have kept: it only ever
  removes what the kind cannot represent.
\<close>

lemma ivl_clamp_id_in_range:
  assumes "a \<le> ivl_top_of k"
  shows "ivl_clamp k a = a"
proof (cases a)
  fix l u assume a: "a = Ivl l u"
  from assms a have "Fin (ik_min k) \<le> l" "u \<le> Fin (ik_max k)"
    by (simp_all add: ivl_top_of_def less_eq_ivl_def)
  then show ?thesis using a
    by (auto simp: less_eq_eint_def eint_le_refl dest: eint_le_antisym)
qed

text \<open>
  Concretization is unchanged on the values the kind can hold, and the clamp
  is sound in general: it never drops an integer that is both described by the
  operand and representable at the kind.
\<close>

lemma gamma_ivl_clamp_sound:
  "v \<in> gamma_ivl a \<Longrightarrow> v \<in> ik_range k \<Longrightarrow> v \<in> gamma_ivl (ivl_clamp k a)"
  by (cases a)
     (auto simp: less_eq_eint_def eint_le_refl
           dest: eint_le_linear[THEN disjE] eint_le_trans)

subsection \<open>Termination of the clamped widening\<close>

text \<open>
  The clamped widening is what a tagged cell computes on a matched pair. Its
  termination argument is the unclamped one with the kind's own extremes in
  place of the infinities: each bound still takes at most one outward jump,
  and the state it jumps to is now \<^term>\<open>Fin (ik_min k)\<close> or
  \<^term>\<open>Fin (ik_max k)\<close> rather than \<^const>\<open>MinInf\<close> or \<^const>\<open>PlusInf\<close>.
  Absorbing either way, so a widen-ascending chain is constant after at most
  two transitions per bound.
\<close>

definition widen_ivl_clamped :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "widen_ivl_clamped k a b = ivl_clamp k (widen_ivl_core a b)"

text \<open>
  One step, at the lower bound. An operand already at or above the kind's
  minimum either keeps its bound or lands exactly on that minimum: the
  unclamped widening offers only the old bound or \<^const>\<open>MinInf\<close>, and the
  clamp maps the first to itself and the second to \<^term>\<open>Fin (ik_min k)\<close>.
\<close>

lemma widen_ivl_clamped_lower_step:
  assumes "Fin (ik_min k) \<le> l1"
  shows "ivl_lower (widen_ivl_clamped k (Ivl l1 u1) (Ivl l2 u2)) = l1
         \<or> ivl_lower (widen_ivl_clamped k (Ivl l1 u1) (Ivl l2 u2)) = Fin (ik_min k)"
  using assms
  by (auto simp: widen_ivl_clamped_def less_eq_eint_def eint_le_refl)

lemma widen_ivl_clamped_upper_step:
  assumes "u1 \<le> Fin (ik_max k)"
  shows "ivl_upper (widen_ivl_clamped k (Ivl l1 u1) (Ivl l2 u2)) = u1
         \<or> ivl_upper (widen_ivl_clamped k (Ivl l1 u1) (Ivl l2 u2)) = Fin (ik_max k)"
  using assms
  by (auto simp: widen_ivl_clamped_def less_eq_eint_def eint_le_refl)

text \<open>
  The clamped widening stays in range, whatever it is handed. This is the
  component-level form of the tagged carrier's own invariant, and it is what
  makes the conversion at the next node exact rather than a give-up.
\<close>

lemma widen_ivl_clamped_in_range: "widen_ivl_clamped k a b \<le> ivl_top_of k"
  unfolding widen_ivl_clamped_def
  by (cases "widen_ivl_core a b")
     (auto simp: ivl_top_of_def less_eq_ivl_def less_eq_eint_def eint_le_refl)

text \<open>
  Every clamped-widen-ascending chain over in-range intervals stabilises. The
  argument is \<open>widen_ivl_core_terminates\<close>'s, with the kind's own extremes as
  the absorbing states: a bound that has reached \<^term>\<open>Fin (ik_min k)\<close> or
  \<^term>\<open>Fin (ik_max k)\<close> can only be offered itself again, so each bound
  changes at most once and the chain is constant after at most two
  transitions.
\<close>

lemma widen_ivl_clamped_terminates:
  assumes chain: "\<And>i. widen_ivl_clamped k (f i) (f (Suc i)) = f (Suc i)"
      and rng: "\<And>i. f i \<le> ivl_top_of k"
  shows "\<exists>n. \<forall>j. n \<le> j \<longrightarrow> f j = f n"
proof -
  define lb where "lb i = ivl_lower (f i)" for i
  define ub where "ub i = ivl_upper (f i)" for i
  have f_eq: "f i = Ivl (lb i) (ub i)" for i
    unfolding lb_def ub_def by (cases "f i") simp
  have bounds: "Fin (ik_min k) \<le> lb i" "ub i \<le> Fin (ik_max k)" for i
    using rng[of i] f_eq[of i]
    by (auto simp: ivl_top_of_def less_eq_ivl_def)
  have step:
    "lb (Suc i) = lb i \<or> lb (Suc i) = Fin (ik_min k)"
    "ub (Suc i) = ub i \<or> ub (Suc i) = Fin (ik_max k)"
    for i
  proof -
    have w: "widen_ivl_clamped k (Ivl (lb i) (ub i)) (Ivl (lb (Suc i)) (ub (Suc i)))
             = Ivl (lb (Suc i)) (ub (Suc i))"
      using chain[of i] f_eq[of i] f_eq[of "Suc i"] by simp
    from widen_ivl_clamped_lower_step[OF bounds(1)[of i],
           of "ub i" "lb (Suc i)" "ub (Suc i)"] w
    show "lb (Suc i) = lb i \<or> lb (Suc i) = Fin (ik_min k)" by simp
    from widen_ivl_clamped_upper_step[OF bounds(2)[of i],
           of "lb i" "lb (Suc i)" "ub (Suc i)"] w
    show "ub (Suc i) = ub i \<or> ub (Suc i) = Fin (ik_max k)" by simp
  qed
  have lb_stay_le: "lb i = Fin (ik_min k) \<Longrightarrow> i \<le> j \<Longrightarrow> lb j = Fin (ik_min k)" for i j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(1) le_SucE by metis
  qed
  have ub_stay_le: "ub i = Fin (ik_max k) \<Longrightarrow> i \<le> j \<Longrightarrow> ub j = Fin (ik_max k)" for i j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(2) le_SucE by metis
  qed
  have lb_const: "(\<forall>m. lb m \<noteq> Fin (ik_min k)) \<Longrightarrow> lb j = lb 0" for j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(1)[of j] by auto
  qed
  have ub_const: "(\<forall>m. ub m \<noteq> Fin (ik_max k)) \<Longrightarrow> ub j = ub 0" for j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(2)[of j] by auto
  qed
  obtain nl where nl: "\<forall>j \<ge> nl. lb j = lb nl"
  proof (cases "\<exists>m. lb m = Fin (ik_min k)")
    case True
    then obtain m where m: "lb m = Fin (ik_min k)" by blast
    then have "\<forall>j \<ge> m. lb j = lb m" using lb_stay_le by metis
    then show ?thesis by (rule that)
  next
    case False
    then have "\<forall>j. lb j = lb 0" using lb_const by blast
    then have "\<forall>j \<ge> 0. lb j = lb 0" by blast
    then show ?thesis by (rule that)
  qed
  obtain nu where nu: "\<forall>j \<ge> nu. ub j = ub nu"
  proof (cases "\<exists>m. ub m = Fin (ik_max k)")
    case True
    then obtain m where m: "ub m = Fin (ik_max k)" by blast
    then have "\<forall>j \<ge> m. ub j = ub m" using ub_stay_le by metis
    then show ?thesis by (rule that)
  next
    case False
    then have "\<forall>j. ub j = ub 0" using ub_const by blast
    then have "\<forall>j \<ge> 0. ub j = ub 0" by blast
    then show ?thesis by (rule that)
  qed
  let ?n = "max nl nu"
  have "\<forall>j. ?n \<le> j \<longrightarrow> f j = f ?n"
  proof (intro allI impI)
    fix j assume jn: "?n \<le> j"
    from jn have "nl \<le> j" "nl \<le> ?n" "nu \<le> j" "nu \<le> ?n" by auto
    then have "lb j = lb ?n" "ub j = ub ?n"
      using nl nu by (metis, metis)
    then show "f j = f ?n" using f_eq by simp
  qed
  then show ?thesis by blast
qed

end
