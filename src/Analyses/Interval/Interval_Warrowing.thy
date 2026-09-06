theory Interval_Warrowing
  imports Interval_Lattice "TD.Update_rules"
begin

section \<open>Interval widening and narrowing\<close>

subsection \<open>Widening\<close>

text \<open>
  Standard interval widening: keep a bound if it did not move outward, otherwise
  push it to the infinite end.  Every widen-ascending chain therefore stabilises
  after at most two steps (each bound takes at most one outward jump).
\<close>

fun widen_ivl_core :: "ivl => ivl => ivl" where
    "widen_ivl_core (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if l1 \<le> l2 then l1 else MinInf)
           (if u2 \<le> u1 then u1 else PlusInf)"

lemma a_le_widen_ivl_core: "(a :: ivl) \<le> widen_ivl_core a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "a \<le> widen_ivl_core a b"
    unfolding less_eq_ivl_def by (auto simp: eint_le_refl)
qed

lemma b_le_widen_ivl_core: "(b :: ivl) \<le> widen_ivl_core a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "b \<le> widen_ivl_core a b"
    unfolding less_eq_ivl_def
    using eint_le_linear[of l1 l2] eint_le_linear[of u2 u1]
    by auto
qed

lemma widen_ivl_core_ub1: "gamma_ivl a \<subseteq> gamma_ivl (widen_ivl_core a b)"
  using gamma_ivl_mono a_le_widen_ivl_core by blast

lemma widen_ivl_core_ub2: "gamma_ivl b \<subseteq> gamma_ivl (widen_ivl_core a b)"
  using gamma_ivl_mono b_le_widen_ivl_core by blast

text \<open>
  Widening termination: every widen-ascending chain stabilises.  At each step
  each bound either stays or jumps to @{text MinInf} / @{text PlusInf}, and once
  a bound reaches the infinite end it remains there.  After at most two
  transitions the chain is constant.
\<close>
lemma widen_ivl_core_terminates:
  assumes "\<forall>i. widen_ivl_core (f i) (f (Suc i)) = f (Suc i)"
  shows "\<exists>n. \<forall>j. n \<le> j \<longrightarrow> f j = f n"
proof -
  define lb where "lb i = ivl_lower (f i)" for i
  define ub where "ub i = ivl_upper (f i)" for i
  have f_eq: "f i = Ivl (lb i) (ub i)" for i
    unfolding lb_def ub_def by (cases "f i") simp
  have step:
    "lb (Suc i) = lb i \<or> lb (Suc i) = MinInf"
    "ub (Suc i) = ub i \<or> ub (Suc i) = PlusInf"
    for i
  proof -
    have "widen_ivl_core (Ivl (lb i) (ub i)) (Ivl (lb (Suc i)) (ub (Suc i))) =
          Ivl (lb (Suc i)) (ub (Suc i))"
      using assms[rule_format, of i] f_eq[of i] f_eq[of "Suc i"] by simp
    then have eqs:
      "lb (Suc i) = (if eint_le (lb i) (lb (Suc i)) then lb i else MinInf)"
      "ub (Suc i) = (if eint_le (ub (Suc i)) (ub i) then ub i else PlusInf)"
      by simp_all
    from eqs(1) show "lb (Suc i) = lb i \<or> lb (Suc i) = MinInf"
      by (auto split: if_splits)
    from eqs(2) show "ub (Suc i) = ub i \<or> ub (Suc i) = PlusInf"
      by (auto split: if_splits)
  qed
  have lb_stay: "lb i = MinInf \<Longrightarrow> lb (Suc i) = MinInf" for i
    using step(1) by metis
  have ub_stay: "ub i = PlusInf \<Longrightarrow> ub (Suc i) = PlusInf" for i
    using step(2) by metis
  have lb_stay_le: "lb i = MinInf \<Longrightarrow> i \<le> j \<Longrightarrow> lb j = MinInf" for i j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using lb_stay le_SucE by metis
  qed
  have ub_stay_le: "ub i = PlusInf \<Longrightarrow> i \<le> j \<Longrightarrow> ub j = PlusInf" for i j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using ub_stay le_SucE by metis
  qed
  have lb_const_if_no_MinInf:
    "(\<forall>k. lb k \<noteq> MinInf) \<Longrightarrow> lb j = lb 0" for j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(1)[of j] by auto
  qed
  have ub_const_if_no_PlusInf:
    "(\<forall>k. ub k \<noteq> PlusInf) \<Longrightarrow> ub j = ub 0" for j
  proof (induct j)
    case 0 thus ?case by simp
  next
    case (Suc j) thus ?case using step(2)[of j] by auto
  qed
  obtain nl where nl: "\<forall>j \<ge> nl. lb j = lb nl"
  proof (cases "\<exists>k. lb k = MinInf")
    case True
    then obtain k where "lb k = MinInf" by blast
    then have "\<forall>j \<ge> k. lb j = MinInf" using lb_stay_le by blast
    then have "\<forall>j \<ge> k. lb j = lb k" using \<open>lb k = MinInf\<close> by simp
    then show ?thesis by (rule that)
  next
    case False
    then have "\<forall>k. lb k \<noteq> MinInf" by blast
    then have "\<forall>j. lb j = lb 0" using lb_const_if_no_MinInf by blast
    then have "\<forall>j \<ge> 0. lb j = lb 0" by blast
    then show ?thesis by (rule that)
  qed
  obtain nu where nu: "\<forall>j \<ge> nu. ub j = ub nu"
  proof (cases "\<exists>k. ub k = PlusInf")
    case True
    then obtain k where "ub k = PlusInf" by blast
    then have "\<forall>j \<ge> k. ub j = PlusInf" using ub_stay_le by blast
    then have "\<forall>j \<ge> k. ub j = ub k" using \<open>ub k = PlusInf\<close> by simp
    then show ?thesis by (rule that)
  next
    case False
    then have "\<forall>k. ub k \<noteq> PlusInf" by blast
    then have "\<forall>j. ub j = ub 0" using ub_const_if_no_PlusInf by blast
    then have "\<forall>j \<ge> 0. ub j = ub 0" by blast
    then show ?thesis by (rule that)
  qed
  let ?n = "max nl nu"
  have "\<forall>j. ?n \<le> j \<longrightarrow> f j = f ?n"
  proof (intro allI impI)
    fix j assume jn: "?n \<le> j"
    have lb_eq: "lb j = lb ?n"
    proof -
      from jn have "nl \<le> j" "nl \<le> ?n" by auto
      then have "lb j = lb nl" "lb ?n = lb nl"
        using nl by blast+
      then show ?thesis by simp
    qed
    have ub_eq: "ub j = ub ?n"
    proof -
      from jn have "nu \<le> j" "nu \<le> ?n" by auto
      then have "ub j = ub nu" "ub ?n = ub nu"
        using nu by blast+
      then show ?thesis by simp
    qed
    show "f j = f ?n"
      using f_eq[of j] f_eq[of ?n] lb_eq ub_eq by simp
  qed
  then show ?thesis by blast
qed


subsection \<open>Type-class widening for TD warrowing solver\<close>

text \<open>Standard interval narrowing: when the recomputed value \<open>b\<close> refines the widened value
  \<open>a\<close> (\<open>b \<le> a\<close>), keep \<open>a\<close>'s finite bounds and only fill an infinite bound of \<open>a\<close> from \<open>b\<close>.
  A bound moves off \<open>\<pm>inf\<close> at most once, so the narrowing descent is finite.  Combined with
  the backward guard filters this recovers loop bounds under \<^emph>\<open>every\<close> update rule (a bounded
  local counter reads \<open>[0, 20]\<close> under \<open>join\<close>, \<open>per_origin\<close> and \<open>warrow\<close> alike).  It does not
  help a \<^emph>\<open>flow-insensitive global\<close>: there the guard never bounds the value written back to
  the slot, so \<open>[0, +inf]\<close> is a genuine fixpoint and narrowing has nothing smaller to descend
  to.\<close>
fun narrow_ivl_td :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "narrow_ivl_td (Ivl l1 u1) (Ivl l2 u2) =
     Ivl (if l1 = MinInf then l2 else l1) (if u1 = PlusInf then u2 else u1)"

instantiation ivl :: warrowing begin
  text \<open>Widening carries the standard bot-law \<open>bot \<nabla> x = x\<close>, \<open>x \<nabla> bot = x\<close>: since
    \<^term>\<open>bot :: ivl\<close> is the empty interval \<^term>\<open>Ivl PlusInf MinInf\<close>, an unguarded
    \<^const>\<open>widen_ivl_core\<close> from bot would jump straight to the top interval, topping any
    unknown on its first stabilisation.  The guard keeps the first contribution exact.\<close>
  definition "widen (a :: ivl) b =
     (if a = bot then b else if b = bot then a else widen_ivl_core a b)"
  definition "narrow (a :: ivl) b = narrow_ivl_td a b"
instance proof intro_classes
  fix a b :: ivl
  show "a \<le> widen a b"
  proof (cases "a = bot")
    case True thus ?thesis by (simp add: widen_ivl_def)
  next
    case False thus ?thesis
      by (cases "b = bot") (simp_all add: widen_ivl_def a_le_widen_ivl_core bot.extremum)
  qed
  show "b \<le> widen a b"
  proof (cases "a = bot")
    case True thus ?thesis by (simp add: widen_ivl_def)
  next
    case False thus ?thesis
      by (cases "b = bot") (simp_all add: widen_ivl_def b_le_widen_ivl_core bot.extremum)
  qed
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b"
    unfolding narrow_ivl_def by (cases a; cases b) (auto simp: less_eq_ivl_def eint_le_refl split: if_splits)
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_ivl_def by (cases a; cases b) (auto simp: less_eq_ivl_def eint_le_refl split: if_splits)
qed
end

instance ivl :: widening_domain ..

end
