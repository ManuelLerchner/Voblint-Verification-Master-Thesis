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

text \<open>Interval narrowing: when the recomputed value \<open>b\<close> refines the widened value \<open>a\<close>
  (\<open>b \<le> a\<close>), keep \<open>a\<close>'s bounds and refill from \<open>b\<close> exactly those bounds that a widening
  step could have produced -- an infinite bound, or a bound resting on a machine-kind extreme.
  Goblint's interval narrowing draws the same line with its \<open>min_ik = x1\<close> and \<open>max_ik = x2\<close>
  guards; it can name the one relevant kind because every \<open>IntDomain\<close> operation there takes
  an \<open>ikind\<close> argument, whereas \<open>narrow :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> is kind-agnostic, so the guard
  below accepts any kind's extreme.  Accepting too many only refills more bounds from \<open>b\<close>,
  which both narrowing laws permit for every \<open>b \<le> a\<close>.

  The descent stays finite.  Under \<open>b \<le> a\<close> the lower bound never decreases and the upper
  bound never increases, and either bound can only move while it sits on one of the finitely
  many extremes, so each moves at most as often as there are extremes below (resp. above) it.\<close>

definition ikinds :: "ikind list" where
  "ikinds = [I8, U8, I16, U16, I32, U32, I64, U64]"

lemma set_ikinds [simp]: "set ikinds = UNIV"
  by (auto simp: ikinds_def) (rename_tac ik, case_tac ik, simp_all)

definition ik_lo_extremes :: "int list" where
  "ik_lo_extremes = map ik_min ikinds"

definition ik_hi_extremes :: "int list" where
  "ik_hi_extremes = map ik_max ikinds"

fun narrow_lo :: "eint \<Rightarrow> eint \<Rightarrow> eint" where
    "narrow_lo MinInf  l2 = l2"
  | "narrow_lo (Fin v) l2 = (if v \<in> set ik_lo_extremes then l2 else Fin v)"
  | "narrow_lo PlusInf l2 = PlusInf"

fun narrow_hi :: "eint \<Rightarrow> eint \<Rightarrow> eint" where
    "narrow_hi PlusInf u2 = u2"
  | "narrow_hi (Fin v) u2 = (if v \<in> set ik_hi_extremes then u2 else Fin v)"
  | "narrow_hi MinInf  u2 = MinInf"

lemma narrow_lo_ge: "eint_le l1 l2 \<Longrightarrow> eint_le l1 (narrow_lo l1 l2)"
  by (cases l1) auto

lemma narrow_lo_le: "eint_le l1 l2 \<Longrightarrow> eint_le (narrow_lo l1 l2) l2"
  by (cases l1) auto

lemma narrow_hi_le: "eint_le u2 u1 \<Longrightarrow> eint_le (narrow_hi u1 u2) u1"
  by (cases u1) auto

lemma narrow_hi_ge: "eint_le u2 u1 \<Longrightarrow> eint_le u2 (narrow_hi u1 u2)"
  by (cases u1) auto

fun narrow_ivl_td :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "narrow_ivl_td (Ivl l1 u1) (Ivl l2 u2) = Ivl (narrow_lo l1 l2) (narrow_hi u1 u2)"

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
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_ivl_def less_eq_ivl_def
    by (cases a; cases b) (auto simp: narrow_lo_ge narrow_hi_le)
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b"
    unfolding narrow_ivl_def less_eq_ivl_def
    by (cases a; cases b) (auto simp: narrow_lo_le narrow_hi_ge)
qed
end

instance ivl :: abstract_domain ..

text \<open>
  \<open>bot \<nabla> bot = bot\<close> and \<open>bot \<Delta> bot = bot\<close>: the two hypotheses \<open>Solver_Side_RG\<close>'s
  \<open>TD_side_warrowing_apinis_solve_Inr_rg\<close> needs to show that its \<open>Inr\<close>-restricted invariant
  (every \<open>Local_Location\<close> slot at \<open>bot\<close>) survives \<open>update_global_warrowing_apinis\<close>. Both hold
  immediately from \<open>widen_ivl_def\<close>'s \<open>bot\<close> guard and \<open>narrow_ivl_td\<close>'s bound-fill shape.
\<close>

lemma ivl_widen_bot_bot: "(bot :: ivl) \<nabla> bot = bot"
  by (simp add: widen_ivl_def)

lemma ivl_narrow_bot_bot: "(bot :: ivl) \<Delta> bot = bot"
  by (simp add: narrow_ivl_def bot_ivl_def)

end
