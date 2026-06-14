theory Interval_Domain
  imports Abstract_Domain Constraint_System "Voblint_IMP2.IMP2_Expr" "Voblint_IMP2.IMP2_Globals"
begin

section \<open>Interval domain: instantiation of abstract_domain\<close>

text \<open>
  An interval @{text "[l, u]"} abstracts the integers @{text "{n. l \<le> n \<and> n \<le> u}"}.
  Bounds are extended integers (@{text MinInf} / @{text "Fin n"} / @{text PlusInf}).
  Empty (e.g. @{text "[+inf, -inf]"}) is @{text bot}; @{text "[-inf, +inf]"} is @{text top}.

  Second concrete domain in the pipeline: infinite height, so it exercises real
  widening (proved here) end to end, unlike the finite Sign lattice.  Plus and
  minus are precise; multiplication is abstracted to @{text top} (sound, and
  monotone by construction -- a precise interval product is not monotone over
  the malformed/empty intervals of the raw lattice).
\<close>

subsection \<open>Extended integers as interval bounds\<close>

datatype eint = MinInf | Fin int | PlusInf

fun eint_le :: "eint => eint => bool" where
    "eint_le MinInf  _       = True"
  | "eint_le _       PlusInf = True"
  | "eint_le (Fin n) (Fin m) = (n <= m)"
  | "eint_le _       MinInf  = False"
  | "eint_le PlusInf _       = False"

lemma eint_le_refl: "eint_le x x"
  by (cases x) simp_all

lemma eint_le_antisym: "eint_le x y \<Longrightarrow> eint_le y x \<Longrightarrow> x = y"
  by (cases x; cases y) simp_all

lemma eint_le_trans: "eint_le x y \<Longrightarrow> eint_le y z \<Longrightarrow> eint_le x z"
  by (cases x; cases y; cases z) simp_all

lemma eint_le_PlusInf [simp]: "eint_le x PlusInf"
  by (cases x) simp_all

lemma eint_le_MinInf_left [simp]: "eint_le MinInf x"
  by simp

lemma eint_le_linear: "eint_le x y \<or> eint_le y x"
  by (cases x; cases y) auto

subsection \<open>Interval type and order\<close>

datatype ivl = Ivl eint eint   \<comment> \<open>@{text "Ivl l u = [l, u]"}\<close>

instantiation ivl :: ord begin
definition less_eq_ivl :: "ivl => ivl => bool" where
  "(a::ivl) <= b = (case (a, b) of (Ivl l1 u1, Ivl l2 u2) => eint_le l2 l1 \<and> eint_le u1 u2)"
definition less_ivl :: "ivl => ivl => bool" where
  "(a::ivl) < b = (a <= b \<and> \<not> b <= a)"
instance ..
end

instantiation ivl :: bot begin
definition bot_ivl :: ivl where
  "bot_ivl = Ivl PlusInf MinInf"
instance ..
end

instantiation ivl :: order begin
instance proof
  fix x y z :: ivl
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_ivl_def by simp
  show "x \<le> x"
    unfolding less_eq_ivl_def by (cases x) (simp add: eint_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_ivl_def by (cases x; cases y; cases z) (auto intro: eint_le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_ivl_def by (cases x; cases y) (auto intro: eint_le_antisym)
qed
end

instantiation ivl :: order_bot begin
instance proof
  fix x :: ivl
  show "bot \<le> x"
    unfolding less_eq_ivl_def bot_ivl_def by (cases x) simp
qed
end

definition ivl_top :: ivl where
  "ivl_top = Ivl MinInf PlusInf"

subsection \<open>Concretization\<close>

fun gamma_ivl :: "ivl => int set" where
    "gamma_ivl (Ivl l u) = {n. eint_le l (Fin n) \<and> eint_le (Fin n) u}"

lemma gamma_ivl_bot: "gamma_ivl bot = {}"
  unfolding bot_ivl_def by auto

lemma gamma_ivl_top: "gamma_ivl ivl_top = UNIV"
  unfolding ivl_top_def by auto

lemma gamma_ivl_mono:
  "a \<le> b \<Longrightarrow> gamma_ivl a \<subseteq> gamma_ivl b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2" and ab: "a \<le> b"
  from ab have le: "eint_le l2 l1" "eint_le u1 u2"
    unfolding less_eq_ivl_def \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close> by simp_all
  show "gamma_ivl a \<subseteq> gamma_ivl b"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using le by (auto intro: eint_le_trans)
qed

subsection \<open>Join (least upper bound)\<close>

fun join_ivl :: "ivl => ivl => ivl" where
    "join_ivl (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if eint_le l1 l2 then l1 else l2)
           (if eint_le u2 u1 then u1 else u2)"

lemma join_ivl_le_ub1: "(a :: ivl) \<le> join_ivl a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "a \<le> join_ivl a b"
    unfolding less_eq_ivl_def
    using eint_le_linear[of l1 l2] eint_le_linear[of u1 u2]
    by (auto simp: eint_le_refl)
qed

lemma join_ivl_le_ub2: "(b :: ivl) \<le> join_ivl a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "b \<le> join_ivl a b"
    unfolding less_eq_ivl_def
    using eint_le_linear[of l1 l2] eint_le_linear[of u1 u2]
    by (auto simp: eint_le_refl)
qed

lemma join_ivl_le_least:
  "(a :: ivl) \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> join_ivl a b \<le> c"
proof (cases a; cases b; cases c)
  fix l1 u1 l2 u2 l3 u3 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2" "c = Ivl l3 u3"
    and "a \<le> c" "b \<le> c"
  then show "join_ivl a b \<le> c"
    unfolding less_eq_ivl_def by auto
qed

instantiation ivl :: sup begin
definition sup_ivl :: "ivl => ivl => ivl" where
  "sup_ivl = join_ivl"
instance ..
end

instance ivl :: semilattice_sup
proof
  fix x y z :: ivl
  show "x \<le> x \<squnion> y" unfolding sup_ivl_def by (rule join_ivl_le_ub1)
  show "y \<le> x \<squnion> y" unfolding sup_ivl_def by (rule join_ivl_le_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    unfolding sup_ivl_def by (rule join_ivl_le_least)
qed

instance ivl :: bounded_semilattice_sup_bot ..

subsection \<open>Meet (greatest lower bound)\<close>

text \<open>
  Interval intersection.  Used by @{text assume_ivl} to refine a variable's
  interval on a guard (@{text "x < n"} narrows the upper bound).
\<close>
fun meet_ivl :: "ivl => ivl => ivl" where
  "meet_ivl (Ivl l1 u1) (Ivl l2 u2) =
     Ivl (if eint_le l2 l1 then l1 else l2) (if eint_le u1 u2 then u1 else u2)"

lemma meet_ivl_gamma:
  "n \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> n \<in> gamma_ivl (meet_ivl a b)"
  by (cases a; cases b; auto split: if_splits intro: eint_le_trans)

lemma meet_ivl_mono1:
  "a1 \<le> a2 \<Longrightarrow> meet_ivl a1 b \<le> meet_ivl a2 b"
  by (cases a1; cases a2; cases b; auto simp: less_eq_ivl_def split: if_splits
        intro: eint_le_trans elim: eint_le.elims)

subsection \<open>Widening\<close>

text \<open>
  Standard interval widening: keep a bound if it did not move outward, otherwise
  push it to the infinite end.  Every widen-ascending chain therefore stabilises
  after at most two steps (each bound takes at most one outward jump).
\<close>

fun widen_ivl :: "ivl => ivl => ivl" where
    "widen_ivl (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if eint_le l1 l2 then l1 else MinInf)
           (if eint_le u2 u1 then u1 else PlusInf)"

lemma a_le_widen_ivl: "(a :: ivl) \<le> widen_ivl a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "a \<le> widen_ivl a b"
    unfolding less_eq_ivl_def by (auto simp: eint_le_refl)
qed

lemma b_le_widen_ivl: "(b :: ivl) \<le> widen_ivl a b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  then show "b \<le> widen_ivl a b"
    unfolding less_eq_ivl_def
    using eint_le_linear[of l1 l2] eint_le_linear[of u2 u1]
    by auto
qed

lemma widen_ivl_ub1: "gamma_ivl a \<subseteq> gamma_ivl (widen_ivl a b)"
  using gamma_ivl_mono a_le_widen_ivl by blast

lemma widen_ivl_ub2: "gamma_ivl b \<subseteq> gamma_ivl (widen_ivl a b)"
  using gamma_ivl_mono b_le_widen_ivl by blast

text \<open>
  Widening termination: every widen-ascending chain stabilises.  At each step
  each bound either stays or jumps to @{text MinInf} / @{text PlusInf}, and once
  a bound reaches the infinite end it remains there.  After at most two
  transitions the chain is constant.
\<close>
lemma widen_ivl_terminates:
  assumes "\<forall>i. widen_ivl (f i) (f (Suc i)) = f (Suc i)"
  shows "\<exists>n. \<forall>j. n \<le> j \<longrightarrow> f j = f n"
proof -
  define lb where "lb i = (case f i of Ivl l _ \<Rightarrow> l)" for i
  define ub where "ub i = (case f i of Ivl _ u \<Rightarrow> u)" for i
  have f_eq: "f i = Ivl (lb i) (ub i)" for i
    unfolding lb_def ub_def by (cases "f i") simp
  have step:
    "lb (Suc i) = lb i \<or> lb (Suc i) = MinInf"
    "ub (Suc i) = ub i \<or> ub (Suc i) = PlusInf"
    for i
  proof -
    have "widen_ivl (Ivl (lb i) (ub i)) (Ivl (lb (Suc i)) (ub (Suc i)))
          = Ivl (lb (Suc i)) (ub (Suc i))"
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

subsection \<open>Abstract domain interpretation\<close>

interpretation ivl_domain: abstract_domain gamma_ivl widen_ivl
proof (unfold_locales)
  show "gamma_ivl bot = {}" by (rule gamma_ivl_bot)
next
  fix a b :: ivl
  assume "a \<le> b"
  then show "gamma_ivl a \<subseteq> gamma_ivl b" by (rule gamma_ivl_mono)
next
  fix a b :: ivl
  show "gamma_ivl a \<subseteq> gamma_ivl (widen_ivl a b)" by (rule widen_ivl_ub1)
next
  fix a b :: ivl
  show "gamma_ivl b \<subseteq> gamma_ivl (widen_ivl a b)" by (rule widen_ivl_ub2)
qed

lemma ivl_gamma_state_conv:
  "(s : ivl_domain.gamma_state sigma) = (s : sound_domain.gamma_state gamma_ivl sigma)"
  unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by simp

subsection \<open>Extended-integer arithmetic\<close>

fun eint_plus :: "eint => eint => eint" where
    "eint_plus (Fin n)   (Fin m)   = Fin (n + m)"
  | "eint_plus (Fin _)   MinInf    = MinInf"
  | "eint_plus (Fin _)   PlusInf   = PlusInf"
  | "eint_plus MinInf    MinInf    = MinInf"
  | "eint_plus MinInf    (Fin _)   = MinInf"
  | "eint_plus MinInf    PlusInf   = MinInf"
  | "eint_plus PlusInf   MinInf    = PlusInf"
  | "eint_plus PlusInf   (Fin _)   = PlusInf"
  | "eint_plus PlusInf   PlusInf   = PlusInf"

fun eint_minus :: "eint => eint => eint" where
    "eint_minus (Fin n)   (Fin m)   = Fin (n - m)"
  | "eint_minus (Fin _)   MinInf    = PlusInf"
  | "eint_minus (Fin _)   PlusInf   = MinInf"
  | "eint_minus MinInf    MinInf    = MinInf"
  | "eint_minus MinInf    (Fin _)   = MinInf"
  | "eint_minus MinInf    PlusInf   = MinInf"
  | "eint_minus PlusInf   MinInf    = PlusInf"
  | "eint_minus PlusInf   (Fin _)   = PlusInf"
  | "eint_minus PlusInf   PlusInf   = PlusInf"

fun ivl_plus :: "ivl => ivl => ivl" where
    "ivl_plus  (Ivl l1 u1) (Ivl l2 u2) = Ivl (eint_plus l1 l2) (eint_plus u1 u2)"

fun ivl_minus :: "ivl => ivl => ivl" where
    "ivl_minus (Ivl l1 u1) (Ivl l2 u2) = Ivl (eint_minus l1 u2) (eint_minus u1 l2)"

text \<open>
  Emptiness test on intervals.  The raw @{typ ivl} lattice contains many
  unnormalised empty intervals (any @{term \<open>Ivl l u\<close>} with @{text "l > u"},
  including @{term bot}).  @{text ivl_nonempty} captures exactly the intervals
  with non-empty concretization (proved below: implied by any witness, and
  monotone along @{text "\<le>"}); multiplication uses it for proper bottom
  handling, which is what makes the precise corner product monotone.
\<close>
fun ivl_nonempty :: "ivl => bool" where
  "ivl_nonempty (Ivl l u) = (eint_le l u \<and> l \<noteq> PlusInf \<and> u \<noteq> MinInf)"

lemma gamma_ivl_nonempty: "i \<in> gamma_ivl v \<Longrightarrow> ivl_nonempty v"
  by (cases v; cases "case v of Ivl l _ => l"; cases "case v of Ivl _ u => u"; auto)

lemma ivl_nonempty_mono: "ivl_nonempty a \<Longrightarrow> a \<le> b \<Longrightarrow> ivl_nonempty b"
  by (cases a; cases b; auto simp: less_eq_ivl_def intro: eint_le_trans
        elim: eint_le.elims)

lemma int_mult_in_corners_lo:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2))) \<le> i * j"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono mult_left_mono_neg mult_right_mono_neg min_def)

lemma int_mult_in_corners_hi:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "i * j \<le> max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono mult_left_mono_neg mult_right_mono_neg max_def)

text \<open>
  Precise multiplication on non-empty intervals.  For all-finite operands the
  product range is the min / max over the four corner products (the box product
  attains its extrema at the corners); any infinite bound falls back to
  @{const ivl_top}.  An empty operand yields @{term bot} -- the proper bottom
  handling that keeps the operator monotone (mapping empties to @{const ivl_top}
  would destroy the ordering).
\<close>
fun ivl_times_core :: "ivl => ivl => ivl" where
    "ivl_times_core (Ivl (Fin l1) (Fin u1)) (Ivl (Fin l2) (Fin u2)) =
       Ivl (Fin (min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2)))))
           (Fin (max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))))"
  | "ivl_times_core _ _ = ivl_top"

definition ivl_times :: "ivl => ivl => ivl" where
  "ivl_times a b = (if ivl_nonempty a \<and> ivl_nonempty b then ivl_times_core a b else bot)"

lemma ivl_plus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i + j \<in> gamma_ivl (ivl_plus a b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i + j \<in> gamma_ivl (ivl_plus a b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_minus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i - j \<in> gamma_ivl (ivl_minus a b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i - j \<in> gamma_ivl (ivl_minus a b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_times_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i * j \<in> gamma_ivl (ivl_times a b)"
proof -
  from assms have ne: "ivl_nonempty a" "ivl_nonempty b"
    by (auto intro: gamma_ivl_nonempty)
  hence eq: "ivl_times a b = ivl_times_core a b" by (simp add: ivl_times_def)
  show ?thesis
  proof (cases a; cases b)
    fix l1 u1 l2 u2 assume ab: "a = Ivl l1 u1" "b = Ivl l2 u2"
    show ?thesis
    proof (cases l1; cases u1; cases l2; cases u2)
      fix n1 m1 n2 m2 assume fin: "l1 = Fin n1" "u1 = Fin m1" "l2 = Fin n2" "u2 = Fin m2"
      from assms ab fin have bnds: "n1 \<le> i" "i \<le> m1" "n2 \<le> j" "j \<le> m2" by auto
      show ?thesis using eq ab fin
        int_mult_in_corners_lo[OF bnds] int_mult_in_corners_hi[OF bnds] by simp
    qed (use eq ab in \<open>simp_all add: ivl_top_def\<close>)
  qed
qed

subsection \<open>Abstract expression evaluation\<close>

fun aval_ivl_hol :: "AExp.aexp => (vname => ivl) => ivl" where
    "aval_ivl_hol (AExp.N n)      sigma = Ivl (Fin n) (Fin n)"
  | "aval_ivl_hol (AExp.V x)      sigma = sigma x"
  | "aval_ivl_hol (AExp.Plus a b) sigma = ivl_plus (aval_ivl_hol a sigma) (aval_ivl_hol b sigma)"

fun aval_ivl :: "aexp => (vname => ivl) => ivl" where
    "aval_ivl (BaseN a)    sigma = aval_ivl_hol a sigma"
  | "aval_ivl (Plus  a b)  sigma = ivl_plus  (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Minus a b)  sigma = ivl_minus (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Times a b)  sigma = ivl_times (aval_ivl a sigma) (aval_ivl b sigma)"

lemma aval_ivl_hol_sound:
  "(\<forall>x. s x \<in> gamma_ivl (sigma x))
   \<Longrightarrow> AExp.aval a s \<in> gamma_ivl (aval_ivl_hol a sigma)"
  by (induction a; simp add: ivl_plus_sound)

lemma aval_ivl_sound:
  "(\<forall>x. s x \<in> gamma_ivl (sigma x))
   \<Longrightarrow> aval a s \<in> gamma_ivl (aval_ivl a sigma)"
  by (induction a;
      simp add: aval.simps aval_ivl.simps aval_ivl_hol_sound
                ivl_plus_sound ivl_minus_sound ivl_times_sound)

subsection \<open>Abstract assume and assignment\<close>

text \<open>
  Guard refinement: on @{term \<open>Less (V x) (N n)\<close>} (i.e. @{text "x < n"}) narrow
  @{text x} to @{text "[.., n-1]"} by meeting with @{term \<open>Ivl MinInf (Fin (n - 1))\<close>}.
  All other guards are treated conservatively (identity).
\<close>
fun assume_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_ivl (Less (V x) (N n)) sigma =
       sigma(x := meet_ivl (sigma x) (Ivl MinInf (Fin (n - 1))))"
  | "assume_ivl _ sigma = sigma"

lemma assume_ivl_default:
  "\<not> (\<exists>x n. b = Less (V x) (N n)) \<Longrightarrow> assume_ivl b sigma = sigma"
  by (cases "(b, sigma)" rule: assume_ivl.cases) auto

lemma assume_ivl_sound:
  assumes gs: "s \<in> ivl_domain.gamma_state sigma" and b: "bval b s"
  shows "s \<in> ivl_domain.gamma_state (assume_ivl b sigma)"
proof (cases "\<exists>x n. b = Less (V x) (N n)")
  case False
  with assume_ivl_default gs show ?thesis by metis
next
  case True
  then obtain x n where bn: "b = Less (V x) (N n)" by blast
  have xv: "s x < n" using b bn by simp
  have "assume_ivl b sigma = sigma(x := meet_ivl (sigma x) (Ivl MinInf (Fin (n-1))))"
    using bn by simp
  moreover have "s x \<in> gamma_ivl (meet_ivl (sigma x) (Ivl MinInf (Fin (n-1))))"
  proof (rule meet_ivl_gamma)
    show "s x \<in> gamma_ivl (sigma x)" using gs unfolding ivl_domain.gamma_state_def by simp
    show "s x \<in> gamma_ivl (Ivl MinInf (Fin (n-1)))" using xv by simp
  qed
  moreover have "\<And>y. y \<noteq> x \<Longrightarrow> s y \<in> gamma_ivl (sigma y)"
    using gs unfolding ivl_domain.gamma_state_def by simp
  ultimately show ?thesis unfolding ivl_domain.gamma_state_def by simp
qed

fun assume_not_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_not_ivl _ sigma = sigma"

definition assign_ivl ::
    "vname => aexp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a sigma = sigma(x := aval_ivl a sigma)"

lemma assign_ivl_sound:
  "s \<in> ivl_domain.gamma_state sigma
   \<Longrightarrow> s(x := aval a s) \<in> ivl_domain.gamma_state (assign_ivl x a sigma)"
  unfolding ivl_domain.gamma_state_def assign_ivl_def
  by (auto simp: aval_ivl_sound)

subsection \<open>Procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval.\<close>
definition enter_ivl :: "ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_ivl sigma = (\<lambda>x. if is_global x then sigma x else Ivl MinInf PlusInf)"

lemma enter_ivl_sound:
  assumes "s \<in> ivl_domain.gamma_state sigma"
  shows "enter_state s \<in> ivl_domain.gamma_state (enter_ivl sigma)"
  using assms unfolding ivl_domain.gamma_state_def enter_ivl_def enter_state_def
  by (intro CollectI allI) (auto simp: gamma_ivl.simps)

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl,
               tf_enter      = enter_ivl |)"

lemma ivl_tf_sound_assign:
  "\<forall>x a sigma. \<forall>st \<in> ivl_domain.gamma_state sigma.
     st(x := aval a st) \<in> ivl_domain.gamma_state (tf_assign ivl_tf x a sigma)"
  unfolding ivl_tf_def by (simp add: assign_ivl_sound)

lemma ivl_tf_sound_assume:
  "\<forall>b sigma. \<forall>st \<in> ivl_domain.gamma_state sigma.
     bval b st \<longrightarrow> st \<in> ivl_domain.gamma_state (tf_assume ivl_tf b sigma)"
  unfolding ivl_tf_def by (simp add: assume_ivl_sound)

lemma ivl_tf_sound_assume_not:
  "\<forall>b sigma. \<forall>st \<in> ivl_domain.gamma_state sigma.
     \<not> bval b st \<longrightarrow> st \<in> ivl_domain.gamma_state (tf_assume_not ivl_tf b sigma)"
  unfolding ivl_tf_def by simp

lemma ivl_tf_sound_enter:
  "\<forall>sigma. \<forall>st \<in> ivl_domain.gamma_state sigma.
     enter_state st \<in> ivl_domain.gamma_state (tf_enter ivl_tf sigma)"
  unfolding ivl_tf_def by (simp add: enter_ivl_sound)

interpretation ivl_sound_tf: sound_transfer gamma_ivl ivl_tf
proof unfold_locales
  show "\<forall>x a sigma. \<forall>s \<in> ivl_domain.gamma_state sigma.
       s(x := aval a s) \<in> ivl_domain.gamma_state (tf_assign ivl_tf x a sigma)"
    by (rule ivl_tf_sound_assign)
  show "\<forall>b sigma. \<forall>s \<in> ivl_domain.gamma_state sigma. bval b s
       \<longrightarrow> s \<in> ivl_domain.gamma_state (tf_assume ivl_tf b sigma)"
    by (rule ivl_tf_sound_assume)
  show "\<forall>b sigma. \<forall>s \<in> ivl_domain.gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> ivl_domain.gamma_state (tf_assume_not ivl_tf b sigma)"
    by (rule ivl_tf_sound_assume_not)
  show "\<forall>sigma. \<forall>s \<in> ivl_domain.gamma_state sigma.
       enter_state s \<in> ivl_domain.gamma_state (tf_enter ivl_tf sigma)"
    by (rule ivl_tf_sound_enter)
qed

subsection \<open>Monotonicity of the transfer functions\<close>

lemma eint_plus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b1 b2 \<Longrightarrow> eint_le (eint_plus a1 b1) (eint_plus a2 b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

lemma eint_minus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b2 b1 \<Longrightarrow> eint_le (eint_minus a1 b1) (eint_minus a2 b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

lemma ivl_plus_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> ivl_plus a1 b1 \<le> ivl_plus a2 b2"
  by (cases a1; cases a2; cases b1; cases b2;
      simp add: less_eq_ivl_def eint_plus_mono)

lemma ivl_minus_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> ivl_minus a1 b1 \<le> ivl_minus a2 b2"
  by (cases a1; cases a2; cases b1; cases b2;
      simp add: less_eq_ivl_def eint_minus_mono)

text \<open>
  Monotonicity of the precise corner product.  Over a larger box the corner
  minimum can only drop and the corner maximum can only rise (each old corner is
  a point of the new box), so widening either operand widens the product.
\<close>
lemma ivl_le_top: "(x::ivl) \<le> ivl_top"
  by (cases x) (simp add: less_eq_ivl_def ivl_top_def)

lemma corner_min_mono:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 :: int
  assumes "a2 \<le> a1" "b1 \<le> b2" "c2 \<le> c1" "d1 \<le> d2" "a1 \<le> b1" "c1 \<le> d1"
  shows "min (a2*c2) (min (a2*d2) (min (b2*c2) (b2*d2)))
       \<le> min (a1*c1) (min (a1*d1) (min (b1*c1) (b1*d1)))"
proof -
  let ?M = "min (a2*c2) (min (a2*d2) (min (b2*c2) (b2*d2)))"
  have d1: "a1 \<le> b2" "c1 \<le> d2" "a2 \<le> b1" "c2 \<le> d1" using assms by auto
  have "?M \<le> a1*c1" by (rule int_mult_in_corners_lo[OF assms(1) d1(1) assms(3) d1(2)])
  moreover have "?M \<le> a1*d1" by (rule int_mult_in_corners_lo[OF assms(1) d1(1) d1(4) assms(4)])
  moreover have "?M \<le> b1*c1" by (rule int_mult_in_corners_lo[OF d1(3) assms(2) assms(3) d1(2)])
  moreover have "?M \<le> b1*d1" by (rule int_mult_in_corners_lo[OF d1(3) assms(2) d1(4) assms(4)])
  ultimately show ?thesis by simp
qed

lemma corner_max_mono:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 :: int
  assumes "a2 \<le> a1" "b1 \<le> b2" "c2 \<le> c1" "d1 \<le> d2" "a1 \<le> b1" "c1 \<le> d1"
  shows "max (a1*c1) (max (a1*d1) (max (b1*c1) (b1*d1)))
       \<le> max (a2*c2) (max (a2*d2) (max (b2*c2) (b2*d2)))"
proof -
  let ?M = "max (a2*c2) (max (a2*d2) (max (b2*c2) (b2*d2)))"
  have d1: "a1 \<le> b2" "c1 \<le> d2" "a2 \<le> b1" "c2 \<le> d1" using assms by auto
  have "a1*c1 \<le> ?M" by (rule int_mult_in_corners_hi[OF assms(1) d1(1) assms(3) d1(2)])
  moreover have "a1*d1 \<le> ?M" by (rule int_mult_in_corners_hi[OF assms(1) d1(1) d1(4) assms(4)])
  moreover have "b1*c1 \<le> ?M" by (rule int_mult_in_corners_hi[OF d1(3) assms(2) assms(3) d1(2)])
  moreover have "b1*d1 \<le> ?M" by (rule int_mult_in_corners_hi[OF d1(3) assms(2) d1(4) assms(4)])
  ultimately show ?thesis by simp
qed

lemma ivl_times_core_top:
  "\<not> (\<exists>la ua lb ub. a = Ivl (Fin la) (Fin ua) \<and> b = Ivl (Fin lb) (Fin ub))
   \<Longrightarrow> ivl_times_core a b = ivl_top"
  by (cases "(a,b)" rule: ivl_times_core.cases) auto

lemma ivl_nonempty_le_fin:
  assumes "ivl_nonempty a" "a \<le> Ivl (Fin l2) (Fin u2)"
  shows "\<exists>l1 u1. a = Ivl (Fin l1) (Fin u1)"
proof (cases a)
  case (Ivl l u)
  with assms show ?thesis by (cases l; cases u; auto simp: less_eq_ivl_def)
qed

lemma ivl_times_core_mono:
  assumes ne: "ivl_nonempty a1" "ivl_nonempty b1"
      and le: "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_times_core a1 b1 \<le> ivl_times_core a2 b2"
proof (cases "\<exists>la ua lb ub. a2 = Ivl (Fin la) (Fin ua) \<and> b2 = Ivl (Fin lb) (Fin ub)")
  case False
  then have "ivl_times_core a2 b2 = ivl_top" by (rule ivl_times_core_top)
  thus ?thesis by (simp add: ivl_le_top)
next
  case True
  then obtain la2 ua2 lb2 ub2 where
    a2: "a2 = Ivl (Fin la2) (Fin ua2)" and b2: "b2 = Ivl (Fin lb2) (Fin ub2)" by blast
  from ivl_nonempty_le_fin[OF ne(1)] le(1) a2 obtain la1 ua1 where
    a1: "a1 = Ivl (Fin la1) (Fin ua1)" by metis
  from ivl_nonempty_le_fin[OF ne(2)] le(2) b2 obtain lb1 ub1 where
    b1: "b1 = Ivl (Fin lb1) (Fin ub1)" by metis
  from le a1 a2 b1 b2 have ord:
    "la2 \<le> la1" "ua1 \<le> ua2" "lb2 \<le> lb1" "ub1 \<le> ub2"
    by (auto simp: less_eq_ivl_def)
  from ne a1 b1 have nemp: "la1 \<le> ua1" "lb1 \<le> ub1" by auto
  show ?thesis
    unfolding a1 a2 b1 b2 ivl_times_core.simps less_eq_ivl_def
    using corner_min_mono[OF ord(1) ord(2) ord(3) ord(4) nemp(1) nemp(2)]
          corner_max_mono[OF ord(1) ord(2) ord(3) ord(4) nemp(1) nemp(2)]
    by simp
qed

lemma ivl_times_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_times a1 b1 \<le> ivl_times a2 b2"
proof (cases "ivl_nonempty a1 \<and> ivl_nonempty b1")
  case False
  then have "ivl_times a1 b1 = bot" by (auto simp add: ivl_times_def)
  thus ?thesis by simp
next
  case True
  hence ne2: "ivl_nonempty a2" "ivl_nonempty b2"
    using assms ivl_nonempty_mono by blast+
  have "ivl_times a1 b1 = ivl_times_core a1 b1"
    using True by (simp add: ivl_times_def)
  moreover have "ivl_times a2 b2 = ivl_times_core a2 b2"
    using ne2 by (simp add: ivl_times_def)
  ultimately show ?thesis
    using ivl_times_core_mono[OF _ _ assms] True by simp
qed

lemma aval_ivl_hol_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_ivl_hol a sigma1 \<le> aval_ivl_hol a sigma2"
  by (induction a arbitrary: sigma1 sigma2)
     (auto simp: ivl_plus_mono le_funD order_refl)

lemma aval_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_ivl a sigma1 \<le> aval_ivl a sigma2"
  by (induction a arbitrary: sigma1 sigma2)
     (auto simp: aval_ivl_hol_mono ivl_plus_mono ivl_minus_mono ivl_times_mono)

lemma assign_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_ivl x a sigma1 \<le> assign_ivl x a sigma2"
  by (simp add: assign_ivl_def aval_ivl_mono le_funD le_funI)

lemma assume_ivl_mono:
  assumes "sigma1 \<le> sigma2"
  shows "assume_ivl b sigma1 \<le> assume_ivl b sigma2"
proof (cases "\<exists>x n. b = Less (V x) (N n)")
  case False
  with assume_ivl_default assms show ?thesis by metis
next
  case True
  then obtain x n where bn: "b = Less (V x) (N n)" by blast
  show ?thesis unfolding bn assume_ivl.simps
  proof (rule le_funI)
    fix y
    show "(sigma1(x := meet_ivl (sigma1 x) (Ivl MinInf (Fin (n-1))))) y
          \<le> (sigma2(x := meet_ivl (sigma2 x) (Ivl MinInf (Fin (n-1))))) y"
      using assms by (cases "y = x"; auto simp: meet_ivl_mono1 le_funD)
  qed
qed

lemma assume_not_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_ivl b sigma1 \<le> assume_not_ivl b sigma2"
  by simp

lemma enter_ivl_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl s1 \<le> enter_ivl s2"
proof (rule le_funI)
  fix x
  show "enter_ivl s1 x \<le> enter_ivl s2 x"
  proof (cases "is_global x")
    case True
    from assms have "s1 x \<le> s2 x" by (simp add: le_funD)
    with True show ?thesis unfolding enter_ivl_def by simp
  next
    case False
    thus ?thesis unfolding enter_ivl_def by (simp add: order_refl)
  qed
qed

lemma ivl_tf_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf ivl_tf a s1 \<le> apply_tf ivl_tf a s2"
  by (cases a)
     (auto simp: ivl_tf_def assign_ivl_mono assume_ivl_mono assume_not_ivl_mono
                 enter_ivl_mono)

end
