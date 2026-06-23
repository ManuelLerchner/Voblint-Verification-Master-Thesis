theory Interval_Domain
  imports Abstract_Domain "TD.Update_rules" Constraint_System "Voblint_IMP2.IMP2_Expr" "Voblint_IMP2.IMP2_Globals"
begin

hide_const (open) Update_rules.N

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

instantiation eint :: ord begin
definition less_eq_eint :: "eint => eint => bool" where "less_eq_eint = eint_le"
definition less_eint    :: "eint => eint => bool" where "(a :: eint) < b = (eint_le a b \<and> \<not> eint_le b a)"
instance ..
end

declare less_eq_eint_def [simp]

instance eint :: linorder
proof
  fix x y z :: eint
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eint_def less_eq_eint_def by simp
  show "x \<le> x"                           unfolding less_eq_eint_def by (rule eint_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"    unfolding less_eq_eint_def by (rule eint_le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"    unfolding less_eq_eint_def by (rule eint_le_antisym)
  show "x \<le> y \<or> y \<le> x"                  unfolding less_eq_eint_def by (rule eint_le_linear)
qed

subsection \<open>Interval type and order\<close>

datatype ivl = Ivl eint eint   \<comment> \<open>@{text "Ivl l u = [l, u]"}\<close>

instantiation ivl :: ord begin
definition less_eq_ivl :: "ivl => ivl => bool" where
  "(a::ivl) <= b = (case (a, b) of (Ivl l1 u1, Ivl l2 u2) => l2 \<le> l1 \<and> u1 \<le> u2)"
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
    "gamma_ivl (Ivl l u) = {n. l \<le> Fin n \<and> Fin n \<le> u}"

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
       Ivl (if l1 \<le> l2 then l1 else l2)
           (if u2 \<le> u1 then u1 else u2)"

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
       Ivl (if l2 \<le> l1 then l1 else l2)
           (if u1 \<le> u2 then u1 else u2)"

instantiation ivl :: inf begin
definition inf_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where "inf_ivl = meet_ivl"
instance ..
end
declare inf_ivl_def [simp]

lemma meet_ivl_gamma:
  "n \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> n \<in> gamma_ivl (a \<sqinter> b)"
  by (cases a; cases b; auto split: if_splits intro: eint_le_trans)

lemma meet_ivl_mono1:
  "(a1 :: ivl) \<le> a2 \<Longrightarrow> a1 \<sqinter> b \<le> a2 \<sqinter> b"
  by (cases a1; cases a2; cases b; auto simp: less_eq_ivl_def split: if_splits
        intro: eint_le_trans elim: eint_le.elims)

lemma meet_ivl_le_lb1: "(a :: ivl) \<sqinter> b \<le> a"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume h: "a = Ivl l1 u1" "b = Ivl l2 u2"
  show "a \<sqinter> b \<le> a"
    using h eint_le_linear[of l2 l1] eint_le_linear[of u1 u2]
    by (auto simp: less_eq_ivl_def split: if_splits simp: eint_le_refl)
qed

lemma meet_ivl_le_lb2: "(a :: ivl) \<sqinter> b \<le> b"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume h: "a = Ivl l1 u1" "b = Ivl l2 u2"
  show "a \<sqinter> b \<le> b"
    using h eint_le_linear[of l1 l2] eint_le_linear[of u1 u2]
    by (auto simp: less_eq_ivl_def split: if_splits simp: eint_le_refl)
qed

lemma meet_ivl_greatest: "(a :: ivl) \<le> c \<Longrightarrow> a \<le> b \<Longrightarrow> a \<le> c \<sqinter> b"
proof (cases a; cases b; cases c)
  fix l1 u1 l2 u2 l3 u3 :: eint
  assume h: "a = Ivl l1 u1" "b = Ivl l2 u2" "c = Ivl l3 u3" "a \<le> c" "a \<le> b"
  show "a \<le> c \<sqinter> b"
    using h by (auto simp: less_eq_ivl_def split: if_splits intro: eint_le_trans)
qed

instance ivl :: semilattice_inf
proof
  fix x y z :: ivl
  show "x \<sqinter> y \<le> x" by (rule meet_ivl_le_lb1)
  show "x \<sqinter> y \<le> y" by (rule meet_ivl_le_lb2)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z" by (rule meet_ivl_greatest)
qed

instance ivl :: lattice ..
instance ivl :: bounded_lattice_bot ..

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
  define lb where "lb i = (case f i of Ivl l _ \<Rightarrow> l)" for i
  define ub where "ub i = (case f i of Ivl _ u \<Rightarrow> u)" for i
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

definition narrow_ivl_td :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "narrow_ivl_td a b = a"

instantiation ivl :: warrowing begin
  definition "widen (a :: ivl) b = widen_ivl_core a b"
  definition "narrow (a :: ivl) b = narrow_ivl_td a b"
instance proof
  fix a b :: ivl
  show "a \<le> widen a b"
    unfolding widen_ivl_def by (rule a_le_widen_ivl_core)
  show "b \<le> widen a b"
    unfolding widen_ivl_def by (rule b_le_widen_ivl_core)
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b"
    unfolding narrow_ivl_def narrow_ivl_td_def by simp
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_ivl_def narrow_ivl_td_def by simp
qed
end



subsection \<open>Abstract domain instantiation\<close>

instantiation ivl :: sound_domain begin
definition gamma_abs_ivl [simp]: "gamma (a :: ivl) = gamma_ivl a"
instance proof
  show "gamma (bot :: ivl) = {}"
    by (simp add: gamma_ivl_bot)
next
  fix a b :: ivl
  assume H: "a \<le> b"
  show "gamma a \<subseteq> gamma b"
  proof -
    have "gamma_ivl a \<subseteq> gamma_ivl b" using H by (rule gamma_ivl_mono)
    then show ?thesis by simp
  qed
qed
end

instance ivl :: abstract_domain ..

subsection \<open>Extended-integer arithmetic\<close>

instantiation eint :: plus begin
fun plus_eint :: "eint => eint => eint" where
    "plus_eint (Fin n)   (Fin m)   = Fin (n + m)"
  | "plus_eint (Fin _)   MinInf    = MinInf"
  | "plus_eint (Fin _)   PlusInf   = PlusInf"
  | "plus_eint MinInf    MinInf    = MinInf"
  | "plus_eint MinInf    (Fin _)   = MinInf"
  | "plus_eint MinInf    PlusInf   = MinInf"
  | "plus_eint PlusInf   MinInf    = PlusInf"
  | "plus_eint PlusInf   (Fin _)   = PlusInf"
  | "plus_eint PlusInf   PlusInf   = PlusInf"
instance ..
end

instantiation eint :: minus begin
fun minus_eint :: "eint => eint => eint" where
    "minus_eint (Fin n)   (Fin m)   = Fin (n - m)"
  | "minus_eint (Fin _)   MinInf    = PlusInf"
  | "minus_eint (Fin _)   PlusInf   = MinInf"
  | "minus_eint MinInf    MinInf    = MinInf"
  | "minus_eint MinInf    (Fin _)   = MinInf"
  | "minus_eint MinInf    PlusInf   = MinInf"
  | "minus_eint PlusInf   MinInf    = PlusInf"
  | "minus_eint PlusInf   (Fin _)   = PlusInf"
  | "minus_eint PlusInf   PlusInf   = PlusInf"
instance ..
end

instantiation ivl :: plus begin
fun plus_ivl :: "ivl => ivl => ivl" where
    "plus_ivl  (Ivl l1 u1) (Ivl l2 u2) = Ivl (l1 + l2) (u1 + u2)"
instance ..
end

instantiation ivl :: minus begin
fun minus_ivl :: "ivl => ivl => ivl" where
    "minus_ivl (Ivl l1 u1) (Ivl l2 u2) = Ivl (l1 - u2) (u1 - l2)"
instance ..
end

text \<open>
  Emptiness test on intervals.  The raw @{typ ivl} lattice contains many
  unnormalised empty intervals (any @{term \<open>Ivl l u\<close>} with @{text "l > u"},
  including @{term bot}).  @{text ivl_nonempty} captures exactly the intervals
  with non-empty concretization (proved below: implied by any witness, and
  monotone along @{text "\<le>"}); multiplication uses it for proper bottom
  handling, which is what makes the precise corner product monotone.
\<close>
fun ivl_nonempty :: "ivl => bool" where
  "ivl_nonempty (Ivl l u) = (l \<le> u \<and> l \<noteq> PlusInf \<and> u \<noteq> MinInf)"

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

instantiation ivl :: times begin
definition times_ivl :: "ivl => ivl => ivl" where
  "times_ivl a b = (if ivl_nonempty a \<and> ivl_nonempty b then ivl_times_core a b else bot)"
instance ..
end

(* times_ivl_def is NOT declared [simp]: the conditional body would
   cause simp to split on ivl_nonempty before ivl_times_sound / ivl_times_mono
   can fire. Add it explicitly in proofs that must unfold * directly. *)

lemma ivl_plus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i + j \<in> gamma_ivl (a + b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i + j \<in> gamma_ivl (a + b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_minus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i - j \<in> gamma_ivl (a - b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i - j \<in> gamma_ivl (a - b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_times_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i * j \<in> gamma_ivl (a * b)"
proof -
  from assms have ne: "ivl_nonempty a" "ivl_nonempty b"
    by (auto intro: gamma_ivl_nonempty)
  hence eq: "a * b = ivl_times_core a b" by (simp add: times_ivl_def)
  show ?thesis
  proof (cases a; cases b)
    fix l1 u1 l2 u2 assume ab: "a = Ivl l1 u1" "b = Ivl l2 u2"
    show ?thesis
    proof (cases l1; cases u1; cases l2; cases u2)
      fix n1 m1 n2 m2 assume fin: "l1 = Fin n1" "u1 = Fin m1" "l2 = Fin n2" "u2 = Fin m2"
      from assms ab fin have bnds: "n1 \<le> i" "i \<le> m1" "n2 \<le> j" "j \<le> m2" by auto
      show ?thesis using eq ab fin
        int_mult_in_corners_lo[OF bnds] int_mult_in_corners_hi[OF bnds] by simp
    qed (use eq ab ne(1) ne(2) in \<open>simp_all add: ivl_top_def\<close>)
  qed
qed

subsection \<open>Abstract expression evaluation\<close>

fun aval_ivl_hol :: "AExp.aexp => (vname => ivl) => ivl" where
    "aval_ivl_hol (AExp.N n)      \<sigma> = Ivl (Fin n) (Fin n)"
  | "aval_ivl_hol (AExp.V x)      \<sigma> = \<sigma> x"
  | "aval_ivl_hol (AExp.Plus a b) \<sigma> = aval_ivl_hol a \<sigma> + aval_ivl_hol b \<sigma>"

fun aval_ivl :: "aexp => (vname => ivl) => ivl" where
    "aval_ivl (BaseN a)    \<sigma> = aval_ivl_hol a \<sigma>"
  | "aval_ivl (Plus  a b)  \<sigma> = aval_ivl a \<sigma> + aval_ivl b \<sigma>"
  | "aval_ivl (Minus a b)  \<sigma> = aval_ivl a \<sigma> - aval_ivl b \<sigma>"
  | "aval_ivl (Times a b)  \<sigma> = aval_ivl a \<sigma> * aval_ivl b \<sigma>"

lemma aval_ivl_hol_sound:
  "(\<forall>x. s x \<in> gamma_ivl (\<sigma> x))
   \<Longrightarrow> AExp.aval a s \<in> gamma_ivl (aval_ivl_hol a \<sigma>)"
  by (induction a; simp add: ivl_plus_sound)

lemma aval_ivl_sound:
  "(\<forall>x. s x \<in> gamma_ivl (\<sigma> x))
   \<Longrightarrow> aval a s \<in> gamma_ivl (aval_ivl a \<sigma>)"
  by (induction a;
      simp add: aval.simps aval_ivl.simps aval_ivl_hol_sound
                ivl_plus_sound ivl_minus_sound ivl_times_sound)

subsection \<open>Backward inverse operators\<close>

text \<open>
  Inverse operators for backward analysis over intervals.
  @{text inv_less_ivl} performs precise interval narrowing: on the true branch
  of @{text "n1 < n2"}, the upper bound of @{text n1} tightens to one below
  the upper bound of @{text n2}, and the lower bound of @{text n2} tightens to
  one above the lower bound of @{text n1}.  On the false branch (@{text "n1 \<ge> n2"}),
  @{text n1}\<open>s\<close> lower bound tightens to the lower bound of @{text n2}, and @{text n2}\<open>s\<close>
  upper bound tightens to the upper bound of @{text n1}.  The remaining inverse
  operators are conservative (identity) for simplicity.
\<close>

fun inv_less_ivl :: "bool => ivl => ivl => ivl * ivl" where
    "inv_less_ivl True  (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl MinInf (u2 - Fin 1),
        Ivl l2 u2 \<sqinter> Ivl (l1 + Fin 1) PlusInf)"
  | "inv_less_ivl False (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl l2 PlusInf,
        Ivl l2 u2 \<sqinter> Ivl MinInf u1)"

fun inv_plus_ivl :: "ivl => ivl => ivl => ivl * ivl" where
  "inv_plus_ivl _ a1 a2 = (a1, a2)"

fun inv_minus_ivl :: "ivl => ivl => ivl => ivl * ivl" where
  "inv_minus_ivl _ a1 a2 = (a1, a2)"

fun inv_times_ivl :: "ivl => ivl => ivl => ivl * ivl" where
  "inv_times_ivl _ a1 a2 = (a1, a2)"

lemma inv_less_ivl_n1_ub:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl MinInf (u2 - Fin 1))"
  by (cases u2; auto simp: gamma_ivl.simps; linarith)

lemma inv_less_ivl_n2_lb:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl (l1 + Fin 1) PlusInf)"
  by (cases l1; auto simp: gamma_ivl.simps; linarith)

lemma inv_less_ivl_n1_ge_lb:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl l2 PlusInf)"
  by (cases l2; auto simp: gamma_ivl.simps; linarith)

lemma inv_less_ivl_n2_le_ub:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl MinInf u1)"
  by (cases u1; auto simp: gamma_ivl.simps; linarith)

lemma inv_less_ivl_sound:
  assumes g1: "n1 \<in> gamma_ivl a1" and g2: "n2 \<in> gamma_ivl a2" and eq: "(n1 < n2) = res"
  shows "n1 \<in> gamma_ivl (fst (inv_less_ivl res a1 a2))
       \<and> n2 \<in> gamma_ivl (snd (inv_less_ivl res a1 a2))"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (cases a1) auto
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (cases a2) auto
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

subsection \<open>Backward-domain interpretation\<close>

global_interpretation ivl_backward_domain:
    backward_domain meet_ivl aval_ivl
                    inv_less_ivl inv_plus_ivl inv_minus_ivl inv_times_ivl
  defines
    afilter_ivl = ivl_backward_domain.afilter
    and bfilter_ivl = ivl_backward_domain.bfilter
proof unfold_locales
  fix n :: int and a b :: ivl
  assume H1: "n \<in> gamma a" and H2: "n \<in> gamma b"
  have h1: "n \<in> gamma_ivl a" using H1 by simp
  have h2: "n \<in> gamma_ivl b" using H2 by simp
  show "n \<in> gamma (meet_ivl a b)"
    using meet_ivl_gamma[simplified, OF h1 h2] by simp
next
  fix s :: store and e :: aexp and \<sigma> :: "vname \<Rightarrow> ivl"
  assume H: "\<forall>x. s x \<in> gamma (\<sigma> x)"
  have h: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" using H by simp
  show "aval e s \<in> gamma (aval_ivl e \<sigma>)"
    using aval_ivl_sound[OF h] by simp
next
  fix n1 n2 :: int and a1 a2 :: ivl and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 < n2) = res"
  have h1: "n1 \<in> gamma_ivl a1" using H1 by simp
  have h2: "n2 \<in> gamma_ivl a2" using H2 by simp
  show "n1 \<in> gamma (fst (inv_less_ivl res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less_ivl res a1 a2))"
    using inv_less_ivl_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 + n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_plus_ivl r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus_ivl r a1 a2))"
    using H1 H2 by simp
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 - n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_minus_ivl r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus_ivl r a1 a2))"
    using H1 H2 by simp
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 * n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_times_ivl r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times_ivl r a1 a2))"
    using H1 H2 by simp
qed

subsection \<open>Abstract assume and assignment\<close>

text \<open>
  Both guards delegate to the generic @{text bfilter} proved sound in
  @{locale backward_domain}.  @{text "assume_ivl b \<sigma>"} filters for @{text "bval b"},
  @{text "assume_not_ivl b \<sigma>"} for @{text "\<not> bval b"}.
\<close>

definition assume_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
  "assume_ivl b \<sigma> = bfilter_ivl b True \<sigma>"

lemma assume_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_ivl b \<sigma>\<rbrakk>"
  unfolding assume_ivl_def
  using ivl_backward_domain.bfilter_sound by simp

definition assume_not_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
  "assume_not_ivl b \<sigma> = bfilter_ivl b False \<sigma>"

lemma assume_not_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_not_ivl b \<sigma>\<rbrakk>"
  unfolding assume_not_ivl_def
  using ivl_backward_domain.bfilter_sound by (simp add: eq_False)

definition assign_ivl ::
    "vname => aexp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a \<sigma> = \<sigma>(x := aval_ivl a \<sigma>)"

lemma assign_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk>
   \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign_ivl x a \<sigma>\<rbrakk>"
  unfolding gamma_state_def assign_ivl_def
  by (auto simp: aval_ivl_sound)

subsection \<open>Procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval.\<close>
definition enter_ivl :: "ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_ivl \<sigma> = (\<lambda>x. if is_global x then \<sigma> x else Ivl MinInf PlusInf)"

lemma enter_ivl_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_ivl \<sigma>\<rbrakk>"
  using assms unfolding gamma_state_def enter_ivl_def enter_state_def
  by (intro CollectI allI) (auto simp: gamma_ivl.simps)

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl,
               tf_enter      = enter_ivl |)"

lemma ivl_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assign_ivl_sound)

lemma ivl_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_ivl_sound)

lemma ivl_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_not_ivl_sound)

lemma ivl_tf_sound_enter:
  "\<forall>\<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. enter_state st \<in> \<lbrakk>tf_enter ivl_tf \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: enter_ivl_sound)

interpretation ivl_sound_tf: sound_transfer ivl_tf
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s(x := aval a s) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assign)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assume)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assume_not)
  show "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. enter_state s \<in> \<lbrakk>tf_enter ivl_tf \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_enter)
qed

subsection \<open>Monotonicity of the transfer functions\<close>

lemma eint_plus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b1 b2 \<Longrightarrow> eint_le (a1 + b1) (a2 + b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

lemma eint_minus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b2 b1 \<Longrightarrow> eint_le (a1 - b1) (a2 - b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

lemma ivl_plus_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> a1 + b1 \<le> a2 + (b2::ivl)"
  by (cases a1; cases a2; cases b1; cases b2;
      simp add: less_eq_ivl_def eint_plus_mono)

lemma ivl_minus_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> a1 - b1 \<le> a2 - (b2::ivl)"
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
  shows "a1 * b1 \<le> a2 * (b2::ivl)"
proof (cases "ivl_nonempty a1 \<and> ivl_nonempty b1")
  case False
  then have "a1 * b1 = bot" by (auto simp add: times_ivl_def)
  thus ?thesis by simp
next
  case True
  hence ne2: "ivl_nonempty a2" "ivl_nonempty b2"
    using assms ivl_nonempty_mono by blast+
  have "a1 * b1 = ivl_times_core a1 b1"
    using True by (simp add: times_ivl_def)
  moreover have "a2 * b2 = ivl_times_core a2 b2"
    using ne2 by (simp add: times_ivl_def)
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

lemma inv_less_ivl_mono:
  assumes a1: "(a1 :: ivl) \<le> a1'" and a2: "(a2 :: ivl) \<le> a2'"
  shows "fst (inv_less_ivl res a1 a2) \<le> fst (inv_less_ivl res a1' a2')
       \<and> snd (inv_less_ivl res a1 a2) \<le> snd (inv_less_ivl res a1' a2')"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (cases a1) auto
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (cases a2) auto
  obtain l1' u1' where ha1': "a1' = Ivl l1' u1'" by (cases a1') auto
  obtain l2' u2' where ha2': "a2' = Ivl l2' u2'" by (cases a2') auto
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

lemma afilter_ivl_mono:
  "a1 \<le> (a2 :: ivl) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_ivl e a1 sigma1 \<le>
   afilter_ivl e a2 sigma2"
proof (induction e arbitrary: a1 a2 sigma1 sigma2)
  case (BaseN a')
  show ?case
  proof (cases a')
    case (V x)
    show ?thesis
      unfolding V ivl_backward_domain.afilter.simps
      using BaseN.prems
    proof (intro le_funI)
      fix y
      show "(sigma1(x := meet_ivl a1 (sigma1 x))) y \<le> (sigma2(x := meet_ivl a2 (sigma2 x))) y"
      proof (cases "y = x")
        case True
        have eq1: "(sigma1(x := meet_ivl a1 (sigma1 x))) y = meet_ivl a1 (sigma1 x)" using True by simp
        have eq2: "(sigma2(x := meet_ivl a2 (sigma2 x))) y = meet_ivl a2 (sigma2 x)" using True by simp
        have mono: "meet_ivl a1 (sigma1 x) \<le> meet_ivl a2 (sigma2 x)"
          using inf_mono[OF BaseN.prems(1) le_funD[OF BaseN.prems(2)]] by simp
        from eq1 eq2 mono show ?thesis by simp
      next
        case False
        have eq1: "(sigma1(x := meet_ivl a1 (sigma1 x))) y = sigma1 y" using False by simp
        have eq2: "(sigma2(x := meet_ivl a2 (sigma2 x))) y = sigma2 y" using False by simp
        have mono: "sigma1 y \<le> sigma2 y" by (rule le_funD[OF BaseN.prems(2)])
        from eq1 eq2 mono show ?thesis by simp
      qed
    qed
  next
    case (N x1)
    have h1: "afilter_ivl (IMP2_Syntax.N x1) a1 sigma1 = sigma1" by simp
    have h2: "afilter_ivl (IMP2_Syntax.N x1) a2 sigma2 = sigma2" by simp
    show ?thesis using BaseN.prems(2) by (subst N)+ (simp add: h1 h2)
  next
    case (Plus x1 x2)
    have h1: "afilter_ivl (BaseN (AExp.aexp.Plus x1 x2)) a1 sigma1 = sigma1" by simp
    have h2: "afilter_ivl (BaseN (AExp.aexp.Plus x1 x2)) a2 sigma2 = sigma2" by simp
    show ?thesis using BaseN.prems(2) by (subst Plus)+ (simp add: h1 h2)
  qed
next
  case (Plus e1 e2)
  have v1: "aval_ivl e1 sigma1 \<le> aval_ivl e1 sigma2" using aval_ivl_mono[OF Plus.prems(2)] .
  have v2: "aval_ivl e2 sigma1 \<le> aval_ivl e2 sigma2" using aval_ivl_mono[OF Plus.prems(2)] .
  have step: "afilter_ivl e2 (aval_ivl e2 sigma1) sigma1 \<le>
              afilter_ivl e2 (aval_ivl e2 sigma2) sigma2"
    using Plus.IH(2)[OF v2 Plus.prems(2)] .
  have lhs: "afilter_ivl (Plus e1 e2) a1 sigma1 =
    afilter_ivl e1 (aval_ivl e1 sigma1) (afilter_ivl e2 (aval_ivl e2 sigma1) sigma1)"
    by simp
  have rhs: "afilter_ivl (Plus e1 e2) a2 sigma2 =
    afilter_ivl e1 (aval_ivl e1 sigma2) (afilter_ivl e2 (aval_ivl e2 sigma2) sigma2)"
    by simp
  show ?case unfolding lhs rhs by (rule Plus.IH(1)[OF v1 step])
next
  case (Minus e1 e2)
  have v1: "aval_ivl e1 sigma1 \<le> aval_ivl e1 sigma2" using aval_ivl_mono[OF Minus.prems(2)] .
  have v2: "aval_ivl e2 sigma1 \<le> aval_ivl e2 sigma2" using aval_ivl_mono[OF Minus.prems(2)] .
  have step: "afilter_ivl e2 (aval_ivl e2 sigma1) sigma1 \<le>
              afilter_ivl e2 (aval_ivl e2 sigma2) sigma2"
    using Minus.IH(2)[OF v2 Minus.prems(2)] .
  have lhs: "afilter_ivl (Minus e1 e2) a1 sigma1 =
    afilter_ivl e1 (aval_ivl e1 sigma1) (afilter_ivl e2 (aval_ivl e2 sigma1) sigma1)"
    by simp
  have rhs: "afilter_ivl (Minus e1 e2) a2 sigma2 =
    afilter_ivl e1 (aval_ivl e1 sigma2) (afilter_ivl e2 (aval_ivl e2 sigma2) sigma2)"
    by simp
  show ?case unfolding lhs rhs by (rule Minus.IH(1)[OF v1 step])
next
  case (Times e1 e2)
  have v1: "aval_ivl e1 sigma1 \<le> aval_ivl e1 sigma2" using aval_ivl_mono[OF Times.prems(2)] .
  have v2: "aval_ivl e2 sigma1 \<le> aval_ivl e2 sigma2" using aval_ivl_mono[OF Times.prems(2)] .
  have step: "afilter_ivl e2 (aval_ivl e2 sigma1) sigma1 \<le>
              afilter_ivl e2 (aval_ivl e2 sigma2) sigma2"
    using Times.IH(2)[OF v2 Times.prems(2)] .
  have lhs: "afilter_ivl (Times e1 e2) a1 sigma1 =
    afilter_ivl e1 (aval_ivl e1 sigma1) (afilter_ivl e2 (aval_ivl e2 sigma1) sigma1)"
    by simp
  have rhs: "afilter_ivl (Times e1 e2) a2 sigma2 =
    afilter_ivl e1 (aval_ivl e1 sigma2) (afilter_ivl e2 (aval_ivl e2 sigma2) sigma2)"
    by simp
  show ?case unfolding lhs rhs by (rule Times.IH(1)[OF v1 step])
qed

lemma bfilter_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   bfilter_ivl b res sigma1 \<le>
   bfilter_ivl b res sigma2"
proof (induction b arbitrary: res sigma1 sigma2)
  case (BaseB b')
  have h1: "bfilter_ivl (BaseB b') res sigma1 = sigma1" by simp
  have h2: "bfilter_ivl (BaseB b') res sigma2 = sigma2" by simp
  show ?case unfolding h1 h2 by (rule BaseB.prems)
next
  case (Not b)
  show ?case
    unfolding ivl_backward_domain.bfilter.simps
    by (rule Not.IH[OF Not.prems])
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    hence r: "res = True" by simp
    have step: "bfilter_ivl b2 True sigma1 \<le>
                bfilter_ivl b2 True sigma2"
      by (rule And.IH(2)[OF And.prems])
    show ?thesis
      unfolding r ivl_backward_domain.bfilter.simps
      by (rule And.IH(1)[OF step])
  next
    case False
    hence r: "res = False" by simp
    have ih1: "bfilter_ivl b1 False sigma1 \<le>
               bfilter_ivl b1 False sigma2"
      by (rule And.IH(1)[OF And.prems])
    have ih2: "bfilter_ivl b2 False sigma1 \<le>
               bfilter_ivl b2 False sigma2"
      by (rule And.IH(2)[OF And.prems])
    show ?thesis
      unfolding r ivl_backward_domain.bfilter.simps
      by (rule sup_mono[OF ih1 ih2])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    hence r: "res = True" by simp
    have ih1: "bfilter_ivl b1 True sigma1 \<le>
               bfilter_ivl b1 True sigma2"
      by (rule Or.IH(1)[OF Or.prems])
    have ih2: "bfilter_ivl b2 True sigma1 \<le>
               bfilter_ivl b2 True sigma2"
      by (rule Or.IH(2)[OF Or.prems])
    show ?thesis
      unfolding r ivl_backward_domain.bfilter.simps
      by (rule sup_mono[OF ih1 ih2])
  next
    case False
    hence r: "res = False" by simp
    have step: "bfilter_ivl b2 False sigma1 \<le>
                bfilter_ivl b2 False sigma2"
      by (rule Or.IH(2)[OF Or.prems])
    show ?thesis
      unfolding r ivl_backward_domain.bfilter.simps
      by (rule Or.IH(1)[OF step])
  qed
next
  case (Less e1 e2)
  have vmono1: "aval_ivl e1 sigma1 \<le> aval_ivl e1 sigma2"
    using aval_ivl_mono[OF Less.prems] .
  have vmono2: "aval_ivl e2 sigma1 \<le> aval_ivl e2 sigma2"
    using aval_ivl_mono[OF Less.prems] .
  have amono: "fst (inv_less_ivl res (aval_ivl e1 sigma1) (aval_ivl e2 sigma1)) \<le>
               fst (inv_less_ivl res (aval_ivl e1 sigma2) (aval_ivl e2 sigma2)) \<and>
               snd (inv_less_ivl res (aval_ivl e1 sigma1) (aval_ivl e2 sigma1)) \<le>
               snd (inv_less_ivl res (aval_ivl e1 sigma2) (aval_ivl e2 sigma2))"
    by (rule inv_less_ivl_mono[OF vmono1 vmono2])
  have step: "afilter_ivl e2
                (snd (inv_less_ivl res (aval_ivl e1 sigma1) (aval_ivl e2 sigma1))) sigma1 \<le>
              afilter_ivl e2
                (snd (inv_less_ivl res (aval_ivl e1 sigma2) (aval_ivl e2 sigma2))) sigma2"
    by (rule afilter_ivl_mono[OF amono[THEN conjunct2] Less.prems])
  show ?case
    unfolding ivl_backward_domain.bfilter.simps Let_def case_prod_beta
    by (rule afilter_ivl_mono[OF amono[THEN conjunct1] step])
next
  case (Eq e1 e2)
  show ?case
  proof (cases res)
    case True
    hence r: "res = True" by simp
    have vmono1: "aval_ivl e1 sigma1 \<le> aval_ivl e1 sigma2"
      using aval_ivl_mono[OF Eq.prems] .
    have vmono2: "aval_ivl e2 sigma1 \<le> aval_ivl e2 sigma2"
      using aval_ivl_mono[OF Eq.prems] .
    have mmono: "meet_ivl (aval_ivl e1 sigma1) (aval_ivl e2 sigma1) \<le>
                 meet_ivl (aval_ivl e1 sigma2) (aval_ivl e2 sigma2)"
      using inf_mono[OF vmono1 vmono2] by simp
    have step: "afilter_ivl e2
                  (meet_ivl (aval_ivl e1 sigma1) (aval_ivl e2 sigma1)) sigma1 \<le>
                afilter_ivl e2
                  (meet_ivl (aval_ivl e1 sigma2) (aval_ivl e2 sigma2)) sigma2"
      using afilter_ivl_mono[OF mmono Eq.prems] .
    show ?thesis
      unfolding r ivl_backward_domain.bfilter.simps Let_def
      by (rule afilter_ivl_mono[OF mmono step])
  next
    case False
    hence r: "res = False" by simp
    have h1: "bfilter_ivl (Eq e1 e2) False sigma1 = sigma1" by simp
    have h2: "bfilter_ivl (Eq e1 e2) False sigma2 = sigma2" by simp
    show ?thesis unfolding r h1 h2 by (rule Eq.prems)
  qed
qed

lemma assume_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_ivl b sigma1 \<le> assume_ivl b sigma2"
  unfolding assume_ivl_def
  by (rule bfilter_ivl_mono)

lemma assume_not_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_ivl b sigma1 \<le> assume_not_ivl b sigma2"
  unfolding assume_not_ivl_def
  by (rule bfilter_ivl_mono)

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

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain.
  Covers the core evaluation rules shared by all interval examples.
  Examples with multiplication also need @{thm [source] times_ivl_def},
  @{thm [source] ivl_times_core.simps}, @{thm [source] ivl_nonempty.simps};
  examples with assume edges also need @{thm [source] assume_ivl_def},
  @{thm [source] assume_not_ivl_def}, @{thm [source] ivl_backward_domain.bfilter.simps};
  examples with procedure calls also need @{thm [source] enter_ivl_def},
  @{thm [source] combine_abs_def}, @{thm [source] is_global_def}.
\<close>
lemmas ivl_eval_simps =
  ivl_tf_def assign_ivl_def
  aval_ivl.simps aval_ivl_hol.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

subsection \<open>Printable instance\<close>

fun string_of_eint :: "eint \<Rightarrow> string" where
    "string_of_eint MinInf  = ''-inf''"
  | "string_of_eint PlusInf = ''+inf''"
  | "string_of_eint (Fin n) = show_int n"

fun string_of_ivl :: "ivl \<Rightarrow> string" where
  "string_of_ivl (Ivl l u) = ''['' @ string_of_eint l @ '','' @ string_of_eint u @ '']''"

instantiation ivl :: show_val begin
definition "show_val_ivl (i :: ivl) = string_of_ivl i"
instance ..
end

lemma show_val_ivl_eq [simp]: "(show_val :: ivl \<Rightarrow> string) = string_of_ivl"
  unfolding show_val_ivl_def by simp

subsection \<open>Executable examples\<close>

value "(Fin 3 :: eint) + Fin (-1)"
value "(PlusInf :: eint) + Fin 100"
value "(Fin 5 :: eint) - Fin 3"
value "(Fin 0 :: eint) - PlusInf"

value "Ivl (Fin 1) (Fin 3) + Ivl (Fin 2) (Fin 5)"
value "Ivl (Fin 5) (Fin 10) - Ivl (Fin 1) (Fin 3)"
value "Ivl (Fin (-2)) (Fin 3) * Ivl (Fin (-1)) (Fin 4)"

value "join_ivl (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 2) (Fin 5))"
value "widen_ivl_core (Ivl (Fin 0) (Fin 1)) (Ivl (Fin 0) (Fin 2))"
value "widen_ivl_core (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 0) (Fin 3))"
value "meet_ivl (Ivl (Fin 0) (Fin 10)) (Ivl (Fin 3) (Fin 7))"

value "string_of_eint MinInf"
value "string_of_eint PlusInf"
value "string_of_ivl (Ivl (Fin (-3)) PlusInf)"

value "aval_ivl (Minus (V ''x'') (N 1)) ((\<lambda>_. ivl_top)(''x'' := Ivl (Fin 5) (Fin 10)))"
value "(assume_ivl (Less (V ''x'') (N 5)) ((\<lambda>_. ivl_top)(''x'' := Ivl (Fin 0) (Fin 10)))) ''x''"

end
