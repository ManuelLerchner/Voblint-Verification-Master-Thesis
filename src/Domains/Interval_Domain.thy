theory Interval_Domain
  imports Abstract_Domain Constraint_System IMP2_Semantics
begin

(*
  Interval Domain -- Instantiation of abstract_domain.

  An interval [l, u] abstracts a set of integers {n | l <= n <= n <= u}.
  Special cases:
    [+inf, -inf]  (i.e., l > u)  -- empty (Bot)
    [-inf, +inf]                  -- all integers (Top)

  This is the main (Tier-2) domain of the thesis.  Key challenges:
    - Widening: needed for convergence on loop-carried values.
    - Narrowing: optional precision recovery after widening.

  Transfer functions are more complex than for signs.
  Connection point: HOL-IMP.Abs_Int2_ivl has a verified interval analysis
  for the original IMP language; we will bridge or re-prove here for IMP2.

  TODO: decide whether to import HOL-IMP.Abs_Int2_ivl (requires adapting
        to IMP2 syntax) or define the interval domain from scratch.
*)

(* ── Extended Integer for Interval Bounds ────────────────────── *)
(*
  We use an option-like type: None = infinity / -infinity.
  Or alternatively use the HOL-IMP approach with  ivl = Ivl int int.
  For now: use int for bounds with a separate "unbounded" flag.
  TODO: pick concrete representation after discussion with supervisors.
*)

datatype eint = MinInf | Fin int | PlusInf

fun eint_le :: "eint => eint => bool" where
    "eint_le MinInf  _       = True"
  | "eint_le _       PlusInf = True"
  | "eint_le (Fin n) (Fin m) = (n <= m)"
  | "eint_le _       MinInf  = False"
  | "eint_le PlusInf _       = False"

(* ── Interval Type ────────────────────────────────────────────── *)

datatype ivl = Ivl eint eint   (* Ivl l u = [l, u] *)

instantiation ivl :: ord begin
definition less_eq_ivl :: "ivl => ivl => bool" where
  "(a::ivl) <= b = (case (a, b) of (Ivl l1 u1, Ivl l2 u2) => eint_le l2 l1 \<and> eint_le u1 u2)"
definition less_ivl :: "ivl => ivl => bool" where
  "(a::ivl) < b = (a <= b \<and> \<not> b <= a)"
instance ..
end

(* bot must come before order_bot *)
instantiation ivl :: bot begin
definition bot_ivl :: ivl where
  "bot_ivl = Ivl PlusInf MinInf"
instance ..
end

(* equal comes from datatype ivl (no separate instantiation). *)

(* eint_le supporting lemmas needed for order proof *)
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
    unfolding less_eq_ivl_def bot_ivl_def
    by (cases x) simp
qed
end

definition ivl_bot :: ivl where
  "ivl_bot = Ivl PlusInf MinInf"   (* empty: l > u *)

definition ivl_top :: ivl where
  "ivl_top = Ivl MinInf PlusInf"   (* full: [-inf, +inf] *)

(* ── Concretization ───────────────────────────────────────────── *)

fun gamma_ivl :: "ivl => int set" where
    "gamma_ivl (Ivl l u) = {n. eint_le l (Fin n) \<and> eint_le (Fin n) u}"

lemma gamma_ivl_bot: "gamma_ivl ivl_bot = {}"
  unfolding ivl_bot_def by auto

lemma gamma_ivl_top: "gamma_ivl ivl_top = UNIV"
  unfolding ivl_top_def by auto

(* ── Join and Widening ────────────────────────────────────────── *)

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

(*
  Standard interval widening: keep l if l decreased, else push to -inf;
  keep u if u increased, else push to +inf.
  Ensures any ascending chain stabilises after at most 2 steps.
*)
fun widen_ivl :: "ivl => ivl => ivl" where
    "widen_ivl (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if eint_le l1 l2 then l1 else MinInf)
           (if eint_le u2 u1 then u1 else PlusInf)"

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

lemma join_ivl_ub1: "gamma_ivl a \<subseteq> gamma_ivl (join_ivl a b)"
  using gamma_ivl_mono join_ivl_le_ub1[unfolded sup_ivl_def[symmetric]]
  by (metis sup_ivl_def)

lemma join_ivl_ub2: "gamma_ivl b \<subseteq> gamma_ivl (join_ivl a b)"
  using gamma_ivl_mono join_ivl_le_ub2[unfolded sup_ivl_def[symmetric]]
  by (metis sup_ivl_def)

lemma join_ivl_comm:  "join_ivl a b = join_ivl b a"
  using sup_commute by (metis sup_ivl_def)

lemma join_ivl_assoc: "join_ivl a (join_ivl b c) = join_ivl (join_ivl a b) c"
  using sup_assoc by (metis sup_ivl_def)

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

(* Widening termination: every widen-ascending chain stabilises.
   At each step each bound either stays or jumps to MinInf/PlusInf, so the
   chain takes values in at most 4 distinct intervals. Once a bound hits
   the infinite end it remains there. After at most 2 transitions the chain
   is constant. *)
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
  (* If lb never hits MinInf it is constant; symmetric for ub. *)
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

(* ── Abstract Domain Instantiation ───────────────────────────── *)

interpretation ivl_domain:
  abstract_domain gamma_ivl widen_ivl
proof (unfold_locales)
  show "gamma_ivl bot = {}"
    unfolding bot_ivl_def by auto
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

(* ── Transfer Functions ──────────────────────────────────────── *)

(* Precise eint addition. The two pathological combinations
   (MinInf + PlusInf and PlusInf + MinInf) are unreachable from non-empty
   intervals, so any total assignment is sound; we pick MinInf / PlusInf. *)
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

(* Precise eint subtraction. Same unreachable-edge handling. *)
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
    "ivl_plus  (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (eint_plus l1 l2) (eint_plus u1 u2)"

fun ivl_minus :: "ivl => ivl => ivl" where
    "ivl_minus (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (eint_minus l1 u2) (eint_minus u1 l2)"

(* Precise interval multiplication for finite bounds.
   When any bound is infinite (MinInf or PlusInf) we fall back to top, since
   precise treatment requires sign-dependent corner reasoning that is much
   more involved with the extended-integer arithmetic. *)
fun ivl_times :: "ivl => ivl => ivl" where
    "ivl_times (Ivl (Fin l1) (Fin u1)) (Ivl (Fin l2) (Fin u2)) =
       Ivl (Fin (min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2)))))
           (Fin (max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2))))) "
  | "ivl_times _ _ = Ivl MinInf PlusInf"

(* ── Soundness of abstract arithmetic ─────────────────────────── *)

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

(* Corner-bound principle for the all-finite case. *)
lemma int_mult_in_corners_lo:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2))) \<le> i * j"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono
                   mult_left_mono_neg mult_right_mono_neg min_def)

lemma int_mult_in_corners_hi:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "i * j \<le> max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono
                   mult_left_mono_neg mult_right_mono_neg max_def)

lemma ivl_times_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i * j \<in> gamma_ivl (ivl_times a b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume ab: "a = Ivl l1 u1" "b = Ivl l2 u2"
  show "i * j \<in> gamma_ivl (ivl_times a b)"
  proof (cases l1; cases u1; cases l2; cases u2)
    fix n1 m1 n2 m2 :: int
    assume fin: "l1 = Fin n1" "u1 = Fin m1" "l2 = Fin n2" "u2 = Fin m2"
    from assms ab fin have bnds:
      "n1 \<le> i" "i \<le> m1" "n2 \<le> j" "j \<le> m2" by auto
    show "i * j \<in> gamma_ivl (ivl_times a b)"
      unfolding ab fin
      using int_mult_in_corners_lo[OF bnds] int_mult_in_corners_hi[OF bnds]
      by simp
  qed (auto simp: ab)
qed

fun aval_ivl_hol :: "AExp.aexp => (vname => ivl) => ivl" where
    "aval_ivl_hol (AExp.N n)      sigma = Ivl (Fin n) (Fin n)"
  | "aval_ivl_hol (AExp.V x)      sigma = sigma x"
  | "aval_ivl_hol (AExp.Plus a b) sigma = ivl_plus (aval_ivl_hol a sigma) (aval_ivl_hol b sigma)"

fun aval_ivl :: "aexp => (vname => ivl) => ivl" where
    "aval_ivl (BaseN a)    sigma = aval_ivl_hol a sigma"
  | "aval_ivl (Plus  a b)  sigma = ivl_plus  (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Minus a b)  sigma = ivl_minus (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Times a b)  sigma = ivl_times (aval_ivl a sigma) (aval_ivl b sigma)"

(* Soundness of abstract arithmetic. *)
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

(* Abstract assume: interval-based branch refinement *)
fun assume_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_ivl _ sigma = sigma"   (* TODO: precise narrowing on Less/Eq *)

fun assume_not_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_not_ivl _ sigma = sigma"   (* TODO *)

definition assign_ivl ::
    "vname => aexp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a sigma = sigma(x := aval_ivl a sigma)"

lemma assign_ivl_sound:
  "s \<in> ivl_domain.gamma_state sigma
   \<Longrightarrow> s(x := aval a s) \<in> ivl_domain.gamma_state (assign_ivl x a sigma)"
  unfolding ivl_domain.gamma_state_def assign_ivl_def
  by (auto simp: aval_ivl_sound)

(* ── Bundled Transfer Functions ──────────────────────────────── *)

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl |)"

end
