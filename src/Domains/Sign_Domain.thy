theory Sign_Domain
  imports Abstract_Domain Constraint_System IMP2_SmallStep
begin

(*
  Sign Domain -- Instantiation of abstract_domain.

  sign abstracts integers by their sign:
    Bot  -- empty (unreachable / undefined)
    Neg  -- strictly negative  {n | n < 0}
    Zero -- exactly zero       {0}
    Pos  -- strictly positive  {n | n > 0}
    Top  -- all integers       UNIV

  Finite lattice, no widening needed (every chain terminates immediately).
  Used as the Tier-1 scaffold domain to validate the full pipeline.
*)

(* ── Sign Datatype ────────────────────────────────────────────── *)

datatype sign = SBot | SNeg | SZero | SPos | STop

(* ── Concretization ───────────────────────────────────────────── *)

fun gamma_sign :: "sign => int set" where
    "gamma_sign SBot  = {}"
  | "gamma_sign SNeg  = {n. n < 0}"
  | "gamma_sign SZero = {0}"
  | "gamma_sign SPos  = {n. n > 0}"
  | "gamma_sign STop  = UNIV"

(* ── Partial Order ────────────────────────────────────────────── *)

fun sign_le :: "sign => sign => bool" where
    "sign_le SBot  _     = True"
  | "sign_le _     STop  = True"
  | "sign_le SNeg  SNeg  = True"
  | "sign_le SZero SZero = True"
  | "sign_le SPos  SPos  = True"
  | "sign_le _     _     = False"

lemma sign_le_refl:    "sign_le s s"                              by (cases s) simp_all

lemma sign_le_antisym:
  assumes st: "sign_le s t" and ts: "sign_le t s"
  shows "s = t"
  using st ts by (cases s; cases t; simp)

lemma sign_le_trans:
  assumes st: "sign_le s t" and tu: "sign_le t u"
  shows "sign_le s u"
  using st tu by (cases s; cases t; cases u; simp)

lemma gamma_sign_mono:
  assumes st: "sign_le s t"
  shows "gamma_sign s <= gamma_sign t"
  using st by (cases s; cases t; auto simp: gamma_sign.simps)

instantiation sign :: ord begin
definition less_eq_sign :: "sign => sign => bool" where "(a::sign) <= b = sign_le a b"
definition less_sign    :: "sign => sign => bool" where "(a::sign) <  b = (sign_le a b \<and> \<not> sign_le b a)"
instance ..
end

instance sign :: preorder
proof
  fix x y z :: sign
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_sign_def less_eq_sign_def by simp
  show "x \<le> x"
    by (simp add: less_eq_sign_def sign_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_sign_def by (rule sign_le_trans)
qed

(* bot instance: required so abs_state = vname => sign has bot, enabling AFP mlup *)
instantiation sign :: bot begin
definition "bot_sign = SBot"
instance ..
end

(* ── Join (Least Upper Bound) ─────────────────────────────────── *)

fun join_sign :: "sign => sign => sign" where
    "join_sign SBot b     = b"
  | "join_sign a    SBot  = a"
  | "join_sign STop _     = STop"
  | "join_sign _    STop  = STop"
  | "join_sign SNeg SNeg  = SNeg"
  | "join_sign SZero SZero = SZero"
  | "join_sign SPos SPos  = SPos"
  | "join_sign _    _     = STop"

lemma join_sign_ub1: "sign_le a (join_sign a b)"
  by (cases a; cases b; simp add: join_sign.simps)

lemma join_sign_ub2: "sign_le b (join_sign a b)"
  by (cases a; cases b; simp add: join_sign.simps)

lemma join_sign_least: "sign_le a c ==> sign_le b c ==> sign_le (join_sign a b) c"
  by (cases a; cases b; cases c; simp add: join_sign.simps)
lemma join_sign_comm:  "join_sign a b = join_sign b a"                 by (cases a; cases b) simp_all
lemma join_sign_assoc: "join_sign a (join_sign b c) = join_sign (join_sign a b) c"  by (cases a; cases b; cases c) simp_all

(* ── Widening (identity for finite domain: widen = join) ────── *)

definition widen_sign :: "sign => sign => sign" where
  "widen_sign a b = join_sign a b"

(* ── Abstract Arithmetic Operations ──────────────────────────── *)
(*
  Define helpers first so aval_sign can call them.
*)

fun sign_plus :: "sign => sign => sign" where
    "sign_plus SBot _     = SBot"
  | "sign_plus _    SBot  = SBot"
  | "sign_plus SNeg SNeg  = SNeg"
  | "sign_plus SPos SPos  = SPos"
  | "sign_plus SZero b    = b"
  | "sign_plus a    SZero = a"
  | "sign_plus _    _     = STop"

fun sign_minus :: "sign => sign => sign" where
    "sign_minus SBot _     = SBot"
  | "sign_minus _    SBot  = SBot"
  | "sign_minus SNeg SPos  = SNeg"
  | "sign_minus SPos SNeg  = SPos"
  | "sign_minus SZero SZero = SZero"
  | "sign_minus _    _     = STop"

fun sign_times :: "sign => sign => sign" where
    "sign_times SBot _     = SBot"
  | "sign_times _    SBot  = SBot"
  | "sign_times SZero _    = SZero"
  | "sign_times _    SZero = SZero"
  | "sign_times SNeg SNeg  = SPos"
  | "sign_times SPos SPos  = SPos"
  | "sign_times SNeg SPos  = SNeg"
  | "sign_times SPos SNeg  = SNeg"
  | "sign_times STop _     = STop"
  | "sign_times _    STop  = STop"

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

lemma sign_of_int_gamma: "n : gamma_sign (sign_of_int n)"
  by (auto simp: sign_of_int.simps gamma_sign.simps split: if_splits)

fun aval_sign_hol :: "AExp.aexp => (vname => sign) => sign" where
    "aval_sign_hol (AExp.N n)      sigma = sign_of_int n"
  | "aval_sign_hol (AExp.V x)      sigma = sigma x"
  | "aval_sign_hol (AExp.Plus a b) sigma = sign_plus (aval_sign_hol a sigma) (aval_sign_hol b sigma)"

fun aval_sign :: "aexp => (vname => sign) => sign" where
    "aval_sign (BaseN a)    sigma = aval_sign_hol a sigma"
  | "aval_sign (Plus  a b)  sigma = sign_plus  (aval_sign a sigma) (aval_sign b sigma)"
  | "aval_sign (Minus a b)  sigma = sign_minus (aval_sign a sigma) (aval_sign b sigma)"
  | "aval_sign (Times a b)  sigma = sign_times (aval_sign a sigma) (aval_sign b sigma)"

lemma sign_plus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i + j \<in> gamma_sign (sign_plus a b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps)

lemma sign_minus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i - j \<in> gamma_sign (sign_minus a b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps)

lemma sign_times_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i * j \<in> gamma_sign (sign_times a b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps mult_neg_neg mult_neg_pos mult_pos_neg)

lemma aval_sign_hol_sound:
  "(\<forall>x. s x \<in> gamma_sign (sigma x))
   \<Longrightarrow> AExp.aval a s \<in> gamma_sign (aval_sign_hol a sigma)"
  by (induction a arbitrary: s sigma; simp add: sign_of_int_gamma sign_plus_sound)

lemma aval_sign_sound:
  "(\<forall>x. s x \<in> gamma_sign (sigma x))
   \<Longrightarrow> aval a s \<in> gamma_sign (aval_sign a sigma)"
  by (induction a arbitrary: s sigma;
      simp add: aval.simps aval_sign.simps aval_sign_hol_sound
                sign_plus_sound sign_minus_sound sign_times_sound)

(* ── Abstract Assume ─────────────────────────────────────────── *)

fun assume_sign :: "bexp => (vname => sign) => (vname => sign)" where
    "assume_sign (Less (V x) (N n)) sigma = (if n = 0 then sigma(x := SNeg) else sigma)"
  | "assume_sign _                  sigma = sigma"

fun assume_not_sign :: "bexp => (vname => sign) => (vname => sign)" where
  "assume_not_sign _ sigma = sigma"   (* conservative: no refinement *)

(* ── Typeclass Instances ──────────────────────────────────────
   Hoisted above the abstract_domain interpretation because the
   sound_domain locale's class constraint is bounded_semilattice_sup_bot. *)

instantiation sign :: order begin
instance proof
  fix x y :: sign
  assume "x \<le> y" "y \<le> x"
  then show "x = y"
    unfolding less_eq_sign_def by (blast intro: sign_le_antisym)
qed
end

instantiation sign :: order_bot begin
instance proof
  fix x :: sign
  show "bot \<le> x"
    unfolding less_eq_sign_def bot_sign_def by simp
qed
end

instantiation sign :: sup begin
definition sup_sign :: "sign => sign => sign" where
  "sup_sign = join_sign"
instance ..
end

instance sign :: semilattice_sup
proof
  fix x y z :: sign
  show "x \<le> x \<squnion> y"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_ub1)
  show "y \<le> x \<squnion> y"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_least)
qed

(* sign in order_bot + semilattice_sup -> bounded_semilattice_sup_bot for free *)
instance sign :: bounded_semilattice_sup_bot ..

(* ── Abstract Domain Interpretation ─────────────────────────── *)

interpretation sign_domain: abstract_domain gamma_sign widen_sign
proof unfold_locales
  show "gamma_sign bot = {}" unfolding bot_sign_def by simp
next
  fix a b :: sign
  assume "a \<le> b"
  then show "gamma_sign a \<subseteq> gamma_sign b"
    unfolding less_eq_sign_def by (rule gamma_sign_mono)
next
  fix a b :: sign
  show "gamma_sign a \<subseteq> gamma_sign (widen_sign a b)"
    unfolding widen_sign_def by (simp add: gamma_sign_mono join_sign_ub1 less_eq_sign_def)
next
  fix a b :: sign
  show "gamma_sign b \<subseteq> gamma_sign (widen_sign a b)"
    unfolding widen_sign_def by (simp add: gamma_sign_mono join_sign_ub2 less_eq_sign_def)
qed

lemma sign_gamma_state_conv:
  "(s : sign_domain.gamma_state sigma) = (s : sound_domain.gamma_state gamma_sign sigma)"
  unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by simp

lemma assume_sign_default:
  "\<not> (\<exists>x n. b = Less (V x) (N n)) \<Longrightarrow> assume_sign b sigma = sigma"
proof (cases b rule: bexp.exhaust)
  case (Less a1 a2)
  assume H: "\<not> (\<exists>x n. b = Less (V x) (N n))" and bL: "b = Less a1 a2"
  with H have "\<nexists>x n. a1 = V x \<and> a2 = N n" by auto
  then show ?thesis unfolding bL
    apply(cases a1;cases a2)
    apply(auto)
    apply (metis AExp.aval.elims assume_sign.simps(6,7))
    by (metis assume_sign.simps(11,12) aval_sign_hol.elims)
qed (simp_all add: assume_sign.simps)

lemma assume_sign_sound:
  assumes gs: "s \<in> sign_domain.gamma_state sigma" and b: "bval b s"
  shows "s \<in> sign_domain.gamma_state (assume_sign b sigma)"
proof (cases "\<exists>x n. b = Less (V x) (N n)")
  case False
  with assume_sign_default have "assume_sign b sigma = sigma"
    by blast
  with gs show ?thesis by simp
next
  case True
  then obtain x n where bn: "b = Less (V x) (N n)" by blast
  have xv: "s x < n"
    using b bn by simp
  show ?thesis
  proof (cases "n = 0")
    case True
    with bn have "assume_sign b sigma = sigma(x := SNeg)"
      by (simp add: assume_sign.simps)
    moreover have "s x \<in> gamma_sign SNeg"
      using xv True by simp
    moreover have "\<And>y. y \<noteq> x \<Longrightarrow> s y \<in> gamma_sign (sigma y)"
      using gs unfolding sign_domain.gamma_state_def by simp
    ultimately show ?thesis
      unfolding sign_domain.gamma_state_def by simp
  next
    case False
    with bn have "assume_sign b sigma = sigma"
      by (simp add: assume_sign.simps False)
    with gs show ?thesis by simp
  qed
qed

lemma assume_not_sign_sound:
  "s \<in> sign_domain.gamma_state sigma \<Longrightarrow> \<not> bval b s
   \<Longrightarrow> s \<in> sign_domain.gamma_state (assume_not_sign b sigma)"
  unfolding assume_not_sign.simps by simp

(* ── Abstract Assignment ─────────────────────────────────────── *)

definition assign_sign ::
    "vname => aexp => (vname => sign) => (vname => sign)"
where
  "assign_sign x a sigma = sigma(x := aval_sign a sigma)"

lemma assign_sign_sound:
  assumes gs: "s \<in> sign_domain.gamma_state sigma"
  shows "s(x := aval a s) \<in> sign_domain.gamma_state (assign_sign x a sigma)"
  unfolding assign_sign_def sign_domain.gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_sign (sigma z)"
    unfolding sign_domain.gamma_state_def by simp
  show "(s(x := aval a s)) y \<in> gamma_sign ((sigma(x := aval_sign a sigma)) y)"
  proof (cases "y = x")
    case True
    with V show ?thesis by (simp add: aval_sign_sound)
  next
    case False
    with V show ?thesis by simp
  qed
qed

(* ── Abstract Domain Instantiation ───────────────────────────── *)

(* ── Bundled Transfer Functions ──────────────────────────────── *)

definition sign_tf :: "sign domain_transfer" where
  "sign_tf = (| tf_assign     = assign_sign,
                tf_assume     = assume_sign,
                tf_assume_not = assume_not_sign |)"

end
