theory Sign_Domain
  imports Abstract_Domain Constraint_System "Voblint_IMP2.IMP2_Expr" "Voblint_IMP2.IMP2_Globals"
begin

section \<open>Sign domain: instantiation of abstract_domain\<close>

text \<open>
  sign abstracts integers by their sign:
    Bot    -- empty (unreachable / undefined)
    Neg    -- strictly negative   {n | n < 0}
    NonPos -- non-positive        {n | n \<le> 0}
    Zero   -- exactly zero        {0}
    NonNeg -- non-negative        {n | n \<ge> 0}
    Pos    -- strictly positive   {n | n > 0}
    Top    -- all integers        UNIV

  Seven-element lattice (Bot \<sqsubseteq> Neg,Zero,Pos \<sqsubseteq> NonPos,NonNeg \<sqsubseteq> Top).
  Finite; no widening needed.
\<close>

subsection \<open>Sign datatype\<close>

datatype sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop

subsection \<open>Concretization\<close>

fun gamma_sign :: "sign => int set" where
    "gamma_sign SBot    = {}"
  | "gamma_sign SNeg    = {n. n < 0}"
  | "gamma_sign SNonPos = {n. n \<le> 0}"
  | "gamma_sign SZero   = {0}"
  | "gamma_sign SNonNeg = {n. n \<ge> 0}"
  | "gamma_sign SPos    = {n. n > 0}"
  | "gamma_sign STop    = UNIV"

subsection \<open>Partial order\<close>

fun sign_le :: "sign => sign => bool" where
    "sign_le SBot    _       = True"
  | "sign_le _       STop    = True"
  | "sign_le SNeg    SNeg    = True"
  | "sign_le SNeg    SNonPos = True"
  | "sign_le SNonPos SNonPos = True"
  | "sign_le SZero   SZero   = True"
  | "sign_le SZero   SNonPos = True"
  | "sign_le SZero   SNonNeg = True"
  | "sign_le SNonNeg SNonNeg = True"
  | "sign_le SPos    SPos    = True"
  | "sign_le SPos    SNonNeg = True"
  | "sign_le _       _       = False"

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

subsection \<open>Join (least upper bound)\<close>

fun join_sign :: "sign => sign => sign" where
    "join_sign SBot    b       = b"
  | "join_sign a       SBot    = a"
  | "join_sign STop    _       = STop"
  | "join_sign _       STop    = STop"
  | "join_sign SNeg    SNeg    = SNeg"
  | "join_sign SNeg    SZero   = SNonPos"
  | "join_sign SNeg    SNonPos = SNonPos"
  | "join_sign SZero   SNeg    = SNonPos"
  | "join_sign SZero   SZero   = SZero"
  | "join_sign SZero   SPos    = SNonNeg"
  | "join_sign SZero   SNonPos = SNonPos"
  | "join_sign SZero   SNonNeg = SNonNeg"
  | "join_sign SNonPos SNeg    = SNonPos"
  | "join_sign SNonPos SZero   = SNonPos"
  | "join_sign SNonPos SNonPos = SNonPos"
  | "join_sign SNonNeg SZero   = SNonNeg"
  | "join_sign SNonNeg SPos    = SNonNeg"
  | "join_sign SNonNeg SNonNeg = SNonNeg"
  | "join_sign SPos    SZero   = SNonNeg"
  | "join_sign SPos    SNonNeg = SNonNeg"
  | "join_sign SPos    SPos    = SPos"
  | "join_sign _       _       = STop"

lemma join_sign_ub1: "sign_le a (join_sign a b)"
  by (cases a; cases b; simp add: join_sign.simps)

lemma join_sign_ub2: "sign_le b (join_sign a b)"
  by (cases a; cases b; simp add: join_sign.simps)

lemma join_sign_least: "sign_le a c ==> sign_le b c ==> sign_le (join_sign a b) c"
  by (cases a; cases b; cases c; simp add: join_sign.simps)
lemma join_sign_comm:  "join_sign a b = join_sign b a"                 by (cases a; cases b) simp_all
lemma join_sign_assoc: "join_sign a (join_sign b c) = join_sign (join_sign a b) c"  by (cases a; cases b; cases c) simp_all

subsection \<open>Widening (identity for finite domain: widen = join)\<close>

definition widen_sign :: "sign => sign => sign" where
  "widen_sign a b = join_sign a b"

subsection \<open>Abstract arithmetic operations\<close>

instantiation sign :: plus begin
fun plus_sign :: "sign => sign => sign" where
    "plus_sign SBot    _       = SBot"
  | "plus_sign _       SBot    = SBot"
  | "plus_sign SNeg    SNeg    = SNeg"
  | "plus_sign SNeg    SNonPos = SNeg"
  | "plus_sign SNonPos SNeg    = SNeg"
  | "plus_sign SNonPos SNonPos = SNonPos"
  | "plus_sign SPos    SPos    = SPos"
  | "plus_sign SPos    SNonNeg = SPos"
  | "plus_sign SNonNeg SPos    = SPos"
  | "plus_sign SNonNeg SNonNeg = SNonNeg"
  | "plus_sign SZero   b       = b"
  | "plus_sign a       SZero   = a"
  | "plus_sign _       _       = STop"
instance ..
end

instantiation sign :: minus begin
fun minus_sign :: "sign => sign => sign" where
    "minus_sign SBot    _       = SBot"
  | "minus_sign _       SBot    = SBot"
  | "minus_sign SNeg    SPos    = SNeg"
  | "minus_sign SNeg    SNonNeg = SNeg"
  | "minus_sign SPos    SNeg    = SPos"
  | "minus_sign SPos    SNonPos = SPos"
  | "minus_sign SNeg    SZero   = SNeg"
  | "minus_sign SPos    SZero   = SPos"
  | "minus_sign SZero   SZero   = SZero"
  | "minus_sign SZero   SNeg    = SPos"
  | "minus_sign SZero   SPos    = SNeg"
  | "minus_sign SZero   SNonNeg = SNonPos"
  | "minus_sign SZero   SNonPos = SNonNeg"
  | "minus_sign SNonNeg SZero   = SNonNeg"
  | "minus_sign SNonNeg SNeg    = SPos"
  | "minus_sign SNonNeg SNonPos = SNonNeg"
  | "minus_sign SNonPos SZero   = SNonPos"
  | "minus_sign SNonPos SPos    = SNeg"
  | "minus_sign SNonPos SNonNeg = SNonPos"
  | "minus_sign _       _       = STop"
instance ..
end

instantiation sign :: times begin
fun times_sign :: "sign => sign => sign" where
    "times_sign SBot    _       = SBot"
  | "times_sign _       SBot    = SBot"
  | "times_sign SZero   _       = SZero"
  | "times_sign _       SZero   = SZero"
  | "times_sign SNeg    SNeg    = SPos"
  | "times_sign SPos    SPos    = SPos"
  | "times_sign SNeg    SPos    = SNeg"
  | "times_sign SPos    SNeg    = SNeg"
  | "times_sign SNeg    SNonPos = SNonNeg"
  | "times_sign SNonPos SNeg    = SNonNeg"
  | "times_sign SNeg    SNonNeg = SNonPos"
  | "times_sign SNonNeg SNeg    = SNonPos"
  | "times_sign SPos    SNonNeg = SNonNeg"
  | "times_sign SNonNeg SPos    = SNonNeg"
  | "times_sign SPos    SNonPos = SNonPos"
  | "times_sign SNonPos SPos    = SNonPos"
  | "times_sign SNonNeg SNonNeg = SNonNeg"
  | "times_sign SNonNeg SNonPos = SNonPos"
  | "times_sign SNonPos SNonNeg = SNonPos"
  | "times_sign SNonPos SNonPos = SNonNeg"
  | "times_sign _       _       = STop"
instance ..
end

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

lemma sign_of_int_gamma: "n : gamma_sign (sign_of_int n)"
  by (auto simp: sign_of_int.simps gamma_sign.simps split: if_splits)

fun aval_sign_hol :: "AExp.aexp => (vname => sign) => sign" where
    "aval_sign_hol (AExp.N n)      \<sigma> = sign_of_int n"
  | "aval_sign_hol (AExp.V x)      \<sigma> = \<sigma> x"
  | "aval_sign_hol (AExp.Plus a b) \<sigma> = aval_sign_hol a \<sigma> + aval_sign_hol b \<sigma>"

fun aval_sign :: "aexp => (vname => sign) => sign" where
    "aval_sign (BaseN a)    \<sigma> = aval_sign_hol a \<sigma>"
  | "aval_sign (Plus  a b)  \<sigma> = aval_sign a \<sigma> + aval_sign b \<sigma>"
  | "aval_sign (Minus a b)  \<sigma> = aval_sign a \<sigma> - aval_sign b \<sigma>"
  | "aval_sign (Times a b)  \<sigma> = aval_sign a \<sigma> * aval_sign b \<sigma>"

lemma sign_plus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i + j \<in> gamma_sign (a + b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps)

lemma sign_minus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i - j \<in> gamma_sign (a - b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps)

lemma sign_times_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i * j \<in> gamma_sign (a * b)"
  using assms by (cases a; cases b; auto simp: gamma_sign.simps mult_neg_neg mult_neg_pos mult_pos_neg
                                                zero_le_mult_iff mult_le_0_iff)

lemma aval_sign_hol_sound:
  "(\<forall>x. s x \<in> gamma_sign (\<sigma> x))
   \<Longrightarrow> AExp.aval a s \<in> gamma_sign (aval_sign_hol a \<sigma>)"
  by (induction a arbitrary: s \<sigma>; simp add: sign_of_int_gamma sign_plus_sound)

lemma aval_sign_sound:
  "(\<forall>x. s x \<in> gamma_sign (\<sigma> x))
   \<Longrightarrow> aval a s \<in> gamma_sign (aval_sign a \<sigma>)"
  by (induction a arbitrary: s \<sigma>;
      simp add: aval.simps aval_sign.simps aval_sign_hol_sound
                sign_plus_sound sign_minus_sound sign_times_sound)

subsection \<open>Abstract assume\<close>

fun assume_sign :: "bexp => (vname => sign) => (vname => sign)" where
    "assume_sign (Less (V x) (N n)) \<sigma> = (if n = 0 then \<sigma>(x := SNeg) else \<sigma>)"
  | "assume_sign _                  \<sigma> = \<sigma>"

fun assume_not_sign :: "bexp => (vname => sign) => (vname => sign)" where
  "assume_not_sign _ \<sigma> = \<sigma>"   (* conservative: no refinement *)

subsection \<open>Typeclass instances\<close>

text \<open>
  Hoisted above the abstract_domain interpretation because the
  sound_domain locale's class constraint is bounded_semilattice_sup_bot.
\<close>

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

subsection \<open>Abstract domain interpretation\<close>

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

notation sign_domain.gamma_state ("\<lbrakk>_\<rbrakk>")

lemma sign_gamma_state_conv:
  "(s : sign_domain.gamma_state \<sigma>) = (s : sound_domain.gamma_state gamma_sign \<sigma>)"
  unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by simp

lemma assume_sign_default:
  "\<not> (\<exists>x n. b = Less (V x) (N n)) \<Longrightarrow> assume_sign b \<sigma> = \<sigma>"
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
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and b: "bval b s"
  shows "s \<in> \<lbrakk>assume_sign b \<sigma>\<rbrakk>"
proof (cases "\<exists>x n. b = Less (V x) (N n)")
  case False
  with assume_sign_default have "assume_sign b \<sigma> = \<sigma>"
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
    with bn have "assume_sign b \<sigma> = \<sigma>(x := SNeg)"
      by (simp add: assume_sign.simps)
    moreover have "s x \<in> gamma_sign SNeg"
      using xv True by simp
    moreover have "\<And>y. y \<noteq> x \<Longrightarrow> s y \<in> gamma_sign (\<sigma> y)"
      using gs unfolding sign_domain.gamma_state_def by simp
    ultimately show ?thesis
      unfolding sign_domain.gamma_state_def by simp
  next
    case False
    with bn have "assume_sign b \<sigma> = \<sigma>"
      by (simp add: assume_sign.simps False)
    with gs show ?thesis by simp
  qed
qed

lemma assume_not_sign_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_not_sign b \<sigma>\<rbrakk>"
  unfolding assume_not_sign.simps by simp
lemma assume_not_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_sign b sigma1 \<le> assume_not_sign b sigma2"
  by (simp add: assume_not_sign.simps)


subsection \<open>Abstract assignment\<close>

definition assign_sign ::
    "vname => aexp => (vname => sign) => (vname => sign)"
where
  "assign_sign x a \<sigma> = \<sigma>(x := aval_sign a \<sigma>)"

lemma assign_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := aval a s) \<in> \<lbrakk>assign_sign x a \<sigma>\<rbrakk>"
  unfolding assign_sign_def sign_domain.gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    unfolding sign_domain.gamma_state_def by simp
  show "(s(x := aval a s)) y \<in> gamma_sign ((\<sigma>(x := aval_sign a \<sigma>)) y)"
  proof (cases "y = x")
    case True
    with V show ?thesis by (simp add: aval_sign_sound)
  next
    case False
    with V show ?thesis by simp
  qed
qed

subsection \<open>Bundled transfer functions\<close>

(* Procedure entry: keep globals, reset locals to Top (unknown). *)
definition enter_sign :: "sign abs_state => sign abs_state" where
  "enter_sign \<sigma> = (\<lambda>x. if is_global x then \<sigma> x else STop)"

lemma enter_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_sign \<sigma>\<rbrakk>"
proof -
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    unfolding sign_domain.gamma_state_def by simp
  show ?thesis
    unfolding sign_domain.gamma_state_def enter_sign_def
    by (intro CollectI allI; cases "is_global x";
        auto simp: enter_state_def V gamma_sign.simps)
qed

lemma enter_sign_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign s1 \<le> enter_sign s2"
proof (rule le_funI)
  fix x
  show "enter_sign s1 x \<le> enter_sign s2 x"
  proof (cases "is_global x")
    assume g: "is_global x"
    from assms have "s1 x \<le> s2 x" by (simp add: le_funD)
    thus ?thesis using g unfolding enter_sign_def less_eq_sign_def by simp
  next
    assume "\<not> is_global x"
    thus ?thesis unfolding enter_sign_def less_eq_sign_def
      by (simp add: sign_le_refl)
  qed
qed

definition combine_sign :: "sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state" where
  "combine_sign = combine_abs"

lemma combine_sign_sound:
  assumes gs: "s \<in> \<lbrakk>sigma_c\<rbrakk>"
      and ge: "t \<in> \<lbrakk>sigma_e\<rbrakk>"
  shows "combine_states s t \<in> \<lbrakk>combine_sign sigma_c sigma_e\<rbrakk>"
proof -
  from gs have Vc: "\<forall>z. s z \<in> gamma_sign (sigma_c z)"
    unfolding sign_domain.gamma_state_def by simp
  from ge have Ve: "\<forall>z. t z \<in> gamma_sign (sigma_e z)"
    unfolding sign_domain.gamma_state_def by simp
  show ?thesis
    unfolding sign_domain.gamma_state_def combine_sign_def combine_abs_def combine_states_def
    by (intro CollectI allI; cases "is_global x"; auto simp: Vc Ve gamma_sign.simps)
qed

definition sign_tf :: "sign domain_transfer" where
  "sign_tf = (| tf_assign     = assign_sign,
                tf_assume     = assume_sign,
                tf_assume_not = assume_not_sign,
                tf_enter      = enter_sign |)"

text \<open>
  The four transfer-function soundness facts for the sign domain, bundled once
  so example theories cite them instead of re-proving the same blocks.  These
  are the tf_sound_* premises of unified_post_fixpoint_sound / the
  per-solver soundness theorems.
\<close>
lemma sign_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign sign_tf x a \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assign_sign_sound)

lemma sign_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume sign_tf b \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assume_sign_sound)

lemma sign_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not sign_tf b \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assume_not_sign_sound)

lemma sign_tf_sound_enter:
  "\<forall>\<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. enter_state st \<in> \<lbrakk>tf_enter sign_tf \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: enter_sign_sound)

interpretation sign_sound_tf: sound_transfer gamma_sign sign_tf
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s(x := aval a s) \<in> \<lbrakk>tf_assign sign_tf x a \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assign)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume sign_tf b \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assume)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume_not sign_tf b \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assume_not)
  show "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. enter_state s \<in> \<lbrakk>tf_enter sign_tf \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_enter)
qed

lemma sign_plus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 + b \<le> a2 + (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_plus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a + b1 \<le> a + (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_minus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 - b \<le> a2 - (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_minus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a - b1 \<le> a - (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_times_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 * b \<le> a2 * (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_times_mono2:
  "b1 \<le> b2 \<Longrightarrow> a * b1 \<le> a * (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

subsection \<open>Printable instance\<close>

fun string_of_sign :: "sign \<Rightarrow> string" where
    "string_of_sign SBot    = ''Bot''"
  | "string_of_sign SNeg    = ''Neg''"
  | "string_of_sign SNonPos = ''<=0''"
  | "string_of_sign SZero   = ''0''"
  | "string_of_sign SNonNeg = ''>=0''"
  | "string_of_sign SPos    = ''Pos''"
  | "string_of_sign STop    = ''T''"

instantiation sign :: show_val begin
definition "show_val_sign (s :: sign) = string_of_sign s"
instance ..
end

lemma show_val_sign_eq [simp]: "(show_val :: sign \<Rightarrow> string) = string_of_sign"
  unfolding show_val_sign_def by simp

lemma sign_plus_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 + b1 \<le> a2 + (b2::sign)"
  by (meson order.trans sign_plus_mono1 sign_plus_mono2)

lemma aval_sign_hol_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_sign_hol a sigma1 \<le> aval_sign_hol a sigma2"
  apply (induction a arbitrary: sigma1 sigma2)
  by(auto simp add: sign_plus_combine_mono le_funD)
 

lemma aval_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_sign a sigma1 \<le> aval_sign a sigma2"
  apply (induction a arbitrary: sigma1 sigma2)
  apply(auto simp add: sign_plus_combine_mono aval_sign_hol_mono)
  apply (meson order.trans sign_minus_mono1 sign_minus_mono2)
  by (meson dual_order.trans sign_times_mono1 sign_times_mono2)

lemma assign_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_sign x a sigma1 \<le> assign_sign x a sigma2"
  by (simp add: assign_sign_def aval_sign_mono le_funD le_funI)
 
lemma assume_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_sign b sigma1 \<le> assume_sign b sigma2"
proof (induction b arbitrary: sigma1 sigma2)
  case (Less a1 a2)
  then show ?case
    unfolding le_fun_def
    apply(auto)
    by (smt (verit, best) assume_sign.simps(1) assume_sign_default fun_upd_other fun_upd_same
        order_class.order_eq_iff)
qed auto


lemma sign_tf_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf sign_tf a s1 \<le> apply_tf sign_tf a s2"
  apply (cases a)
  by (auto simp: sign_tf_def assign_sign_mono assume_sign_mono assume_not_sign_mono
           enter_sign_mono)

subsection \<open>Executable examples\<close>

value "sign_of_int (-5)"
value "sign_of_int 0"
value "sign_of_int 3"

value "(SNeg::sign) + SPos"
value "(SPos::sign) - SPos"
value "(SNeg::sign) * SNeg"
value "(SZero::sign) * STop"

value "join_sign SNeg SPos"
value "join_sign SNeg SZero"
value "join_sign SPos SZero"

value "string_of_sign STop"
value "string_of_sign SNonPos"

value "aval_sign (Times (N (-2)) (N 3)) (\<lambda>_. SBot)"
value "aval_sign (Plus (V ''x'') (V ''x'')) ((\<lambda>_. SBot)(''x'' := SPos))"

value "assign_sign ''x'' (N 1) (\<lambda>_. SBot) ''x''"
value "(assume_sign (Less (V ''x'') (N 0)) (\<lambda>_. STop)) ''x''"
value "(assume_sign (Less (V ''x'') (N 5)) (\<lambda>_. STop)) ''x''"

end
