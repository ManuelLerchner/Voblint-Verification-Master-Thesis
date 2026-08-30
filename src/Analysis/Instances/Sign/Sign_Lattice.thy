theory Sign_Lattice
  imports "Voblint_Domain.Abstract_Domain" "TD.Update_rules"
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
  using st by (cases s; cases t; auto)

instantiation sign :: ord begin
definition less_eq_sign :: "sign => sign => bool" where "(a::sign) <= b = sign_le a b"
definition less_sign    :: "sign => sign => bool" where "(a::sign) <  b = (sign_le a b \<and> \<not> sign_le b a)"
instance ..
end

instance sign :: preorder
proof intro_classes
  fix x y z :: sign
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_sign_def less_eq_sign_def by simp
  show "x \<le> x"
    by (simp add: less_eq_sign_def sign_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_sign_def by (rule sign_le_trans)
qed

text \<open>The bottom instance lifts pointwise to abstract states and enables monotone least-upper-bound iteration.\<close>
instantiation sign :: bot begin
definition "bot_sign = SBot"
instance ..
end

text \<open>
  \<open>SBot\<close> is the only empty value a finite enumerated domain can have (every
  other constructor denotes a nonempty set of integers), so a direct
  equality test is already exact --- unlike Interval's analogous fact,
  which cannot use equality against one representative because Interval's
  bound-pair representation has many empty values besides its canonical
  \<open>bot\<close>. Exposed here, at the domain's own theory, rather than inlined
  where a caller happens to need it, so every consumer (not just one) gets
  the same domain-owned fact.
\<close>

definition is_bottom_sign :: "sign \<Rightarrow> bool" where
  "is_bottom_sign s = (s = SBot)"

lemma is_bottom_sign_correct: "is_bottom_sign s \<longleftrightarrow> gamma_sign s = {}"
  unfolding is_bottom_sign_def
  by (cases s) (auto simp: gamma_sign.simps intro: exI[of _ "-1"] exI[of _ "0"] exI[of _ "1"])



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
  by (cases a; cases b; simp)

lemma join_sign_ub2: "sign_le b (join_sign a b)"
  by (cases a; cases b; simp)

lemma join_sign_least: "sign_le a csg \<Longrightarrow> sign_le b csg \<Longrightarrow> sign_le (join_sign a b) csg"
  by (cases a; cases b; cases csg; simp)
lemma join_sign_comm:  "join_sign a b = join_sign b a"                 by (cases a; cases b) simp_all
lemma join_sign_assoc: "join_sign a (join_sign b csg) = join_sign (join_sign a b) csg"  by (cases a; cases b; cases csg) simp_all

subsection \<open>Abstract arithmetic operations\<close>

subsection \<open>Typeclass instances\<close>

text \<open>
  Hoisted above the abstract_domain interpretation because the
  sound_domain locale's class constraint is bounded_semilattice_sup_bot.
\<close>

instantiation sign :: order begin
instance proof intro_classes
  fix x y :: sign
  assume "x \<le> y" "y \<le> x"
  then show "x = y"
    unfolding less_eq_sign_def by (blast intro: sign_le_antisym)
qed
end

instantiation sign :: order_bot begin
instance proof intro_classes
  fix x :: sign
  show "bot \<le> x"
    unfolding less_eq_sign_def bot_sign_def by simp
qed
end

instantiation sign :: top begin
definition "top_sign = STop"
instance ..
end

instantiation sign :: order_top begin
instance proof intro_classes
  fix x :: sign
  show "x \<le> top"
    unfolding less_eq_sign_def top_sign_def by (cases x) simp_all
qed
end

text \<open>\<open>STop\<close> is likewise the unique top of a finite enumeration.\<close>

definition is_top_sign :: "sign \<Rightarrow> bool" where
  "is_top_sign s = (s = STop)"

lemma is_top_sign_correct: "is_top_sign s \<longleftrightarrow> s = top"
  unfolding is_top_sign_def top_sign_def ..

lemma gamma_sign_top: "gamma_sign top = UNIV"
  unfolding top_sign_def by simp

instantiation sign :: sup begin
definition sup_sign :: "sign => sign => sign" where
  "sup_sign = join_sign"
instance ..
end

instance sign :: semilattice_sup
proof intro_classes
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


subsection \<open>Type-class warrowing for TD warrowing solver\<close>

definition narrow_sign_td :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "narrow_sign_td a b = a"

instantiation sign :: warrowing begin
  definition "widen (a :: sign) b = join_sign a b"
  definition "narrow (a :: sign) b = narrow_sign_td a b"
instance proof intro_classes
  fix a b :: sign
  show "a \<le> widen a b"
    unfolding less_eq_sign_def widen_sign_def by (rule join_sign_ub1)
  show "b \<le> widen a b"
    unfolding less_eq_sign_def widen_sign_def by (rule join_sign_ub2)
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b"
    unfolding narrow_sign_def narrow_sign_td_def by simp
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a"
    unfolding narrow_sign_def narrow_sign_td_def by simp
qed
end

subsection \<open>Abstract domain instantiation\<close>

instantiation sign :: sound_domain begin
definition gamma_abs_sign [simp]: "gamma (a :: sign) = gamma_sign a"
definition is_bot_sign [simp]: "is_bot (a :: sign) = is_bottom_sign a"
definition is_top_sign' [simp]: "is_top (a :: sign) = is_top_sign a"
instance proof intro_classes
  show "gamma (bot :: sign) = {}"
    unfolding bot_sign_def by simp
next
  fix a b :: sign
  assume H: "a \<le> b"
  show "gamma a \<subseteq> gamma b"
  proof -
    have "gamma_sign a \<subseteq> gamma_sign b"
      using H unfolding less_eq_sign_def by (rule gamma_sign_mono)
    then show ?thesis by simp
  qed
next
  fix a :: sign
  show "is_bot a \<longleftrightarrow> gamma a = {}"
    by (simp add: is_bottom_sign_correct)
next
  fix a :: sign
  show "is_top a \<longleftrightarrow> a = top"
    by (simp add: is_top_sign_correct)
qed
end

instance sign :: abstract_domain ..

end
