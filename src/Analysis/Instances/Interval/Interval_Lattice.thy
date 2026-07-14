theory Interval_Lattice
  imports Abstract_Domain Interval_Bounds
begin

section \<open>Interval lattice\<close>

text \<open>
  An interval @{text "[l, u]"} abstracts the integers @{text "{n. l \<le> n \<and> n \<le> u}"}.
  Bounds are extended integers (@{text MinInf} / @{text "Fin n"} / @{text PlusInf}).
  Empty (e.g. @{text "[+inf, -inf]"}) is @{text bot}; @{text "[-inf, +inf]"} is @{text top}.
\<close>

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



text \<open>
  \<^bold>\<open>Canonical empty interval.\<close>  The raw \<^typ>\<open>ivl\<close> lattice has infinitely many empty
  representations (any \<^term>\<open>Ivl l u\<close> with \<open>l > u\<close>, or an infinite bound on the wrong
  side).  \<open>normalize_ivl\<close> collapses every empty interval to the single \<^const>\<open>bot\<close>
  representative \<^term>\<open>Ivl PlusInf MinInf\<close>, leaving non-empty intervals untouched.

  Arithmetic feeds its operands through \<open>normalize_ivl\<close> first.  Since the pointwise
  sum/difference of \<^const>\<open>bot\<close> with anything is again \<^const>\<open>bot\<close>, this keeps every empty
  result canonical.  Without it, \<open>[1,0] + [1,1] = [2,1]\<close> would manufacture ever-new empty
  representations, which as context keys defeat fixpoint convergence in the recursive
  interval example.\<close>

definition normalize_ivl :: "ivl \<Rightarrow> ivl" where
  "normalize_ivl v =
     (case v of Ivl l u \<Rightarrow>
        if l \<le> u \<and> l \<noteq> PlusInf \<and> u \<noteq> MinInf then v else bot)"

lemma normalize_ivl_gamma: "gamma_ivl (normalize_ivl v) = gamma_ivl v"
  by (cases v) (auto simp: normalize_ivl_def bot_ivl_def eint_le.simps
        split: eint.splits if_splits intro: eint_le_trans)


lemma normalize_ivl_mono: "x \<le> y \<Longrightarrow> normalize_ivl x \<le> normalize_ivl y"
  by (cases x; cases y)
     (auto simp: normalize_ivl_def less_eq_ivl_def bot_ivl_def eint_le.simps
        eint_le_PlusInf_iff eint_le_MinInf_iff
        split: eint.splits if_splits intro: eint_le_trans)

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

lemma ivl_le_top: "(x::ivl) \<le> ivl_top"
  by (cases x) (simp add: less_eq_ivl_def ivl_top_def)

end
