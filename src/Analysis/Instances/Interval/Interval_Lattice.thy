theory Interval_Lattice
  imports Voblint_Core.Abstract_Domain Interval_Bounds
begin

section \<open>Interval lattice\<close>

text \<open>
  An interval @{text "[l, u]"} abstracts the integers @{text "{n. l \<le> n \<and> n \<le> u}"}.
  Bounds are extended integers (@{text MinInf} / @{text "Fin n"} / @{text PlusInf}).
  Empty (e.g. @{text "[+inf, -inf]"}) is @{text bot}; @{text "[-inf, +inf]"} is @{text top}.
\<close>

subsection \<open>Interval type and order\<close>

datatype ivl = Ivl (ivl_lower: eint) (ivl_upper: eint)   \<comment> \<open>@{text "Ivl l u = [l, u]"}\<close>

(* Named exhaustion, cited instead of `(cases x) auto` at every destructuring site. *)
lemma ivl_exhaustE:
  obtains l u where "x = Ivl l u"
  by (cases x) auto

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
instance proof intro_classes
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
instance proof intro_classes
  fix x :: ivl
  show "bot \<le> x"
    unfolding less_eq_ivl_def bot_ivl_def by (cases x) simp
qed
end

definition ivl_top :: ivl where
  "ivl_top = Ivl MinInf PlusInf"

instantiation ivl :: top begin
definition "top_ivl = ivl_top"
instance ..
end

instantiation ivl :: order_top begin
instance proof intro_classes
  fix x :: ivl
  show "x \<le> top"
    unfolding top_ivl_def by (cases x) (simp add: less_eq_ivl_def ivl_top_def)
qed
end

subsection \<open>Concretization\<close>

fun gamma_ivl :: "ivl => int set" where
    "gamma_ivl (Ivl l u) = {n. l \<le> Fin n \<and> Fin n \<le> u}"

lemma gamma_ivl_bot: "gamma_ivl bot = {}"
  unfolding bot_ivl_def by auto

lemma gamma_ivl_top: "gamma_ivl ivl_top = UNIV"
  unfolding ivl_top_def by auto

text \<open>
  Unlike \<open>bot\<close>, \<open>top\<close> has no other representation: \<^term>\<open>gamma_ivl (Ivl l u)
  = UNIV\<close> forces \<open>l \<le> Fin n\<close> and \<open>Fin n \<le> u\<close> for every \<open>n\<close>, which pins
  \<open>l = MinInf\<close> and \<open>u = PlusInf\<close> exactly --- so a direct equality test
  against \<^const>\<open>ivl_top\<close> is already exact, no bound comparison needed.
\<close>

definition is_top_ivl :: "ivl \<Rightarrow> bool" where
  "is_top_ivl i = (i = ivl_top)"

lemma is_top_ivl_correct: "is_top_ivl i \<longleftrightarrow> i = top"
  unfolding is_top_ivl_def top_ivl_def ..

text \<open>
  \<open>bot\<close> is one fixed empty interval (\<^term>\<open>Ivl PlusInf MinInf\<close>), but the
  \<open>\<le>\<close> instance's bound comparison makes \<open>x \<le> bot\<close> true only for that exact
  representation: any other inverted bound pair (e.g. a guard refinement
  narrowing a variable against its own infeasible range,
  \<^term>\<open>Ivl (Fin 5) (Fin (-1))\<close>) is just as empty by @{const gamma_ivl},
  yet not \<open>\<le> bot\<close> --- the instance never normalizes. \<open>is_bottom_ivl\<close> tests
  emptiness directly against the bounds instead of against one particular
  representative.

  Bound comparison alone is not quite enough, though: \<^term>\<open>Ivl MinInf
  MinInf\<close> has \<open>l \<le> u\<close> (reflexively), yet no integer is "at" \<open>MinInf\<close>
  itself, so its @{const gamma_ivl} is still empty (symmetrically for
  \<^term>\<open>Ivl PlusInf PlusInf\<close>). \<open>l = PlusInf\<close> and \<open>u = MinInf\<close> are exactly
  the two cases where \<^const>\<open>eint_le\<close> can hold reflexively without any
  integer ever satisfying it, so both are called out explicitly alongside
  the general inverted-bounds case.
\<close>

definition is_bottom_ivl :: "ivl \<Rightarrow> bool" where
  "is_bottom_ivl i =
     (case i of Ivl l u \<Rightarrow> l = PlusInf \<or> u = MinInf \<or> \<not> l \<le> u)"

lemma is_bottom_ivl_correct: "is_bottom_ivl i \<longleftrightarrow> gamma_ivl i = {}"
proof (cases i)
  case (Ivl l u)
  show ?thesis
    unfolding Ivl is_bottom_ivl_def
    by (cases l; cases u) (auto simp: less_eq_eint_def eint_le.simps)
qed

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
proof intro_classes
  fix x y z :: ivl
  show "x \<le> x \<squnion> y" unfolding sup_ivl_def by (rule join_ivl_le_ub1)
  show "y \<le> x \<squnion> y" unfolding sup_ivl_def by (rule join_ivl_le_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    unfolding sup_ivl_def by (rule join_ivl_le_least)
qed

instance ivl :: bounded_semilattice_sup_bot ..

subsection \<open>Meet (greatest lower bound)\<close>

text \<open>
  Interval intersection.  Used by @{text bfilter_ivl} to refine a variable's
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
proof intro_classes
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
definition is_bot_ivl [simp]: "is_bot (a :: ivl) = is_bottom_ivl a"
definition is_top_ivl' [simp]: "is_top (a :: ivl) = is_top_ivl a"
instance proof intro_classes
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
next
  fix a :: ivl
  show "is_bot a \<longleftrightarrow> gamma a = {}"
    by (simp add: is_bottom_ivl_correct)
next
  fix a :: ivl
  show "is_top a \<longleftrightarrow> a = top"
    by (simp add: is_top_ivl_correct)
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

subsection \<open>Canonical representatives\<close>

text \<open>
  \<^const>\<open>normalize_ivl\<close> picks one representative per abstract value: non-empty
  intervals are already determined by their bounds, and every empty one collapses
  to \<^const>\<open>bot\<close>.  This mirrors the component-local normalisation each Goblint
  integer domain performs for itself (@{text Interval.norm} sending \<open>l > u\<close> to
  \<open>None\<close>, @{text Congruence.normalize} pinning the residue and modulus), which is
  what makes a structural stability test on a representation meaningful.

  \<^const>\<open>is_bottom_ivl\<close> stays an exact test on arbitrary bounds rather than an
  equality against \<^const>\<open>bot\<close>: \<^typ>\<open>ivl\<close> is an ordinary datatype, so
  \<^term>\<open>Ivl (Fin 5) (Fin 3)\<close> remains writable by any caller and must still be
  recognised as empty.
\<close>

lemma is_bottom_ivl_iff_not_nonempty:
  "is_bottom_ivl v \<longleftrightarrow> \<not> ivl_nonempty v"
  by (cases v) (auto simp: is_bottom_ivl_def)

lemma is_bottom_ivl_bot [simp]: "is_bottom_ivl bot"
  by (simp add: is_bottom_ivl_def bot_ivl_def)

lemma normalize_ivl_bot_case [simp]:
  "is_bottom_ivl v \<Longrightarrow> normalize_ivl v = bot"
  by (cases v) (auto simp: normalize_ivl_def is_bottom_ivl_def)

lemma normalize_ivl_id [simp]:
  "\<not> is_bottom_ivl v \<Longrightarrow> normalize_ivl v = v"
  by (cases v) (simp add: normalize_ivl_def is_bottom_ivl_def)

lemma normalize_ivl_bot [simp]: "normalize_ivl bot = bot"
  by simp

lemma normalize_ivl_idem [simp]:
  "normalize_ivl (normalize_ivl v) = normalize_ivl v"
  by (cases "is_bottom_ivl v") simp_all

lemma normalize_ivl_le: "normalize_ivl v \<le> v"
  by (cases "is_bottom_ivl v") simp_all

lemma is_bottom_ivl_normalize [simp]:
  "is_bottom_ivl (normalize_ivl v) = is_bottom_ivl v"
  by (cases "is_bottom_ivl v") simp_all

definition mk_ivl :: "eint \<Rightarrow> eint \<Rightarrow> ivl" where
  [simp]: "mk_ivl l u = normalize_ivl (Ivl l u)"

text \<open>
  \<^const>\<open>mk_ivl\<close> is the canonical constructor: any operation that computes new
  bounds should build its result through it instead of applying \<^const>\<open>Ivl\<close> to
  possibly inverted bounds and leaving the emptiness implicit.  Its defining
  equation is a simp rule, like \<^const>\<open>inf\<close>'s above, so a caller that already
  rewrites with \<^const>\<open>normalize_ivl\<close>'s equations sees through it rather than
  meeting an opaque constant.
\<close>

lemma gamma_mk_ivl [simp]: "gamma_ivl (mk_ivl l u) = gamma_ivl (Ivl l u)"
  by (simp add: normalize_ivl_gamma)

lemma normalize_ivl_mk_ivl [simp]: "normalize_ivl (mk_ivl l u) = mk_ivl l u"
  by simp

lemma mk_ivl_mono:
  "Ivl l1 u1 \<le> Ivl l2 u2 \<Longrightarrow> mk_ivl l1 u1 \<le> mk_ivl l2 u2"
  by (simp add: normalize_ivl_mono)

lemma mk_ivl_le: "mk_ivl l u \<le> Ivl l u"
  by (simp add: normalize_ivl_le)

text \<open>
  \<^const>\<open>inf\<close> is the one operation that is deliberately left un-normalised: it
  intersects the bounds and lets an infeasible intersection come out as an
  inverted pair.
\<close>

lemma meet_ivl_not_canonical:
  "normalize_ivl (Ivl (Fin 0) (Fin 3) \<sqinter> Ivl (Fin 5) (Fin 9))
     \<noteq> Ivl (Fin 0) (Fin 3) \<sqinter> Ivl (Fin 5) (Fin 9)"
  by (simp add: normalize_ivl_def bot_ivl_def)

text \<open>
  Normalising it instead would break \<^class>\<open>semilattice_inf\<close>: the greatest-lower-bound
  law @{thm [source] meet_ivl_greatest} quantifies over *all* lower bounds, including
  the un-normalised empty ones a caller may write down, and those are not below
  \<^const>\<open>bot\<close>.  The three facts below are exactly that counterexample --
  \<^term>\<open>Ivl (Fin 5) (Fin 3)\<close> is a lower bound of both operands, yet it is not below
  the normalised meet.  Canonicity therefore belongs to the operations that build
  new values (arithmetic, \<^const>\<open>mk_ivl\<close>), not to the order-theoretic \<^const>\<open>inf\<close>.
\<close>

lemma meet_ivl_normalized_breaks_greatest:
  "Ivl (Fin 5) (Fin 3) \<le> Ivl (Fin 0) (Fin 3)"
  "Ivl (Fin 5) (Fin 3) \<le> Ivl (Fin 5) (Fin 9)"
  "\<not> Ivl (Fin 5) (Fin 3)
       \<le> normalize_ivl (Ivl (Fin 0) (Fin 3) \<sqinter> Ivl (Fin 5) (Fin 9))"
  by (simp_all add: less_eq_ivl_def normalize_ivl_def bot_ivl_def)

subsection \<open>Semantic intersection\<close>

fun meet_ivl_norm :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "meet_ivl_norm (Ivl l1 u1) (Ivl l2 u2) =
     mk_ivl (if l2 \<le> l1 then l1 else l2) (if u1 \<le> u2 then u1 else u2)"

text \<open>
  \<^const>\<open>inf\<close> is the greatest lower bound of the representation order; the
  operation a backward filter actually wants is the intersection of the
  concretizations, which is a weaker requirement --- it need only preserve
  \<^const>\<open>gamma_ivl\<close> and be reductive and monotone, and is free to pick any
  representative of the result.  \<^const>\<open>meet_ivl_norm\<close> is that operation: the
  same bound intersection, built through \<^const>\<open>mk_ivl\<close> so an infeasible
  intersection comes out as \<^const>\<open>bot\<close> rather than as a reversed pair.

  Goblint's interval @{text meet} is simultaneously both, because its carrier
  keeps only canonical inhabited values --- @{text norm} maps \<open>l > u\<close> to
  @{text None}, so no element corresponding to \<^term>\<open>Ivl (Fin 5) (Fin 3)\<close>
  exists there to be a common lower bound.  On this larger raw carrier the two
  notions come apart, which is what
  @{thm [source] meet_ivl_normalized_breaks_greatest} records.
\<close>

lemma meet_ivl_norm_eq: "meet_ivl_norm a b = normalize_ivl (meet_ivl a b)"
  by (cases a; cases b) simp

lemma gamma_meet_ivl_norm [simp]:
  "gamma_ivl (meet_ivl_norm a b) = gamma_ivl (meet_ivl a b)"
  by (simp add: meet_ivl_norm_eq normalize_ivl_gamma)

lemma meet_ivl_norm_gamma:
  "n \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> n \<in> gamma_ivl (meet_ivl_norm a b)"
  using meet_ivl_gamma[of n a b] by simp

lemma meet_ivl_norm_le1: "meet_ivl_norm a b \<le> a"
proof -
  have "normalize_ivl (meet_ivl a b) \<le> meet_ivl a b" by (rule normalize_ivl_le)
  also have "meet_ivl a b \<le> a" using meet_ivl_le_lb1[of a b] by simp
  finally show ?thesis by (simp add: meet_ivl_norm_eq)
qed

lemma meet_ivl_norm_le2: "meet_ivl_norm a b \<le> b"
proof -
  have "normalize_ivl (meet_ivl a b) \<le> meet_ivl a b" by (rule normalize_ivl_le)
  also have "meet_ivl a b \<le> b" using meet_ivl_le_lb2[of a b] by simp
  finally show ?thesis by (simp add: meet_ivl_norm_eq)
qed

lemma meet_ivl_norm_mono:
  assumes "a1 \<le> a2" and "b1 \<le> b2"
  shows "meet_ivl_norm a1 b1 \<le> meet_ivl_norm a2 b2"
proof -
  have "meet_ivl a1 b1 \<le> meet_ivl a2 b2" using inf_mono[OF assms] by simp
  then show ?thesis by (simp add: meet_ivl_norm_eq normalize_ivl_mono)
qed

lemma normalize_ivl_meet_ivl_norm [simp]:
  "normalize_ivl (meet_ivl_norm a b) = meet_ivl_norm a b"
  by (simp add: meet_ivl_norm_eq)

lemma is_bottom_ivl_meet_ivl_norm:
  "is_bottom_ivl (meet_ivl_norm a b) \<longleftrightarrow> is_bottom_ivl (meet_ivl a b)"
  by (simp add: meet_ivl_norm_eq)

lemma ivl_le_top: "(x::ivl) \<le> ivl_top"
  by (cases x) (simp add: less_eq_ivl_def ivl_top_def)

end
