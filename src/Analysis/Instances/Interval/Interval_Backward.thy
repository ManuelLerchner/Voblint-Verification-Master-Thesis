theory Interval_Backward
  imports Interval_Arithmetic Exec_Backward "Voblint_VIMP.VIMP_Expr"
    Abstract_Arithmetic Interval_Numeric_Queries
begin

section \<open>Interval backward filtering\<close>

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>interval_lt\<close>/\<open>interval_eqb\<close>/\<open>interval_tobool\<close> restate
  \<open>Interval_Numeric_Queries\<close>'s \<open>interval_less_true\<close>/\<open>interval_less_false\<close>/
  \<open>interval_eq_true\<close>/\<open>interval_eq_false\<close> as the three-valued \<open>bool option\<close>
  queries \<open>Voblint_Analysis.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale expects: \<open>Some True\<close>/\<open>Some False\<close> when the bound-based table decides
  it, \<open>None\<close> otherwise. \<open>interval_tobool\<close> is truthiness against the point
  interval \<open>[0,0]\<close>.
\<close>

definition interval_lt :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_lt a b =
     (if interval_less_true a b then Some True
      else if interval_less_false a b then Some False
      else None)"

definition interval_eqb :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_eqb a b =
     (if interval_eq_true a b then Some True
      else if interval_eq_false a b then Some False
      else None)"

definition interval_tobool :: "ivl \<Rightarrow> bool option" where
  "interval_tobool a =
     (if interval_eq_false a (Ivl (Fin 0) (Fin 0)) then Some True
      else if interval_eq_true a (Ivl (Fin 0) (Fin 0)) then Some False
      else None)"

lemma interval_lt_sound:
  assumes "interval_lt p q = Some b" and "i \<in> gamma_ivl p" and "j \<in> gamma_ivl q"
  shows "(i < j) = b"
  using assms unfolding interval_lt_def
  by (auto split: if_splits dest: interval_less_true_sound interval_less_false_sound)

lemma interval_eqb_sound:
  assumes "interval_eqb p q = Some b" and "i \<in> gamma_ivl p" and "j \<in> gamma_ivl q"
  shows "(i = j) = b"
  using assms unfolding interval_eqb_def
  by (auto split: if_splits dest: interval_eq_true_sound interval_eq_false_sound)

lemma interval_tobool_sound:
  assumes "interval_tobool p = Some b" and "i \<in> gamma_ivl p"
  shows "truthy i = b"
proof -
  have z: "(0::int) \<in> gamma_ivl (Ivl (Fin 0) (Fin 0))" by simp
  show ?thesis
    using assms z
    unfolding interval_tobool_def truthy_def
    by (auto split: if_splits dest: interval_eq_false_sound interval_eq_true_sound)
qed

lemma interval_lt_mono:
  assumes hp: "\<not> is_empty (p1::ivl)" and hq: "\<not> is_empty q1"
      and hpm: "p1 \<le> p2" and hqm: "q1 \<le> q2"
      and hwide: "interval_lt p2 q2 = Some b"
  shows "interval_lt p1 q1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  obtain l2 u2 where q1_def: "q1 = Ivl l2 u2" by (cases q1)
  obtain l2' u2' where q2_def: "q2 = Ivl l2' u2'" by (cases q2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_empty_ivl is_bottom_ivl_def by auto
  have ne_q1: "l2 \<le> u2" using hq unfolding q1_def is_empty_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'" "l2' \<le> l2" "u2 \<le> u2'"
    using hpm hqm unfolding p1_def p2_def q1_def q2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" and ne_q2: "l2' \<le> u2'"
    using bnds ne_p1 ne_q1 by order+
  show ?thesis
  proof (cases "interval_less_true p2 q2")
    case True
    then have "u1' < l2'" using p2_def q2_def ne_p2 ne_q2 by simp
    then have "u1 < l2" using bnds by order
    then have p1q1: "interval_less_true p1 q1" using p1_def q1_def ne_p1 ne_q1 by simp
    have "interval_lt p2 q2 = Some True" using True unfolding interval_lt_def by simp
    with hwide have "b = True" by simp
    then show ?thesis using p1q1 unfolding interval_lt_def by simp
  next
    case False
    then have hlf: "interval_less_false p2 q2"
      using hwide unfolding interval_lt_def by (auto split: if_splits)
    then have "u2' \<le> l1'" using p2_def q2_def ne_p2 ne_q2 by simp
    then have hle: "u2 \<le> l1" using bnds by order
    then have p1q1f: "interval_less_false p1 q1" using p1_def q1_def ne_p1 ne_q1 by simp
    have p1q1nt: "\<not> interval_less_true p1 q1"
    proof
      assume "interval_less_true p1 q1"
      then have "u1 < l2" using p1_def q1_def ne_p1 ne_q1 by simp
      with hle ne_p1 ne_q1 show False by order
    qed
    have "interval_lt p2 q2 = Some False" using False hlf unfolding interval_lt_def by simp
    with hwide have "b = False" by simp
    then show ?thesis using p1q1f p1q1nt unfolding interval_lt_def by simp
  qed
qed


lemma interval_eqb_mono:
  assumes hp: "\<not> is_empty (p1::ivl)" and hq: "\<not> is_empty q1"
      and hpm: "p1 \<le> p2" and hqm: "q1 \<le> q2"
      and hwide: "interval_eqb p2 q2 = Some b"
  shows "interval_eqb p1 q1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  obtain l2 u2 where q1_def: "q1 = Ivl l2 u2" by (cases q1)
  obtain l2' u2' where q2_def: "q2 = Ivl l2' u2'" by (cases q2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_empty_ivl is_bottom_ivl_def by auto
  have ne_q1: "l2 \<le> u2" using hq unfolding q1_def is_empty_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'" "l2' \<le> l2" "u2 \<le> u2'"
    using hpm hqm unfolding p1_def p2_def q1_def q2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" and ne_q2: "l2' \<le> u2'"
    using bnds ne_p1 ne_q1 by order+
  show ?thesis
    using hwide ne_p1 ne_q1 ne_p2 ne_q2 bnds
    unfolding interval_eqb_def p1_def p2_def q1_def q2_def
    by (auto split: if_splits; order)
qed

lemma interval_tobool_mono:
  assumes hp: "\<not> is_empty (p1::ivl)" and hpm: "p1 \<le> p2"
      and hwide: "interval_tobool p2 = Some b"
  shows "interval_tobool p1 = Some b"
proof -
  obtain l1 u1 where p1_def: "p1 = Ivl l1 u1" by (cases p1)
  obtain l1' u1' where p2_def: "p2 = Ivl l1' u1'" by (cases p2)
  have ne_p1: "l1 \<le> u1" using hp unfolding p1_def is_empty_ivl is_bottom_ivl_def by auto
  have bnds: "l1' \<le> l1" "u1 \<le> u1'"
    using hpm unfolding p1_def p2_def less_eq_ivl_def by auto
  have ne_p2: "l1' \<le> u1'" using bnds ne_p1 by order
  show ?thesis
    using hwide ne_p1 ne_p2 bnds
    unfolding interval_tobool_def p1_def p2_def
    by (auto split: if_splits; order)
qed

subsection \<open>Abstract expression evaluation\<close>

fun aval_ivl :: "exp => (vname => ivl) => ivl" where
    "aval_ivl (N n)        \<sigma> = Ivl (Fin n) (Fin n)"
  | "aval_ivl (V x)        \<sigma> = \<sigma> x"
  | "aval_ivl (Plus  a b)  \<sigma> = aval_ivl a \<sigma> + aval_ivl b \<sigma>"
  | "aval_ivl (Minus a b)  \<sigma> = aval_ivl a \<sigma> - aval_ivl b \<sigma>"
  | "aval_ivl (Times a b)  \<sigma> = aval_ivl a \<sigma> * aval_ivl b \<sigma>"
  | "aval_ivl (Less a b)   \<sigma> =
       (if is_empty (aval_ivl a \<sigma>) \<or> is_empty (aval_ivl b \<sigma>) then bot
        else if interval_lt (aval_ivl a \<sigma>) (aval_ivl b \<sigma>) = Some True then Ivl (Fin 1) (Fin 1)
        else if interval_lt (aval_ivl a \<sigma>) (aval_ivl b \<sigma>) = Some False then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl (exp.Eq a b) \<sigma> =
       (if is_empty (aval_ivl a \<sigma>) \<or> is_empty (aval_ivl b \<sigma>) then bot
        else if interval_eqb (aval_ivl a \<sigma>) (aval_ivl b \<sigma>) = Some True then Ivl (Fin 1) (Fin 1)
        else if interval_eqb (aval_ivl a \<sigma>) (aval_ivl b \<sigma>) = Some False then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl (exp.Not a)  \<sigma> =
       (if is_empty (aval_ivl a \<sigma>) then bot
        else if interval_tobool (aval_ivl a \<sigma>) = Some True then Ivl (Fin 0) (Fin 0)
        else if interval_tobool (aval_ivl a \<sigma>) = Some False then Ivl (Fin 1) (Fin 1)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl (And a b)    \<sigma> =
       (if is_empty (aval_ivl a \<sigma>) \<or> is_empty (aval_ivl b \<sigma>) then bot
        else if interval_tobool (aval_ivl a \<sigma>) = Some False \<or> interval_tobool (aval_ivl b \<sigma>) = Some False
        then Ivl (Fin 0) (Fin 0)
        else if interval_tobool (aval_ivl a \<sigma>) = Some True \<and> interval_tobool (aval_ivl b \<sigma>) = Some True
        then Ivl (Fin 1) (Fin 1)
        else Ivl (Fin 0) (Fin 1))"
  | "aval_ivl (Or a b)     \<sigma> =
       (if is_empty (aval_ivl a \<sigma>) \<or> is_empty (aval_ivl b \<sigma>) then bot
        else if interval_tobool (aval_ivl a \<sigma>) = Some True \<or> interval_tobool (aval_ivl b \<sigma>) = Some True
        then Ivl (Fin 1) (Fin 1)
        else if interval_tobool (aval_ivl a \<sigma>) = Some False \<and> interval_tobool (aval_ivl b \<sigma>) = Some False
        then Ivl (Fin 0) (Fin 0)
        else Ivl (Fin 0) (Fin 1))"

interpretation ivl_arith: expression_domain_sound
    aval_ivl "\<lambda>n. Ivl (Fin n) (Fin n)" interval_lt interval_eqb interval_tobool
  by unfold_locales
     (simp_all add: ivl_plus_sound ivl_minus_sound ivl_times_sound
                     ivl_plus_mono ivl_minus_mono ivl_times_mono
                     interval_lt_sound interval_eqb_sound
                     interval_tobool_sound[unfolded truthy_def]
                     interval_lt_mono interval_eqb_mono interval_tobool_mono
                     sup_ivl_def join_ivl.simps truthy_def)

lemmas aval_ivl_sound = ivl_arith.aval_dom_sound[unfolded gamma_abs_ivl]


subsection \<open>Backward inverse operators\<close>

text \<open>
  Inverse operators for backward analysis over intervals.
  @{text inv_less_ivl} performs precise interval narrowing: on the true branch
  of @{text "n1 < n2"}, the upper bound of @{text n1} tightens to one below
  the upper bound of @{text n2}, and the lower bound of @{text n2} tightens to
  one above the lower bound of @{text n1}.  On the false branch (@{text "n1 \<ge> n2"}),
  @{text n1}\<open>s\<close> lower bound tightens to the lower bound of @{text n2}, and @{text n2}\<open>s\<close>
  upper bound tightens to the upper bound of @{text n1}.  Plus/minus/times
  instantiate the shared @{const inv_conservative} (identity) instead of a
  per-domain no-op.
\<close>

fun inv_less_ivl :: "bool => ivl => ivl => ivl * ivl" where
    "inv_less_ivl True  (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl MinInf (u2 - Fin 1),
        Ivl l2 u2 \<sqinter> Ivl (l1 + Fin 1) PlusInf)"
  | "inv_less_ivl False (Ivl l1 u1) (Ivl l2 u2) =
       (Ivl l1 u1 \<sqinter> Ivl l2 PlusInf,
        Ivl l2 u2 \<sqinter> Ivl MinInf u1)"

lemma inv_less_ivl_n1_ub:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl MinInf (u2 - Fin 1))"
  by (cases u2; auto; linarith)

lemma inv_less_ivl_n2_lb:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl (l1 + Fin 1) PlusInf)"
  by (cases l1; auto; linarith)

lemma inv_less_ivl_n1_ge_lb:
  "n2 \<in> gamma_ivl (Ivl l2 u2) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n1 \<in> gamma_ivl (Ivl l2 PlusInf)"
  by (cases l2; auto; linarith)

lemma inv_less_ivl_n2_le_ub:
  "n1 \<in> gamma_ivl (Ivl l1 u1) \<Longrightarrow> \<not> n1 < n2
   \<Longrightarrow> n2 \<in> gamma_ivl (Ivl MinInf u1)"
  by (cases u1; auto; linarith)

lemma inv_less_ivl_sound:
  assumes g1: "n1 \<in> gamma_ivl a1" and g2: "n2 \<in> gamma_ivl a2" and eq: "(n1 < n2) = res"
  shows "n1 \<in> gamma_ivl (fst (inv_less_ivl res a1 a2))
       \<and> n2 \<in> gamma_ivl (snd (inv_less_ivl res a1 a2))"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (rule ivl_exhaustE)
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (rule ivl_exhaustE)
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

subsection \<open>Backward inverse operator for equality\<close>

text \<open>
  @{text inv_eq_ivl} narrows on a guard @{text \<open>e1 = e2\<close>} known true or false.
  The true branch narrows both operands to their intersection, the same
  argument as the sign instance via \<open>meet_ivl_gamma\<close>. The false
  branch is the sound identity: a precise refinement is possible in specific
  cases (e.g. excluding a known point value from one bound of the other
  operand when that point sits exactly at that bound), but @{typ ivl}'s
  infinite domain makes proving that refinement's monotonicity
  disproportionately more expensive than for the finite sign lattice ---
  attempted and abandoned; the guard conditions needed access the interval's
  own bound values, and a boundary-matching guard is not compatible with the
  order-based case-split technique that closed the sign proof. This is a
  documented precision gap, not a soundness one: \<open>bfilter\<close>'s @{text
  \<open>Eq _ _ False\<close>} case under this instance narrows exactly as much for
  Interval as it already does today (not at all), while Sign gains real
  precision from its own instance.
\<close>

fun inv_eq_ivl :: "bool => ivl => ivl => ivl * ivl" where
    "inv_eq_ivl True  a1 a2 = (meet_ivl a1 a2, meet_ivl a1 a2)"
  | "inv_eq_ivl False a1 a2 = (a1, a2)"

lemma inv_eq_ivl_sound:
  assumes "n1 \<in> gamma_ivl a1" and "n2 \<in> gamma_ivl a2" and "(n1 = n2) = res"
  shows "n1 \<in> gamma_ivl (fst (inv_eq_ivl res a1 a2))
       \<and> n2 \<in> gamma_ivl (snd (inv_eq_ivl res a1 a2))"
proof (cases res)
  case True
  then have "n1 = n2" using assms(3) by simp
  then have "n1 \<in> gamma_ivl a2" using assms(2) by simp
  then have "n1 \<in> gamma_ivl (meet_ivl a1 a2)" using meet_ivl_gamma[OF assms(1)] by simp
  then show ?thesis using True \<open>n1 = n2\<close> by simp
next
  case False
  then show ?thesis using assms(1,2) by simp
qed

lemma inv_eq_ivl_mono:
  assumes A1: "a1 \<le> (a1' :: ivl)" and A2: "a2 \<le> a2'"
  shows
    "fst (inv_eq_ivl r a1 a2) \<le> fst (inv_eq_ivl r a1' a2') \<and>
     snd (inv_eq_ivl r a1 a2) \<le> snd (inv_eq_ivl r a1' a2')"
proof (cases r)
  case True
  have "a1 \<sqinter> a2 \<le> a1' \<sqinter> a2'" by (rule inf_mono[OF A1 A2])
  then show ?thesis using True by (simp add: inf_ivl_def)
next
  case False
  then show ?thesis using A1 A2 by simp
qed

lemmas aval_ivl_mono = ivl_arith.aval_dom_mono

lemma inv_less_ivl_mono:
  assumes a1: "(a1 :: ivl) \<le> a1'" and a2: "(a2 :: ivl) \<le> a2'"
  shows "fst (inv_less_ivl res a1 a2) \<le> fst (inv_less_ivl res a1' a2')
       \<and> snd (inv_less_ivl res a1 a2) \<le> snd (inv_less_ivl res a1' a2')"
proof -
  obtain l1 u1 where ha1: "a1 = Ivl l1 u1" by (rule ivl_exhaustE)
  obtain l2 u2 where ha2: "a2 = Ivl l2 u2" by (rule ivl_exhaustE)
  obtain l1' u1' where ha1': "a1' = Ivl l1' u1'" by (rule ivl_exhaustE)
  obtain l2' u2' where ha2': "a2' = Ivl l2' u2'" by (rule ivl_exhaustE)
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

text \<open>
  Reductiveness: @{const inv_less_ivl}/@{const inv_eq_ivl} only ever narrow an
  operand via @{const meet_ivl} or pass it through unchanged. \<open>meet_ivl_le_lb1\<close>/
  \<open>meet_ivl_le_lb2\<close> are stated via \<open>(\<sqinter>)\<close>, not \<open>meet_ivl\<close> itself, so restate them
  directly in terms of \<open>meet_ivl\<close> here (matching the case-split style already
  used in the @{class semilattice_inf} instance proof) for direct use below.
\<close>

lemma meet_ivl_le1: "meet_ivl a b \<le> a"
  by (cases a; cases b;
      simp add: less_eq_ivl_def;
      metis eint_le_linear eint_le_trans eint_le_refl)

lemma meet_ivl_le2: "meet_ivl a b \<le> b"
  by (cases a; cases b;
      auto simp: less_eq_ivl_def split: if_splits intro: eint_le_trans eint_le_refl)

lemma inv_less_ivl_reductive1: "fst (inv_less_ivl res a1 a2) \<le> a1"
  apply (cases res; cases a1; cases a2)
  using eint_le_linear less_eq_ivl_def by(auto)

lemma inv_less_ivl_reductive2: "snd (inv_less_ivl res a1 a2) \<le> a2"
  apply (cases res; cases a1; cases a2)
  using eint_le_linear less_eq_ivl_def by(auto)

lemma inv_eq_ivl_reductive1: "fst (inv_eq_ivl res a1 a2) \<le> a1"
  by (cases res; simp add: meet_ivl_le1)

lemma inv_eq_ivl_reductive2: "snd (inv_eq_ivl res a1 a2) \<le> a2"
  by (cases res; simp add: meet_ivl_le2)


subsection \<open>Backward-domain interpretation\<close>

text \<open>
  One interpretation discharges soundness, monotonicity, and reductiveness
  together against @{locale backward_domain_refined} -- each \<open>inv_*\<close>'s
  mono/reductive obligation is one @{const le_pair} fact, built from the
  componentwise per-operator lemmas above.

  The \<open>intersect\<close> parameter is instantiated with \<^const>\<open>intersect_ivl\<close>, not with the
  lattice \<^const>\<open>inf\<close>. The locale only requires \<open>intersect\<close> to preserve
  concretizations, to be reductive in both arguments, and to be monotone --- never
  that it is the greatest lower bound of the representation order --- and the
  normalising variant additionally keeps every filtered state canonical, so an
  infeasible guard stores \<^const>\<open>bot\<close> instead of a reversed bound pair.
  \<^const>\<open>inf\<close> itself cannot be normalised without losing the greatest-lower-bound
  law; @{thm [source] meet_ivl_normalized_breaks_greatest} is that counterexample.
\<close>

global_interpretation ivl_backward_domain:
    backward_domain_refined intersect_ivl aval_ivl interval_tobool
                    inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative
  defines
    afilter_ivl = ivl_backward_domain.afilter
    and feasible_ivl = ivl_backward_domain.feasible
    and bfilter_ivl = ivl_backward_domain.bfilter
    and branch_ivl = ivl_backward_domain.branch
    and branch_lifted_ivl = ivl_backward_domain.branch_lifted
    and afilter_ivl_st = ivl_backward_domain.afilter_st
    and bfilter_ivl_st = ivl_backward_domain.bfilter_st
    and branch_ivl_st = ivl_backward_domain.branch_st
proof unfold_locales
  fix n :: int and a b :: ivl
  assume H1: "n \<in> gamma a" and H2: "n \<in> gamma b"
  have h1: "n \<in> gamma_ivl a" using H1 by simp
  have h2: "n \<in> gamma_ivl b" using H2 by simp
  show "n \<in> gamma (intersect_ivl a b)"
    using intersect_ivl_gamma[OF h1 h2] by simp
next
  fix s :: store and e :: exp and \<sigma> :: "vname \<Rightarrow> ivl"
  assume H: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  have h: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" using gamma_stateD[OF H] by simp
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
  fix n1 n2 :: int and a1 a2 :: ivl and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 = n2) = res"
  have h1: "n1 \<in> gamma_ivl a1" using H1 by simp
  have h2: "n2 \<in> gamma_ivl a2" using H2 by simp
  show "n1 \<in> gamma (fst (inv_eq_ivl res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq_ivl res a1 a2))"
    using inv_eq_ivl_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 + n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 - n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 r :: ivl
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 * n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix p :: ivl and b :: bool and i :: int
  assume "interval_tobool p = Some b" and "i \<in> gamma p"
  then show "truthy i = b" using interval_tobool_sound by simp
next
  fix a1 a2 b1 b2 :: ivl
  assume "a1 \<le> a2" and "b1 \<le> b2"
  thus "intersect_ivl a1 b1 \<le> intersect_ivl a2 b2" by (rule intersect_ivl_mono)
next
  fix e :: exp and \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> ivl"
  assume "\<sigma>1 \<le> \<sigma>2"
  thus "aval_ivl e \<sigma>1 \<le> aval_ivl e \<sigma>2" by (rule aval_ivl_mono)
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_less_ivl res x1 y1) (inv_less_ivl res x2 y2)"
    using inv_less_ivl_mono[OF A B] by simp
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_eq_ivl res x1 y1) (inv_eq_ivl res x2 y2)"
    using inv_eq_ivl_mono[OF A B] by simp
next
  fix r1 r2 x1 x2 y1 y2 :: ivl
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_conservative r1 x1 y1) (inv_conservative r2 x2 y2)"
    using A B by (simp add: inv_conservative_def)
next
  fix a b :: ivl
  show "intersect_ivl a b \<le> a" by (rule intersect_ivl_le1)
next
  fix a b :: ivl
  show "intersect_ivl a b \<le> b" by (rule intersect_ivl_le2)
next
  fix p1 p2 :: ivl and bv :: bool
  assume "\<not> is_empty p1" and "p1 \<le> p2" and "interval_tobool p2 = Some bv"
  then show "interval_tobool p1 = Some bv" using interval_tobool_mono by simp
qed

text \<open>
  Executable @{typ "ivl resolved_st_q"} mirror of \<open>afilter_ivl\<close> /
  \<open>bfilter_ivl\<close>, and its commutation with the abstract filters through
  @{const fun_of_resolved_st_q_for}. Both come from the generic
  @{locale backward_domain} executable mirror (\<open>Exec_Backward\<close>).
\<close>

lemmas afilter_ivl_st_commute = ivl_backward_domain.afilter_st_commute
lemmas bfilter_ivl_st_commute = ivl_backward_domain.bfilter_st_commute
lemmas branch_ivl_st_commute = ivl_backward_domain.branch_st_commute

lemma afilter_ivl_mono:
  "a1 \<le> (a2 :: ivl) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_ivl e a1 sigma1 \<le> afilter_ivl e a2 sigma2"
  using ivl_backward_domain.afilter_mono by (simp add: afilter_ivl_def)

lemma bfilter_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_ivl b res sigma1 \<le> bfilter_ivl b res sigma2"
  using ivl_backward_domain.bfilter_mono by (simp add: bfilter_ivl_def)

lemma branch_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_ivl b res sigma1 \<le> branch_ivl b res sigma2"
  using ivl_backward_domain.branch_mono by (simp add: branch_ivl_def)

lemma branch_ivl_le_bfilter_ivl: "branch_ivl e pol \<sigma> \<le> bfilter_ivl e pol \<sigma>"
  using ivl_backward_domain.branch_le_bfilter by (simp add: branch_ivl_def bfilter_ivl_def)

end

