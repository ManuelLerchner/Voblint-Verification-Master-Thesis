theory Interval_Backward
  imports Interval_Arithmetic Voblint_Core.Exec_Backward "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Interval backward filtering\<close>

subsection \<open>Abstract expression evaluation\<close>

fun aval_ivl :: "aexp => (vname => ivl) => ivl" where
    "aval_ivl (N n)        \<sigma> = Ivl (Fin n) (Fin n)"
  | "aval_ivl (V x)        \<sigma> = \<sigma> x"
  | "aval_ivl (Plus  a b)  \<sigma> = aval_ivl a \<sigma> + aval_ivl b \<sigma>"
  | "aval_ivl (Minus a b)  \<sigma> = aval_ivl a \<sigma> - aval_ivl b \<sigma>"
  | "aval_ivl (Times a b)  \<sigma> = aval_ivl a \<sigma> * aval_ivl b \<sigma>"

lemma aval_ivl_sound:
  "(\<forall>x. s x \<in> gamma_ivl (\<sigma> x))
   \<Longrightarrow> aval a s \<in> gamma_ivl (aval_ivl a \<sigma>)"
  by (induction a;
      simp add: ivl_plus_sound ivl_minus_sound ivl_times_sound)

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

subsection \<open>Backward-domain interpretation\<close>

global_interpretation ivl_backward_domain:
    backward_domain meet_ivl aval_ivl
                    inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative
  defines
    afilter_ivl = ivl_backward_domain.afilter
    and bfilter_ivl = ivl_backward_domain.bfilter
    and afilter_ivl_st = ivl_backward_domain.afilter_st
    and bfilter_ivl_st = ivl_backward_domain.bfilter_st
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
qed

text \<open>
  Executable @{typ "ivl resolved_st_q"} mirror of \<open>afilter_ivl\<close> /
  \<open>bfilter_ivl\<close>, and its commutation with the abstract filters through
  @{const fun_of_resolved_st_q_for}. Both come from the generic
  @{locale backward_domain} executable mirror (\<open>Exec_Backward\<close>).
\<close>

lemmas afilter_ivl_st_commute = ivl_backward_domain.afilter_st_commute
lemmas bfilter_ivl_st_commute = ivl_backward_domain.bfilter_st_commute

lemma aval_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_ivl a sigma1 \<le> aval_ivl a sigma2"
  by (induction a arbitrary: sigma1 sigma2)
     (auto simp: ivl_plus_mono ivl_minus_mono ivl_times_mono le_funD)


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
  Monotonicity of @{const afilter_ivl} / @{const bfilter_ivl} is the generic
  @{locale backward_domain_mono} result: interpret it at the interval operators
  (the parent @{term ivl_backward_domain} already discharges soundness, so only the
  six operator-mono facts remain) and the filter monotonicity follows.
\<close>

context begin
interpretation ivl_bdm:
  backward_domain_mono meet_ivl aval_ivl
                       inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative
proof unfold_locales
  fix a1 a2 b1 b2 :: ivl
  assume "a1 \<le> a2" and "b1 \<le> b2"
  hence "a1 \<sqinter> b1 \<le> a2 \<sqinter> b2" by (rule inf_mono)
  thus "meet_ivl a1 b1 \<le> meet_ivl a2 b2" by (simp add: inf_ivl_def)
next
  fix e :: aexp and \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> ivl"
  assume "\<sigma>1 \<le> \<sigma>2"
  thus "aval_ivl e \<sigma>1 \<le> aval_ivl e \<sigma>2" by (rule aval_ivl_mono)
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_less_ivl res x1 y1) \<le> fst (inv_less_ivl res x2 y2) \<and>
        snd (inv_less_ivl res x1 y1) \<le> snd (inv_less_ivl res x2 y2)"
    by (rule inv_less_ivl_mono)
next
  fix x1 x2 y1 y2 :: ivl and res :: bool
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_eq_ivl res x1 y1) \<le> fst (inv_eq_ivl res x2 y2) \<and>
        snd (inv_eq_ivl res x1 y1) \<le> snd (inv_eq_ivl res x2 y2)"
    by (rule inv_eq_ivl_mono)
next
  fix r1 r2 x1 x2 y1 y2 :: ivl
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_conservative r1 x1 y1) \<le> fst (inv_conservative r2 x2 y2) \<and>
        snd (inv_conservative r1 x1 y1) \<le> snd (inv_conservative r2 x2 y2)"
    by (simp add: inv_conservative_def)

qed

lemma afilter_ivl_mono:
  "a1 \<le> (a2 :: ivl) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_ivl e a1 sigma1 \<le> afilter_ivl e a2 sigma2"
  using ivl_bdm.afilter_mono by (simp add: afilter_ivl_def)

lemma bfilter_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_ivl b res sigma1 \<le> bfilter_ivl b res sigma2"
  using ivl_bdm.bfilter_mono by (simp add: bfilter_ivl_def)

end

end
