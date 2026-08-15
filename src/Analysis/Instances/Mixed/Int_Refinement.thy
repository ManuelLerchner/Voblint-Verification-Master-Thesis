theory Int_Refinement
  imports
    Int_Domain
    "HOL-Library.While_Combinator"
begin

section \<open>Closed-world integer-domain refinement\<close>

text \<open>
  Refinement exchanges a fixed vocabulary of facts between the components of
  the concrete integer-domain record. Reduction-step laws isolate progressive
  composition from the record representation.
\<close>

definition int_reduction_step :: "(int_dom => int_dom) => bool" where
  "int_reduction_step step \<longleftrightarrow>
     (\<forall>d. gamma_int_dom (step d) = gamma_int_dom d) \<and>
     (\<forall>d. step d \<le> d) \<and>
     mono step"

lemma int_reduction_step_exact:
  assumes "int_reduction_step step"
  shows "gamma_int_dom (step d) = gamma_int_dom d"
  using assms unfolding int_reduction_step_def by blast

lemma int_reduction_step_reductive:
  assumes "int_reduction_step step"
  shows "step d \<le> d"
  using assms unfolding int_reduction_step_def by blast

lemma int_reduction_step_mono:
  assumes "int_reduction_step step"
  shows "mono step"
  using assms unfolding int_reduction_step_def by blast

lemma int_reduction_step_id [simp]:
  "int_reduction_step id"
  unfolding int_reduction_step_def mono_def by simp

lemma int_reduction_step_comp:
  assumes f: "int_reduction_step f"
      and g: "int_reduction_step g"
  shows "int_reduction_step (g o f)"
proof (unfold int_reduction_step_def, intro conjI allI)
  fix d
  show "gamma_int_dom ((g o f) d) = gamma_int_dom d"
    using int_reduction_step_exact[OF g, of "f d"]
          int_reduction_step_exact[OF f, of d]
    by simp
next
  fix d
  have "g (f d) \<le> f d"
    by (rule int_reduction_step_reductive[OF g])
  also have "f d \<le> d"
    by (rule int_reduction_step_reductive[OF f])
  finally show "(g o f) d \<le> d"
    by simp
next
  show "mono (g o f)"
    using int_reduction_step_mono[OF f]
          int_reduction_step_mono[OF g]
    unfolding mono_def by auto
qed

fun apply_reduction_steps ::
  "(int_dom => int_dom) list => int_dom => int_dom" where
  "apply_reduction_steps [] d = d"
| "apply_reduction_steps (step # steps) d =
     apply_reduction_steps steps (step d)"

lemma apply_reduction_steps_append:
  "apply_reduction_steps (xs @ ys) =
   apply_reduction_steps ys o apply_reduction_steps xs"
  by (induction xs) (auto simp: fun_eq_iff)

lemma int_reduction_steps:
  assumes "\<forall>step \<in> set steps. int_reduction_step step"
  shows "int_reduction_step (apply_reduction_steps steps)"
  using assms
proof (induction steps)
  case Nil
  then show ?case
    unfolding int_reduction_step_def mono_def by simp
next
  case (Cons step steps)
  have step: "int_reduction_step step"
    using Cons.prems by simp
  have rest: "int_reduction_step (apply_reduction_steps steps)"
    using Cons.IH Cons.prems by simp
  have valid: "int_reduction_step (apply_reduction_steps steps o step)"
    by (rule int_reduction_step_comp[OF step rest])
  from valid show ?case
    unfolding int_reduction_step_def mono_def by simp
qed

subsection \<open>Refinement facts and semantic intersections\<close>

type_synonym interval_fact = ivl
type_synonym congruence_fact = congruence

definition interval_fact_of_ivl :: "ivl => interval_fact" where
  "interval_fact_of_ivl i = i"

fun intersect_sign :: "sign => sign => sign" where
  "intersect_sign SBot b = SBot"
| "intersect_sign SNeg b =
     (case b of
        SBot => SBot
      | SNeg => SNeg
      | SNonPos => SNeg
      | SZero => SBot
      | SNonNeg => SBot
      | SPos => SBot
      | STop => SNeg)"
| "intersect_sign SNonPos b =
     (case b of
        SBot => SBot
      | SNeg => SNeg
      | SNonPos => SNonPos
      | SZero => SZero
      | SNonNeg => SZero
      | SPos => SBot
      | STop => SNonPos)"
| "intersect_sign SZero b =
     (case b of
        SBot => SBot
      | SNeg => SBot
      | SNonPos => SZero
      | SZero => SZero
      | SNonNeg => SZero
      | SPos => SBot
      | STop => SZero)"
| "intersect_sign SNonNeg b =
     (case b of
        SBot => SBot
      | SNeg => SBot
      | SNonPos => SZero
      | SZero => SZero
      | SNonNeg => SNonNeg
      | SPos => SPos
      | STop => SNonNeg)"
| "intersect_sign SPos b =
     (case b of
        SBot => SBot
      | SNeg => SBot
      | SNonPos => SBot
      | SZero => SBot
      | SNonNeg => SPos
      | SPos => SPos
      | STop => SPos)"
| "intersect_sign STop b = b"

lemma gamma_intersect_sign [simp]:
  "gamma_sign (intersect_sign a b) =
   gamma_sign a \<inter> gamma_sign b"
  by (cases a; cases b) auto

lemma intersect_sign_le1:
  "intersect_sign a b \<le> a"
  by (cases a; cases b)
     (simp_all add: less_eq_sign_def)

lemma intersect_sign_le2:
  "intersect_sign a b \<le> b"
  by (cases a; cases b)
     (simp_all add: less_eq_sign_def)

lemma intersect_sign_mono:
  assumes "a1 \<le> a2" and "b1 \<le> b2"
  shows "intersect_sign a1 b1 \<le> intersect_sign a2 b2"
  using assms
  by (cases a1; cases a2; cases b1; cases b2)
     (simp_all add: less_eq_sign_def)

fun intersect_parity :: "parity => parity => parity" where
  "intersect_parity PBot b = PBot"
| "intersect_parity PEven b =
     (case b of
        PBot => PBot
      | PEven => PEven
      | POdd => PBot
      | PTop => PEven)"
| "intersect_parity POdd b =
     (case b of
        PBot => PBot
      | PEven => PBot
      | POdd => POdd
      | PTop => POdd)"
| "intersect_parity PTop b = b"

lemma gamma_intersect_parity [simp]:
  "gamma_parity (intersect_parity a b) =
   gamma_parity a \<inter> gamma_parity b"
  by (cases a; cases b) auto

lemma intersect_parity_le1:
  "intersect_parity a b \<le> a"
  by (cases a; cases b)
     (simp_all add: less_eq_parity_def)

lemma intersect_parity_le2:
  "intersect_parity a b \<le> b"
  by (cases a; cases b)
     (simp_all add: less_eq_parity_def)

lemma intersect_parity_mono:
  assumes "a1 \<le> a2" and "b1 \<le> b2"
  shows "intersect_parity a1 b1 \<le> intersect_parity a2 b2"
  using assms
  by (cases a1; cases a2; cases b1; cases b2)
     (simp_all add: less_eq_parity_def)

definition interval_sign_fact :: "interval_fact => sign" where
  "interval_sign_fact i =
     (if is_bottom_ivl i then SBot
      else case i of Ivl l u =>
        if u < Fin 0 then SNeg
        else if u = Fin 0 then
          (if l = Fin 0 then SZero else SNonPos)
        else if Fin 0 < l then SPos
        else if l = Fin 0 then SNonNeg
        else STop)"

definition interval_parity_fact :: "interval_fact => parity" where
  "interval_parity_fact i =
     (if is_bottom_ivl i then PBot
      else case i of
        Ivl (Fin l) (Fin u) =>
          if l = u then if even l then PEven else POdd else PTop
      | _ => PTop)"

lemma interval_sign_fact_sound:
  "gamma_ivl i \<subseteq> gamma_sign (interval_sign_fact i)"
proof
  fix n
  assume n: "n \<in> gamma_ivl i"
  obtain l u where i: "i = Ivl l u"
    by (rule ivl_exhaustE)
  from n have bounds: "l \<le> Fin n" "Fin n \<le> u"
    unfolding i by auto
  from n have nonempty: "\<not> is_bottom_ivl i"
    using is_bottom_ivl_correct by auto
  show "n \<in> gamma_sign (interval_sign_fact i)"
    unfolding interval_sign_fact_def i
    using bounds nonempty
    by (cases l; cases u)
       (auto simp: is_bottom_ivl_def less_eint_def
          split: if_splits)
qed

lemma interval_parity_fact_sound:
  "gamma_ivl i \<subseteq> gamma_parity (interval_parity_fact i)"
proof
  fix n
  assume n: "n \<in> gamma_ivl i"
  obtain l u where i: "i = Ivl l u"
    by (rule ivl_exhaustE)
  from n have bounds: "l \<le> Fin n" "Fin n \<le> u"
    unfolding i by auto
  from n have nonempty: "\<not> is_bottom_ivl i"
    using is_bottom_ivl_correct by auto
  show "n \<in> gamma_parity (interval_parity_fact i)"
    unfolding interval_parity_fact_def i
    using bounds nonempty
    by (cases l; cases u)
       (auto simp: is_bottom_ivl_def
          split: if_splits)

qed

lemma interval_fact_of_sign_mono:
  assumes "s \<le> t"
  shows "interval_fact_of_sign s \<le> interval_fact_of_sign t"
  using assms
  by (cases s; cases t)
     (simp_all add: less_eq_sign_def less_eq_ivl_def
        bot_ivl_def top_ivl_def ivl_top_def)

lemma interval_sign_fact_mono:
  assumes "i \<le> j"
  shows "interval_sign_fact i \<le> interval_sign_fact j"
proof -
  obtain l1 u1 where i: "i = Ivl l1 u1"
    by (rule ivl_exhaustE)
  obtain l2 u2 where j: "j = Ivl l2 u2"
    by (rule ivl_exhaustE)
  show ?thesis
    using assms
    unfolding i j interval_sign_fact_def
    by (cases l1; cases u1; cases l2; cases u2)
       (auto simp: less_eq_ivl_def is_bottom_ivl_def
          less_eint_def less_eq_sign_def
          split: if_splits)
qed

lemma interval_parity_fact_mono:
  assumes "i \<le> j"
  shows "interval_parity_fact i \<le> interval_parity_fact j"
proof -
  obtain l1 u1 where i: "i = Ivl l1 u1"
    by (rule ivl_exhaustE)
  obtain l2 u2 where j: "j = Ivl l2 u2"
    by (rule ivl_exhaustE)
  show ?thesis
    using assms
    unfolding i j interval_parity_fact_def
    by (cases l1; cases u1; cases l2; cases u2)
       (auto simp: less_eq_ivl_def is_bottom_ivl_def
          less_eq_parity_def
          split: if_splits)

qed

subsection \<open>Interval-fact fan-out\<close>

definition refine_sign_with_interval ::
  "interval_fact => sign => sign" where
  "refine_sign_with_interval fct s =
     intersect_sign (interval_sign_fact fct) s"

definition refine_ivl_with_interval ::
  "interval_fact => ivl => ivl" where
  "refine_ivl_with_interval fct i = intersect_ivl fct i"

definition refine_parity_with_interval ::
  "interval_fact => parity => parity" where
  "refine_parity_with_interval fct p =
     intersect_parity (interval_parity_fact fct) p"

definition interval_fact_of_int_dom :: "int_dom => interval_fact" where
  "interval_fact_of_int_dom d =
     intersect_ivl
       (interval_fact_of_sign (int_sign d))
       (interval_fact_of_ivl (int_ivl d))"

definition refine_interval :: "int_dom => int_dom" where
  "refine_interval d =
     (let fct = interval_fact_of_int_dom d
      in d\<lparr>
           int_sign := refine_sign_with_interval fct (int_sign d),
           int_ivl := refine_ivl_with_interval fct (int_ivl d),
           int_parity := refine_parity_with_interval fct (int_parity d)
         \<rparr>)"

lemma gamma_refine_sign_with_interval [simp]:
  "gamma_sign (refine_sign_with_interval fct s) =
   gamma_sign (interval_sign_fact fct) \<inter> gamma_sign s"
  by (simp add: refine_sign_with_interval_def)

lemma gamma_refine_ivl_with_interval:
  "gamma_ivl (refine_ivl_with_interval fct i) =
   gamma_ivl fct \<inter> gamma_ivl i"
  by (simp only: refine_ivl_with_interval_def gamma_intersect_ivl_exact)

lemma gamma_refine_parity_with_interval [simp]:
  "gamma_parity (refine_parity_with_interval fct p) =
   gamma_parity (interval_parity_fact fct) \<inter> gamma_parity p"
  by (simp add: refine_parity_with_interval_def)

lemma refine_sign_with_interval_le:
  "refine_sign_with_interval fct s \<le> s"
  unfolding refine_sign_with_interval_def
  by (rule intersect_sign_le2)

lemma refine_ivl_with_interval_le:
  "refine_ivl_with_interval fct i \<le> i"
  unfolding refine_ivl_with_interval_def
  by (rule intersect_ivl_le2)

lemma refine_parity_with_interval_le:
  "refine_parity_with_interval fct p \<le> p"
  unfolding refine_parity_with_interval_def
  by (rule intersect_parity_le2)

lemma refine_sign_with_interval_mono:
  assumes "fct1 \<le> fct2" and "s1 \<le> s2"
  shows
    "refine_sign_with_interval fct1 s1 \<le>
     refine_sign_with_interval fct2 s2"
  unfolding refine_sign_with_interval_def
  by (rule intersect_sign_mono;
      use assms interval_sign_fact_mono in blast)

lemma refine_ivl_with_interval_mono:
  assumes "fct1 \<le> fct2" and "i1 \<le> i2"
  shows
    "refine_ivl_with_interval fct1 i1 \<le>
     refine_ivl_with_interval fct2 i2"
  unfolding refine_ivl_with_interval_def
  by (rule intersect_ivl_mono; fact)

lemma refine_parity_with_interval_mono:
  assumes "fct1 \<le> fct2" and "p1 \<le> p2"
  shows
    "refine_parity_with_interval fct1 p1 \<le>
     refine_parity_with_interval fct2 p2"
  unfolding refine_parity_with_interval_def
  by (rule intersect_parity_mono;
      use assms interval_parity_fact_mono in blast)

lemma gamma_interval_fact_of_int_dom:
  "gamma_ivl (interval_fact_of_int_dom d) =
   gamma_sign (int_sign d) \<inter> gamma_ivl (int_ivl d)"
  unfolding interval_fact_of_int_dom_def interval_fact_of_ivl_def
  by (simp only: gamma_intersect_ivl_exact gamma_interval_fact_of_sign)

lemma interval_fact_of_int_dom_mono:
  assumes "d \<le> e"
  shows "interval_fact_of_int_dom d \<le> interval_fact_of_int_dom e"
proof -
  from assms have components:
    "int_sign d \<le> int_sign e"
    "int_ivl d \<le> int_ivl e"
    by (simp_all add: less_eq_int_dom_ext_def)
  show ?thesis
    unfolding interval_fact_of_int_dom_def interval_fact_of_ivl_def
    by (rule intersect_ivl_mono)
       (use components interval_fact_of_sign_mono in auto)
qed

lemma refine_interval_exact:
  "gamma_int_dom (refine_interval d) = gamma_int_dom d"
proof -
  let ?fct = "interval_fact_of_int_dom d"
  have fct:
    "gamma_ivl ?fct =
     gamma_sign (int_sign d) \<inter> gamma_ivl (int_ivl d)"
    by (rule gamma_interval_fact_of_int_dom)
  have sign_cover:
    "gamma_ivl ?fct \<subseteq>
     gamma_sign (interval_sign_fact ?fct)"
    by (rule interval_sign_fact_sound)
  have parity_cover:
    "gamma_ivl ?fct \<subseteq>
     gamma_parity (interval_parity_fact ?fct)"
    by (rule interval_parity_fact_sound)
  show ?thesis
    unfolding refine_interval_def gamma_int_dom_def Let_def
    using fct sign_cover parity_cover
    by (auto simp: gamma_refine_ivl_with_interval)
qed

lemma refine_interval_reductive:
  "refine_interval d \<le> d"
  unfolding refine_interval_def Let_def
  by (simp add: less_eq_int_dom_ext_def
        refine_sign_with_interval_le
        refine_ivl_with_interval_le
        refine_parity_with_interval_le)

lemma refine_interval_mono:
  "mono refine_interval"
proof (rule monoI)
  fix d e :: int_dom
  assume de: "d \<le> e"
  from de have components:
    "int_sign d \<le> int_sign e"
    "int_ivl d \<le> int_ivl e"
    "int_parity d \<le> int_parity e"
    "int_congruence d \<le> int_congruence e"
    by (simp_all add: less_eq_int_dom_ext_def)
  have fct_le:
    "interval_fact_of_int_dom d \<le> interval_fact_of_int_dom e"
    by (rule interval_fact_of_int_dom_mono[OF de])
  show "refine_interval d \<le> refine_interval e"
    unfolding refine_interval_def Let_def
    by (simp add: less_eq_int_dom_ext_def
          refine_sign_with_interval_mono[OF fct_le components(1)]
          refine_ivl_with_interval_mono[OF fct_le components(2)]
          refine_parity_with_interval_mono[OF fct_le components(3)]
          components(4))
qed

lemma int_reduction_step_refine_interval:
  "int_reduction_step refine_interval"
  unfolding int_reduction_step_def
  using refine_interval_exact refine_interval_reductive refine_interval_mono
  by blast


subsection \<open>Congruence-fact fan-out\<close>

definition congruence_fact_of_congruence ::
  "congruence => congruence_fact" where
  "congruence_fact_of_congruence c = c"

definition congruence_fact_of_int_dom ::
  "int_dom => congruence_fact" where
  "congruence_fact_of_int_dom d =
     restrict_congruence_by_parity
       (int_parity d)
       (congruence_fact_of_congruence (int_congruence d))"

fun congruence_lower_bound :: "int => int => eint => eint" where
  "congruence_lower_bound c m MinInf = MinInf"
| "congruence_lower_bound c m (Fin l) =
     Fin (l + ((c - l) mod m))"
| "congruence_lower_bound c m PlusInf = PlusInf"

fun congruence_upper_bound :: "int => int => eint => eint" where
  "congruence_upper_bound c m MinInf = MinInf"
| "congruence_upper_bound c m (Fin u) =
     Fin (u - ((u - c) mod m))"
| "congruence_upper_bound c m PlusInf = PlusInf"

fun refine_ivl_with_congruence_rep ::
  "congruence_rep => ivl => ivl" where
  "refine_ivl_with_congruence_rep None i = bot"
| "refine_ivl_with_congruence_rep (Some (c, m)) (Ivl l u) =
     (if m = 0 then
        intersect_ivl (Ivl (Fin c) (Fin c)) (Ivl l u)
      else
        intersect_ivl
          (mk_ivl
            (congruence_lower_bound c m l)
            (congruence_upper_bound c m u))
          (Ivl l u))"

definition refine_ivl_with_congruence ::
  "congruence_fact => ivl => ivl" where
  "refine_ivl_with_congruence fct i =
     refine_ivl_with_congruence_rep (Rep_congruence fct) i"

fun parity_fact_of_congruence_rep ::
  "congruence_rep => parity" where
  "parity_fact_of_congruence_rep None = PBot"
| "parity_fact_of_congruence_rep (Some (c, m)) =
     (if m = 0 \<or> even m then
        if even c then PEven else POdd
      else PTop)"

definition parity_fact_of_congruence ::
  "congruence_fact => parity" where
  "parity_fact_of_congruence fct =
     parity_fact_of_congruence_rep (Rep_congruence fct)"

definition refine_parity_with_congruence ::
  "congruence_fact => parity => parity" where
  "refine_parity_with_congruence fct p =
     intersect_parity (parity_fact_of_congruence fct) p"

definition refine_congruence_with_congruence ::
  "congruence_fact => congruence => congruence" where
  "refine_congruence_with_congruence fct c = fct"

lemma gamma_congruence_fact_of_int_dom [simp]:
  "gamma_congruence (congruence_fact_of_int_dom d) =
   gamma_parity (int_parity d) \<inter>
   gamma_congruence (int_congruence d)"
  unfolding congruence_fact_of_int_dom_def
    congruence_fact_of_congruence_def
  by simp

lemma congruence_fact_of_int_dom_mono:
  assumes de: "d <= e"
  shows
    "congruence_fact_of_int_dom d <=
     congruence_fact_of_int_dom e"
proof -
  from de have parity:
    "int_parity d <= int_parity e"
    by (simp add: less_eq_int_dom_ext_def)
  from de have congruence:
    "int_congruence d <= int_congruence e"
    by (simp add: less_eq_int_dom_ext_def)
  have parity_gamma:
    "gamma_parity (int_parity d) \<subseteq>
     gamma_parity (int_parity e)"
    using parity
    unfolding less_eq_parity_def
    by (rule gamma_parity_mono)
  have congruence_gamma:
    "gamma_congruence (int_congruence d) \<subseteq>
     gamma_congruence (int_congruence e)"
    using congruence
    unfolding less_eq_congruence_def congruence_le_iff_gamma .
  show ?thesis
    unfolding less_eq_congruence_def congruence_le_iff_gamma
    using parity_gamma congruence_gamma by auto
qed

lemma congruence_fact_of_int_dom_le_congruence:
  "congruence_fact_of_int_dom d <= int_congruence d"
  unfolding less_eq_congruence_def congruence_le_iff_gamma
  by auto

lemma congruence_lower_bound_le:
  fixes c m l n :: int
  assumes modulus: "0 < m"
      and lower: "l <= n"
      and congruent: "m dvd n - c"
  shows "l + ((c - l) mod m) <= n"
proof -
  obtain k where difference: "n - c = m * k"
    using congruent unfolding dvd_def by blast
  have reverse: "m dvd c - n"
    unfolding dvd_def
  proof
    show "c - n = m * (- k)"
      using difference by simp
  qed
  have residues:
    "(c - l) mod m = (n - l) mod m"
    using reverse by (simp add: mod_eq_dvd_iff)
  have nonnegative: "0 <= n - l"
    using lower by simp
  have remainder: "(n - l) mod m <= n - l"
    by (rule zmod_le_nonneg_dividend[OF nonnegative])
  from residues remainder show ?thesis by linarith
qed

lemma le_congruence_upper_bound:
  fixes c m n u :: int
  assumes modulus: "0 < m"
      and upper: "n <= u"
      and congruent: "m dvd n - c"
  shows "n <= u - ((u - c) mod m)"
proof -
  have residues:
    "(u - c) mod m = (u - n) mod m"
    using congruent by (simp add: mod_eq_dvd_iff)
  have nonnegative: "0 <= u - n"
    using upper by simp
  have remainder: "(u - n) mod m <= u - n"
    by (rule zmod_le_nonneg_dividend[OF nonnegative])
  from residues remainder show ?thesis by linarith
qed

lemma refine_ivl_with_congruence_cover:
  "gamma_ivl i \<inter> gamma_congruence fct \<subseteq>
   gamma_ivl (refine_ivl_with_congruence fct i)"
proof
  fix n
  assume member:
    "n \<in> gamma_ivl i \<inter> gamma_congruence fct"
  obtain l u where i: "i = Ivl l u"
    by (rule ivl_exhaustE)
  have normalized:
    "normalized_congruence_rep (Rep_congruence fct)"
    using Rep_congruence[of fct] by simp
  show
    "n \<in> gamma_ivl (refine_ivl_with_congruence fct i)"
  proof (cases "Rep_congruence fct")
    case None
    with member show ?thesis
      unfolding gamma_congruence_def by simp
  next
    case (Some cm)
    obtain c m where cm: "cm = (c, m)"
      by (cases cm)
    have rep: "Rep_congruence fct = Some (c, m)"
      using Some cm by simp
    have normalized':
      "normalized_congruence_rep (Some (c, m))"
      using normalized unfolding rep .
    from member have in_i: "n \<in> gamma_ivl i"
      by simp
    from member have congruent: "m dvd n - c"
      unfolding gamma_congruence_def rep by simp
    show ?thesis
    proof (cases "m = 0")
      case True
      from congruent True have n: "n = c" by simp
      have in_point:
        "n \<in> gamma_ivl (Ivl (Fin c) (Fin c))"
        using n by simp
      have in_i': "n \<in> gamma_ivl (Ivl l u)"
        using in_i unfolding i .
      have refined:
        "refine_ivl_with_congruence fct i =
         intersect_ivl (Ivl (Fin c) (Fin c)) (Ivl l u)"
        unfolding refine_ivl_with_congruence_def rep i
        using True by simp
      show ?thesis
        unfolding refined
        by (rule intersect_ivl_gamma[OF in_point in_i'])
    next
      case False
      have modulus: "0 < m"
        by (rule normalized_congruence_rep_nonzero[
              OF normalized' False])
      have lower:
        "congruence_lower_bound c m l <= Fin n"
        using in_i congruent modulus
        unfolding i
        by (cases l)
           (auto intro: congruence_lower_bound_le)
      have upper:
        "Fin n <= congruence_upper_bound c m u"
        using in_i congruent modulus
        unfolding i
        by (cases u)
           (auto intro: le_congruence_upper_bound)
      have in_hull:
        "n \<in> gamma_ivl
          (mk_ivl
            (congruence_lower_bound c m l)
            (congruence_upper_bound c m u))"
        using lower upper
        by (simp only: gamma_mk_ivl gamma_ivl.simps
            mem_Collect_eq)
      have in_i': "n \<in> gamma_ivl (Ivl l u)"
        using in_i unfolding i .
      have refined:
        "refine_ivl_with_congruence fct i =
         intersect_ivl
           (mk_ivl
             (congruence_lower_bound c m l)
             (congruence_upper_bound c m u))
           (Ivl l u)"
        unfolding refine_ivl_with_congruence_def rep i
        using False by simp
      show ?thesis
        unfolding refined
        by (rule intersect_ivl_gamma[OF in_hull in_i'])
    qed
  qed
qed

lemma refine_ivl_with_congruence_le:
  "refine_ivl_with_congruence fct i <= i"
proof (cases "Rep_congruence fct")
  case None
  then show ?thesis
    unfolding refine_ivl_with_congruence_def by simp
next
  case (Some cm)
  obtain c m where cm: "cm = (c, m)"
    by (cases cm)
  have rep: "Rep_congruence fct = Some (c, m)"
    using Some cm by simp
  obtain l u where i: "i = Ivl l u"
    by (rule ivl_exhaustE)
  show ?thesis
  proof (cases "m = 0")
    case True
    have refined:
      "refine_ivl_with_congruence fct i =
       intersect_ivl (Ivl (Fin c) (Fin c)) i"
      unfolding refine_ivl_with_congruence_def rep i
      using True by simp
    show ?thesis
      unfolding refined by (rule intersect_ivl_le2)
  next
    case False
    have refined:
      "refine_ivl_with_congruence fct i =
       intersect_ivl
         (mk_ivl
           (congruence_lower_bound c m l)
           (congruence_upper_bound c m u))
         i"
      unfolding refine_ivl_with_congruence_def rep i
      using False by simp
    show ?thesis
      unfolding refined by (rule intersect_ivl_le2)
  qed
qed

lemma normalize_refine_ivl_with_congruence [simp]:
  "normalize_ivl (refine_ivl_with_congruence fct i) =
   refine_ivl_with_congruence fct i"
  unfolding refine_ivl_with_congruence_def
  by (cases "Rep_congruence fct"; cases i)
     (auto simp only:
        refine_ivl_with_congruence_rep.simps
        normalize_ivl_bot
        normalize_ivl_intersect_ivl
        split: prod.splits if_splits)

lemma congruence_lower_bound_congruent:
  fixes c m l :: int
  shows
    "m dvd
     (l + ((c - l) mod m)) - c"
proof -
  have base:
    "m dvd (c - l) - ((c - l) mod m)"
    by (rule dvd_minus_mod)
  have negated:
    "m dvd - ((c - l) - ((c - l) mod m))"
    by (subst dvd_minus_iff) (rule base)
  have equal:
    "- ((c - l) - ((c - l) mod m)) =
     (l + ((c - l) mod m)) - c"
    by linarith
  from negated show ?thesis
    unfolding equal .
qed

lemma congruence_upper_bound_congruent:
  fixes c m u :: int
  shows
    "m dvd
     (u - ((u - c) mod m)) - c"
proof -
  have base:
    "m dvd (u - c) - ((u - c) mod m)"
    by (rule dvd_minus_mod)
  have equal:
    "(u - c) - ((u - c) mod m) =
     (u - ((u - c) mod m)) - c"
    by linarith
  from base show ?thesis
    unfolding equal .
qed

lemma congruence_lower_bound_mono:
  fixes c1 m1 c2 m2 :: int
    and l1 l2 :: eint
  assumes m1: "0 < m1"
      and m2: "0 < m2"
      and moduli: "m2 dvd m1"
      and residues: "m2 dvd c1 - c2"
      and bounds: "l2 <= l1"
  shows
    "congruence_lower_bound c2 m2 l2 <=
     congruence_lower_bound c1 m1 l1"
proof (cases l1)
  case MinInf
  then show ?thesis
    using bounds by (cases l2) simp_all
next
  case (Fin a)
  have l1: "l1 = Fin a"
    by (rule Fin)
  show ?thesis
  proof (cases l2)
    case MinInf
    then show ?thesis by simp
  next
    case (Fin b)
    have ba: "b <= a"
      using bounds l1 Fin by simp
    let ?n = "a + ((c1 - a) mod m1)"
    have a_le_n: "a <= ?n"
      using pos_mod_sign[OF m1, of "c1 - a"]
      by linarith
    have congruent1: "m1 dvd ?n - c1"
      by (rule congruence_lower_bound_congruent)
    have congruent2a: "m2 dvd ?n - c1"
      by (rule dvd_trans[OF moduli congruent1])
    have congruent2: "m2 dvd ?n - c2"
    proof -
      have combined:
        "m2 dvd (?n - c1) + (c1 - c2)"
        by (rule dvd_add[OF congruent2a residues])
      have equal:
        "(?n - c1) + (c1 - c2) = ?n - c2"
        by linarith
      from combined show ?thesis
        unfolding equal .
    qed
    have b_le_n: "b <= ?n"
      using ba a_le_n by linarith
    have
      "b + ((c2 - b) mod m2) <= ?n"
      by (rule congruence_lower_bound_le[
            OF m2 b_le_n congruent2])
    with l1 Fin show ?thesis by simp
  next
    case PlusInf
    with bounds l1 show ?thesis by simp
  qed
next
  case PlusInf
  then show ?thesis by simp
qed

lemma congruence_upper_bound_mono:
  fixes c1 m1 c2 m2 :: int
    and u1 u2 :: eint
  assumes m1: "0 < m1"
      and m2: "0 < m2"
      and moduli: "m2 dvd m1"
      and residues: "m2 dvd c1 - c2"
      and bounds: "u1 <= u2"
  shows
    "congruence_upper_bound c1 m1 u1 <=
     congruence_upper_bound c2 m2 u2"
proof (cases u1)
  case MinInf
  then show ?thesis by simp
next
  case (Fin a)
  have u1: "u1 = Fin a"
    by (rule Fin)
  show ?thesis
  proof (cases u2)
    case MinInf
    with bounds u1 show ?thesis by simp
  next
    case (Fin b)
    have ab: "a <= b"
      using bounds u1 Fin by simp
    let ?n = "a - ((a - c1) mod m1)"
    have n_le_a: "?n <= a"
      using pos_mod_sign[OF m1, of "a - c1"]
      by linarith
    have congruent1: "m1 dvd ?n - c1"
      by (rule congruence_upper_bound_congruent)
    have congruent2a: "m2 dvd ?n - c1"
      by (rule dvd_trans[OF moduli congruent1])
    have congruent2: "m2 dvd ?n - c2"
    proof -
      have combined:
        "m2 dvd (?n - c1) + (c1 - c2)"
        by (rule dvd_add[OF congruent2a residues])
      have equal:
        "(?n - c1) + (c1 - c2) = ?n - c2"
        by linarith
      from combined show ?thesis
        unfolding equal .
    qed
    have n_le_b: "?n <= b"
      using n_le_a ab by linarith
    have
      "?n <= b - ((b - c2) mod m2)"
      by (rule le_congruence_upper_bound[
            OF m2 n_le_b congruent2])
    with u1 Fin show ?thesis by simp
  next
    case PlusInf
    then show ?thesis by simp
  qed
next
  case PlusInf
  then show ?thesis
    using bounds by (cases u2) simp_all
qed

lemma intersect_ivl_eq_bot_if_disjoint:
  assumes
    "gamma_ivl a \<inter> gamma_ivl b = {}"
  shows "intersect_ivl a b = bot"
proof -
  have empty:
    "gamma_ivl (intersect_ivl a b) = {}"
    using assms gamma_intersect_ivl_exact by simp
  have bottom:
    "is_bottom_ivl (intersect_ivl a b)"
    using empty is_bottom_ivl_correct by blast
  have normalized:
    "normalize_ivl (intersect_ivl a b) =
     intersect_ivl a b"
    by simp
  show ?thesis
    using normalize_ivl_bot_case[OF bottom] normalized
    by simp
qed

lemma refine_ivl_with_congruence_mono:
  assumes "fct1 <= fct2" "i1 <= i2"
  shows
    "refine_ivl_with_congruence fct1 i1 <=
     refine_ivl_with_congruence fct2 i2"
proof -
  have rep_le:
    "congruence_le_rep
       (Rep_congruence fct1)
       (Rep_congruence fct2)"
    using assms(1)
    unfolding less_eq_congruence_def congruence_le_def .
  have normalized1:
    "normalized_congruence_rep (Rep_congruence fct1)"
    using Rep_congruence[of fct1] by simp
  have normalized2:
    "normalized_congruence_rep (Rep_congruence fct2)"
    using Rep_congruence[of fct2] by simp
  obtain l1 u1 where i1: "i1 = Ivl l1 u1"
    by (rule ivl_exhaustE)
  obtain l2 u2 where i2: "i2 = Ivl l2 u2"
    by (rule ivl_exhaustE)
  have bounds: "l2 <= l1" "u1 <= u2"
    using assms(2)
    unfolding i1 i2 less_eq_ivl_def
    by simp_all
  have singleton_le_iff:
    "Ivl (Fin n) (Fin n) <= i \<longleftrightarrow>
     n \<in> gamma_ivl i"
    for n i
    by (cases i) (simp add: less_eq_ivl_def)
  show ?thesis
  proof (cases "Rep_congruence fct1")
    case None
    then show ?thesis
      unfolding refine_ivl_with_congruence_def by simp
  next
    case (Some cm1)
    obtain c1 m1 where cm1: "cm1 = (c1, m1)"
      by (cases cm1)
    have rep1: "Rep_congruence fct1 = Some (c1, m1)"
      using Some cm1 by simp
    show ?thesis
    proof (cases "Rep_congruence fct2")
      case None
      with rep_le rep1 show ?thesis by simp
    next
      case (Some cm2)
      obtain c2 m2 where cm2: "cm2 = (c2, m2)"
        by (cases cm2)
      have rep2: "Rep_congruence fct2 = Some (c2, m2)"
        using Some cm2 by simp
      have relation:
        "m2 dvd m1" "m2 dvd c1 - c2"
        using rep_le unfolding rep1 rep2
        by simp_all
      have normalized1':
        "normalized_congruence_rep (Some (c1, m1))"
        using normalized1 unfolding rep1 .
      have normalized2':
        "normalized_congruence_rep (Some (c2, m2))"
        using normalized2 unfolding rep2 .
      show ?thesis
      proof (cases "m1 = 0")
        case True
        show ?thesis
        proof (cases "m2 = 0")
          case True2: True
          have residues: "c1 = c2"
            using relation(2) True2 by simp
          have point_le:
            "Ivl (Fin c1) (Fin c1) <=
             Ivl (Fin c2) (Fin c2)"
            using residues by simp
          have refined1:
            "refine_ivl_with_congruence fct1 i1 =
             intersect_ivl (Ivl (Fin c1) (Fin c1)) i1"
            unfolding refine_ivl_with_congruence_def rep1 i1
            using True by simp
          have refined2:
            "refine_ivl_with_congruence fct2 i2 =
             intersect_ivl (Ivl (Fin c2) (Fin c2)) i2"
            unfolding refine_ivl_with_congruence_def rep2 i2
            using True2 by simp
          show ?thesis
            unfolding refined1 refined2
            by (rule intersect_ivl_mono[OF point_le assms(2)])
        next
          case False
          have modulus2: "0 < m2"
            by (rule normalized_congruence_rep_nonzero(3)
                  [OF normalized2' False])
          show ?thesis
          proof (cases "c1 \<in> gamma_ivl i1")
            case False
            have empty:
              "gamma_ivl (Ivl (Fin c1) (Fin c1)) \<inter>
               gamma_ivl i1 = {}"
              using False by auto
            have source_refined:
              "refine_ivl_with_congruence fct1 i1 =
               intersect_ivl
                 (Ivl (Fin c1) (Fin c1)) i1"
              unfolding refine_ivl_with_congruence_def rep1 i1
              using True by simp
            have source_bottom:
              "refine_ivl_with_congruence fct1 i1 = bot"
              unfolding source_refined
              by (rule intersect_ivl_eq_bot_if_disjoint[OF empty])
            then show ?thesis by simp
          next
            case TrueMember: True
            have c1_i2: "c1 \<in> gamma_ivl i2"
              by (rule subsetD[OF gamma_ivl_mono[OF assms(2)]
                    TrueMember])
            have c1_fct2: "c1 \<in> gamma_congruence fct2"
              unfolding gamma_congruence_def rep2
              using relation(2) by simp
            have c1_target:
              "c1 \<in> gamma_ivl
                (refine_ivl_with_congruence fct2 i2)"
              by (rule subsetD[
                    OF refine_ivl_with_congruence_cover])
                 (use c1_i2 c1_fct2 in auto)
            have point_le:
              "Ivl (Fin c1) (Fin c1) <=
               refine_ivl_with_congruence fct2 i2"
              using c1_target singleton_le_iff by blast
            have source_refined:
              "refine_ivl_with_congruence fct1 i1 =
               intersect_ivl
                 (Ivl (Fin c1) (Fin c1)) i1"
              unfolding refine_ivl_with_congruence_def rep1 i1
              using True by simp
            have source_le:
              "refine_ivl_with_congruence fct1 i1 <=
               Ivl (Fin c1) (Fin c1)"
              unfolding source_refined
              by (rule intersect_ivl_le1)
            show ?thesis
              by (rule order_trans[OF source_le point_le])
          qed
        qed
      next
        case False
        have modulus1: "0 < m1"
          by (rule normalized_congruence_rep_nonzero(3)
                [OF normalized1' False])
        have m2_nonzero: "m2 \<noteq> 0"
          using relation(1) modulus1 by auto
        have modulus2: "0 < m2"
          by (rule normalized_congruence_rep_nonzero(3)
                [OF normalized2' m2_nonzero])
        have lower:
          "congruence_lower_bound c2 m2 l2 <=
           congruence_lower_bound c1 m1 l1"
          by (rule congruence_lower_bound_mono[
                OF modulus1 modulus2 relation(1)
                  relation(2) bounds(1)])
        have upper:
          "congruence_upper_bound c1 m1 u1 <=
           congruence_upper_bound c2 m2 u2"
          by (rule congruence_upper_bound_mono[
                OF modulus1 modulus2 relation(1)
                  relation(2) bounds(2)])
        have raw_hull:
          "Ivl
             (congruence_lower_bound c1 m1 l1)
             (congruence_upper_bound c1 m1 u1) <=
           Ivl
             (congruence_lower_bound c2 m2 l2)
             (congruence_upper_bound c2 m2 u2)"
          using lower upper
          by (simp add: less_eq_ivl_def)
        have hull:
          "mk_ivl
             (congruence_lower_bound c1 m1 l1)
             (congruence_upper_bound c1 m1 u1) <=
           mk_ivl
             (congruence_lower_bound c2 m2 l2)
             (congruence_upper_bound c2 m2 u2)"
          by (rule mk_ivl_mono[OF raw_hull])
        have refined1:
          "refine_ivl_with_congruence fct1 i1 =
           intersect_ivl
             (mk_ivl
               (congruence_lower_bound c1 m1 l1)
               (congruence_upper_bound c1 m1 u1))
             i1"
          unfolding refine_ivl_with_congruence_def rep1 i1
          using False by simp
        have refined2:
          "refine_ivl_with_congruence fct2 i2 =
           intersect_ivl
             (mk_ivl
               (congruence_lower_bound c2 m2 l2)
               (congruence_upper_bound c2 m2 u2))
             i2"
          unfolding refine_ivl_with_congruence_def rep2 i2
          using m2_nonzero by simp
        show ?thesis
          unfolding refined1 refined2
          by (rule intersect_ivl_mono[OF hull assms(2)])
      qed
    qed
  qed
qed

lemma parity_fact_of_congruence_sound:
  "gamma_congruence fct \<subseteq>
   gamma_parity (parity_fact_of_congruence fct)"
proof
  fix n
  assume member: "n \<in> gamma_congruence fct"
  show
    "n \<in> gamma_parity (parity_fact_of_congruence fct)"
  proof (cases "Rep_congruence fct")
    case None
    with member show ?thesis
      unfolding gamma_congruence_def by simp
  next
    case (Some cm)
    obtain c m where cm: "cm = (c, m)"
      by (cases cm)
    have rep: "Rep_congruence fct = Some (c, m)"
      using Some cm by simp
    have congruent: "m dvd n - c"
      using member
      unfolding gamma_congruence_def rep by simp
    show ?thesis
    proof (cases "m = 0 \<or> even m")
      case True
      have same_parity: "even n = even c"
      proof (cases "m = 0")
        case True
        with congruent have "n = c" by simp
        then show ?thesis by simp
      next
        case False
        with True have even_m: "even m" by simp
        have even_difference: "even (n - c)"
          using even_m congruent
          by (meson dvd_trans)
        then show ?thesis
          by (simp add: even_diff_iff)
      qed
      show ?thesis
        unfolding parity_fact_of_congruence_def rep
        using True same_parity
        by auto
    next
      case False
      then show ?thesis
        unfolding parity_fact_of_congruence_def rep
        by simp
    qed
  qed
qed

lemma parity_fact_of_congruence_mono:
  assumes "fct1 <= fct2"
  shows
    "parity_fact_of_congruence fct1 <=
     parity_fact_of_congruence fct2"
proof -
  have rep_le:
    "congruence_le_rep
       (Rep_congruence fct1)
       (Rep_congruence fct2)"
    using assms
    unfolding less_eq_congruence_def congruence_le_def .
  show ?thesis
  proof (cases "Rep_congruence fct1")
    case None
    then show ?thesis
      unfolding parity_fact_of_congruence_def
        less_eq_parity_def
      by simp
  next
    case (Some cm1)
    obtain c1 m1 where cm1: "cm1 = (c1, m1)"
      by (cases cm1)
    have rep1: "Rep_congruence fct1 = Some (c1, m1)"
      using Some cm1 by simp
    show ?thesis
    proof (cases "Rep_congruence fct2")
      case None
      with rep_le rep1 show ?thesis by simp
    next
      case (Some cm2)
      obtain c2 m2 where cm2: "cm2 = (c2, m2)"
        by (cases cm2)
      have rep2: "Rep_congruence fct2 = Some (c2, m2)"
        using Some cm2 by simp
      have relation:
        "m2 dvd m1" "m2 dvd c1 - c2"
        using rep_le unfolding rep1 rep2
        by simp_all
      show ?thesis
      proof (cases "m2 = 0 \<or> even m2")
        case False
        have target_top:
          "parity_fact_of_congruence fct2 = (top :: parity)"
          unfolding parity_fact_of_congruence_def rep2
            top_parity_def
          using False by simp
        show ?thesis
          unfolding target_top by simp
      next
        case True
        have source_precise: "m1 = 0 \<or> even m1"
        proof (cases "m2 = 0")
          case True
          with relation(1) have "m1 = 0" by simp
          then show ?thesis by simp
        next
          case False
          with True have even_m2: "even m2" by simp
          have "even m1"
            using even_m2 relation(1)
            by (meson dvd_trans)
          then show ?thesis by simp
        qed
        have same_parity: "even c1 = even c2"
        proof (cases "m2 = 0")
          case True
          with relation(2) have "c1 = c2" by simp
          then show ?thesis by simp
        next
          case False
          with True have even_m2: "even m2" by simp
          have even_difference: "even (c1 - c2)"
            using even_m2 relation(2)
            by (meson dvd_trans)
          then show ?thesis
            by (simp add: even_diff_iff)
        qed
        have equal_facts:
          "parity_fact_of_congruence fct1 =
           parity_fact_of_congruence fct2"
          unfolding parity_fact_of_congruence_def rep1 rep2
          using True source_precise same_parity
          by auto
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma gamma_refine_parity_with_congruence [simp]:
  "gamma_parity (refine_parity_with_congruence fct p) =
   gamma_parity (parity_fact_of_congruence fct) \<inter>
   gamma_parity p"
  by (simp add: refine_parity_with_congruence_def)

lemma refine_parity_with_congruence_le:
  "refine_parity_with_congruence fct p <= p"
  unfolding refine_parity_with_congruence_def
  by (rule intersect_parity_le2)

lemma refine_parity_with_congruence_mono:
  assumes "fct1 <= fct2" "p1 <= p2"
  shows
    "refine_parity_with_congruence fct1 p1 <=
     refine_parity_with_congruence fct2 p2"
  unfolding refine_parity_with_congruence_def
  by (rule intersect_parity_mono)
     (use assms parity_fact_of_congruence_mono in auto)

lemma refine_congruence_with_congruence_le:
  assumes "fct <= c"
  shows "refine_congruence_with_congruence fct c <= c"
  using assms
  unfolding refine_congruence_with_congruence_def .

lemma refine_congruence_with_congruence_mono:
  assumes "fct1 <= fct2"
  shows
    "refine_congruence_with_congruence fct1 c1 <=
     refine_congruence_with_congruence fct2 c2"
  using assms
  unfolding refine_congruence_with_congruence_def .

definition refine_congruence :: "int_dom => int_dom" where
  "refine_congruence d =
     (let fct = congruence_fact_of_int_dom d
      in d\<lparr>
           int_ivl :=
             refine_ivl_with_congruence fct (int_ivl d),
           int_parity :=
             refine_parity_with_congruence fct (int_parity d),
           int_congruence :=
             refine_congruence_with_congruence
               fct (int_congruence d)
         \<rparr>)"

lemma refine_congruence_exact:
  "gamma_int_dom (refine_congruence d) = gamma_int_dom d"
proof -
  let ?fct = "congruence_fact_of_int_dom d"
  have ivl_cover:
    "gamma_ivl (int_ivl d) \<inter>
     gamma_congruence ?fct \<subseteq>
     gamma_ivl
       (refine_ivl_with_congruence ?fct (int_ivl d))"
    by (rule refine_ivl_with_congruence_cover)
  have ivl_subset:
    "gamma_ivl
       (refine_ivl_with_congruence ?fct (int_ivl d))
     \<subseteq> gamma_ivl (int_ivl d)"
    by (rule gamma_ivl_mono)
       (rule refine_ivl_with_congruence_le)
  have parity_cover:
    "gamma_congruence ?fct \<subseteq>
     gamma_parity
       (refine_parity_with_congruence
         ?fct (int_parity d))"
  proof -
    have fact_sound:
      "gamma_congruence ?fct \<subseteq>
       gamma_parity (parity_fact_of_congruence ?fct)"
      by (rule parity_fact_of_congruence_sound)
    show ?thesis
      using fact_sound
      by auto
  qed
  show ?thesis
    unfolding refine_congruence_def gamma_int_dom_def
      Let_def refine_congruence_with_congruence_def
    using ivl_cover ivl_subset parity_cover
    by auto
qed

lemma refine_congruence_reductive:
  "refine_congruence d <= d"
  unfolding refine_congruence_def Let_def
  by (simp add: less_eq_int_dom_ext_def
        refine_ivl_with_congruence_le
        refine_parity_with_congruence_le
        refine_congruence_with_congruence_le
        congruence_fact_of_int_dom_le_congruence)

lemma refine_congruence_mono:
  "mono refine_congruence"
proof (rule monoI)
  fix d e :: int_dom
  assume de: "d <= e"
  from de have components:
    "int_sign d <= int_sign e"
    "int_ivl d <= int_ivl e"
    "int_parity d <= int_parity e"
    "int_congruence d <= int_congruence e"
    by (simp_all add: less_eq_int_dom_ext_def)
  have fct_le:
    "congruence_fact_of_int_dom d <=
     congruence_fact_of_int_dom e"
    by (rule congruence_fact_of_int_dom_mono[OF de])
  show "refine_congruence d <= refine_congruence e"
    unfolding refine_congruence_def Let_def
    by (simp add: less_eq_int_dom_ext_def
          components(1)
          refine_ivl_with_congruence_mono[
            OF fct_le components(2)]
          refine_parity_with_congruence_mono[
            OF fct_le components(3)]
          refine_congruence_with_congruence_mono[
            OF fct_le])
qed

lemma refine_congruence_reduction_step:
  "int_reduction_step refine_congruence"
  unfolding int_reduction_step_def
  using refine_congruence_exact
    refine_congruence_reductive
    refine_congruence_mono
  by blast

definition refinement_steps :: "(int_dom => int_dom) list" where
  "refinement_steps = [refine_interval, refine_congruence]"

definition refine_round :: "int_dom => int_dom" where
  "refine_round = apply_reduction_steps refinement_steps"

lemma refine_round_reduction_step:
  "int_reduction_step refine_round"
  unfolding refine_round_def
  by (rule int_reduction_steps)
     (simp add: refinement_steps_def
        int_reduction_step_refine_interval
        refine_congruence_reduction_step)


section \<open>Refinement control\<close>

datatype refine_mode =
    Refine_Never
  | Refine_Once
  | Refine_Fixpoint

definition canonical_refine_step :: "int_dom => int_dom" where
  "canonical_refine_step d =
     (let d' = refine_round d
      in if is_bot d' then bot else d')"

definition refine_fix_option :: "int_dom => int_dom option" where
  "refine_fix_option d =
     while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step
       d"

text \<open>
  The option result is \<open>None\<close> exactly when structural iteration does not
  stabilize. The total logical wrapper returns the input in that branch; generated
  execution remains in the structural-equality loop.
\<close>

definition refine_fix :: "int_dom => int_dom" where
  "refine_fix d =
     (case refine_fix_option d of
        Some r => r
      | None => d)"

definition refine :: "refine_mode => int_dom => int_dom" where
  "refine mode d =
     (case mode of
        Refine_Never => d
      | Refine_Once => refine_round d
      | Refine_Fixpoint => refine_fix d)"


lemma canonical_refine_step_exact:
  "gamma_int_dom (canonical_refine_step d) = gamma_int_dom d"
proof (cases "is_bot (refine_round d)")
  case True
  have round_empty:
    "gamma_int_dom (refine_round d) = {}"
    using True
    by (simp add: is_bottom_int_dom_correct)
  have input_empty: "gamma_int_dom d = {}"
    using round_empty
      int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
  have bottom_empty:
    "gamma_int_dom (bot :: int_dom) = {}"
  proof -
    have "gamma (bot :: int_dom) = {}"
      by (rule gamma_bot)
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding canonical_refine_step_def Let_def
    using True input_empty bottom_empty by simp
next
  case False
  show ?thesis
    unfolding canonical_refine_step_def Let_def
    using False
      int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
qed


lemma canonical_refine_step_collapses_bottom:
  assumes "is_bot (refine_round d)"
  shows "canonical_refine_step d = bot"
  using assms
  unfolding canonical_refine_step_def Let_def
  by simp

lemma refine_fix_option_exact:
  assumes result: "refine_fix_option d = Some r"
  shows "gamma_int_dom r = gamma_int_dom d"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  have invariant:
    "\<And>x.
       gamma_int_dom x = gamma_int_dom d \<Longrightarrow>
       canonical_refine_step x \<noteq> x \<Longrightarrow>
       gamma_int_dom (canonical_refine_step x) =
       gamma_int_dom d"
    using canonical_refine_step_exact by simp
  show ?thesis
  proof (rule while_option_rule[
      where P="\<lambda>x.
        gamma_int_dom x = gamma_int_dom d"
        and b="\<lambda>x.
          canonical_refine_step x \<noteq> x"
        and c=canonical_refine_step
        and s=d
        and t=r])
    fix x
    assume "gamma_int_dom x = gamma_int_dom d"
      "canonical_refine_step x \<noteq> x"
    then show
      "gamma_int_dom (canonical_refine_step x) =
       gamma_int_dom d"
      using canonical_refine_step_exact by simp
  next
    show
      "while_option
        (\<lambda>x. canonical_refine_step x \<noteq> x)
        canonical_refine_step d = Some r"
      by (rule loop)
  next
    show "gamma_int_dom d = gamma_int_dom d"
      by simp
  qed
qed

lemma refine_fix_option_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "canonical_refine_step r = r"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  have "\<not> canonical_refine_step r \<noteq> r"
    by (rule while_option_stop[OF loop])
  then show ?thesis by simp
qed

lemma refine_round_bot [simp]:
  "refine_round (bot :: int_dom) = bot"
proof (rule antisym)
  show "refine_round (bot :: int_dom) <= bot"
    by (rule int_reduction_step_reductive[
          OF refine_round_reduction_step])
  show "bot <= refine_round (bot :: int_dom)"
    by simp
qed

lemma refine_fix_option_round_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "refine_round r = r"
proof -
  have stable: "canonical_refine_step r = r"
    by (rule refine_fix_option_stable[OF result])
  show ?thesis
  proof (cases "is_bot (refine_round r)")
    case True
    have "r = bot"
      using stable True
      unfolding canonical_refine_step_def Let_def
      by simp
    then show ?thesis by simp
  next
    case False
    with stable show ?thesis
      unfolding canonical_refine_step_def Let_def
      by simp
  qed
qed


lemma refine_fix_exact [simp]:
  "gamma_int_dom (refine_fix d) = gamma_int_dom d"
proof (cases "refine_fix_option d")
  case None
  then show ?thesis
    unfolding refine_fix_def by simp
next
  case (Some r)
  have "gamma_int_dom r = gamma_int_dom d"
    by (rule refine_fix_option_exact[OF Some])
  with Some show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_fix_round_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "refine_round (refine_fix d) = refine_fix d"
proof -
  have "refine_round r = r"
    by (rule refine_fix_option_round_stable[OF result])
  with result show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_never [simp]:
  "refine Refine_Never d = d"
  by (simp add: refine_def)

lemma refine_once [simp]:
  "refine Refine_Once d = refine_round d"
  by (simp add: refine_def)

lemma refine_fixpoint [simp]:
  "refine Refine_Fixpoint d = refine_fix d"
  by (simp add: refine_def)

lemma refine_once_reduction_step:
  "int_reduction_step (refine Refine_Once)"
proof -
  have "refine Refine_Once = refine_round"
    by (rule ext) simp
  then show ?thesis
    by (simp add: refine_round_reduction_step)
qed

lemma refine_once_exact:
  "gamma_int_dom (refine Refine_Once d) = gamma_int_dom d"
  by (rule int_reduction_step_exact[
        OF refine_once_reduction_step])

lemma refine_once_reductive:
  "refine Refine_Once d <= d"
  by (rule int_reduction_step_reductive[
        OF refine_once_reduction_step])

lemma refine_once_mono:
  "mono (refine Refine_Once)"
  by (rule int_reduction_step_mono[
        OF refine_once_reduction_step])

lemma refine_fixpoint_exact:
  "gamma_int_dom (refine Refine_Fixpoint d) =
   gamma_int_dom d"
  by simp

lemma refine_fixpoint_round_stable:
  assumes "refine_fix_option d = Some r"
  shows
    "refine_round (refine Refine_Fixpoint d) =
     refine Refine_Fixpoint d"
  using refine_fix_round_stable[OF assms] by simp

lemma refine_exact:
  "gamma_int_dom (refine mode d) = gamma_int_dom d"
proof (cases mode)
  case Refine_Never
  then show ?thesis by simp
next
  case Refine_Once
  then show ?thesis
    using int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
next
  case Refine_Fixpoint
  then show ?thesis by simp
qed

lemma canonical_refine_step_reductive:
  "canonical_refine_step d <= d"
proof (cases "is_bot (refine_round d)")
  case True
  then show ?thesis
    unfolding canonical_refine_step_def Let_def
    by simp
next
  case False
  then show ?thesis
    unfolding canonical_refine_step_def Let_def
    using int_reduction_step_reductive[OF refine_round_reduction_step]
    by simp
qed

lemma refine_fix_option_reductive:
  assumes result: "refine_fix_option d = Some r"
  shows "r <= d"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  show ?thesis
  proof (rule while_option_rule[
      where P="\<lambda>x. x <= d"
        and b="\<lambda>x. canonical_refine_step x \<noteq> x"
        and c=canonical_refine_step
        and s=d
        and t=r])
    fix x
    assume "x <= d" "canonical_refine_step x \<noteq> x"
    then show "canonical_refine_step x <= d"
      using canonical_refine_step_reductive[of x] by simp
  next
    show
      "while_option
        (\<lambda>x. canonical_refine_step x \<noteq> x)
        canonical_refine_step d = Some r"
      by (rule loop)
  next
    show "d <= d" by simp
  qed
qed

lemma refine_fix_reductive [simp]:
  "refine_fix d <= d"
proof (cases "refine_fix_option d")
  case None
  then show ?thesis
    unfolding refine_fix_def by simp
next
  case (Some r)
  have "r <= d"
    by (rule refine_fix_option_reductive[OF Some])
  with Some show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_fixpoint_reductive:
  "refine Refine_Fixpoint d <= d"
  by simp

lemma refine_reductive:
  "refine mode d <= d"
proof (cases mode)
  case Refine_Never
  then show ?thesis by simp
next
  case Refine_Once
  then show ?thesis
    using refine_once_reductive by simp
next
  case Refine_Fixpoint
  then show ?thesis by simp
qed

end
