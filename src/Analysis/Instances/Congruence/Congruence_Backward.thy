theory Congruence_Backward
  imports
    Congruence_Arithmetic
    Voblint_Core.Exec_Backward
    "HOL-Computational_Algebra.Euclidean_Algorithm"
begin

section \<open>Exact congruence intersection\<close>

text \<open>
  Intersecting two non-singleton congruence classes is the executable Chinese
  remainder construction. The Bezout coefficient computes one shared residue;
  the least common multiple is the period of every shared solution.
\<close>

fun intersect_congruence_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "intersect_congruence_rep None y = None"
| "intersect_congruence_rep x None = None"
| "intersect_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     normalize_congruence_rep
       (if m1 = 0 then
          if m2 dvd c1 - c2 then Some (c1, 0) else None
        else if m2 = 0 then
          if m1 dvd c2 - c1 then Some (c2, 0) else None
        else
          let g = gcd m1 m2
          in if g dvd c2 - c1 then
               let s = fst (bezout_coefficients m1 m2);
                   q = (c2 - c1) div g
               in Some (c1 + m1 * (q * s), lcm m1 m2)
             else None)"

lemma normalized_intersect_congruence_rep [simp]:
  "normalized_congruence_rep (intersect_congruence_rep x y)"
  by (cases x; cases y)
     (auto simp: split_def split: if_splits prod.splits)

lift_definition intersect_congruence ::
    "congruence => congruence => congruence"
  is intersect_congruence_rep
  by simp

lemma bezout_shared_residue:
  assumes compatible: "gcd m1 m2 dvd c2 - c1"
  defines
    "q == (c2 - c1) div gcd m1 m2"
  shows
    "m1 dvd
       (c1 + m1 * (q * fst (bezout_coefficients m1 m2))) - c1 \<and>
     m2 dvd
       (c1 + m1 * (q * fst (bezout_coefficients m1 m2))) - c2"
proof (intro conjI)
  show
    "m1 dvd
      c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c1"
    by simp
  have bezout:
    "fst (bezout_coefficients m1 m2) * m1 +
     snd (bezout_coefficients m1 m2) * m2 =
     gcd m1 m2"
    by (rule bezout_coefficients_fst_snd)
  have quotient:
    "q * gcd m1 m2 = c2 - c1"
    unfolding q_def
    using dvd_mult_div_cancel[OF compatible]
    by (simp add: mult.commute)
  have scaled0:
    "q * (fst (bezout_coefficients m1 m2) * m1 +
       snd (bezout_coefficients m1 m2) * m2) =
     q * gcd m1 m2"
    by (rule arg_cong[OF bezout])
  have scaled:
    "m1 * (q * fst (bezout_coefficients m1 m2)) +
     m2 * (q * snd (bezout_coefficients m1 m2)) =
     q * gcd m1 m2"
    using scaled0 by (simp add: algebra_simps)
  show
    "m2 dvd
      c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c2"
    unfolding dvd_def
  proof (rule exI[of _ "- q * snd (bezout_coefficients m1 m2)"])
    show
      "c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c2 =
       m2 * (- q * snd (bezout_coefficients m1 m2))"
      using scaled quotient by (simp add: algebra_simps)
  qed
qed


lemma gamma_intersect_congruence_rep:
  assumes normalized_x: "normalized_congruence_rep x"
      and normalized_y: "normalized_congruence_rep y"
  shows
    "gamma_congruence_rep (intersect_congruence_rep x y) =
     gamma_congruence_rep x \<inter> gamma_congruence_rep y"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some cm1)
  note x_some = Some
  obtain c1 m1 where cm1: "cm1 = (c1, m1)"
    by (cases cm1)
  show ?thesis
  proof (cases y)
    case None
    with x_some show ?thesis by simp
  next
    case (Some cm2)
    note y_some = Some
    obtain c2 m2 where cm2: "cm2 = (c2, m2)"
      by (cases cm2)
    show ?thesis
    proof (cases "m1 = 0")
      case True
      with x_some y_some cm1 cm2 show ?thesis
        by auto
    next
      case m1_nonzero: False
      show ?thesis
      proof (cases "m2 = 0")
        case True
        with x_some y_some cm1 cm2 show ?thesis
          by auto
      next
        case m2_nonzero: False
        let ?g = "gcd m1 m2"
        let ?q = "(c2 - c1) div ?g"
        let ?s = "fst (bezout_coefficients m1 m2)"
        let ?z = "c1 + m1 * (?q * ?s)"
        show ?thesis
        proof (cases "?g dvd c2 - c1")
          case incompatible: False
          have empty:
            "{n. m1 dvd n - c1} \<inter>
             {n. m2 dvd n - c2} = {}"
          proof (rule ccontr)
            assume
              "{n. m1 dvd n - c1} \<inter>
               {n. m2 dvd n - c2} ~= {}"
            then obtain n where
              n1: "m1 dvd n - c1" and
              n2: "m2 dvd n - c2"
              by blast
            have g1: "?g dvd n - c1"
              using gcd_dvd1 n1 by (rule dvd_trans)
            have g2: "?g dvd n - c2"
              using gcd_dvd2 n2 by (rule dvd_trans)
            have "?g dvd (n - c1) - (n - c2)"
              by (rule dvd_diff[OF g1 g2])
            then have "?g dvd c2 - c1"
              by simp
            with incompatible show False by contradiction
          qed
          with x_some y_some cm1 cm2 m1_nonzero m2_nonzero
            incompatible
          show ?thesis by simp
        next
          case compatible: True
          have shared:
            "m1 dvd ?z - c1 \<and> m2 dvd ?z - c2"
            by (rule bezout_shared_residue[OF compatible])
          have classes:
            "{n. lcm m1 m2 dvd n - ?z} =
             {n. m1 dvd n - c1} \<inter>
             {n. m2 dvd n - c2}"
          proof
            show
              "{n. lcm m1 m2 dvd n - ?z} \<subseteq>
               {n. m1 dvd n - c1} \<inter>
               {n. m2 dvd n - c2}"
            proof
              fix n
              assume n: "n : {n. lcm m1 m2 dvd n - ?z}"
              have lcm_dvd: "lcm m1 m2 dvd n - ?z"
                using n by simp
              have n1: "m1 dvd n - ?z"
                using dvd_lcm1 lcm_dvd by (rule dvd_trans)
              have n2: "m2 dvd n - ?z"
                using dvd_lcm2 lcm_dvd by (rule dvd_trans)
              have "m1 dvd (n - ?z) + (?z - c1)"
                by (rule dvd_add[OF n1 shared[THEN conjunct1]])
              moreover have "m2 dvd (n - ?z) + (?z - c2)"
                by (rule dvd_add[OF n2 shared[THEN conjunct2]])
              ultimately show
                "n : {n. m1 dvd n - c1} \<inter>
                     {n. m2 dvd n - c2}"
                by simp
            qed
            show
              "{n. m1 dvd n - c1} \<inter>
               {n. m2 dvd n - c2} \<subseteq>
               {n. lcm m1 m2 dvd n - ?z}"
            proof
              fix n
              assume n:
                "n : {n. m1 dvd n - c1} \<inter>
                     {n. m2 dvd n - c2}"
              have n1: "m1 dvd n - c1"
                using n by simp
              have n2: "m2 dvd n - c2"
                using n by simp
              have z1: "m1 dvd ?z - c1"
                using shared by simp
              have z2: "m2 dvd ?z - c2"
                using shared by simp
              have d1: "m1 dvd (n - c1) - (?z - c1)"
                by (rule dvd_diff[OF n1 z1])
              have d2: "m2 dvd (n - c2) - (?z - c2)"
                by (rule dvd_diff[OF n2 z2])
              have d1': "m1 dvd n - ?z"
                using d1 by (simp add: algebra_simps)
              have d2': "m2 dvd n - ?z"
                using d2 by (simp add: algebra_simps)
              have "lcm m1 m2 dvd n - ?z"
                by (rule lcm_least[OF d1' d2'])
              then show "n : {n. lcm m1 m2 dvd n - ?z}"
                by simp
            qed
          qed
          have normalized_gamma:
            "gamma_congruence_rep
               (normalize_congruence_rep
                 (Some (?z, lcm m1 m2))) =
             {n. lcm m1 m2 dvd n - ?z}"
            by (simp only: gamma_normalize_congruence_rep
                gamma_congruence_rep.simps)
          from x_some y_some cm1 cm2 m1_nonzero m2_nonzero
            compatible normalized_gamma classes
          show ?thesis
            by (simp only: intersect_congruence_rep.simps if_False
                if_True Let_def gamma_congruence_rep.simps)
        qed
      qed
    qed
  qed
qed

lemma gamma_intersect_congruence [simp]:
  "gamma_congruence (intersect_congruence a b) =
   gamma_congruence a \<inter> gamma_congruence b"
proof -
  have norm_a: "normalized_congruence_rep (Rep_congruence a)"
    using Rep_congruence[of a] by simp
  have norm_b: "normalized_congruence_rep (Rep_congruence b)"
    using Rep_congruence[of b] by simp
  show ?thesis
    using gamma_intersect_congruence_rep[OF norm_a norm_b]
    by (simp add: gamma_congruence_def intersect_congruence.rep_eq)
qed

lemma intersect_congruence_sound:
  assumes "n : gamma_congruence a"
      and "n : gamma_congruence b"
  shows "n : gamma_congruence (intersect_congruence a b)"
  using assms by simp

lemma intersect_congruence_le1:
  "intersect_congruence a b <= a"
  unfolding less_eq_congruence_def congruence_le_iff_gamma
  by simp

lemma intersect_congruence_le2:
  "intersect_congruence a b <= b"
  unfolding less_eq_congruence_def congruence_le_iff_gamma
  by simp

lemma intersect_congruence_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows
    "intersect_congruence a1 b1 <=
     intersect_congruence a2 b2"
  using assms
  unfolding less_eq_congruence_def congruence_le_iff_gamma
  by auto


section \<open>Multiplication preimages\<close>

text \<open>
  For a known factor k, the preimage of c modulo m solves the linear
  congruence k*x = c modulo m. Dividing by gcd(k,m) and using the executable
  Bezout coefficient yields the complete solution class.
\<close>

fun preimage_times_const_rep ::
    "congruence_rep => int => congruence_rep"
where
  "preimage_times_const_rep None k = None"
| "preimage_times_const_rep (Some (c, m)) k =
     normalize_congruence_rep
       (if m = 0 then
          if k = 0 then
            if c = 0 then Some (0, 1) else None
          else if k dvd c then Some (c div k, 0) else None
        else
          let g = gcd k m
          in if g dvd c then
               let s = fst (bezout_coefficients k m)
               in Some ((c div g) * s, m div g)
             else None)"

lemma normalized_preimage_times_const_rep [simp]:
  "normalized_congruence_rep (preimage_times_const_rep r k)"
  by (cases r)
     (auto simp: split_def split: if_splits prod.splits)

lift_definition preimage_times_const ::
    "congruence => int => congruence"
  is preimage_times_const_rep
  by simp

lemma bezout_linear_congruence:
  assumes g_nonzero: "gcd k m ~= 0"
      and compatible: "gcd k m dvd c"
  shows
    "m div gcd k m dvd
       x - (c div gcd k m) * fst (bezout_coefficients k m)
     \<longleftrightarrow>
     m dvd k * x - c"
proof -
  let ?g = "gcd k m"
  let ?s = "fst (bezout_coefficients k m)"
  let ?t = "snd (bezout_coefficients k m)"
  let ?q = "c div ?g"
  let ?kp = "k div ?g"
  let ?mp = "m div ?g"
  have gk: "?g dvd k"
    by (rule gcd_dvd1)
  have gm: "?g dvd m"
    by (rule gcd_dvd2)
  have k_eq: "?g * ?kp = k"
    using dvd_mult_div_cancel[OF gk]
    by (simp add: mult.commute)
  have m_eq: "?g * ?mp = m"
    using dvd_mult_div_cancel[OF gm]
    by (simp add: mult.commute)
  have c_eq: "?g * ?q = c"
    using dvd_mult_div_cancel[OF compatible]
    by (simp add: mult.commute)
  have bezout:
    "?s * k + ?t * m = ?g"
    by (rule bezout_coefficients_fst_snd)
  have scaled:
    "?g * (?s * ?kp + ?t * ?mp) = ?g"
  proof -
    have
      "?g * (?s * ?kp + ?t * ?mp) =
       ?s * (?g * ?kp) + ?t * (?g * ?mp)"
      by (simp only: ring_distribs mult.assoc mult.commute
          mult.left_commute)
    also have "... = ?s * k + ?t * m"
      by (simp only: k_eq m_eq)
    also have "... = ?g"
      by (rule bezout)
    finally show ?thesis .
  qed
  have scaled':
    "?g * (?s * ?kp + ?t * ?mp) = ?g * 1"
    using scaled by simp
  have unit: "?s * ?kp + ?t * ?mp = 1"
    using scaled'
    by (simp only: mult_left_cancel[OF g_nonzero])
  show ?thesis
  proof
    assume solution: "?mp dvd x - ?q * ?s"
    obtain u where solution_eq:
      "x - ?q * ?s = ?mp * u"
      using solution unfolding dvd_def by blast
    have coprime_offset: "?s * ?kp - 1 = ?mp * (- ?t)"
      using unit by (simp add: algebra_simps)
    have q_unit:
      "?q * (?s * ?kp + ?t * ?mp) = ?q"
      using unit by simp
    have reduced:
      "?kp * x - ?q = ?mp * (?kp * u + ?q * (- ?t))"
      using solution_eq q_unit
      by (simp add: algebra_simps)
    show "m dvd k * x - c"
      unfolding dvd_def
    proof (rule exI[of _ "?kp * u + ?q * (- ?t)"])
      have scaled_reduced:
        "?g * (?kp * x - ?q) =
         ?g * (?mp * (?kp * u + ?q * (- ?t)))"
        by (rule arg_cong[OF reduced])
      show
        "k * x - c =
         m * (?kp * u + ?q * (- ?t))"
      proof -
        have "k * x - c = ?g * (?kp * x - ?q)"
          using k_eq c_eq by (simp add: algebra_simps)
        also have "... =
          ?g * (?mp * (?kp * u + ?q * (- ?t)))"
          by (rule scaled_reduced)
        also have "... =
          (?g * ?mp) * (?kp * u + ?q * (- ?t))"
          by (simp only: mult.assoc)
        also have "... = m * (?kp * u + ?q * (- ?t))"
          by (simp only: m_eq)
        finally show ?thesis .
      qed
    qed
  next
    assume target: "m dvd k * x - c"
    obtain u where target_eq:
      "k * x - c = m * u"
      using target unfolding dvd_def by blast
    have scaled_reduced:
      "?g * (?kp * x - ?q) = ?g * (?mp * u)"
      using target_eq k_eq m_eq c_eq
      by (simp add: algebra_simps)
    have reduced: "?kp * x - ?q = ?mp * u"
      using scaled_reduced
      by (simp only: mult_left_cancel[OF g_nonzero])
    show "?mp dvd x - ?q * ?s"
      unfolding dvd_def
    proof (rule exI[of _ "?s * u + ?t * x"])
      have scaled_solution:
        "?s * (?kp * x - ?q) = ?s * (?mp * u)"
        using reduced by simp
      have unit_x:
        "x * (?s * ?kp + ?t * ?mp) = x"
        using unit by simp
      show
        "x - ?q * ?s = ?mp * (?s * u + ?t * x)"
        using scaled_solution unit_x
        by (simp add: algebra_simps)
    qed
  qed
qed

lemma gamma_preimage_times_const_rep:
  assumes "normalized_congruence_rep r"
  shows
    "gamma_congruence_rep (preimage_times_const_rep r k) =
     {x. k * x : gamma_congruence_rep r}"
proof (cases r)
  case None
  then show ?thesis by simp
next
  case (Some cm)
  note r_some = Some
  obtain c m where cm: "cm = (c, m)"
    by (cases cm)
  have normalized:
    "normalized_congruence_rep (Some (c, m))"
    using assms r_some cm by simp
  show ?thesis
  proof (cases "m = 0")
    case m_zero: True
    show ?thesis
    proof (cases "k = 0")
      case k_zero: True
      show ?thesis
      proof (cases "c = 0")
        case True
        with r_some cm m_zero k_zero show ?thesis by simp
      next
        case False
        with r_some cm m_zero k_zero show ?thesis by simp
      qed
    next
      case k_nonzero: False
      show ?thesis
      proof (cases "k dvd c")
        case compatible: True
        have quotient: "k * (c div k) = c"
          by (rule dvd_mult_div_cancel[OF compatible])
        have solution_iff:
          "k * x = c \<longleftrightarrow> x = c div k" for x
        proof -
          have
            "(k * x = c) =
             (k * x = k * (c div k))"
            using quotient by simp
          also have "... = (x = c div k)"
            by (rule mult_left_cancel[OF k_nonzero])
          finally show ?thesis .
        qed
        with r_some cm m_zero k_nonzero compatible
        show ?thesis
          by simp
      next
        case incompatible: False
        have no_solution: "k * x ~= c" for x
        proof
          assume "k * x = c"
          then have "k dvd c"
            unfolding dvd_def by blast
          with incompatible show False by contradiction
        qed
        with r_some cm m_zero k_nonzero incompatible
        show ?thesis
          by simp
      qed
    qed
  next
    case m_nonzero: False
    let ?g = "gcd k m"
    let ?q = "c div ?g"
    let ?s = "fst (bezout_coefficients k m)"
    have g_nonzero: "?g ~= 0"
      using m_nonzero by simp
    show ?thesis
    proof (cases "?g dvd c")
      case incompatible: False
      have no_solution: "~ m dvd k * x - c" for x
      proof
        assume target: "m dvd k * x - c"
        have g_product: "?g dvd k * x"
          by (rule dvd_mult2[OF gcd_dvd1])
        have g_target: "?g dvd k * x - c"
          using gcd_dvd2 target by (rule dvd_trans)
        have "?g dvd k * x - (k * x - c)"
          by (rule dvd_diff[OF g_product g_target])
        then have "?g dvd c"
          by simp
        with incompatible show False by contradiction
      qed
      with r_some cm m_nonzero incompatible
      show ?thesis by simp
    next
      case compatible: True
      have solution_iff:
        "m div ?g dvd x - ?q * ?s \<longleftrightarrow>
         m dvd k * x - c" for x
        by (rule bezout_linear_congruence[OF g_nonzero compatible])
      have normalized_gamma:
        "gamma_congruence_rep
           (normalize_congruence_rep
             (Some (?q * ?s, m div ?g))) =
         {x. m div ?g dvd x - ?q * ?s}"
        by (simp only: gamma_normalize_congruence_rep
            gamma_congruence_rep.simps)
      from r_some cm m_nonzero compatible normalized_gamma
        solution_iff
      show ?thesis
        by (simp only: preimage_times_const_rep.simps if_False
            if_True Let_def gamma_congruence_rep.simps
            Set.set_eq_iff mem_Collect_eq;
            simp)
    qed
  qed
qed

lemma gamma_preimage_times_const [simp]:
  "gamma_congruence (preimage_times_const r k) =
   {x. k * x : gamma_congruence r}"
proof -
  have norm_r:
    "normalized_congruence_rep (Rep_congruence r)"
    using Rep_congruence[of r] by simp
  show ?thesis
    using gamma_preimage_times_const_rep[OF norm_r, of k]
    by (simp add: gamma_congruence_def preimage_times_const.rep_eq)
qed

lemma preimage_times_const_mono:
  assumes "r1 <= r2"
  shows "preimage_times_const r1 k <= preimage_times_const r2 k"
  using assms
  unfolding less_eq_congruence_def congruence_le_iff_gamma
  by auto

fun inverse_times_candidate_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "inverse_times_candidate_rep None factor = None"
| "inverse_times_candidate_rep r None = None"
| "inverse_times_candidate_rep
     (Some (c, m)) (Some (k, n)) =
     (if n = 0
      then preimage_times_const_rep (Some (c, m)) k
      else Some (0, 1))"

lemma normalized_inverse_times_candidate_rep [simp]:
  assumes "normalized_congruence_rep r"
      and "normalized_congruence_rep factor"
  shows
    "normalized_congruence_rep
       (inverse_times_candidate_rep r factor)"
  using assms
  by (cases r; cases factor)
     (auto split: prod.splits if_splits)

lift_definition inverse_times_candidate ::
    "congruence => congruence => congruence"
  is inverse_times_candidate_rep
  by simp

lemma inverse_times_candidate_sound:
  assumes "z : gamma_congruence r"
      and "y : gamma_congruence factor"
      and "x * y = z"
  shows "x : gamma_congruence (inverse_times_candidate r factor)"
proof (cases "Rep_congruence r")
  case None
  with assms(1) show ?thesis
    unfolding gamma_congruence_def by simp
next
  case (Some rp)
  note r_some = Some
  obtain c m where rp: "rp = (c, m)"
    by (cases rp)
  show ?thesis
  proof (cases "Rep_congruence factor")
    case None
    with assms(2) show ?thesis
      unfolding gamma_congruence_def by simp
  next
    case (Some fp)
    note factor_some = Some
    obtain k n where fp: "fp = (k, n)"
      by (cases fp)
    show ?thesis
    proof (cases "n = 0")
      case singleton: True
      have y_eq: "y = k"
        using assms(2) factor_some fp singleton
        unfolding gamma_congruence_def by simp
      have x_preimage:
        "x : gamma_congruence (preimage_times_const r k)"
        using assms(1,3) y_eq
        by (simp add: mult.commute)
      from x_preimage r_some factor_some rp fp singleton
      show ?thesis
        unfolding gamma_congruence_def
        by (simp add: inverse_times_candidate.rep_eq
            preimage_times_const.rep_eq)
    next
      case nonsingleton: False
      with r_some factor_some rp fp show ?thesis
        unfolding gamma_congruence_def
        by (simp add: inverse_times_candidate.rep_eq)
    qed
  qed
qed

lemma inverse_times_candidate_mono:
  assumes "r1 <= r2" and "factor1 <= factor2"
  shows
    "inverse_times_candidate r1 factor1 <=
     inverse_times_candidate r2 factor2"
proof -
  have r_subset:
    "gamma_congruence r1 \<subseteq> gamma_congruence r2"
    using assms(1)
    unfolding less_eq_congruence_def congruence_le_iff_gamma .
  have factor_subset:
    "gamma_congruence factor1 \<subseteq> gamma_congruence factor2"
    using assms(2)
    unfolding less_eq_congruence_def congruence_le_iff_gamma .
  show ?thesis
  proof (cases "Rep_congruence r1")
    case None
    then show ?thesis
      unfolding less_eq_congruence_def congruence_le_iff_gamma
        gamma_congruence_def
      by (simp add: inverse_times_candidate.rep_eq)
  next
    case (Some rp1)
    note r1_some = Some
    obtain c1 m1 where rp1: "rp1 = (c1, m1)"
      by (cases rp1)
    have c1_member: "c1 : gamma_congruence r1"
      using r1_some rp1
      by (simp add: gamma_congruence_def)
    show ?thesis
    proof (cases "Rep_congruence factor1")
      case None
      with r1_some rp1 show ?thesis
        unfolding less_eq_congruence_def congruence_le_iff_gamma
          gamma_congruence_def
        by (simp add: inverse_times_candidate.rep_eq)
    next
      case (Some fp1)
      note factor1_some = Some
      obtain k1 n1 where fp1: "fp1 = (k1, n1)"
        by (cases fp1)
      have k1_member: "k1 : gamma_congruence factor1"
        using factor1_some fp1
        by (simp add: gamma_congruence_def)
      have shifted_member:
        "k1 + n1 : gamma_congruence factor1"
        using factor1_some fp1
        by (simp add: gamma_congruence_def)
      show ?thesis
      proof (cases "Rep_congruence r2")
        case None
        have "c1 : gamma_congruence r2"
          by (rule subsetD[OF r_subset c1_member])
        with None show ?thesis
          unfolding gamma_congruence_def by simp
      next
        case (Some rp2)
        note r2_some = Some
        obtain c2 m2 where rp2: "rp2 = (c2, m2)"
          by (cases rp2)
        show ?thesis
        proof (cases "Rep_congruence factor2")
          case None
          have "k1 : gamma_congruence factor2"
            by (rule subsetD[OF factor_subset k1_member])
          with None show ?thesis
            unfolding gamma_congruence_def by simp
        next
          case (Some fp2)
          note factor2_some = Some
          obtain k2 n2 where fp2: "fp2 = (k2, n2)"
            by (cases fp2)
          show ?thesis
          proof (cases "n2 = 0")
            case factor2_singleton: True
            have k1_in_factor2:
              "k1 : gamma_congruence factor2"
              by (rule subsetD[OF factor_subset k1_member])
            have shifted_in_factor2:
              "k1 + n1 : gamma_congruence factor2"
              by (rule subsetD[OF factor_subset shifted_member])
            have k1_eq: "k1 = k2"
              using k1_in_factor2 factor2_some fp2
                factor2_singleton
              unfolding gamma_congruence_def by simp
            have shifted_eq: "k1 + n1 = k2"
              using shifted_in_factor2 factor2_some fp2
                factor2_singleton
              unfolding gamma_congruence_def by simp
            have n1_zero: "n1 = 0"
              using k1_eq shifted_eq by simp
            have preimage_le:
              "preimage_times_const r1 k1 <=
               preimage_times_const r2 k2"
              using preimage_times_const_mono[OF assms(1), of k1]
                k1_eq
              by simp
            from preimage_le r1_some factor1_some rp1 fp1
              r2_some factor2_some rp2 fp2 n1_zero
              factor2_singleton
            show ?thesis
              unfolding less_eq_congruence_def congruence_le_iff_gamma
                gamma_congruence_def
              by (simp add: inverse_times_candidate.rep_eq
                  preimage_times_const.rep_eq)
          next
            case factor2_nonsingleton: False
            with r2_some factor2_some rp2 fp2
            show ?thesis
              unfolding less_eq_congruence_def congruence_le_iff_gamma
                gamma_congruence_def
              by (simp add: inverse_times_candidate.rep_eq)
          qed
        qed
      qed
    qed
  qed
qed


section \<open>Backward inverse operators\<close>

definition inv_less_congruence ::
    "bool => congruence => congruence => congruence * congruence"
where
  "inv_less_congruence result a b = (a, b)"

fun inv_eq_congruence ::
    "bool => congruence => congruence => congruence * congruence"
where
  "inv_eq_congruence True a b =
     (intersect_congruence a b, intersect_congruence a b)"
| "inv_eq_congruence False a b = (a, b)"

definition inv_plus_congruence ::
    "congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_plus_congruence r a b =
     (intersect_congruence a (r - b),
      intersect_congruence b (r - a))"

definition inv_minus_congruence ::
    "congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_minus_congruence r a b =
     (intersect_congruence a (r + b),
      intersect_congruence b (a - r))"

definition inv_times_congruence ::
    "congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_times_congruence r a b =
     (intersect_congruence a (inverse_times_candidate r b),
      intersect_congruence b (inverse_times_candidate r a))"

lemma inv_less_congruence_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
  shows
    "x : gamma_congruence
       (fst (inv_less_congruence result a b)) \<and>
     y : gamma_congruence
       (snd (inv_less_congruence result a b))"
  using assms by (simp add: inv_less_congruence_def)

lemma inv_eq_congruence_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "(x = y) = result"
  shows
    "x : gamma_congruence
       (fst (inv_eq_congruence result a b)) \<and>
     y : gamma_congruence
       (snd (inv_eq_congruence result a b))"
  using assms
  by (cases result) auto

lemma inv_plus_congruence_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "x + y : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_plus_congruence r a b)) \<and>
     y : gamma_congruence
       (snd (inv_plus_congruence r a b))"
proof -
  have x_candidate: "x : gamma_congruence (r - b)"
    using congruence_minus_sound[OF assms(3) assms(2)]
    by simp
  have y_candidate: "y : gamma_congruence (r - a)"
    using congruence_minus_sound[OF assms(3) assms(1)]
    by simp
  show ?thesis
    using assms(1,2) x_candidate y_candidate
    by (simp add: inv_plus_congruence_def)
qed

lemma inv_minus_congruence_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "x - y : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_minus_congruence r a b)) \<and>
     y : gamma_congruence
       (snd (inv_minus_congruence r a b))"
proof -
  have x_candidate: "x : gamma_congruence (r + b)"
    using congruence_plus_sound[OF assms(3) assms(2)]
    by simp
  have y_candidate: "y : gamma_congruence (a - r)"
    using congruence_minus_sound[OF assms(1) assms(3)]
    by simp
  show ?thesis
    using assms(1,2) x_candidate y_candidate
    by (simp add: inv_minus_congruence_def)
qed

lemma inv_times_congruence_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "x * y : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_times_congruence r a b)) \<and>
     y : gamma_congruence
       (snd (inv_times_congruence r a b))"
proof -
  have x_candidate:
    "x : gamma_congruence (inverse_times_candidate r b)"
  proof (rule inverse_times_candidate_sound[
      where z = "x * y" and y = y])
    show "x * y : gamma_congruence r"
      by (rule assms(3))
    show "y : gamma_congruence b"
      by (rule assms(2))
    show "x * y = x * y" by simp
  qed
  have y_candidate:
    "y : gamma_congruence (inverse_times_candidate r a)"
  proof (rule inverse_times_candidate_sound[
      where z = "x * y" and y = x])
    show "x * y : gamma_congruence r"
      by (rule assms(3))
    show "x : gamma_congruence a"
      by (rule assms(1))
    show "y * x = x * y"
      by (simp add: mult.commute)
  qed
  show ?thesis
    using assms(1,2) x_candidate y_candidate
    by (simp add: inv_times_congruence_def)
qed

lemma inv_less_congruence_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_less_congruence result a1 b1)
      (inv_less_congruence result a2 b2)"
  using assms by (simp add: inv_less_congruence_def le_pair_def)

lemma inv_eq_congruence_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_eq_congruence result a1 b1)
      (inv_eq_congruence result a2 b2)"
  using assms intersect_congruence_mono
  by (cases result) (auto simp: le_pair_def)

lemma inv_plus_congruence_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_plus_congruence r1 a1 b1)
      (inv_plus_congruence r2 a2 b2)"
  using assms congruence_minus_mono intersect_congruence_mono
  by (auto simp: inv_plus_congruence_def le_pair_def)

lemma inv_minus_congruence_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_minus_congruence r1 a1 b1)
      (inv_minus_congruence r2 a2 b2)"
  using assms congruence_plus_mono congruence_minus_mono
    intersect_congruence_mono
  by (auto simp: inv_minus_congruence_def le_pair_def)

lemma inv_times_congruence_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_times_congruence r1 a1 b1)
      (inv_times_congruence r2 a2 b2)"
  using assms inverse_times_candidate_mono intersect_congruence_mono
  by (auto simp: inv_times_congruence_def le_pair_def)

lemma inv_less_congruence_reductive:
  "le_pair (inv_less_congruence result a b) (a, b)"
  by (simp add: inv_less_congruence_def le_pair_def)

lemma inv_eq_congruence_reductive:
  "le_pair (inv_eq_congruence result a b) (a, b)"
  using intersect_congruence_le1 intersect_congruence_le2
  by (cases result) (auto simp: le_pair_def)

lemma inv_plus_congruence_reductive:
  "le_pair (inv_plus_congruence r a b) (a, b)"
  by (simp add: inv_plus_congruence_def le_pair_def
        intersect_congruence_le1)

lemma inv_minus_congruence_reductive:
  "le_pair (inv_minus_congruence r a b) (a, b)"
  by (simp add: inv_minus_congruence_def le_pair_def
        intersect_congruence_le1)

lemma inv_times_congruence_reductive:
  "le_pair (inv_times_congruence r a b) (a, b)"
  by (simp add: inv_times_congruence_def le_pair_def
        intersect_congruence_le1)

text \<open>
  \<open>inv_plus_congruence\<close>/\<open>inv_minus_congruence\<close>/\<open>inv_times_congruence\<close> take
  \<open>r\<close> as an exact fact about the operation's result. In the \<open>int_dom\<close>
  composite, the register standing for that result is itself an ikind-wrapped
  value: what is actually known is \<open>ik_norm ik (x + y) : gamma_congruence r\<close>,
  not \<open>x + y : gamma_congruence r\<close>. \<open>cong_unwrap\<close> bridges exactly this gap,
  so composing it with the unchanged \<open>inv_plus_congruence\<close> family gives a
  sound, monotone, reductive ikind-aware inverse -- uniformly for plus, minus,
  and times, since all three share the same "\<open>r\<close> is the exact result" premise
  shape.
\<close>

definition inv_plus_congruence_ik ::
    "ikind => congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_plus_congruence_ik ik r a b =
     inv_plus_congruence (cong_unwrap ik r) a b"

definition inv_minus_congruence_ik ::
    "ikind => congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_minus_congruence_ik ik r a b =
     inv_minus_congruence (cong_unwrap ik r) a b"

definition inv_times_congruence_ik ::
    "ikind => congruence => congruence => congruence =>
     congruence * congruence"
where
  "inv_times_congruence_ik ik r a b =
     inv_times_congruence (cong_unwrap ik r) a b"

lemma inv_plus_congruence_ik_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "ik_norm ik (x + y) : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_plus_congruence_ik ik r a b)) \<and>
     y : gamma_congruence
       (snd (inv_plus_congruence_ik ik r a b))"
proof -
  have "x + y : gamma_congruence (cong_unwrap ik r)"
    using cong_unwrap_sound[OF assms(3)] .
  then show ?thesis
    using inv_plus_congruence_sound[OF assms(1) assms(2)]
    by (simp add: inv_plus_congruence_ik_def)
qed

lemma inv_minus_congruence_ik_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "ik_norm ik (x - y) : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_minus_congruence_ik ik r a b)) \<and>
     y : gamma_congruence
       (snd (inv_minus_congruence_ik ik r a b))"
proof -
  have "x - y : gamma_congruence (cong_unwrap ik r)"
    using cong_unwrap_sound[OF assms(3)] .
  then show ?thesis
    using inv_minus_congruence_sound[OF assms(1) assms(2)]
    by (simp add: inv_minus_congruence_ik_def)
qed

lemma inv_times_congruence_ik_sound:
  assumes "x : gamma_congruence a"
      and "y : gamma_congruence b"
      and "ik_norm ik (x * y) : gamma_congruence r"
  shows
    "x : gamma_congruence
       (fst (inv_times_congruence_ik ik r a b)) \<and>
     y : gamma_congruence
       (snd (inv_times_congruence_ik ik r a b))"
proof -
  have "x * y : gamma_congruence (cong_unwrap ik r)"
    using cong_unwrap_sound[OF assms(3)] .
  then show ?thesis
    using inv_times_congruence_sound[OF assms(1) assms(2)]
    by (simp add: inv_times_congruence_ik_def)
qed

lemma inv_plus_congruence_ik_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_plus_congruence_ik ik r1 a1 b1)
      (inv_plus_congruence_ik ik r2 a2 b2)"
  using assms cong_unwrap_mono inv_plus_congruence_mono
  by (simp add: inv_plus_congruence_ik_def)

lemma inv_minus_congruence_ik_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_minus_congruence_ik ik r1 a1 b1)
      (inv_minus_congruence_ik ik r2 a2 b2)"
  using assms cong_unwrap_mono inv_minus_congruence_mono
  by (simp add: inv_minus_congruence_ik_def)

lemma inv_times_congruence_ik_mono:
  assumes "r1 <= r2" and "a1 <= a2" and "b1 <= b2"
  shows
    "le_pair
      (inv_times_congruence_ik ik r1 a1 b1)
      (inv_times_congruence_ik ik r2 a2 b2)"
  using assms cong_unwrap_mono inv_times_congruence_mono
  by (simp add: inv_times_congruence_ik_def)

lemma inv_plus_congruence_ik_reductive:
  "le_pair (inv_plus_congruence_ik ik r a b) (a, b)"
  by (simp add: inv_plus_congruence_ik_def inv_plus_congruence_reductive)

lemma inv_minus_congruence_ik_reductive:
  "le_pair (inv_minus_congruence_ik ik r a b) (a, b)"
  by (simp add: inv_minus_congruence_ik_def inv_minus_congruence_reductive)

lemma inv_times_congruence_ik_reductive:
  "le_pair (inv_times_congruence_ik ik r a b) (a, b)"
  by (simp add: inv_times_congruence_ik_def inv_times_congruence_reductive)


subsection \<open>Backward-domain interpretation\<close>

global_interpretation congruence_backward_domain:
    backward_domain_refined intersect_congruence aval_congruence congruence_tobool
      inv_less_congruence inv_eq_congruence
      inv_plus_congruence_ik inv_minus_congruence_ik inv_times_congruence_ik
  defines
    afilter_congruence = congruence_backward_domain.afilter
    and feasible_congruence = congruence_backward_domain.feasible
    and bfilter_congruence = congruence_backward_domain.bfilter
    and afilter_congruence_st = congruence_backward_domain.afilter_st
    and bfilter_congruence_st = congruence_backward_domain.bfilter_st
proof unfold_locales
  fix n :: int and a b :: congruence
  assume H1: "n : gamma a" and H2: "n : gamma b"
  have h1: "n : gamma_congruence a" using H1 by simp
  have h2: "n : gamma_congruence b" using H2 by simp
  show "n : gamma (intersect_congruence a b)"
    using intersect_congruence_sound[OF h1 h2] by simp
next
  fix s :: store and e :: exp and \<Gamma> :: tyenv and ik :: ikind
    and sigma :: "vname => congruence"
  assume H: "\<forall>x. s x : gamma (sigma x)"
  show "taval \<Gamma> ik e s : gamma (aval_congruence \<Gamma> ik e sigma)"
    using aval_congruence_sound[of s sigma \<Gamma> ik e] H by simp
next
  fix n1 n2 :: int and a1 a2 :: congruence and result :: bool
  assume H1: "n1 : gamma a1"
      and H2: "n2 : gamma a2"
      and H3: "(n1 < n2) = result"
  have h1: "n1 : gamma_congruence a1" using H1 by simp
  have h2: "n2 : gamma_congruence a2" using H2 by simp
  show
    "n1 : gamma (fst (inv_less_congruence result a1 a2)) \<and>
     n2 : gamma (snd (inv_less_congruence result a1 a2))"
    using inv_less_congruence_sound[OF h1 h2] by simp
next
  fix n1 n2 :: int and a1 a2 :: congruence and result :: bool
  assume H1: "n1 : gamma a1"
      and H2: "n2 : gamma a2"
      and H3: "(n1 = n2) = result"
  have h1: "n1 : gamma_congruence a1" using H1 by simp
  have h2: "n2 : gamma_congruence a2" using H2 by simp
  show
    "n1 : gamma (fst (inv_eq_congruence result a1 a2)) \<and>
     n2 : gamma (snd (inv_eq_congruence result a1 a2))"
    using inv_eq_congruence_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: congruence and ik :: ikind
  assume H1: "n1 : gamma a1"
      and H2: "n2 : gamma a2"
      and H3: "ik_norm ik (n1 + n2) : gamma r"
  have h1: "n1 : gamma_congruence a1" using H1 by simp
  have h2: "n2 : gamma_congruence a2" using H2 by simp
  have h3: "ik_norm ik (n1 + n2) : gamma_congruence r" using H3 by simp
  show
    "n1 : gamma (fst (inv_plus_congruence_ik ik r a1 a2)) \<and>
     n2 : gamma (snd (inv_plus_congruence_ik ik r a1 a2))"
    using inv_plus_congruence_ik_sound[OF h1 h2 h3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: congruence and ik :: ikind
  assume H1: "n1 : gamma a1"
      and H2: "n2 : gamma a2"
      and H3: "ik_norm ik (n1 - n2) : gamma r"
  have h1: "n1 : gamma_congruence a1" using H1 by simp
  have h2: "n2 : gamma_congruence a2" using H2 by simp
  have h3: "ik_norm ik (n1 - n2) : gamma_congruence r" using H3 by simp
  show
    "n1 : gamma (fst (inv_minus_congruence_ik ik r a1 a2)) \<and>
     n2 : gamma (snd (inv_minus_congruence_ik ik r a1 a2))"
    using inv_minus_congruence_ik_sound[OF h1 h2 h3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: congruence and ik :: ikind
  assume H1: "n1 : gamma a1"
      and H2: "n2 : gamma a2"
      and H3: "ik_norm ik (n1 * n2) : gamma r"
  have h1: "n1 : gamma_congruence a1" using H1 by simp
  have h2: "n2 : gamma_congruence a2" using H2 by simp
  have h3: "ik_norm ik (n1 * n2) : gamma_congruence r" using H3 by simp
  show
    "n1 : gamma (fst (inv_times_congruence_ik ik r a1 a2)) \<and>
     n2 : gamma (snd (inv_times_congruence_ik ik r a1 a2))"
    using inv_times_congruence_ik_sound[OF h1 h2 h3] by simp
next
  fix p :: congruence and b :: bool and i :: int
  assume "congruence_tobool p = Some b" and "i : gamma p"
  then show "truthy i = b" using congruence_tobool_sound by simp
next
  fix a1 a2 b1 b2 :: congruence
  assume "a1 <= a2" and "b1 <= b2"
  then show
    "intersect_congruence a1 b1 <=
     intersect_congruence a2 b2"
    by (rule intersect_congruence_mono)
next
  fix e :: exp and \<Gamma> :: tyenv and ik :: ikind and sigma1 sigma2 :: "vname => congruence"
  assume "sigma1 <= sigma2"
  then show "aval_congruence \<Gamma> ik e sigma1 <= aval_congruence \<Gamma> ik e sigma2"
    by (rule aval_congruence_mono)
next
  fix x1 x2 y1 y2 :: congruence and result :: bool
  assume "x1 <= x2" and "y1 <= y2"
  then show
    "le_pair
      (inv_less_congruence result x1 y1)
      (inv_less_congruence result x2 y2)"
    by (rule inv_less_congruence_mono)
next
  fix x1 x2 y1 y2 :: congruence and result :: bool
  assume "x1 <= x2" and "y1 <= y2"
  then show
    "le_pair
      (inv_eq_congruence result x1 y1)
      (inv_eq_congruence result x2 y2)"
    by (rule inv_eq_congruence_mono)
next
  fix r1 r2 x1 x2 y1 y2 :: congruence and ik :: ikind
  assume "r1 <= r2" and "x1 <= x2" and "y1 <= y2"
  then show
    "le_pair
      (inv_plus_congruence_ik ik r1 x1 y1)
      (inv_plus_congruence_ik ik r2 x2 y2)"
    by (rule inv_plus_congruence_ik_mono)
next
  fix r1 r2 x1 x2 y1 y2 :: congruence and ik :: ikind
  assume "r1 <= r2" and "x1 <= x2" and "y1 <= y2"
  then show
    "le_pair
      (inv_minus_congruence_ik ik r1 x1 y1)
      (inv_minus_congruence_ik ik r2 x2 y2)"
    by (rule inv_minus_congruence_ik_mono)
next
  fix r1 r2 x1 x2 y1 y2 :: congruence and ik :: ikind
  assume "r1 <= r2" and "x1 <= x2" and "y1 <= y2"
  then show
    "le_pair
      (inv_times_congruence_ik ik r1 x1 y1)
      (inv_times_congruence_ik ik r2 x2 y2)"
    by (rule inv_times_congruence_ik_mono)
next
  fix a b :: congruence
  show "intersect_congruence a b <= a"
    by (rule intersect_congruence_le1)
next
  fix a b :: congruence
  show "intersect_congruence a b <= b"
    by (rule intersect_congruence_le2)
next
  fix result :: bool and a b :: congruence
  show "le_pair (inv_less_congruence result a b) (a, b)"
    by (rule inv_less_congruence_reductive)
next
  fix result :: bool and a b :: congruence
  show "le_pair (inv_eq_congruence result a b) (a, b)"
    by (rule inv_eq_congruence_reductive)
next
  fix r a b :: congruence and ik :: ikind
  show "le_pair (inv_plus_congruence_ik ik r a b) (a, b)"
    by (rule inv_plus_congruence_ik_reductive)
next
  fix r a b :: congruence and ik :: ikind
  show "le_pair (inv_minus_congruence_ik ik r a b) (a, b)"
    by (rule inv_minus_congruence_ik_reductive)
next
  fix r a b :: congruence and ik :: ikind
  show "le_pair (inv_times_congruence_ik ik r a b) (a, b)"
    by (rule inv_times_congruence_ik_reductive)
next
  fix p1 p2 :: congruence and bv :: bool
  assume "\<not> is_bot p1" and "p1 <= p2" and "congruence_tobool p2 = Some bv"
  then show "congruence_tobool p1 = Some bv" using congruence_tobool_mono by simp
qed

lemmas afilter_congruence_st_commute =
  congruence_backward_domain.afilter_st_commute
lemmas bfilter_congruence_st_commute =
  congruence_backward_domain.bfilter_st_commute

lemma afilter_congruence_mono:
  "a1 <= (a2 :: congruence) \<Longrightarrow> sigma1 <= sigma2 \<Longrightarrow>
   afilter_congruence \<Gamma> ik e a1 sigma1 <= afilter_congruence \<Gamma> ik e a2 sigma2"
  using congruence_backward_domain.afilter_mono
  by (simp add: afilter_congruence_def)

lemma bfilter_congruence_mono:
  "sigma1 <= sigma2 \<Longrightarrow>
   bfilter_congruence \<Gamma> b result sigma1 <=
   bfilter_congruence \<Gamma> b result sigma2"
  using congruence_backward_domain.bfilter_mono
  by (simp add: bfilter_congruence_def)
end
