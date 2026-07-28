theory Sign_Backward
  imports Sign_Arithmetic
begin

section \<open>Sign backward filtering\<close>

subsection \<open>Meet (greatest lower bound)\<close>

text \<open>
  The seven-element sign lattice has a well-defined glb.  Adding @{class semilattice_inf}
  here gives @{text \<open>inf_mono\<close>} for free, which is needed for the monotonicity proof
  of @{text bfilter}.
\<close>

fun meet_sign :: "sign => sign => sign" where
    "meet_sign SBot    _       = SBot"
  | "meet_sign _       SBot    = SBot"
  | "meet_sign STop    b       = b"
  | "meet_sign a       STop    = a"
  | "meet_sign SNeg    SNeg    = SNeg"
  | "meet_sign SNeg    SNonPos = SNeg"
  | "meet_sign SNonPos SNeg    = SNeg"
  | "meet_sign SNonPos SNonPos = SNonPos"
  | "meet_sign SNonPos SZero   = SZero"
  | "meet_sign SZero   SNonPos = SZero"
  | "meet_sign SNonPos SNonNeg = SZero"
  | "meet_sign SNonNeg SNonPos = SZero"
  | "meet_sign SZero   SZero   = SZero"
  | "meet_sign SZero   SNonNeg = SZero"
  | "meet_sign SNonNeg SZero   = SZero"
  | "meet_sign SNonNeg SNonNeg = SNonNeg"
  | "meet_sign SNonNeg SPos    = SPos"
  | "meet_sign SPos    SNonNeg = SPos"
  | "meet_sign SPos    SPos    = SPos"
  | "meet_sign _       _       = SBot"

lemma meet_sign_sound:
  "n \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> n \<in> gamma_sign (meet_sign a b)"
  by (cases a; cases b; auto)

instantiation sign :: inf begin
definition inf_sign :: "sign => sign => sign" where
  "inf_sign = meet_sign"
instance ..
end

declare inf_sign_def [simp]

instance sign :: semilattice_inf
proof intro_classes
  fix x y z :: sign
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z; auto simp: less_eq_sign_def)
qed

instance sign :: lattice ..
instance sign :: bounded_lattice_bot ..

subsection \<open>Backward-analysis: inverse operators\<close>

text \<open>
  Per the backward-domain plan, @{text inv_less_sign} provides sign-specific
  refinement when a guard @{text "e1 < e2"} is known true or false.
  @{text inv_plus_sign}, @{text inv_minus_sign}, @{text inv_times_sign} are
  conservative (identity): sign is too coarse for useful arithmetic inversion;
  the structural bfilter propagation (And/Or/Not/Eq) is where sign gains.
\<close>

fun inv_less_sign :: "bool => sign => sign => sign * sign" where
    "inv_less_sign True  a1 a2 =
       (let a1' = if sign_le a2 SNonPos then meet_sign a1 SNeg else a1 ;
                a2' = if sign_le a1 SNonNeg then meet_sign a2 SPos else a2
        in (a1', a2'))"
  | "inv_less_sign False a1 a2 =
       (let a1' = if sign_le a2 SPos then meet_sign a1 SPos
                  else if sign_le a2 SNonNeg then meet_sign a1 SNonNeg
                  else a1 ;
                a2' = if sign_le a1 SNeg then meet_sign a2 SNeg
                  else if sign_le a1 SNonPos then meet_sign a2 SNonPos
                  else a2
        in (a1', a2'))"

fun inv_plus_sign :: "sign => sign => sign => sign * sign" where
  "inv_plus_sign _ a1 a2 = (a1, a2)"

fun inv_minus_sign :: "sign => sign => sign => sign * sign" where
  "inv_minus_sign _ a1 a2 = (a1, a2)"

fun inv_times_sign :: "sign => sign => sign => sign * sign" where
  "inv_times_sign _ a1 a2 = (a1, a2)"

lemma inv_less_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> (n1 < n2) = res
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_less_sign res a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_less_sign res a1 a2))"
  by (cases res; cases a1; cases a2;
      auto simp: less_eq_sign_def; linarith)

lemma inv_plus_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> n1 + n2 \<in> gamma_sign r
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_plus_sign r a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_plus_sign r a1 a2))"
  by simp

lemma inv_minus_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> n1 - n2 \<in> gamma_sign r
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_minus_sign r a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_minus_sign r a1 a2))"
  by simp

lemma inv_times_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> n1 * n2 \<in> gamma_sign r
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_times_sign r a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_times_sign r a1 a2))"
  by simp

subsection \<open>Backward-domain interpretation\<close>

global_interpretation sign_backward_domain:
    backward_domain meet_sign aval_sign
                    inv_less_sign inv_plus_sign inv_minus_sign inv_times_sign
  defines
    afilter_sign = sign_backward_domain.afilter
    and bfilter_sign = sign_backward_domain.bfilter
proof unfold_locales
  fix n :: int and a b :: sign
  assume H1: "n \<in> gamma a" and H2: "n \<in> gamma b"
  have h1: "n \<in> gamma_sign a" using H1 by simp
  have h2: "n \<in> gamma_sign b" using H2 by simp
  show "n \<in> gamma (meet_sign a b)"
    using meet_sign_sound[OF h1 h2] by simp
next
  fix s :: store and e :: aexp and \<sigma> :: "vname \<Rightarrow> sign"
  assume H: "\<forall>x. s x \<in> gamma (\<sigma> x)"
  have h: "\<forall>x. s x \<in> gamma_sign (\<sigma> x)" using H by simp
  show "aval e s \<in> gamma (aval_sign e \<sigma>)"
    using aval_sign_sound[OF h] by simp
next
  fix n1 n2 :: int and a1 a2 :: sign and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 < n2) = res"
  have h1: "n1 \<in> gamma_sign a1" using H1 by simp
  have h2: "n2 \<in> gamma_sign a2" using H2 by simp
  show "n1 \<in> gamma (fst (inv_less_sign res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less_sign res a1 a2))"
    using inv_less_sign_sound[OF h1 h2 H3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 + n2 \<in> gamma r"
  have h1: "n1 \<in> gamma_sign a1" using H1 by simp
  have h2: "n2 \<in> gamma_sign a2" using H2 by simp
  have h3: "n1 + n2 \<in> gamma_sign r" using H3 by simp
  show "n1 \<in> gamma (fst (inv_plus_sign r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus_sign r a1 a2))"
    using inv_plus_sign_sound[OF h1 h2 h3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 - n2 \<in> gamma r"
  have h1: "n1 \<in> gamma_sign a1" using H1 by simp
  have h2: "n2 \<in> gamma_sign a2" using H2 by simp
  have h3: "n1 - n2 \<in> gamma_sign r" using H3 by simp
  show "n1 \<in> gamma (fst (inv_minus_sign r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus_sign r a1 a2))"
    using inv_minus_sign_sound[OF h1 h2 h3] by simp
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 * n2 \<in> gamma r"
  have h1: "n1 \<in> gamma_sign a1" using H1 by simp
  have h2: "n2 \<in> gamma_sign a2" using H2 by simp
  have h3: "n1 * n2 \<in> gamma_sign r" using H3 by simp
  show "n1 \<in> gamma (fst (inv_times_sign r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times_sign r a1 a2))"
    using inv_times_sign_sound[OF h1 h2 h3] by simp
qed

subsection \<open>Abstract assume\<close>

text \<open>
  Guard refinement via backward evaluation.  @{text assume_sign} narrows the
  abstract state on the then-branch; @{text assume_not_sign} on the else-branch.
  Both delegate to the generic @{text bfilter} proved sound in @{locale backward_domain}.
\<close>

definition assume_sign :: "bexp => (vname => sign) => (vname => sign)" where
  "assume_sign b \<sigma> = bfilter_sign b True \<sigma>"

definition assume_not_sign :: "bexp => (vname => sign) => (vname => sign)" where
  "assume_not_sign b \<sigma> = bfilter_sign b False \<sigma>"

lemma assume_sign_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_sign b \<sigma>\<rbrakk>"
  unfolding assume_sign_def
  using sign_backward_domain.bfilter_sound by simp

lemma assume_not_sign_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_not_sign b \<sigma>\<rbrakk>"
  unfolding assume_not_sign_def
  using sign_backward_domain.bfilter_sound by simp


lemma sign_le_iff:
  "sign_le a b \<longleftrightarrow> a \<le> b"
  by (cases a; cases b; auto simp: less_eq_sign_def)

lemma narrow1_mono:
  fixes x x' y y' c d :: "'a::semilattice_inf"
  assumes xx': "x \<le> x'"
      and yy': "y \<le> y'"
  shows
    "(if y \<le> c then x \<sqinter> d else x)
      \<le> (if y' \<le> c then x' \<sqinter> d else x')"
  using xx' yy' inf_mono
  by auto

lemma narrow2_mono:
  fixes x x' y y' c1 c2 :: "'a::semilattice_inf"
  assumes xx': "x \<le> x'"
      and yy': "y \<le> y'"
      and cc': "c1 \<le> c2"
  shows
    "(if y \<le> c1 then x \<sqinter> c1
      else if y \<le> c2 then x \<sqinter> c2
      else x)
      \<le>
     (if y' \<le> c1 then x' \<sqinter> c1
      else if y' \<le> c2 then x' \<sqinter> c2
      else x')"
  using xx' yy' cc' inf_mono
  by (auto simp add: inf.coboundedI1 inf.coboundedI2)

lemma inv_less_sign_mono:
  assumes A1: "a1 \<le> (a1' :: sign)"
      and A2: "a2 \<le> a2'"
  shows
    "fst (inv_less_sign r a1 a2)
       \<le> fst (inv_less_sign r a1' a2') \<and>
     snd (inv_less_sign r a1 a2)
       \<le> snd (inv_less_sign r a1' a2')"
proof (cases r)
  case True

  have fst_mono:
    "(if a2 \<le> SNonPos then a1 \<sqinter> SNeg else a1)
      \<le>
     (if a2' \<le> SNonPos then a1' \<sqinter> SNeg else a1')"
    using narrow1_mono[OF A1 A2, of SNonPos SNeg] .

  have snd_mono:
    "(if a1 \<le> SNonNeg then a2 \<sqinter> SPos else a2)
      \<le>
     (if a1' \<le> SNonNeg then a2' \<sqinter> SPos else a2')"
    using narrow1_mono[OF A2 A1, of SNonNeg SPos] .

  show ?thesis
    using fst_mono snd_mono True sign_le_iff
    by auto
next
  case False

  have pos_order: "(SPos :: sign) \<le> SNonNeg"
    by (simp add: less_eq_sign_def)

  have neg_order: "(SNeg :: sign) \<le> SNonPos"
    by (simp add: less_eq_sign_def)

  have fst_mono:
    "(if a2 \<le> SPos then a1 \<sqinter> SPos
      else if a2 \<le> SNonNeg then a1 \<sqinter> SNonNeg
      else a1)
      \<le>  
     (if a2' \<le> SPos then a1' \<sqinter> SPos
      else if a2' \<le> SNonNeg then a1' \<sqinter> SNonNeg
      else a1')"
    using narrow2_mono[OF A1 A2, of SPos SNonNeg] pos_order by simp

  have snd_mono:
    "(if a1 \<le> SNeg then a2 \<sqinter> SNeg
      else if a1 \<le> SNonPos then a2 \<sqinter> SNonPos
      else a2)
      \<le>
     (if a1' \<le> SNeg then a2' \<sqinter> SNeg
      else if a1' \<le> SNonPos then a2' \<sqinter> SNonPos
      else a2')"
    using narrow2_mono[OF A2 A1, of SNeg SNonPos] neg_order by simp

  show ?thesis
    using fst_mono snd_mono False sign_le_iff
    by fastforce
qed

text \<open>
  Monotonicity of @{const afilter_sign} / @{const bfilter_sign} is the generic
  @{locale backward_domain_mono} result: interpret it at the sign operators
  (soundness as in @{term sign_backward_domain}, plus the six operator-mono facts)
  and the filter monotonicity follows by the shared induction.
\<close>

context begin
interpretation sign_bdm:
  backward_domain_mono meet_sign aval_sign
                       inv_less_sign inv_plus_sign inv_minus_sign inv_times_sign
proof unfold_locales
  fix a1 a2 b1 b2 :: sign
  assume "a1 \<le> a2" and "b1 \<le> b2"
  thus "meet_sign a1 b1 \<le> meet_sign a2 b2"
    using inf_mono[OF \<open>a1 \<le> a2\<close> \<open>b1 \<le> b2\<close>] by simp
next
  fix e :: aexp and \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> sign"
  assume "\<sigma>1 \<le> \<sigma>2"
  thus "aval_sign e \<sigma>1 \<le> aval_sign e \<sigma>2" by (rule aval_sign_mono)
next
  fix x1 x2 y1 y2 :: sign and res :: bool
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_less_sign res x1 y1) \<le> fst (inv_less_sign res x2 y2) \<and>
        snd (inv_less_sign res x1 y1) \<le> snd (inv_less_sign res x2 y2)"
    by (rule inv_less_sign_mono)
next
  fix r1 r2 x1 x2 y1 y2 :: sign
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_plus_sign r1 x1 y1) \<le> fst (inv_plus_sign r2 x2 y2) \<and>
        snd (inv_plus_sign r1 x1 y1) \<le> snd (inv_plus_sign r2 x2 y2)" by simp
next
  fix r1 r2 x1 x2 y1 y2 :: sign
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_minus_sign r1 x1 y1) \<le> fst (inv_minus_sign r2 x2 y2) \<and>
        snd (inv_minus_sign r1 x1 y1) \<le> snd (inv_minus_sign r2 x2 y2)" by simp
next
  fix r1 r2 x1 x2 y1 y2 :: sign
  assume "x1 \<le> x2" and "y1 \<le> y2"
  thus "fst (inv_times_sign r1 x1 y1) \<le> fst (inv_times_sign r2 x2 y2) \<and>
        snd (inv_times_sign r1 x1 y1) \<le> snd (inv_times_sign r2 x2 y2)" by simp
qed

lemma afilter_sign_mono:
  "a1 \<le> (a2::sign) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_sign e a1 sigma1 \<le> afilter_sign e a2 sigma2"
  using sign_bdm.afilter_mono by (simp add: afilter_sign_def)

lemma bfilter_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_sign b res sigma1 \<le> bfilter_sign b res sigma2"
  using sign_bdm.bfilter_mono by (simp add: bfilter_sign_def)

end

end
