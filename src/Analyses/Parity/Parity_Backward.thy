theory Parity_Backward
  imports
    Parity_Domain
    "Voblint_Nonrelational.Exec_Backward"
begin

section \<open>Parity backward refinement\<close>

text \<open>
  A guard tells Parity something whenever it pins a sum, a difference, a product
  or an equality. Parity of a sum or difference is the exclusive or of its
  operands' parities, so knowing the result and one operand fixes the other; an
  odd product forces both factors odd; and an equality that held gives both
  sides the meet of their parities. An order comparison says nothing about
  parity, so its inverse is the conservative no-op.
\<close>

subsection \<open>Inverse operators\<close>

definition inv_eq_parity :: "bool \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity \<times> parity" where
  "inv_eq_parity res a b = (if res then (a \<sqinter> b, a \<sqinter> b) else (a, b))"

definition inv_plus_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity \<times> parity" where
  "inv_plus_parity r a b = (a \<sqinter> (r - b), b \<sqinter> (r - a))"

definition inv_minus_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity \<times> parity" where
  "inv_minus_parity r a b = (a \<sqinter> (r + b), b \<sqinter> (a - r))"

text \<open>The parity both factors of a product with result parity \<open>r\<close> must have.\<close>

fun factor_parity :: "parity \<Rightarrow> parity" where
    "factor_parity PBot = PBot"
  | "factor_parity POdd = POdd"
  | "factor_parity _ = PTop"

definition inv_times_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity \<Rightarrow> parity \<times> parity" where
  "inv_times_parity r a b = (a \<sqinter> factor_parity r, b \<sqinter> factor_parity r)"

lemma inv_eq_parity_sound:
  "n1 \<in> gamma_parity a1 \<Longrightarrow> n2 \<in> gamma_parity a2 \<Longrightarrow> (n1 = n2) = res
   \<Longrightarrow> n1 \<in> gamma_parity (fst (inv_eq_parity res a1 a2))
     \<and> n2 \<in> gamma_parity (snd (inv_eq_parity res a1 a2))"
  by (auto simp: inv_eq_parity_def)

lemma inv_plus_parity_sound:
  assumes "n1 \<in> gamma_parity a1" and "n2 \<in> gamma_parity a2" and "n1 + n2 \<in> gamma_parity r"
  shows "n1 \<in> gamma_parity (fst (inv_plus_parity r a1 a2))
     \<and> n2 \<in> gamma_parity (snd (inv_plus_parity r a1 a2))"
  using assms parity_minus_sound[OF assms(3) assms(2)] parity_minus_sound[OF assms(3) assms(1)]
  by (simp add: inv_plus_parity_def)

lemma inv_minus_parity_sound:
  assumes "n1 \<in> gamma_parity a1" and "n2 \<in> gamma_parity a2" and "n1 - n2 \<in> gamma_parity r"
  shows "n1 \<in> gamma_parity (fst (inv_minus_parity r a1 a2))
     \<and> n2 \<in> gamma_parity (snd (inv_minus_parity r a1 a2))"
  using assms parity_plus_sound[OF assms(3) assms(2)] parity_minus_sound[OF assms(1) assms(3)]
  by (simp add: inv_minus_parity_def)

lemma factor_parity_sound:
  "n1 * n2 \<in> gamma_parity r \<Longrightarrow> n1 \<in> gamma_parity (factor_parity r) \<and> n2 \<in> gamma_parity (factor_parity r)"
  by (cases r) auto

lemma inv_times_parity_sound:
  "n1 \<in> gamma_parity a1 \<Longrightarrow> n2 \<in> gamma_parity a2 \<Longrightarrow> n1 * n2 \<in> gamma_parity r
   \<Longrightarrow> n1 \<in> gamma_parity (fst (inv_times_parity r a1 a2))
     \<and> n2 \<in> gamma_parity (snd (inv_times_parity r a1 a2))"
  using factor_parity_sound by (simp add: inv_times_parity_def)

lemma factor_parity_mono: "r1 \<le> r2 \<Longrightarrow> factor_parity r1 \<le> factor_parity r2"
  by (cases r1; cases r2) (simp_all add: less_eq_parity_def)

lemma inv_eq_parity_mono:
  "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_eq_parity res x1 y1) (inv_eq_parity res x2 y2)"
  by (auto simp: inv_eq_parity_def intro: le_infI1 le_infI2)

lemma inv_plus_parity_mono:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_plus_parity r1 x1 y1) (inv_plus_parity r2 x2 y2)"
  by (auto simp: inv_plus_parity_def intro: le_infI1 le_infI2 parity_minus_combine_mono)

lemma inv_minus_parity_mono:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_minus_parity r1 x1 y1) (inv_minus_parity r2 x2 y2)"
  by (auto simp: inv_minus_parity_def
      intro: le_infI1 le_infI2 parity_plus_combine_mono parity_minus_combine_mono)

lemma inv_times_parity_mono:
  "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_times_parity r1 x1 y1) (inv_times_parity r2 x2 y2)"
  by (auto simp: inv_times_parity_def intro: le_infI1 le_infI2 factor_parity_mono)

subsection \<open>The refinement operations and their certificate\<close>

text \<open>
  \<open>parity_refine_ops\<close> bundles the parity inverses; parity has no ordering, so
  \<open>r_inv_less\<close> is \<open>inv_conservative\<close>. \<open>parity_backward_domain\<close> certifies the
  bundle as a monotone refinement over \<open>aval_parity\<close>.
\<close>

definition parity_refine_ops :: "parity refine_ops" where
  "parity_refine_ops =
     \<lparr>r_tobool = parity_tobool, r_inv_less = inv_conservative, r_inv_eq = inv_eq_parity,
      r_inv_plus = inv_plus_parity, r_inv_minus = inv_minus_parity,
      r_inv_times = inv_times_parity, r_intersect = inf\<rparr>"

lemma parity_refine_ops_simps [simp]:
  "r_tobool parity_refine_ops = parity_tobool"
  "r_inv_less parity_refine_ops = inv_conservative"
  "r_inv_eq parity_refine_ops = inv_eq_parity"
  "r_inv_plus parity_refine_ops = inv_plus_parity"
  "r_inv_minus parity_refine_ops = inv_minus_parity"
  "r_inv_times parity_refine_ops = inv_times_parity"
  "r_intersect parity_refine_ops = inf"
  by (simp_all add: parity_refine_ops_def)

lemma parity_backward_domain:
  "mono_refinement inf aval_parity parity_tobool
     inv_conservative inv_eq_parity inv_plus_parity inv_minus_parity inv_times_parity"
proof unfold_locales
qed (simp_all add: inv_conservative_def inv_eq_parity_sound inv_plus_parity_sound
       inv_minus_parity_sound inv_times_parity_sound parity_tobool_sound[unfolded truthy_def]
       inf_mono parity_arith.aval_dom_mono inv_eq_parity_mono inv_plus_parity_mono
       inv_minus_parity_mono inv_times_parity_mono parity_tobool_mono le_infI1 le_infI2)

subsection \<open>Executable refinement tests\<close>

text \<open>
  Evaluated regression cases: an odd sum with an even operand forces the other
  odd, and an odd product forces both factors odd.
\<close>

lemma parity_inverse_regression:
  "inv_plus_parity POdd PTop PEven = (POdd, PEven)"
  "inv_minus_parity PEven PTop POdd = (POdd, POdd)"
  "inv_times_parity POdd PTop PTop = (POdd, POdd)"
  "inv_eq_parity True PTop PEven = (PEven, PEven)"
  by eval+

end
