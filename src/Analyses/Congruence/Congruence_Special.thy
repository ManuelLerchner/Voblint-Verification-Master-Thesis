theory Congruence_Special
  imports Congruence_Arithmetic "Voblint_Nonrelational.Special_Ops"
begin

section \<open>What a Min or Max call tells you about a residue class\<close>

text \<open>
  \<open>Min a b\<close> and \<open>Max a b\<close> each return one of their two operands, never a
  newly computed integer, so whatever describes both operands describes the
  result. Congruence answers with the join of the two argument classes: sound
  for either selection, and the sharpest answer available without knowing
  which one is taken. \<open>Nondet_Int\<close> constrains nothing and lands at \<open>top\<close>.

  The reader needs \<open>aval_congruence\<close>, Congruence's expression evaluator, from
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Arithmetic\<close>.
\<close>

text \<open>
  Two known-even operands stay even, exactly as Parity's \<open>parity_min\<close> keeps
  \<open>PEven\<close>; a mismatch of moduli falls back on their common coarsening rather
  than on \<open>top\<close>, which is where the join earns over a constant answer.
\<close>

definition congruence_min :: "congruence => congruence => congruence" where
  "congruence_min a b = a \<squnion> b"

definition congruence_max :: "congruence => congruence => congruence" where
  "congruence_max a b = a \<squnion> b"

lemma gamma_congruence_sup_ub1: "gamma_congruence a \<subseteq> gamma_congruence (a \<squnion> b)"
proof -
  have "\<gamma> (a::congruence) \<subseteq> \<gamma> (a \<squnion> b)" by (rule gamma_mono[OF sup_ge1])
  then show ?thesis by simp
qed

lemma gamma_congruence_sup_ub2: "gamma_congruence b \<subseteq> gamma_congruence (a \<squnion> b)"
proof -
  have "\<gamma> (b::congruence) \<subseteq> \<gamma> (a \<squnion> b)" by (rule gamma_mono[OF sup_ge2])
  then show ?thesis by simp
qed

lemma congruence_min_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "min i j \<in> gamma_congruence (congruence_min a b)"
  using assms gamma_congruence_sup_ub1[of a b] gamma_congruence_sup_ub2[of b a]
  unfolding congruence_min_def min_def by auto

lemma congruence_max_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "max i j \<in> gamma_congruence (congruence_max a b)"
  using assms gamma_congruence_sup_ub1[of a b] gamma_congruence_sup_ub2[of b a]
  unfolding congruence_max_def max_def by auto

lemma congruence_min_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> congruence_min a1 b1 \<le> congruence_min a2 (b2::congruence)"
  unfolding congruence_min_def by (rule sup_mono)

lemma congruence_max_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> congruence_max a1 b1 \<le> congruence_max a2 (b2::congruence)"
  unfolding congruence_max_def by (rule sup_mono)

subsection \<open>Special-call dispatch\<close>

definition congruence_special_ops :: "congruence special_ops" where
  "congruence_special_ops = (| special_min = congruence_min, special_max = congruence_max |)"

lemma congruence_special_ops_min [simp]: "special_min congruence_special_ops = congruence_min"
  by (simp add: congruence_special_ops_def)

lemma congruence_special_ops_max [simp]: "special_max congruence_special_ops = congruence_max"
  by (simp add: congruence_special_ops_def)

interpretation congruence_special: sound_special_ops congruence_special_ops aval_congruence
proof unfold_locales
  fix i j :: int and p q :: congruence
  assume "i \<in> \<gamma> p" and "j \<in> \<gamma> q"
  then show "min i j \<in> \<gamma> (special_min congruence_special_ops p q)"
    using congruence_min_sound by simp
next
  fix i j :: int and p q :: congruence
  assume "i \<in> \<gamma> p" and "j \<in> \<gamma> q"
  then show "max i j \<in> \<gamma> (special_max congruence_special_ops p q)"
    using congruence_max_sound by simp
next
  fix p1 p2 q1 q2 :: congruence
  assume "p1 \<le> p2" and "q1 \<le> q2"
  then show "special_min congruence_special_ops p1 q1
               \<le> special_min congruence_special_ops p2 q2"
    by (simp add: congruence_min_mono)
next
  fix p1 p2 q1 q2 :: congruence
  assume "p1 \<le> p2" and "q1 \<le> q2"
  then show "special_max congruence_special_ops p1 q1
               \<le> special_max congruence_special_ops p2 q2"
    by (simp add: congruence_max_mono)
next
  fix s :: store and \<sigma> :: "vname \<Rightarrow> congruence" and e :: exp
  assume "\<forall>x. s x \<in> \<gamma> (\<sigma> x)"
  then show "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (aval_congruence e \<sigma>)"
    by (rule congruence_arith.aval_dom_sound)
next
  fix \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> congruence" and e :: exp
  assume "\<sigma>1 \<le> \<sigma>2"
  then show "aval_congruence e \<sigma>1 \<le> aval_congruence e \<sigma>2"
    by (rule congruence_arith.aval_dom_mono)
qed

fun special_congruence ::
    "special_call => vname => (vname => congruence) => (vname => congruence)"
where
  "special_congruence Nondet_Int x \<sigma> = \<sigma>(x := top)"
| "special_congruence (Min a b) x \<sigma> =
     \<sigma>(x := congruence_min (aval_congruence a \<sigma>) (aval_congruence b \<sigma>))"
| "special_congruence (Max a b) x \<sigma> =
     \<sigma>(x := congruence_max (aval_congruence a \<sigma>) (aval_congruence b \<sigma>))"

lemma special_congruence_eq_transfer:
  "special_congruence sc x \<sigma> = congruence_special.special_transfer sc x \<sigma>"
  by (cases sc) simp_all

lemmas special_congruence_sound =
  congruence_special.special_transfer_sound[folded special_congruence_eq_transfer]
lemmas special_congruence_mono =
  congruence_special.special_transfer_mono[folded special_congruence_eq_transfer]

end
