theory Abstract_Domain
  imports "Voblint_IMP2.IMP2_Syntax" "Voblint_IMP2.IMP2_Expr" "TD.Update_rules"
begin

hide_const (open) Update_rules.N

unbundle lattice_syntax

section \<open>Abstract domain: locale and lifted state concretization\<close>

text \<open>
  An abstract domain is a type 'a equipped with:
    bot     : bottom element (empty concretization)
    sup     : sound upper bound (for RHS fold over predecessor edges)
    widen   : widening operator (ensures termination)
    \<gamma>   : concretization map  'a => int set

  bot and sup come from the bounded_semilattice_sup_bot type class.
  'a abs_state = vname => 'a inherits the same class pointwise via HOL's
  fun instances, so we never need to define lifted-bot / lifted-join.
\<close>

type_synonym 'a abs_state = "vname => 'a"

(* HOL ships fun :: (type, bounded_lattice) bounded_lattice but not this
   weaker pointwise instance; abs_state needs it for TD_side part_post_solution. *)
instance "fun" :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

(* Helper exposed globally: sup over any semilattice_sup is comp_fun_commute.
   Available to downstream proofs that thread mem_image_le_fold etc. *)
lemma comp_fun_commute_sup:
  "comp_fun_commute ((\<squnion>) :: 'a::semilattice_sup \<Rightarrow> 'a \<Rightarrow> 'a)"
  by unfold_locales (simp add: fun_eq_iff sup_left_commute)

(* P3 discharge: pointwise sup on abs_state is comp_fun_idem.  Follows from
   the standard `comp_fun_idem_sup` because (vname => 'a) inherits
   semilattice_sup pointwise from 'a.  Used downstream to drop the
   `comp_fun_idem (ac_join cfg)` assumption from pipeline theorems. *)
lemma join_state_comp_fun_idem:
  "comp_fun_idem ((\<squnion>) ::
     'a::semilattice_sup abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  by (rule comp_fun_idem_sup)

subsection \<open>Sound-domain type class\<close>

class sound_domain = bounded_semilattice_sup_bot +
  fixes gamma :: "'a \<Rightarrow> int set"
  assumes gamma_bot: "gamma bot = {}"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"

subsection \<open>Lifted concretization\<close>

definition gamma_state :: "('a::sound_domain) abs_state \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>") where
  "gamma_state \<sigma> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}"

(* Note: pointwise bot / sup on 'a abs_state come from HOL's
   fun :: bot and fun :: sup instances; no extra definitions needed. *)

subsection \<open>Derived gamma-sup bounds\<close>

lemma gamma_sup_ub1: "gamma a \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_sup_ub2: "gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  by (rule gamma_mono[OF sup_ge2])

lemma gamma_sup_sound: "gamma a \<union> gamma b \<subseteq> gamma (a \<squnion> b)" for a b :: "'a::sound_domain"
  using gamma_sup_ub1 gamma_sup_ub2 by blast

subsection \<open>Lifted concretization lemmas\<close>

lemma gamma_state_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> \<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot:
  "\<lbrakk>bot :: 'a::sound_domain abs_state\<rbrakk> = {}"
  unfolding gamma_state_def bot_fun_def using gamma_bot by auto

lemma gamma_state_sup_ub1:
  "\<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub1 by blast

lemma gamma_state_sup_ub2:
  "\<lbrakk>sigma2\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub2 by blast

lemma sup_fold_ge:
  fixes S :: "'a::bounded_semilattice_sup_bot set"
  assumes "finite S" and "x \<in> S"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot S"
  using assms
proof (induct S rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert a F)
  have fold_ins: "Finite_Set.fold (\<squnion>) bot (insert a F)
      = a \<squnion> Finite_Set.fold (\<squnion>) bot F"
    by (metis (full_types) Sup_fin.eq_fold Sup_fin.insert finite.simps insert.hyps(1) insert_commute
        insert_not_empty)
  show ?case
  proof (cases "x = a")
    case True show ?thesis using True fold_ins by simp
  next
    case False
    then have "x \<in> F" using insert.prems by simp
    then have "x \<le> Finite_Set.fold (\<squnion>) bot F" by (rule insert.hyps(3))
    then show ?thesis using fold_ins le_supI2 by metis
  qed
qed

lemma gamma_abs_sup_set_ub:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> gamma x \<subseteq> gamma (Finite_Set.fold (\<squnion>) bot S)"
  for x :: "'a::sound_domain"
  using gamma_mono sup_fold_ge by auto

subsection \<open>Abstract domain locale (with widening)\<close>

text \<open>
  Extends sound_domain with widening for termination guarantees.
  Required when connecting to the TD solver for a domain with
  infinite ascending chains (e.g., intervals).

  Finite domains (sign, parity) instantiate this with widen = sup;
  the widen axioms then hold trivially from sup_ge1/sup_ge2.
\<close>

subsection \<open>Abstract-domain type class (with widening)\<close>

text \<open>
  Extends sound_domain with widening for termination guarantees.
  Required when connecting to the TD solver for a domain with
  infinite ascending chains (e.g., intervals).

  Finite domains (sign, parity) instantiate this with widen = sup;
  the widen axioms then hold trivially from sup_ge1/sup_ge2.

  Inherits widen from TD.Update_rules widening rather than re-fixing it,
  so sign :: warrowing and ivl :: warrowing instantiations remain consistent.
\<close>

class abstract_domain = sound_domain + widening

subsection \<open>Derived widening-gamma bounds\<close>

lemma widen_ub1: "gamma a \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::abstract_domain"
  by (rule gamma_mono[OF widen_ge1])

lemma widen_ub2: "gamma b \<subseteq> gamma (a \<nabla> b)" for a b :: "'a::abstract_domain"
  by (rule gamma_mono[OF widen_ge2])

subsection \<open>Lifted widening\<close>

definition widen_state ::
    "('a::abstract_domain) abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  where
  "widen_state sigma1 sigma2 = (\<lambda>x. widen (sigma1 x) (sigma2 x))"

subsection \<open>Backward-analysis locale\<close>

text \<open>
  Extends @{class sound_domain} with the infrastructure for backward
  (inverse) evaluation of guards and arithmetic expressions.
  Per-domain: provide meet, aval_abs, and inv_* operators; the generic
  afilter / bfilter and their soundness theorems follow by induction.
\<close>

locale backward_domain =
  fixes
    meet     :: "'a::sound_domain => 'a => 'a"
    and aval_abs  :: "aexp => 'a abs_state => 'a"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
    meet_sound:
      "n \<in> gamma a \<Longrightarrow> n \<in> gamma b \<Longrightarrow> n \<in> gamma (meet a b)"
  and aval_abs_sound:
      "(\<forall>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> aval e s \<in> gamma (aval_abs e \<sigma>)"
  and inv_less_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
  and inv_plus_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 + n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_plus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus r a1 a2))"
  and inv_minus_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 - n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_minus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus r a1 a2))"
  and inv_times_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 * n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_times r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times r a1 a2))"
begin

fun afilter :: "aexp => 'a => 'a abs_state => 'a abs_state" where
    "afilter (BaseN (AExp.V x)) a \<sigma> = \<sigma>(x := meet a (\<sigma> x))"
  | "afilter (Plus  e1 e2) a \<sigma> =
       (let (a1, a2) = inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter (Minus e1 e2) a \<sigma> =
       (let (a1, a2) = inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter (Times e1 e2) a \<sigma> =
       (let (a1, a2) = inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter _ a \<sigma> = \<sigma>"

fun bfilter :: "bexp => bool => 'a abs_state => 'a abs_state" where
    "bfilter (Less e1 e2) res \<sigma> =
       (let (a1, a2) = inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "bfilter (Not b) res \<sigma> = bfilter b (\<not> res) \<sigma>"
  | "bfilter (And b1 b2) True  \<sigma> = bfilter b1 True  (bfilter b2 True  \<sigma>)"
  | "bfilter (And b1 b2) False \<sigma> = bfilter b1 False \<sigma> \<squnion> bfilter b2 False \<sigma>"
  | "bfilter (Or  b1 b2) True  \<sigma> = bfilter b1 True  \<sigma> \<squnion> bfilter b2 True  \<sigma>"
  | "bfilter (Or  b1 b2) False \<sigma> = bfilter b1 False (bfilter b2 False \<sigma>)"
  | "bfilter (Eq  e1 e2) True  \<sigma> =
       (let a = meet (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a (afilter e2 a \<sigma>))"
  | "bfilter _ _ \<sigma> = \<sigma>"

lemma afilter_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "aval e s \<in> gamma a"
  shows "s \<in> \<lbrakk>afilter e a \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: a \<sigma>)
  case (BaseN a')
  show ?case proof (cases a')
    case (V x)
    have sx_a: "s x \<in> gamma a"
      using BaseN.prems(2) V by (simp add: aval.simps AExp.aval.simps)
    have sx_s: "s x \<in> gamma (\<sigma> x)"
      using BaseN.prems(1) unfolding gamma_state_def by simp
    show ?thesis
      unfolding V gamma_state_def afilter.simps
    proof (intro CollectI allI)
      fix y show "s y \<in> gamma ((\<sigma>(x := meet a (\<sigma> x))) y)"
        using meet_sound[OF sx_a sx_s] BaseN.prems(1)[unfolded gamma_state_def]
        by (cases "y = x") auto
    qed
  qed (auto simp: afilter.simps BaseN.prems(1))
next
  case (Plus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using Plus.prems(1) unfolding gamma_state_def by simp
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have asum: "aval e1 s + aval e2 s \<in> gamma a" using Plus.prems(2) by (simp add: aval.simps)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_plus_sound[OF e1a e2a asum] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Plus.IH(2)[OF Plus.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Plus.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Minus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using Minus.prems(1) unfolding gamma_state_def by simp
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have adiff: "aval e1 s - aval e2 s \<in> gamma a" using Minus.prems(2) by (simp add: aval.simps)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_minus_sound[OF e1a e2a adiff] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Minus.IH(2)[OF Minus.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Minus.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Times e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using Times.prems(1) unfolding gamma_state_def by simp
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have aprod: "aval e1 s * aval e2 s \<in> gamma a" using Times.prems(2) by (simp add: aval.simps)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_times_sound[OF e1a e2a aprod] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Times.IH(2)[OF Times.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Times.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
qed

lemma bfilter_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "bval b s = res"
  shows "s \<in> \<lbrakk>bfilter b res \<sigma>\<rbrakk>"
using assms proof (induction b arbitrary: res \<sigma>)
  case (BaseB b') thus ?case by (simp add: bfilter.simps)
next
  case (Not b)
  have bv': "bval b s = (\<not> res)" using Not.prems(2) by (auto)
  from Not.IH[OF Not.prems(1) bv'] show ?case by (simp add: bfilter.simps)
next
  case (And b1 b2)
  show ?case proof (cases res)
    case True
    have v1: "bval b1 s = True" and v2: "bval b2 s = True"
      using And.prems(2) True by (simp_all add: bval.simps)
    have gs2: "s \<in> \<lbrakk>bfilter b2 True \<sigma>\<rbrakk>"
      using And.IH(2)[OF And.prems(1) v2] by simp
    show ?thesis
      using And.IH(1)[OF gs2 v1] by (simp add: True bfilter.simps)
  next
    case False
    have disj: "\<not> bval b1 s \<or> \<not> bval b2 s"
      using And.prems(2) False by (auto simp: bval.simps)
    show ?thesis proof (cases "bval b1 s")
      case b1F: False
      have v1: "bval b1 s = False" using b1F by simp
      have h: "s \<in> \<lbrakk>bfilter b1 False \<sigma>\<rbrakk>"
        using And.IH(1)[OF And.prems(1) v1] by simp
      have sup1: "s \<in> \<lbrakk>bfilter b1 False \<sigma> \<squnion> bfilter b2 False \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1[of "bfilter b1 False \<sigma>" "bfilter b2 False \<sigma>"] h]
        by simp
      show ?thesis using False sup1
        using bfilter.simps(4) by presburger
    next
      case b1T: True
      have v2: "bval b2 s = False" using disj b1T by simp
      have h: "s \<in> \<lbrakk>bfilter b2 False \<sigma>\<rbrakk>"
        using And.IH(2)[OF And.prems(1) v2] by simp
      have sup2: "s \<in> \<lbrakk>bfilter b1 False \<sigma> \<squnion> bfilter b2 False \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2[of "bfilter b2 False \<sigma>" "bfilter b1 False \<sigma>"] h]
        by simp
      show ?thesis using False sup2
        using bfilter.simps(4) by presburger 
    qed
  qed
next
  case (Or b1 b2)
  show ?case proof (cases res)
    case True
    have disj: "bval b1 s \<or> bval b2 s" using Or.prems(2) True by (simp add: bval.simps)
    show ?thesis proof (cases "bval b1 s")
      case b1T: True
      have v1: "bval b1 s = True" using b1T by simp
      have h: "s \<in> \<lbrakk>bfilter b1 True \<sigma>\<rbrakk>"
        using Or.IH(1)[OF Or.prems(1) v1] by simp
      have sup1: "s \<in> \<lbrakk>bfilter b1 True \<sigma> \<squnion> bfilter b2 True \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1[of "bfilter b1 True \<sigma>" "bfilter b2 True \<sigma>"] h]
        by simp
      show ?thesis using True sup1
        using bfilter.simps(5) by presburger 
    next
      case b1F: False
      have v2: "bval b2 s = True" using disj b1F by simp
      have h: "s \<in> \<lbrakk>bfilter b2 True \<sigma>\<rbrakk>"
        using Or.IH(2)[OF Or.prems(1) v2] by simp
      have sup2: "s \<in> \<lbrakk>bfilter b1 True \<sigma> \<squnion> bfilter b2 True \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2[of "bfilter b2 True \<sigma>" "bfilter b1 True \<sigma>"] h]
        by simp
      show ?thesis using True sup2
        using bfilter.simps(5) by presburger
    qed
  next
    case False
    have v1: "bval b1 s = False" and v2: "bval b2 s = False"
      using Or.prems(2) False by (simp_all add: bval.simps)
    have gs2: "s \<in> \<lbrakk>bfilter b2 False \<sigma>\<rbrakk>"
      using Or.IH(2)[OF Or.prems(1) v2] by simp
    show ?thesis
      using Or.IH(1)[OF gs2 v1] by (simp add: False bfilter.simps)
  qed
next
  case (Less e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using Less.prems(1) unfolding gamma_state_def by simp
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have less: "(aval e1 s < aval e2 s) = res" using Less.prems(2) by (simp add: bval.simps)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_less_sound[OF e1a e2a less] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using afilter_sound[OF Less.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding bfilter.simps pair[symmetric] Let_def
    using afilter_sound[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Eq e1 e2)
  show ?case proof (cases res)
    case True
    have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using Eq.prems(1) unfolding gamma_state_def by simp
    have eq: "aval e1 s = aval e2 s" using Eq.prems(2) True by (simp add: bval.simps)
    have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
    have e2a: "aval e1 s \<in> gamma (aval_abs e2 \<sigma>)"
      using aval_abs_sound[OF gs] eq by simp
    have ma: "aval e1 s \<in> gamma (meet (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))"
      using meet_sound[OF e1a e2a] by simp
    have me2: "aval e2 s \<in> gamma (meet (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))"
      using ma eq by simp
    have gs2: "s \<in> \<lbrakk>afilter e2 (meet (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)) \<sigma>\<rbrakk>"
      using afilter_sound[OF Eq.prems(1) me2] by simp
    show ?thesis
      unfolding True bfilter.simps Let_def
      using afilter_sound[OF gs2 ma]
      by (metis True bfilter.simps(7))
  next
    case False
    then show ?thesis using Eq.prems(1) by (simp add: bfilter.simps)
  qed
qed

end

subsection \<open>Printable-domain typeclass\<close>

text \<open>
  The @{text show_val} class equips an abstract value type with a string
  printer.  Separate from @{class abstract_domain} so the abstract-domain
  class stays a purely semantic object; rendering is a separate concern.

  Every domain used in visualisation instantiates this class.
  The @{text Analysis_GraphViz} rendering layer is parameterised over any
  @{text "'a::show_val"} and needs no domain-specific code paths.
\<close>

class show_val =
  fixes show_val :: "'a \<Rightarrow> string"

subsection \<open>String utilities for show_val instances\<close>

text \<open>
  Shared nat/int-to-string helpers so domain @{class show_val} instances
  do not each re-define them.
\<close>

fun show_nat :: "nat \<Rightarrow> string" where
  "show_nat n =
     (if n < 10 then [char_of (n + 48)]
      else show_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition show_int :: "int \<Rightarrow> string" where
  "show_int i =
     (if i < 0 then ''-'' @ show_nat (nat (- i))
      else show_nat (nat i))"

end
