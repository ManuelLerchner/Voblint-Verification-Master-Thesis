theory Abstract_Domain
  imports "Voblint_VIMP.VIMP_Syntax" "Voblint_VIMP.VIMP_Expr" "TD.Update_rules"
    "Voblint_CFG.CFG_Def"
begin

hide_const (open) Update_rules.N

text \<open>The solver unknown for a program point is a CFG node.  Analysis-facing code keeps the
  short name \<open>pp\<close> for it; a return node is \<^term>\<open>FunctionResult p\<close>, a callee entry
  \<^term>\<open>FunctionEntry p\<close>, an ordinary location \<^term>\<open>Statement n\<close>.\<close>
type_synonym pp = cfg_node

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

text \<open>Pointwise join on abstract states is idempotent because the value-domain
  semilattice structure lifts pointwise.  Finite folds can therefore use the
  standard idempotent-join laws without a separate state-level assumption.\<close>
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

(* The pointwise projection gamma_state_def unfolds to; downstream proofs
   cite this instead of re-unfolding the definition at each site. *)
lemma gamma_stateD [dest]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<forall>x. s x \<in> gamma (\<sigma> x)"
  for \<sigma> :: "'a::sound_domain abs_state"
  unfolding gamma_state_def by simp

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
    "afilter (V x) a \<sigma> = \<sigma>(x := meet a (\<sigma> x))"
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
  case (N n)
  then show ?case by simp
next
  case (V x)
  have sx_a: "s x \<in> gamma a"
    using V.prems(2) by simp
  have sx_s: "s x \<in> gamma (\<sigma> x)"
    using gamma_stateD[OF V.prems(1)] by simp
  show ?case
    unfolding gamma_state_def afilter.simps
  proof (intro CollectI allI)
    fix y show "s y \<in> gamma ((\<sigma>(x := meet a (\<sigma> x))) y)"
      using meet_sound[OF sx_a sx_s] gamma_stateD[OF V.prems(1)]
      by (cases "y = x") auto
  qed
next
  case (Plus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Plus.prems(1)] .
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have asum: "aval e1 s + aval e2 s \<in> gamma a" using Plus.prems(2) by simp
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
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Minus.prems(1)] .
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have adiff: "aval e1 s - aval e2 s \<in> gamma a" using Minus.prems(2) by simp
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
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Times.prems(1)] .
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have aprod: "aval e1 s * aval e2 s \<in> gamma a" using Times.prems(2) by simp
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
  case (Bc b') thus ?case by simp
next
  case (Not b)
  have bv': "bval b s = (\<not> res)" using Not.prems(2) by (auto)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And b1 b2)
  show ?case proof (cases res)
    case True
    have v1: "bval b1 s = True" and v2: "bval b2 s = True"
      using And.prems(2) True by simp_all
    have gs2: "s \<in> \<lbrakk>bfilter b2 True \<sigma>\<rbrakk>"
      using And.IH(2)[OF And.prems(1) v2] by simp
    show ?thesis
      using And.IH(1)[OF gs2 v1] by (simp add: True)
  next
    case False
    have disj: "\<not> bval b1 s \<or> \<not> bval b2 s"
      using And.prems(2) False by auto
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
    have disj: "bval b1 s \<or> bval b2 s" using Or.prems(2) True by simp
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
      using Or.prems(2) False by simp_all
    have gs2: "s \<in> \<lbrakk>bfilter b2 False \<sigma>\<rbrakk>"
      using Or.IH(2)[OF Or.prems(1) v2] by simp
    show ?thesis
      using Or.IH(1)[OF gs2 v1] by (simp add: False)
  qed
next
  case (Less e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Less.prems(1)] .
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF gs] by simp
  have less: "(aval e1 s < aval e2 s) = res" using Less.prems(2) by simp
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
    have gs: "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD[OF Eq.prems(1)] .
    have eq: "aval e1 s = aval e2 s" using Eq.prems(2) True by simp
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
      using afilter_sound[OF gs2 ma]
      by (simp add: True Let_def)
  next
    case False
    then show ?thesis using Eq.prems(1) by simp
  qed
qed

end

subsection \<open>Conservative inverse operator\<close>

text \<open>
  A domain that is too coarse for useful arithmetic inversion (e.g. sign,
  which cannot narrow either operand of a plus/minus/times from its result)
  instantiates @{term inv_plus} / @{term inv_minus} / @{term inv_times} with
  this shared no-op: both operands pass through unchanged. Any
  @{class sound_domain} discharges its soundness for free, so domains share
  one proof instead of each restating the same trivial obligation.
\<close>

definition inv_conservative :: "'a => 'a => 'a => 'a * 'a" where
  "inv_conservative r a1 a2 = (a1, a2)"

lemma inv_conservative_sound:
  fixes a1 a2 :: "'a::sound_domain"
  assumes "n1 \<in> gamma a1" and "n2 \<in> gamma a2"
  shows "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
  using assms by (simp add: inv_conservative_def)

subsection \<open>Monotone backward-analysis locale\<close>

text \<open>
  Extends @{locale backward_domain} with monotonicity of the domain-author
  operators.  The generic @{term afilter} / @{term bfilter} are then monotone in
  the abstract state (and target value) by the same induction that proves their
  soundness -- discharged once here instead of once per domain.  A concrete
  domain interprets this locale by supplying the six operator-monotonicity facts;
  the inv-operator obligations are stated in the componentwise @{term fst} /
  @{term snd} shape the domains prove directly.
\<close>

locale backward_domain_mono = backward_domain +
  assumes meet_mono:
      "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> meet a1 b1 \<le> meet a2 b2"
  and aval_abs_mono:
      "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> aval_abs e \<sigma>1 \<le> aval_abs e \<sigma>2"
  and inv_less_mono:
      "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       fst (inv_less res x1 y1) \<le> fst (inv_less res x2 y2) \<and>
       snd (inv_less res x1 y1) \<le> snd (inv_less res x2 y2)"
  and inv_plus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       fst (inv_plus r1 x1 y1) \<le> fst (inv_plus r2 x2 y2) \<and>
       snd (inv_plus r1 x1 y1) \<le> snd (inv_plus r2 x2 y2)"
  and inv_minus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       fst (inv_minus r1 x1 y1) \<le> fst (inv_minus r2 x2 y2) \<and>
       snd (inv_minus r1 x1 y1) \<le> snd (inv_minus r2 x2 y2)"
  and inv_times_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow>
       fst (inv_times r1 x1 y1) \<le> fst (inv_times r2 x2 y2) \<and>
       snd (inv_times r1 x1 y1) \<le> snd (inv_times r2 x2 y2)"
begin

text \<open>Expose the @{term afilter} arithmetic recursions in @{term fst} / @{term snd} form.\<close>
lemma afilter_Plus_unfold:
  "afilter (Plus e1 e2) a \<sigma> =
     afilter e1 (fst (inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Minus_unfold:
  "afilter (Minus e1 e2) a \<sigma> =
     afilter e1 (fst (inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Times_unfold:
  "afilter (Times e1 e2) a \<sigma> =
     afilter e1 (fst (inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma bfilter_Less_unfold:
  "bfilter (Less e1 e2) res \<sigma> =
     afilter e1 (fst (inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_mono:
  "a1 \<le> a2 \<Longrightarrow> \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> afilter e a1 \<sigma>1 \<le> afilter e a2 \<sigma>2"
proof (induction e arbitrary: a1 a2 \<sigma>1 \<sigma>2)
  case (N n)
  then show ?case by simp
next
  case (V x)
  show ?case
    unfolding afilter.simps
  proof (rule le_funI)
    fix y
    show "(\<sigma>1(x := meet a1 (\<sigma>1 x))) y \<le> (\<sigma>2(x := meet a2 (\<sigma>2 x))) y"
    proof (cases "y = x")
      case True
      thus ?thesis using meet_mono[OF V.prems(1) le_funD[OF V.prems(2)]] by simp
    next
      case False thus ?thesis using le_funD[OF V.prems(2)] by simp
    qed
  qed
next
  case (Plus e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have iv: "fst (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_plus_mono[OF Plus.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Plus.IH(2)[OF conjunct2[OF iv] Plus.prems(2)])
  show ?case unfolding afilter_Plus_unfold
    by (rule Plus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Minus e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have iv: "fst (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_minus_mono[OF Minus.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Minus.IH(2)[OF conjunct2[OF iv] Minus.prems(2)])
  show ?case unfolding afilter_Minus_unfold
    by (rule Minus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Times e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have iv: "fst (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_times_mono[OF Times.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Times.IH(2)[OF conjunct2[OF iv] Times.prems(2)])
  show ?case unfolding afilter_Times_unfold
    by (rule Times.IH(1)[OF conjunct1[OF iv] step])
qed

lemma bfilter_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> bfilter b res \<sigma>1 \<le> bfilter b res \<sigma>2"
proof (induction b arbitrary: res \<sigma>1 \<sigma>2)
  case (Bc b') thus ?case by simp
next
  case (Not b) show ?case unfolding bfilter.simps by (rule Not.IH[OF Not.prems])
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    have c: "bfilter b2 True \<sigma>1 \<le> bfilter b2 True \<sigma>2" by (rule And.IH(2)[OF And.prems])
    have "bfilter b1 True (bfilter b2 True \<sigma>1) \<le> bfilter b1 True (bfilter b2 True \<sigma>2)"
      by (rule And.IH(1)[OF c])
    thus ?thesis using True by simp
  next
    case False
    have resF: "res = False" using False by simp
    have c1: "bfilter b1 False \<sigma>1 \<le> bfilter b1 False \<sigma>2" by (rule And.IH(1)[OF And.prems])
    have c2: "bfilter b2 False \<sigma>1 \<le> bfilter b2 False \<sigma>2" by (rule And.IH(2)[OF And.prems])
    have e1: "bfilter (And b1 b2) res \<sigma>1 = bfilter b1 False \<sigma>1 \<squnion> bfilter b2 False \<sigma>1"
      using resF by simp
    have e2: "bfilter (And b1 b2) res \<sigma>2 = bfilter b1 False \<sigma>2 \<squnion> bfilter b2 False \<sigma>2"
      using resF by simp
    show ?thesis unfolding e1 e2 by (rule sup_mono[OF c1 c2])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have resT: "res = True" using True by simp
    have c1: "bfilter b1 True \<sigma>1 \<le> bfilter b1 True \<sigma>2" by (rule Or.IH(1)[OF Or.prems])
    have c2: "bfilter b2 True \<sigma>1 \<le> bfilter b2 True \<sigma>2" by (rule Or.IH(2)[OF Or.prems])
    have e1: "bfilter (Or b1 b2) res \<sigma>1 = bfilter b1 True \<sigma>1 \<squnion> bfilter b2 True \<sigma>1"
      using resT by simp
    have e2: "bfilter (Or b1 b2) res \<sigma>2 = bfilter b1 True \<sigma>2 \<squnion> bfilter b2 True \<sigma>2"
      using resT by simp
    show ?thesis unfolding e1 e2 by (rule sup_mono[OF c1 c2])
  next
    case False
    have c: "bfilter b2 False \<sigma>1 \<le> bfilter b2 False \<sigma>2" by (rule Or.IH(2)[OF Or.prems])
    have "bfilter b1 False (bfilter b2 False \<sigma>1) \<le> bfilter b1 False (bfilter b2 False \<sigma>2)"
      by (rule Or.IH(1)[OF c])
    thus ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have iv: "fst (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_less_mono[OF v1 v2])
  have step: "afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule afilter_mono[OF conjunct2[OF iv] Less.prems])
  show ?case unfolding bfilter_Less_unfold
    by (rule afilter_mono[OF conjunct1[OF iv] step])
next
  case (Eq e1 e2)
  show ?case
  proof (cases res)
    case True
    have m: "meet (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1) \<le> meet (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2)"
      by (rule meet_mono[OF aval_abs_mono[OF Eq.prems] aval_abs_mono[OF Eq.prems]])
    have step: "afilter e2 (meet (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1)) \<sigma>1
              \<le> afilter e2 (meet (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2)) \<sigma>2"
      by (rule afilter_mono[OF m Eq.prems])
    show ?thesis using afilter_mono[OF m step] by (simp add: True Let_def)
  next
    case False thus ?thesis using Eq.prems by simp
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
