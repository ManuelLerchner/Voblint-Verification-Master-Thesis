theory Abstract_Domain
  imports "Voblint_IMP2.IMP2_Syntax"
begin

(* Re-enable HOL.Lattices' \<squnion> / \<sqinter> notation (HOL-IMP parent strips it). *)
notation sup (infixl "\<squnion>" 65)
notation inf (infixl "\<sqinter>" 70)

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

locale sound_domain =
  fixes \<gamma> :: "'a::bounded_semilattice_sup_bot => int set"
  assumes gamma_bot:
    "\<gamma> bot = {}"
  assumes gamma_mono:
    "a \<le> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
begin

subsection \<open>Derived \<gamma>-sup bounds\<close>

lemma gamma_sup_ub1: "\<gamma> a \<subseteq> \<gamma> (a \<squnion> b)"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_sup_ub2: "\<gamma> b \<subseteq> \<gamma> (a \<squnion> b)"
  by (rule gamma_mono[OF sup_ge2])

lemma gamma_sup_sound:
  "\<gamma> a \<union> \<gamma> b \<subseteq> \<gamma> (a \<squnion> b)"
  using gamma_sup_ub1 gamma_sup_ub2 by blast

subsection \<open>Lifted concretization\<close>

definition gamma_state :: "'a abs_state => store set" where
  "gamma_state \<sigma> = {s. \<forall>x. s x \<in> \<gamma> (\<sigma> x)}"

(* Note: pointwise bot / sup on 'a abs_state come from HOL's
   fun :: bot and fun :: sup instances; no extra definitions needed. *)

lemma gamma_state_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> gamma_state sigma1 \<subseteq> gamma_state sigma2"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot:
  "gamma_state bot = {}"
  unfolding gamma_state_def bot_fun_def using gamma_bot by auto

lemma gamma_state_sup_ub1:
  "gamma_state sigma1 \<subseteq> gamma_state (sigma1 \<squnion> sigma2)"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub1 by blast

lemma gamma_state_sup_ub2:
  "gamma_state sigma2 \<subseteq> gamma_state (sigma1 \<squnion> sigma2)"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub2 by blast

end

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

context sound_domain
begin

lemma gamma_abs_sup_set_ub:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> \<gamma> x \<subseteq> \<gamma> (Finite_Set.fold (\<squnion>) bot S)"
  using gamma_mono sup_fold_ge by auto

end

subsection \<open>Abstract domain locale (with widening)\<close>

text \<open>
  Extends sound_domain with widening for termination guarantees.
  Required when connecting to the TD solver for a domain with
  infinite ascending chains (e.g., intervals).

  Finite domains (sign, parity) instantiate this with widen = sup;
  the widen axioms then hold trivially from sup_ge1/sup_ge2.
\<close>

locale abstract_domain = sound_domain +
  fixes widen :: "'a => 'a => 'a"
  assumes widen_ub1:
    "\<gamma> a \<subseteq> \<gamma> (widen a b)"
  assumes widen_ub2:
    "\<gamma> b \<subseteq> \<gamma> (widen a b)"
begin

definition widen_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "widen_state sigma1 sigma2 = (\<lambda>x. widen (sigma1 x) (sigma2 x))"

end

end
