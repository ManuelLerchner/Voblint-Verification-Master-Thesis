theory Abstract_Domain
  imports IMP2_Syntax
begin

(* Re-enable HOL.Lattices' \<squnion> / \<sqinter> notation (HOL-IMP parent strips it). *)
notation sup (infixl "\<squnion>" 65)
notation inf (infixl "\<sqinter>" 70)

(*
  Abstract Domain -- Locale and Lifted State Concretization.

  An abstract domain is a type 'a equipped with:
    bot     : bottom element (empty concretization)
    join    : sound upper bound (for RHS fold over predecessor edges)
    widen   : widening operator (ensures termination)
    gamma   : concretization map  'a => int set

  For program analysis, individual variable values are abstracted by
  'a, and a full abstract program store is  vname => 'a.
  The concretization is lifted pointwise to store sets.
*)

(* ── Abstract Store Type (global synonym, parameterised) ────────
   An abstract store maps each variable to an abstract value.
   Defined outside any locale so it is available theory-wide. *)

type_synonym 'a abs_state = "vname => 'a"

(* ── Sound Domain Locale ─────────────────────────────────────────
   Minimal requirements for stating and proving soundness:
     - gamma  : concretization  'a => int set
     - bot    : bottom element  (empty concretization)
     - join_op: sound upper bound (for RHS fold over predecessor edges)

   This locale is sufficient for post_fixpoint_sound.
   It does NOT require widening soundness is independent of termination. *)

locale sound_domain =
  fixes gamma :: "'a::bounded_semilattice_sup_bot => int set"
  assumes gamma_bot:
    "gamma bot = {}"
  assumes gamma_mono:
    "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"
begin

(* ── Derived gamma-join bounds ──────────────────────────────── *)

lemma gamma_join_ub1: "gamma a \<subseteq> gamma (a \<squnion> b)"
  by (rule gamma_mono[OF sup_ge1])

lemma gamma_join_ub2: "gamma b \<subseteq> gamma (a \<squnion> b)"
  by (rule gamma_mono[OF sup_ge2])

(* ── Lifted Concretization ───────────────────────────────────── *)

definition gamma_state :: "'a abs_state => store set" where
  "gamma_state sigma = {s. \<forall>x. s x \<in> gamma (sigma x)}"

(* ── Pointwise Lifts of bot and join ────────────────────────── *)

definition bot_state :: "'a abs_state" where
  "bot_state = (\<lambda>_. bot)"

definition join_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "join_state sigma1 sigma2 = (\<lambda>x. sigma1 x \<squnion> sigma2 x)"

(* ── comp_fun_commute (needed for fold-based join over edge sets) *)

lemma join_comp_fun_commute: "comp_fun_commute ((\<squnion>) :: 'a => 'a => 'a)"
  by unfold_locales (simp add: fun_eq_iff sup_left_commute)

lemma join_state_comp_fun_commute: "comp_fun_commute join_state"
  by unfold_locales
     (simp add: fun_eq_iff join_state_def sup_left_commute)

lemma join_state_comm: "join_state s1 s2 = join_state s2 s1"
  unfolding join_state_def by (simp add: fun_eq_iff sup_commute)

(* ── Key Properties ──────────────────────────────────────────── *)

lemma gamma_join_sound:
  "gamma a \<union> gamma b \<subseteq> gamma (a \<squnion> b)"
  using gamma_join_ub1 gamma_join_ub2 by blast

(* Each element of a finite set is below the fold-join over that set.
   TODO: re-derive via comp_fun_idem_sup; higher-order unification through
   Finite_Set.fold currently resists tactics here. *)
lemma join_fold_ge:
  assumes "finite S" and "x \<in> S"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot S"
  sorry

lemma gamma_abs_join_set_ub:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> gamma x \<subseteq> gamma (Finite_Set.fold (\<squnion>) bot S)"
  using gamma_mono join_fold_ge by auto

lemma gamma_state_mono:
  "sigma1 <= sigma2 ==> gamma_state sigma1 <= gamma_state sigma2"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot:
  "gamma_state bot_state = {}"
  unfolding gamma_state_def bot_state_def using gamma_bot by auto

lemma gamma_state_join_ub1:
  "gamma_state sigma1 <= gamma_state (join_state sigma1 sigma2)"
  unfolding gamma_state_def join_state_def
  using gamma_join_ub1 by blast

lemma gamma_state_join_ub2:
  "gamma_state sigma2 <= gamma_state (join_state sigma1 sigma2)"
  unfolding gamma_state_def join_state_def
  using gamma_join_ub2 by blast

end

(* ── Abstract Domain Locale ──────────────────────────────────────
   Extends sound_domain with widening for termination guarantees.
   Required when connecting to the TD solver for a domain with
   infinite ascending chains (e.g., intervals).

   Finite domains (sign, parity) instantiate this with widen = join;
   the widen axioms then hold trivially from the join axioms. *)

locale abstract_domain = sound_domain +
  fixes widen :: "'a => 'a => 'a"
  assumes widen_ub1:
    "gamma a <= gamma (widen a b)"
  assumes widen_ub2:
    "gamma b <= gamma (widen a b)"
begin

definition widen_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "widen_state sigma1 sigma2 = (\<lambda>x. widen (sigma1 x) (sigma2 x))"

end

end
