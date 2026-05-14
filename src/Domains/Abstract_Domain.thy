theory Abstract_Domain
  imports IMP2_Syntax
begin

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
   It does NOT require widening — soundness is independent of termination. *)

locale sound_domain =
  fixes gamma   :: "'a::{preorder,bot} => int set"
  fixes join_op :: "'a => 'a => 'a"
  assumes gamma_bot:
    "gamma bot = {}"
  assumes gamma_mono:
    "a <= b ==> gamma a <= gamma b"
  assumes join_ub1:
    "a <= join_op a b"
  assumes join_ub2:
    "b <= join_op a b"
  assumes join_comm:
    "join_op a b = join_op b a"
  assumes join_assoc:
    "join_op a (join_op b c) = join_op (join_op a b) c"
begin

(* ── Derived gamma-join bounds (from join_ub + gamma_mono) ─── *)

lemma gamma_join_ub1: "gamma a <= gamma (join_op a b)"
  by (rule gamma_mono[OF join_ub1])

lemma gamma_join_ub2: "gamma b <= gamma (join_op a b)"
  by (rule gamma_mono[OF join_ub2])

(* ── Lifted Concretization ───────────────────────────────────── *)

definition gamma_state :: "'a abs_state => store set" where
  "gamma_state sigma = {s. \<forall>x. s x \<in> gamma (sigma x)}"

(* ── Pointwise Lifts of bot and join ────────────────────────── *)

definition bot_state :: "'a abs_state" where
  "bot_state = (\<lambda>_. bot)"

definition join_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "join_state sigma1 sigma2 = (\<lambda>x. join_op (sigma1 x) (sigma2 x))"

(* ── comp_fun_commute (needed for fold-based join over edge sets) *)

lemma join_comp_fun_commute: "comp_fun_commute join_op"
  apply (unfold_locales)
  apply (simp add: fun_eq_iff join_assoc[symmetric])
  by (metis join_assoc join_comm)

lemma join_state_comp_fun_commute: "comp_fun_commute join_state"
  apply (unfold_locales)
  apply (simp add: fun_eq_iff join_state_def)
  by (metis join_assoc join_comm)

lemma join_state_comm: "join_state s1 s2 = join_state s2 s1"
  unfolding join_state_def by (simp add: fun_eq_iff join_comm)

(* ── Key Properties ──────────────────────────────────────────── *)

lemma gamma_join_sound:
  "gamma a \<union> gamma b <= gamma (join_op a b)"
  using gamma_join_ub1 gamma_join_ub2 by blast

(* Each element of a finite set is below the fold-join over that set.
   Needed for collect_pp_abstract_sound. *)
lemma gamma_abs_join_set_ub:
  "finite S ==> x \<in> S ==> gamma x <= gamma (Finite_Set.fold join_op bot S)"
  sorry

lemma gamma_state_mono:
  "sigma1 <= sigma2 ==> gamma_state sigma1 <= gamma_state sigma2"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot:
  "gamma_state bot_state = {}"
  sorry

lemma gamma_state_join_ub1:
  "gamma_state sigma1 <= gamma_state (join_state sigma1 sigma2)"
  sorry

lemma gamma_state_join_ub2:
  "gamma_state sigma2 <= gamma_state (join_state sigma1 sigma2)"
  sorry

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
