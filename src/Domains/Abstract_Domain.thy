theory Abstract_Domain
  imports IMP2_Syntax
begin

(*
  Abstract Domain -- Locale and Lifted State Concretization.

  An abstract domain is a type 'a equipped with:
    bot     : bottom element (empty concretization)
    join    : least upper bound (sound join)
    widen   : widening operator (ensures termination)
    gamma   : concretization map  'a => int set

  For program analysis, individual variable values are abstracted by
  'a, and a full abstract program state is  vname => 'a.
  The concretization is lifted pointwise to state sets.
*)

(* ── Abstract State Type (global synonym, parameterised) ────────
   An abstract state maps each variable to an abstract value.
   Defined outside the locale so it is available theory-wide. *)

type_synonym 'a abs_state = "vname => 'a"

(* ── Abstract Domain Locale ───────────────────────────────────── *)

locale abstract_domain =
  fixes gamma    :: "'a::ord => int set"         (* per-value concretization *)
  fixes bot      :: "'a"                         (* bottom = empty           *)
  fixes join_op  :: "'a => 'a => 'a"             (* sound upper bound        *)
  fixes widen    :: "'a => 'a => 'a"             (* widening for termination *)
  assumes gamma_bot:
    "gamma bot = {}"
  assumes gamma_join_ub1:
    "gamma a <= gamma (join_op a b)"
  assumes gamma_join_ub2:
    "gamma b <= gamma (join_op a b)"
  assumes widen_ub1:
    "gamma a <= gamma (widen a b)"
  assumes widen_ub2:
    "gamma b <= gamma (widen a b)"
  (* Semilattice axioms: required for fold-based join over sets to be order-independent. *)
  assumes join_comm:  "join_op a b = join_op b a"
  assumes join_assoc: "join_op a (join_op b c) = join_op (join_op a b) c"
begin

(* ── Lifted Concretization to Abstract States ─────────────────── *)

definition gamma_state :: "'a abs_state => state set" where
  "gamma_state sigma = {s. ALL x. s x : gamma (sigma x)}"

(* ── Pointwise Lift of bot, join, widen to abs_state ──────────── *)

definition bot_state :: "'a abs_state" where
  "bot_state = (%_. bot)"

definition join_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "join_state sigma1 sigma2 = (%x. join_op (sigma1 x) (sigma2 x))"

definition widen_state :: "'a abs_state => 'a abs_state => 'a abs_state" where
  "widen_state sigma1 sigma2 = (%x. widen (sigma1 x) (sigma2 x))"

(* ── comp_fun_commute for join_op (from comm + assoc) ─────────── *)
(*
  Required so Finite_Set.fold join_op bot_abs S is independent of order.
  Proof: join_op b (join_op a z) = join_op a (join_op b z)
         via assoc + comm on outer pair.
*)

lemma join_comp_fun_commute: "comp_fun_commute join_op"
  apply (unfold_locales)
  apply (simp add: fun_eq_iff join_assoc[symmetric])
  by (metis join_assoc join_comm)

lemma join_state_comp_fun_commute: "comp_fun_commute join_state"
  apply (unfold_locales)
  apply (simp add: fun_eq_iff join_state_def)
  by (metis join_assoc join_comm)

(* ── Key Properties of the Lifted Operations ─────────────────── *)

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

end
