theory Sign_Domain
  imports Abstract_Domain Constraint_System
begin

(*
  Sign Domain -- Instantiation of abstract_domain.

  sign abstracts integers by their sign:
    Bot  -- empty (unreachable / undefined)
    Neg  -- strictly negative  {n | n < 0}
    Zero -- exactly zero       {0}
    Pos  -- strictly positive  {n | n > 0}
    Top  -- all integers       UNIV

  Finite lattice, no widening needed (every chain terminates immediately).
  Used as the Tier-1 scaffold domain to validate the full pipeline.
*)

(* ── Sign Datatype ────────────────────────────────────────────── *)

datatype sign = SBot | SNeg | SZero | SPos | STop

(* ── Concretization ───────────────────────────────────────────── *)

fun gamma_sign :: "sign => int set" where
    "gamma_sign SBot  = {}"
  | "gamma_sign SNeg  = {n. n < 0}"
  | "gamma_sign SZero = {0}"
  | "gamma_sign SPos  = {n. n > 0}"
  | "gamma_sign STop  = UNIV"

(* ── Partial Order ────────────────────────────────────────────── *)

fun sign_le :: "sign => sign => bool" where
    "sign_le SBot  _     = True"
  | "sign_le _     STop  = True"
  | "sign_le SNeg  SNeg  = True"
  | "sign_le SZero SZero = True"
  | "sign_le SPos  SPos  = True"
  | "sign_le _     _     = False"

lemma sign_le_refl:    "sign_le s s"                              by (cases s) simp_all
lemma sign_le_antisym: "sign_le s t ==> sign_le t s ==> s = t"   sorry
lemma sign_le_trans:   "sign_le s t ==> sign_le t u ==> sign_le s u"  sorry
lemma gamma_sign_mono: "sign_le s t ==> gamma_sign s <= gamma_sign t"  sorry

instantiation sign :: ord begin
definition less_eq_sign :: "sign => sign => bool" where "(a::sign) <= b = sign_le a b"
definition less_sign    :: "sign => sign => bool" where "(a::sign) <  b = (sign_le a b \<and> \<not> sign_le b a)"
instance ..
end

(* bot instance: required so abs_state = vname => sign has bot, enabling AFP mlup *)
instantiation sign :: bot begin
definition "bot_sign = SBot"
instance ..
end

(* ── Join (Least Upper Bound) ─────────────────────────────────── *)

fun join_sign :: "sign => sign => sign" where
    "join_sign SBot b     = b"
  | "join_sign a    SBot  = a"
  | "join_sign STop _     = STop"
  | "join_sign _    STop  = STop"
  | "join_sign SNeg SNeg  = SNeg"
  | "join_sign SZero SZero = SZero"
  | "join_sign SPos SPos  = SPos"
  | "join_sign _    _     = STop"

lemma join_sign_ub1:   "sign_le a (join_sign a b)"                    sorry
lemma join_sign_ub2:   "sign_le b (join_sign a b)"                    sorry
lemma join_sign_least: "sign_le a c ==> sign_le b c ==> sign_le (join_sign a b) c"  sorry
lemma join_sign_comm:  "join_sign a b = join_sign b a"                 by (cases a; cases b) simp_all
lemma join_sign_assoc: "join_sign a (join_sign b c) = join_sign (join_sign a b) c"  by (cases a; cases b; cases c) simp_all

(* ── Widening (identity for finite domain: widen = join) ────── *)

definition widen_sign :: "sign => sign => sign" where
  "widen_sign a b = join_sign a b"

(* ── Abstract Arithmetic Operations ──────────────────────────── *)
(*
  Define helpers first so aval_sign can call them.
*)

fun sign_plus :: "sign => sign => sign" where
    "sign_plus SBot _     = SBot"
  | "sign_plus _    SBot  = SBot"
  | "sign_plus SNeg SNeg  = SNeg"
  | "sign_plus SPos SPos  = SPos"
  | "sign_plus SZero b    = b"
  | "sign_plus a    SZero = a"
  | "sign_plus _    _     = STop"

fun sign_minus :: "sign => sign => sign" where
    "sign_minus SBot _     = SBot"
  | "sign_minus _    SBot  = SBot"
  | "sign_minus SNeg SPos  = SNeg"
  | "sign_minus SPos SNeg  = SPos"
  | "sign_minus SZero SZero = SZero"
  | "sign_minus _    _     = STop"

fun sign_times :: "sign => sign => sign" where
    "sign_times SBot _     = SBot"
  | "sign_times _    SBot  = SBot"
  | "sign_times SZero _    = SZero"
  | "sign_times _    SZero = SZero"
  | "sign_times SNeg SNeg  = SPos"
  | "sign_times SPos SPos  = SPos"
  | "sign_times SNeg SPos  = SNeg"
  | "sign_times SPos SNeg  = SNeg"
  | "sign_times STop _     = STop"
  | "sign_times _    STop  = STop"

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

fun aval_sign :: "aexp => (vname => sign) => sign" where
    "aval_sign (N n)       sigma = sign_of_int n"
  | "aval_sign (V x)       sigma = sigma x"
  | "aval_sign (Plus  a b) sigma = sign_plus  (aval_sign a sigma) (aval_sign b sigma)"
  | "aval_sign (Minus a b) sigma = sign_minus (aval_sign a sigma) (aval_sign b sigma)"
  | "aval_sign (Times a b) sigma = sign_times (aval_sign a sigma) (aval_sign b sigma)"

lemma aval_sign_sound:
  "(\<forall>x. s x \<in> gamma_sign (sigma x))
   ==>  aval a s : gamma_sign (aval_sign a sigma)"
  sorry

(* ── Abstract Assume ─────────────────────────────────────────── *)

fun assume_sign :: "bexp => (vname => sign) => (vname => sign)" where
    "assume_sign (Less (V x) (N n)) sigma = (if n = 0 then sigma(x := SNeg) else sigma)"
  | "assume_sign _                  sigma = sigma"

fun assume_not_sign :: "bexp => (vname => sign) => (vname => sign)" where
  "assume_not_sign _ sigma = sigma"   (* conservative: no refinement *)

interpretation sign_domain:
  abstract_domain gamma_sign join_sign widen_sign
  sorry

(* ── Typeclass Instances (required by TD solver interface) ────── *)

(* sign :: bot already defined above (bot_sign = SBot) *)

(* equal comes from datatype sign (no separate instantiation). *)

(* sign :: ord already defined above (less_eq_sign = sign_le). *)
instantiation sign :: order begin
instance sorry (* discharge via sign_le_refl / sign_le_antisym / sign_le_trans once proved *)
end

instantiation sign :: order_bot begin
instance sorry
end

lemma assume_sign_sound:
  "s : sign_domain.gamma_state sigma ==> bval b s
   ==> s : sign_domain.gamma_state (assume_sign b sigma)"
  sorry

lemma assume_not_sign_sound:
  "s : sign_domain.gamma_state sigma ==> \<not> bval b s
   ==> s : sign_domain.gamma_state (assume_not_sign b sigma)"
  sorry

(* ── Abstract Assignment ─────────────────────────────────────── *)

definition assign_sign ::
    "vname => aexp => (vname => sign) => (vname => sign)"
where
  "assign_sign x a sigma = sigma(x := aval_sign a sigma)"

lemma assign_sign_sound:
  "s : sign_domain.gamma_state sigma
   ==>  s(x := aval a s) : sign_domain.gamma_state (assign_sign x a sigma)"
  sorry

(* ── Abstract Domain Instantiation ───────────────────────────── *)

(* ── Bundled Transfer Functions ──────────────────────────────── *)

definition sign_tf :: "sign domain_transfer" where
  "sign_tf = (| tf_assign     = assign_sign,
                tf_assume     = assume_sign,
                tf_assume_not = assume_not_sign |)"

end
