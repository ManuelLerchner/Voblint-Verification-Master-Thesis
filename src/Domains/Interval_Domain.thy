theory Interval_Domain
  imports Abstract_Domain Constraint_System
begin

(*
  Interval Domain -- Instantiation of abstract_domain.

  An interval [l, u] abstracts a set of integers {n | l <= n <= n <= u}.
  Special cases:
    [+inf, -inf]  (i.e., l > u)  -- empty (Bot)
    [-inf, +inf]                  -- all integers (Top)

  This is the main (Tier-2) domain of the thesis.  Key challenges:
    - Widening: needed for convergence on loop-carried values.
    - Narrowing: optional precision recovery after widening.

  Transfer functions are more complex than for signs.
  Connection point: HOL-IMP.Abs_Int2_ivl has a verified interval analysis
  for the original IMP language; we will bridge or re-prove here for IMP2.

  TODO: decide whether to import HOL-IMP.Abs_Int2_ivl (requires adapting
        to IMP2 syntax) or define the interval domain from scratch.
*)

(* ── Extended Integer for Interval Bounds ────────────────────── *)
(*
  We use an option-like type: None = infinity / -infinity.
  Or alternatively use the HOL-IMP approach with  ivl = Ivl int int.
  For now: use int for bounds with a separate "unbounded" flag.
  TODO: pick concrete representation after discussion with supervisors.
*)

datatype eint = MinInf | Fin int | PlusInf

fun eint_le :: "eint => eint => bool" where
    "eint_le MinInf  _       = True"
  | "eint_le _       PlusInf = True"
  | "eint_le (Fin n) (Fin m) = (n <= m)"
  | "eint_le _       MinInf  = False"
  | "eint_le PlusInf _       = False"

(* ── Interval Type ────────────────────────────────────────────── *)

datatype ivl = Ivl eint eint   (* Ivl l u = [l, u] *)

instantiation ivl :: ord begin
definition less_eq_ivl :: "ivl => ivl => bool" where
  "(a::ivl) <= b = (case (a, b) of (Ivl l1 u1, Ivl l2 u2) => eint_le l2 l1 & eint_le u1 u2)"
definition less_ivl :: "ivl => ivl => bool" where
  "(a::ivl) < b = (a <= b & ~ b <= a)"
instance ..
end

instantiation ivl :: bot begin
definition bot_ivl :: ivl where
  "bot_ivl = Ivl PlusInf MinInf"
instance ..
end

definition ivl_bot :: ivl where
  "ivl_bot = Ivl PlusInf MinInf"   (* empty: l > u *)

definition ivl_top :: ivl where
  "ivl_top = Ivl MinInf PlusInf"   (* full: [-inf, +inf] *)

(* ── Concretization ───────────────────────────────────────────── *)

fun gamma_ivl :: "ivl => int set" where
    "gamma_ivl (Ivl l u) = {n. eint_le l (Fin n) & eint_le (Fin n) u}"

lemma gamma_ivl_bot: "gamma_ivl ivl_bot = {}"
  sorry

lemma gamma_ivl_top: "gamma_ivl ivl_top = UNIV"
  sorry

(* ── Join and Widening ────────────────────────────────────────── *)

fun join_ivl :: "ivl => ivl => ivl" where
    "join_ivl (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if eint_le l1 l2 then l1 else l2)
           (if eint_le u2 u1 then u1 else u2)"

(*
  Standard interval widening: keep l if l decreased, else push to -inf;
  keep u if u increased, else push to +inf.
  Ensures any ascending chain stabilises after at most 2 steps.
*)
fun widen_ivl :: "ivl => ivl => ivl" where
    "widen_ivl (Ivl l1 u1) (Ivl l2 u2) =
       Ivl (if eint_le l1 l2 then l1 else MinInf)
           (if eint_le u2 u1 then u1 else PlusInf)"

lemma gamma_ivl_mono:
  "a <= b ==> gamma_ivl a <= gamma_ivl b"
  (* a ≤ b means Ivl l2 u2 ≤ Ivl l1 u1, i.e. l1 tighter on left, u1 tighter on right.
     Concretely: [l1,u1] ⊆ [l2,u2]. Proof by cases on a and b, unfolding less_eq_ivl. *)
  sorry

lemma join_ivl_ub1: "gamma_ivl a <= gamma_ivl (join_ivl a b)"     sorry
lemma join_ivl_ub2: "gamma_ivl b <= gamma_ivl (join_ivl a b)"     sorry
lemma join_ivl_comm:  "join_ivl a b = join_ivl b a"                sorry
lemma join_ivl_assoc: "join_ivl a (join_ivl b c) = join_ivl (join_ivl a b) c"  sorry

lemma widen_ivl_ub1: "gamma_ivl a <= gamma_ivl (widen_ivl a b)"   sorry
lemma widen_ivl_ub2: "gamma_ivl b <= gamma_ivl (widen_ivl a b)"   sorry

(* Widening termination: every widen-ascending chain stabilises. *)
lemma widen_ivl_terminates:
  assumes "ALL i. widen_ivl (f i) (f (Suc i)) = f (Suc i)"
  shows "EX n. ALL j. n <= j --> f j = f n"
  sorry

(* ── Abstract Domain Instantiation ───────────────────────────── *)

interpretation ivl_domain:
  abstract_domain gamma_ivl ivl_bot join_ivl widen_ivl
  sorry

(* ── Transfer Functions (stubs) ──────────────────────────────── *)

(* Abstract arithmetic: conservative stubs (TODO: precise implementations) *)

fun ivl_plus :: "ivl => ivl => ivl" where
    "ivl_plus  (Ivl l1 u1) (Ivl l2 u2) = Ivl MinInf PlusInf"

fun ivl_minus :: "ivl => ivl => ivl" where
    "ivl_minus (Ivl l1 u1) (Ivl l2 u2) = Ivl MinInf PlusInf"

fun ivl_times :: "ivl => ivl => ivl" where
    "ivl_times (Ivl l1 u1) (Ivl l2 u2) = Ivl MinInf PlusInf"

fun aval_ivl :: "aexp => (vname => ivl) => ivl" where
    "aval_ivl (N n)       sigma = Ivl (Fin n) (Fin n)"
  | "aval_ivl (V x)       sigma = sigma x"
  | "aval_ivl (Plus  a b) sigma = ivl_plus  (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Minus a b) sigma = ivl_minus (aval_ivl a sigma) (aval_ivl b sigma)"
  | "aval_ivl (Times a b) sigma = ivl_times (aval_ivl a sigma) (aval_ivl b sigma)"

(* Soundness of abstract arithmetic *)
lemma aval_ivl_sound:
  "(ALL x. s x : gamma_ivl (sigma x))
   ==>  aval a s : gamma_ivl (aval_ivl a sigma)"
  sorry

(* Abstract assume: interval-based branch refinement *)
fun assume_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_ivl _ sigma = sigma"   (* TODO: precise narrowing on Less/Eq *)

fun assume_not_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
    "assume_not_ivl _ sigma = sigma"   (* TODO *)

definition assign_ivl ::
    "vname => aexp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a sigma = sigma(x := aval_ivl a sigma)"

lemma assign_ivl_sound:
  "s : ivl_domain.gamma_state sigma
   ==>  s(x := aval a s) : ivl_domain.gamma_state (assign_ivl x a sigma)"
  sorry

(* ── Bundled Transfer Functions ──────────────────────────────── *)

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl |)"

end
