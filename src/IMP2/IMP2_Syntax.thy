theory IMP2_Syntax
  imports Main
begin

(*
  IMP2 -- Source Language Syntax.

  A simple imperative language extending the HOL-IMP baseline:
    aexp:  adds Minus, Times  (IMP only has Plus)
    bexp:  adds Or, Eq        (IMP only has And, Less)
    com:   same structure as IMP (SKIP, Assign, Seq, If, While)

  We define IMP2 from scratch (not importing HOL-IMP.Com) so the
  CFG-based pipeline is self-contained and notation is unambiguous.
*)

type_synonym vname = string
type_synonym state  = "vname => int"

(* ── Arithmetic Expressions ───────────────────────────────────── *)

datatype aexp =
    N     int                    (* integer literal         *)
  | V     vname                  (* variable read           *)
  | Plus  aexp aexp              (* a + b                   *)
  | Minus aexp aexp              (* a - b                   *)
  | Times aexp aexp              (* a * b                   *)

(* ── Boolean Expressions ──────────────────────────────────────── *)

datatype bexp =
    Bc    bool                   (* boolean constant        *)
  | Not   bexp                   (* negation                *)
  | And   bexp bexp              (* conjunction             *)
  | Or    bexp bexp              (* disjunction             *)
  | Less  aexp aexp              (* a < b                   *)
  | Eq    aexp aexp              (* a = b                   *)

(* ── Commands ─────────────────────────────────────────────────── *)

datatype com =
    SKIP
  | Assign vname aexp            ("_ ::= _"  [1000, 61] 61)
  | Seq    com   com             ("_ ;; _"   [60,  61]  60)
  | If     bexp  com  com        ("IF _ THEN _ ELSE _"   [0, 0, 61] 61)
  | While  bexp  com             ("WHILE _ DO _"         [0, 61]    61)

end
