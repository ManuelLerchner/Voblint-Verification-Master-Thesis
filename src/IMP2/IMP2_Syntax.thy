theory IMP2_Syntax
  imports Main "HOL-Library.Countable"
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
type_synonym store  = "vname => int"

(* \<midarrow>\<midarrow> Arithmetic Expressions \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

datatype aexp =
    N     int                    (* integer literal         *)
  | V     vname                  (* variable read           *)
  | Plus  aexp aexp              (* a + b                   *)
  | Minus aexp aexp              (* a - b                   *)
  | Times aexp aexp              (* a * b                   *)

(* \<midarrow>\<midarrow> Boolean Expressions \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

datatype bexp =
    Bc    bool                   (* boolean constant        *)
  | Not   bexp                   (* negation                *)
  | And   bexp bexp              (* conjunction             *)
  | Or    bexp bexp              (* disjunction             *)
  | Less  aexp aexp              (* a < b                   *)
  | Eq    aexp aexp              (* a = b                   *)

(* \<midarrow>\<midarrow> Commands \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

datatype com =
    SKIP
  | Assign vname aexp            ("_ ::= _"  [1000, 61] 61)
  | Seq    com   com             ("_ ;; _"   [60,  61]  60)
  | If     bexp  com  com        ("IF _ THEN _ ELSE _"   [0, 0, 61] 61)
  | While  bexp  com             ("WHILE _ DO _"         [0, 61]    61)

(* Countability and a fixed linear order (pull-back from @{const to_nat})
   used for @{const sorted_list_of_set} on finite predecessor sets in the CFG. *)

instance aexp :: countable
  by countable_datatype

instance bexp :: countable
  by countable_datatype

instantiation aexp :: linorder
begin

definition less_eq_aexp_def:
  "((\<le>) :: aexp \<Rightarrow> aexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x \<le> to_nat y"

definition less_aexp_def:
  "((<) :: aexp \<Rightarrow> aexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x < to_nat y"

instance
  apply (intro_classes)
  by(auto simp add: less_aexp_def less_eq_aexp_def)
end

instantiation bexp :: linorder
begin

definition less_eq_bexp_def:
  "((\<le>) :: bexp \<Rightarrow> bexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x \<le> to_nat y"

definition less_bexp_def:
  "((<) :: bexp \<Rightarrow> bexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x < to_nat y"

instance
  apply (intro_classes)
  by(auto simp add: less_bexp_def less_eq_bexp_def)
end

end
