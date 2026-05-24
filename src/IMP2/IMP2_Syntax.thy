theory IMP2_Syntax
  imports Main "HOL-Library.Countable" HOL_IMP_Countable
begin

(*
  IMP2 -- Source Language Syntax.

  Design (Approach 1c from docs/IMP_SYNTAX_NIPKOW_EXTENSION.md):
  We wrap Nipkow's HOL-IMP.AExp/BExp via leaf constructors BaseN/BaseB
  and keep compound constructors (Plus, Not, And, Or, Less) plus our
  extensions (Minus, Times, Or, Eq) as native constructors of our own
  datatype. Nipkow's Plus/And/Less/Not are typed over Nipkow's own
  datatypes, so we cannot express "Plus over our extended aexp" inside
  the Base wrap; those compound shared constructors are therefore
  native here too.

  Reuse payoff (small): for the leaf forms N, V, Bc the abbreviations
  bind to BaseN/BaseB wraps of Nipkow constructors, and the wrapped
  cases of aval/bval delegate to AExp.aval/BExp.bval.

  Cost: abbreviations N, V, Bc do not unfold in pattern matches; any
  fun/case clause that splits on a leaf must spell BaseN (AExp.N _) etc.
*)

(* vname comes from HOL-IMP.AExp (= string); kept as a re-affirmation. *)
type_synonym store = "vname => int"

(* -- Arithmetic Expressions ---------------------------------------- *)

datatype aexp =
    BaseN "AExp.aexp"          (* literal / variable / Nipkow Plus subtree *)
  | Plus  aexp aexp            (* a + b over our (extended) aexp           *)
  | Minus aexp aexp            (* a - b   (extension)                      *)
  | Times aexp aexp            (* a * b   (extension)                      *)

abbreviation N :: "int \<Rightarrow> aexp"
  where "N n \<equiv> BaseN (AExp.N n)"

abbreviation V :: "vname \<Rightarrow> aexp"
  where "V x \<equiv> BaseN (AExp.V x)"

(* -- Boolean Expressions -------------------------------------------- *)

datatype bexp =
    BaseB "BExp.bexp"          (* boolean constant via Nipkow              *)
  | Not   bexp
  | And   bexp bexp
  | Or    bexp bexp            (* (extension)                              *)
  | Less  aexp aexp
  | Eq    aexp aexp            (* (extension)                              *)

abbreviation Bc :: "bool \<Rightarrow> bexp"
  where "Bc v \<equiv> BaseB (BExp.Bc v)"

(* -- Commands ------------------------------------------------------- *)

datatype com =
    SKIP
  | Assign vname aexp            ("_ ::= _"  [1000, 61] 61)
  | Seq    com   com             ("_ ;; _"   [60,  61]  60)
  | If     bexp  com  com        ("IF _ THEN _ ELSE _"   [0, 0, 61] 61)
  | While  bexp  com             ("WHILE _ DO _"         [0, 61]    61)

(* Linear orders for @{const sorted_list_of_set} in the TD solver (not part of the spec). *)
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

(* -- Short-name printing for clashing constructors --------------------
   Nipkow's HOL-IMP defines AExp.aexp.Plus and BExp.bexp.Bc, which clash
   with our IMP2_Syntax.aexp.Plus and the IMP2_Syntax.Bc abbreviation.
   Without these hides, Isabelle prints fully-qualified names in goals
   (e.g. "IMP2_Syntax.aexp.Plus", "IMP2_Syntax.Bc"), cluttering proof
   state and presentation extracts. `(open)` keeps the Nipkow versions
   reachable via the fully qualified path (AExp.Plus, BExp.Bc) for any
   code that delegates to Nipkow's aval/bval. *)
hide_const (open) AExp.Plus BExp.Bc

end

