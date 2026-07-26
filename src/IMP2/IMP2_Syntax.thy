theory IMP2_Syntax
  imports Main "HOL-Library.Countable" HOL_IMP_Countable
begin

section \<open>Source-language expressions\<close>

text \<open>
  IMP2 wraps the HOL-IMP arithmetic and Boolean leaf constructors in \<open>BaseN\<close> and
  \<open>BaseB\<close>.  Compound expressions remain native IMP2 constructors because their operands
  must admit the extended expression language.  Evaluation delegates wrapped leaves to HOL-IMP.

  The \<open>N\<close>, \<open>V\<close>, and \<open>Bc\<close> abbreviations improve source notation.  Pattern matches
  use the underlying \<open>BaseN\<close> and \<open>BaseB\<close> constructors because abbreviations do not
  unfold as datatype patterns.
\<close>

(* vname aliases HOL-IMP.AExp's type (= string). *)
type_synonym store = "vname => int"

(* -- Arithmetic Expressions ---------------------------------------- *)

datatype aexp =
    BaseN "AExp.aexp"          (* wrapped base arithmetic expression       *)
  | Plus  aexp aexp            (* a + b over our (extended) aexp           *)
  | Minus aexp aexp            (* a - b   (extension)                      *)
  | Times aexp aexp            (* a * b   (extension)                      *)

abbreviation N :: "int \<Rightarrow> aexp"
  where "N n \<equiv> BaseN (AExp.N n)"

abbreviation V :: "vname \<Rightarrow> aexp"
  where "V x \<equiv> BaseN (AExp.V x)"

(* -- Boolean Expressions -------------------------------------------- *)

datatype bexp =
    BaseB "BExp.bexp"          (* wrapped base Boolean expression          *)
  | Not   bexp
  | And   bexp bexp
  | Or    bexp bexp            (* (extension)                              *)
  | Less  aexp aexp
  | Eq    aexp aexp            (* (extension)                              *)

abbreviation Bc :: "bool \<Rightarrow> bexp"
  where "Bc v \<equiv> BaseB (BExp.Bc v)"

instance aexp :: countable
  by countable_datatype

instance bexp :: countable
  by countable_datatype

text \<open>The executable linear order gives @{const sorted_list_of_set} a deterministic
  representation of CFG edge sets. A @{typ bexp} order has no comparable consumer, and
  deriving one adds duplicate simplification rules.\<close>
derive linorder aexp

text \<open>The imported and extended expression types share constructor base names.
  Hiding the imported short names keeps proof states compact while their qualified names
  remain available to expression evaluation.\<close>
hide_const (open) AExp.Plus BExp.Bc

end

