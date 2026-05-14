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

(* Countability and a fixed linear order (pull-back from @{const to_nat}) —
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
proof (intro_classes)
  fix x y z :: aexp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_aexp_def less_eq_aexp_def
    using linorder_not_le by force
  show "x \<le> x"
    by (simp add: less_eq_aexp_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (simp add: less_eq_aexp_def order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_aexp_def to_nat_split)
  show "x \<le> y \<or> y \<le> x"
    by (simp add: less_eq_aexp_def linear)
qed

end

instantiation bexp :: linorder
begin

definition less_eq_bexp_def:
  "((\<le>) :: bexp \<Rightarrow> bexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x \<le> to_nat y"

definition less_bexp_def:
  "((<) :: bexp \<Rightarrow> bexp \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x < to_nat y"

instance
proof (intro_classes)
  fix x y z :: bexp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_bexp_def less_eq_bexp_def
    using linorder_not_le by force
  show "x \<le> x"
    by (simp add: less_eq_bexp_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (simp add: less_eq_bexp_def order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_bexp_def to_nat_split)
  show "x \<le> y \<or> y \<le> x"
    by (simp add: less_eq_bexp_def linear)
qed

end

end
