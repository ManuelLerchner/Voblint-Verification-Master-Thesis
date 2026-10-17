(* Typed expressions in VIMP's concrete syntax, through Vimp_printer's
   grammar-generated operator table. A variable prints as its identity's label
   and a conversion as a cast; literals and operators carry their kind in the IR
   but print as the source wrote them. *)

module C = Voblint
module P = Vimp_printer

let aop_op = function
  | C.AAdd -> P.op_plus
  | C.ASub -> P.op_minus
  | C.AMul -> P.op_times
  | C.ADiv -> P.op_div
  | C.AMod -> P.op_mod

let cop_op = function
  | C.CLt -> P.op_less
  | C.CLe -> P.op_less_eq
  | C.CGt -> P.op_greater
  | C.CGe -> P.op_greater_eq
  | C.CEq -> P.op_eq
  | C.CNe -> P.op_not_eq

(* A local prints by its own name, as the source wrote it; its label qualifies it by
   its procedure. *)
let var_name x =
  match x with
  | C.ScopedId (_, n) -> n
  | C.ReturnId _ | C.ReturnVar -> "return"
  | C.GlobalId n -> n

let rec texp_at ctx = function
  | C.TN (_, n) -> P.print_int_lit ctx n
  | C.TVar (_, x) -> var_name x
  | C.TCast (k, a) -> P.print_cast texp_at ctx k a
  | C.TArith (_, op, a, b) -> P.print_binop texp_at ctx (aop_op op) a b
  | C.TCmp (op, a, b) -> P.print_binop texp_at ctx (cop_op op) a b
  | C.TAnd (a, b) -> P.print_binop texp_at ctx P.op_and a b
  | C.TOr (a, b) -> P.print_binop texp_at ctx P.op_or a b
  | C.TNot a -> P.print_prefix texp_at ctx P.op_not a

let string_of_texp e = texp_at 0 e

(* The variables an expression reads, in first-occurrence order. *)
let texp_vars e =
  let rec go acc = function
    | C.TN _ -> acc
    | C.TVar (_, x) -> if List.mem x acc then acc else acc @ [ x ]
    | C.TCast (_, a) | C.TNot a -> go acc a
    | C.TArith (_, _, a, b) | C.TCmp (_, a, b) | C.TAnd (a, b) | C.TOr (a, b) ->
        go (go acc a) b
  in
  go [] e
