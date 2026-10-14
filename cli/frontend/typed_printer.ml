(* Typed expressions in VIMP's concrete syntax, at the precedence levels
   Vimp_printer uses. A variable prints as its identity's label and a conversion
   as a cast; literals and operators carry their kind in the IR but print as the
   source wrote them. *)

module C = Voblint

let paren = Vimp_printer.paren

let aop_text = function
  | C.AAdd -> ("+", 5)
  | C.ASub -> ("-", 5)
  | C.AMul -> ("*", 6)
  | C.ADiv -> ("/", 6)
  | C.AMod -> ("%", 6)

let cop_text = function
  | C.CLt -> ("<", 4)
  | C.CLe -> ("<=", 4)
  | C.CGt -> (">", 4)
  | C.CGe -> (">=", 4)
  | C.CEq -> ("==", 3)
  | C.CNe -> ("!=", 3)

(* A local prints by its own name, as the source wrote it; its label qualifies it by
   its procedure. *)
let var_name x =
  match x with C.ScopedId (_, n) -> n | C.ReturnId _ | C.ReturnVar -> "return" | C.GlobalId n -> n

let rec texp_at ctx = function
  | C.TN (_, n) -> paren ctx 8 (Vimp_printer.string_of_int_lit n)
  | C.TVar (_, x) -> var_name x
  | C.TCast (k, a) ->
      paren ctx 7 ("(" ^ Vimp_printer.string_of_kind k ^ ") " ^ texp_at 7 a)
  | C.TArith (_, op, a, b) ->
      let s, l = aop_text op in
      paren ctx l (texp_at l a ^ " " ^ s ^ " " ^ texp_at (l + 1) b)
  | C.TCmp (op, a, b) ->
      let s, l = cop_text op in
      paren ctx l (texp_at (l + 1) a ^ " " ^ s ^ " " ^ texp_at (l + 1) b)
  | C.TAnd (a, b) -> paren ctx 2 (texp_at 2 a ^ " && " ^ texp_at 3 b)
  | C.TOr (a, b) -> paren ctx 1 (texp_at 1 a ^ " || " ^ texp_at 2 b)
  | C.TNot a -> paren ctx 7 ("!" ^ texp_at 7 a)

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
