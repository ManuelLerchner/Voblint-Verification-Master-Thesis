(* Assembles a parsed program and decides what its integers mean.

   A program that writes no kind anywhere is untyped: it keeps VIMP's
   mathematical integers and goes to the analyzer as parsed. A program that
   writes a kind on a global line, a formal, a return type or a local
   declaration is typed, and then every declaration must carry one:

     global u8 g;
     fun u16 f(u8 n) { u8 x; x = n + 1; return x; }

   Its declarations become the verified elaboration's kind_decls, and the
   program goes to the analyzer as `typed_prog p decls`, whose soundness
   theorems cover the typed semantics. Declared locals are not zero: the parser
   starts the body with `x = __voblint_nondet_int();` for each one, so a local
   holds an arbitrary value of its kind until the program writes it, as an
   uninitialized C automatic does. Globals start at zero, as C's static
   storage does. *)

type global_line = string list * Voblint.ikind option
type formal = string * Voblint.ikind option

(* (name, formals, return kind, declared locals, body with the locals'
   initializations prepended) *)
type definition =
  string
  * formal list
  * Voblint.ikind option
  * (string * Voblint.ikind) list
  * (unit, string, Voblint.exp) Voblint.gcom

let rec exp_vars acc = function
  | Voblint.N _ -> acc
  | Voblint.V x -> x :: acc
  | Voblint.Plus (a, b)
  | Voblint.Minus (a, b)
  | Voblint.Times (a, b)
  | Voblint.Div (a, b)
  | Voblint.Mod (a, b)
  | Voblint.Less (a, b)
  | Voblint.LessEq (a, b)
  | Voblint.Greater (a, b)
  | Voblint.GreaterEq (a, b)
  | Voblint.NotEq (a, b)
  | Voblint.Eq (a, b)
  | Voblint.And (a, b)
  | Voblint.Or (a, b) ->
      exp_vars (exp_vars acc a) b
  | Voblint.Not a | Voblint.Cast (_, a) -> exp_vars acc a

(* Every variable a command reads or writes, and whether it returns a value. *)
let rec com_vars acc = function
  | Voblint.SKIP _ | Voblint.Restore _ | Voblint.Unwind _ -> acc
  | Voblint.Assign (_, x, e) -> exp_vars (x :: acc) e
  | Voblint.Check (_, _, e) -> exp_vars acc e
  | Voblint.Seq (c1, c2) -> com_vars (com_vars acc c1) c2
  | Voblint.If (_, b, c1, c2) -> com_vars (com_vars (exp_vars acc b) c1) c2
  | Voblint.While (_, b, c) -> com_vars (exp_vars acc b) c
  | Voblint.Call (_, dst, _, es) ->
      List.fold_left exp_vars
        (Option.fold ~none:acc ~some:(fun x -> x :: acc) dst)
        es
  | Voblint.Return (_, e) -> Option.fold ~none:acc ~some:(exp_vars acc) e

(* Every integer literal of a command. *)
let rec exp_literals acc = function
  | Voblint.N (Voblint.Int_of_integer n) -> n :: acc
  | Voblint.V _ -> acc
  | Voblint.Plus (a, b)
  | Voblint.Minus (a, b)
  | Voblint.Times (a, b)
  | Voblint.Div (a, b)
  | Voblint.Mod (a, b)
  | Voblint.Less (a, b)
  | Voblint.LessEq (a, b)
  | Voblint.Greater (a, b)
  | Voblint.GreaterEq (a, b)
  | Voblint.NotEq (a, b)
  | Voblint.Eq (a, b)
  | Voblint.And (a, b)
  | Voblint.Or (a, b) ->
      exp_literals (exp_literals acc a) b
  | Voblint.Not a | Voblint.Cast (_, a) -> exp_literals acc a

let rec com_literals acc = function
  | Voblint.SKIP _ | Voblint.Restore _ | Voblint.Unwind _ -> acc
  | Voblint.Assign (_, _, e) | Voblint.Check (_, _, e) -> exp_literals acc e
  | Voblint.Seq (c1, c2) -> com_literals (com_literals acc c1) c2
  | Voblint.If (_, b, c1, c2) ->
      com_literals (com_literals (exp_literals acc b) c1) c2
  | Voblint.While (_, b, c) -> com_literals (exp_literals acc b) c
  | Voblint.Call (_, _, _, es) -> List.fold_left exp_literals acc es
  | Voblint.Return (_, e) -> Option.fold ~none:acc ~some:(exp_literals acc) e

let rec returns_value = function
  | Voblint.Return (_, Some _) -> true
  | Voblint.Seq (c1, c2) | Voblint.If (_, _, c1, c2) ->
      returns_value c1 || returns_value c2
  | Voblint.While (_, _, c) -> returns_value c
  | _ -> false

let is_typed globals defs =
  List.exists (fun (_, k) -> k <> None) globals
  || List.exists
       (fun (_, fs, rk, ls, _) ->
         rk <> None || ls <> [] || List.exists (fun (_, k) -> k <> None) fs)
       defs

let fail fmt = Printf.ksprintf failwith fmt

(* C gives an unsuffixed decimal literal the first of int, long, long long that
   holds it and has no type for a larger one. The typed semantics would wrap
   such a literal at i64, so a typed program may not write one. *)
let check_literal n =
  let i64_min = Z.neg (Z.shift_left Z.one 63)
  and i64_max = Z.pred (Z.shift_left Z.one 63) in
  if Z.lt n i64_min || Z.gt n i64_max then
    fail "literal %s does not fit i64, the widest kind" (Z.to_string n)

let check_distinct what names =
  let rec go seen = function
    | [] -> ()
    | x :: xs ->
        if List.mem x seen then fail "duplicate %s '%s'" what x
        else go (x :: seen) xs
  in
  go [] names

(* The declarations of a typed program, checked so that every variable resolves
   to exactly one declared identity. *)
let kind_decls globals defs =
  let global_kinds =
    List.concat_map
      (fun (xs, k) ->
        match k with
        | Some k -> List.map (fun x -> (x, k)) xs
        | None ->
            fail "global '%s' needs a kind in a typed program"
              (String.concat ", " xs))
      globals
  in
  let gnames = List.map fst global_kinds in
  check_distinct "global" gnames;
  let proc_decls (name, formals, ret, locals, body) =
    let formal_kinds =
      List.map
        (fun (x, k) ->
          match k with
          | Some k -> (x, k)
          | None ->
              fail "formal '%s' of '%s' needs a kind in a typed program" x name)
        formals
    in
    let fnames = List.map fst formal_kinds and lnames = List.map fst locals in
    check_distinct (Printf.sprintf "variable of '%s'" name) (fnames @ lnames);
    List.iter
      (fun x ->
        if List.mem x gnames then fail "'%s' in '%s' shadows a global" x name)
      (fnames @ lnames);
    List.iter
      (fun x ->
        if not (List.mem x gnames || List.mem x fnames || List.mem x lnames)
        then fail "undeclared variable '%s' in '%s'" x name)
      (com_vars [] body);
    List.iter check_literal (com_literals [] body);
    (match ret with
    | None when returns_value body ->
        fail "'%s' returns a value but declares no return kind" name
    | Some _ when name = "main" -> fail "'main' cannot declare a return kind"
    | _ -> ());
    List.map
      (fun (x, k) -> (Voblint.ScopedId (name, x), k))
      (formal_kinds @ locals)
    @ Option.fold ~none:[] ~some:(fun k -> [ (Voblint.ReturnId name, k) ]) ret
  in
  List.map (fun (x, k) -> (Voblint.GlobalId x, k)) global_kinds
  @ List.concat_map proc_decls defs

(* The last program before lowering, with its kind declarations: the experimental
   typed run (--typed) analyzes this pair, not the lowered program. *)
let source_program :
    (unit Voblint.imp_prog_ext * (Voblint.var_id * Voblint.ikind) list) option ref =
  ref None

let program (globals : global_line list) (defs : definition list) :
    unit Voblint.imp_prog_ext =
  let mains, procs = List.partition (fun (n, _, _, _, _) -> n = "main") defs in
  let main_body =
    match mains with
    | [ (_, [], _, _, b) ] -> b
    | [ (_, _ :: _, _, _, _) ] -> failwith "'main' must have no formals"
    | [] -> failwith "missing 'fun main() { ... }'"
    | _ -> failwith "more than one 'fun main()'"
  in
  let p =
    Voblint.mk_program
      (List.map
         (fun (n, formals, _, _, b) ->
           (n, Voblint.Gproc_decl_ext (List.map fst formals, b, ())))
         procs)
      main_body
      (List.concat_map fst globals)
  in
  if is_typed globals defs then begin
    let ds = kind_decls globals defs in
    source_program := Some (p, ds);
    Voblint.typed_prog p ds
  end
  else begin
    source_program := Some (p, []);
    p
  end
