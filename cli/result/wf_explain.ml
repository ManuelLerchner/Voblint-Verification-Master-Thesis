(* Why run_voblint answered Malformed_Program.

   The verdict itself is the generated well-formedness test; the export keeps
   that test's parts private, so this restates each conjunct over the AST only
   to name the first one a program breaks. It decides nothing: a program it
   finds no fault in still reads as malformed, just without a reason. Keep it in
   step with wf_program_compile_input_exec, wf_proc_decl and wf_source_com. *)

module C = Voblint_CLI.Generated

(* The generated ret_var; the lexer cannot produce it, but a hand-built AST can. *)
let ret_var = "#ret"

let special_arity = function
  | "__voblint_nondet_int" -> Some 0
  | "min" | "max" -> Some 2
  | _ -> None

let rec exp_vars = function
  | C.N _ -> []
  | C.V x -> [ x ]
  | C.Not a -> exp_vars a
  | C.Plus (a, b)
  | C.Minus (a, b)
  | C.Times (a, b)
  | C.Div (a, b)
  | C.Mod (a, b)
  | C.Less (a, b)
  | C.LessEq (a, b)
  | C.Greater (a, b)
  | C.GreaterEq (a, b)
  | C.NotEq (a, b)
  | C.Eq (a, b)
  | C.And (a, b)
  | C.Or (a, b) ->
      exp_vars a @ exp_vars b

let source_exp a = not (List.mem ret_var (exp_vars a))

let rec may_fallthrough = function
  | C.Seq (c1, c2) -> may_fallthrough c1 && may_fallthrough c2
  | C.If (_, c1, c2) -> may_fallthrough c1 || may_fallthrough c2
  | C.Return _ | C.Restore | C.Unwind -> false
  | C.SKIP | C.Assign _ | C.Check _ | C.While _ | C.Call _ -> true

let rec may_return returns = function
  | C.Seq (c1, c2) ->
      may_return returns c1 || (may_fallthrough c1 && may_return returns c2)
  | C.If (_, c1, c2) -> may_return returns c1 || may_return returns c2
  | C.While (_, c) -> may_return returns c
  | C.Return e -> returns e
  | _ -> false

let value_providing body =
  (not (may_fallthrough body))
  && (not (may_return Option.is_none body))
  && may_return Option.is_some body

let rec has_return = function
  | C.Seq (c1, c2) | C.If (_, c1, c2) -> has_return c1 || has_return c2
  | C.While (_, c) -> has_return c
  | C.Return _ -> true
  | _ -> false

let rec duplicate = function
  | [] -> None
  | x :: xs -> if List.mem x xs then Some x else duplicate xs

let first f xs = List.find_map f xs
let plural n word = Printf.sprintf "%d %s%s" n word (if n = 1 then "" else "s")

(* The first fault in one command, [where] naming the procedure it sits in. *)
let rec com_fault program where = function
  | C.SKIP | C.Restore | C.Unwind -> None
  | C.Assign (x, a) ->
      if x = ret_var || not (source_exp a) then
        Some (where ^ ": assignment to a reserved name")
      else None
  | C.Check c ->
      if source_exp c then None
      else Some (where ^ ": check reads a reserved name")
  | C.Seq (c1, c2) | C.If (_, c1, c2) -> (
      match com_fault program where c1 with
      | Some _ as fault -> fault
      | None -> com_fault program where c2)
  | C.While (_, c) -> com_fault program where c
  | C.Return _ -> None
  | C.Call (dst, callee, actuals) -> (
      let given = List.length actuals in
      match (special_arity callee, C.prog_table program callee) with
      | Some arity, _ when given <> arity ->
          Some
            (Printf.sprintf "%s: %s takes %s, given %d" where callee
               (plural arity "argument") given)
      | Some _, _ when dst = None ->
          Some
            (Printf.sprintf "%s: the result of %s must be assigned" where callee)
      | Some _, _ -> None
      | None, None ->
          Some
            (Printf.sprintf "%s: call to undefined procedure %s" where callee)
      | None, Some (C.Proc_decl_ext (formals, body, ())) ->
          let expected = List.length formals in
          if given <> expected then
            Some
              (Printf.sprintf "%s: %s takes %s, given %d" where callee
                 (plural expected "argument")
                 given)
          else if dst <> None && not (value_providing body) then
            Some
              (Printf.sprintf
                 "%s: the result of %s is assigned, but not every path through \
                  %s ends in return with a value"
                 where callee callee)
          else None)

let explain program =
  let procs = C.prog_procs program in
  let globals = C.declared_global_vars program in
  let decl name =
    match C.prog_table program name with
    | Some (C.Proc_decl_ext (formals, body, ())) -> Some (formals, body)
    | None -> None
  in
  let proc_fault name =
    match decl name with
    | None -> None
    | Some (formals, body) -> (
        match duplicate formals with
        | Some x ->
            Some (Printf.sprintf "in %s: parameter %s is declared twice" name x)
        | None -> (
            match List.find_opt (fun x -> List.mem x globals) formals with
            | Some x ->
                Some
                  (Printf.sprintf
                     "in %s: parameter %s is also a declared global" name x)
            | None -> com_fault program ("in " ^ name) body))
  in
  let main = C.prog_main program in
  let faults =
    [
      (fun () ->
        if List.mem ret_var globals then Some "a global uses a reserved name"
        else None);
      (fun () ->
        Option.map
          (Printf.sprintf "procedure %s is defined more than once")
          (duplicate procs));
      (fun () ->
        first
          (fun p ->
            Option.map
              (fun _ ->
                Printf.sprintf "procedure %s has the name of a built-in" p)
              (special_arity p))
          procs);
      (fun () -> if has_return main then Some "main must not return" else None);
      (fun () -> com_fault program "in main" main);
      (fun () -> first proc_fault procs);
    ]
  in
  first (fun fault -> fault ()) faults
