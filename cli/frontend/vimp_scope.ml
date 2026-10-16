(* C block scoping for declarations, resolved while parsing.

   Every variable a body names is a global, a formal or a local declared before
   the use in an enclosing block; any other name is rejected. A procedure's
   locals form one flat set of identities (ScopedId proc name), so two
   declarations of the same source name in one procedure must reach the verified
   elaboration under different names. The parser therefore renames each
   declaration whose name is already taken in its procedure -- by a global, a
   formal or an earlier declaration -- to `x#2`, `x#3`, ..., and resolves every
   variable use to the innermost declaration in scope. `#` cannot occur in a
   source identifier, so a renamed local never collides with a written one.

   A declaration's scope starts at its declarator, as in C, and ends with its
   enclosing braces. Resolution happens when the parser reduces a use; an LR
   parser reduces a use before it shifts the closing brace of the block around
   it, so the scope stack is exact at that moment. That this renaming is
   faithful to C's scoping is trusted: no theorem covers the parser. *)

exception Error of { line : int; col : int; msg : string }

type scope = (string * string) list

(* Innermost scope first. *)
let scopes : scope list ref = ref []
let globals : string list ref = ref []
let formals : string list ref = ref []

(* How many declarations each source name has had in the current procedure. *)
let taken : (string, int) Hashtbl.t = Hashtbl.create 16

(* The names the current procedure used with no declaration in scope, each with
   the position of its first use. A later declaration of one of them reports
   the use as coming before it; the end of the procedure reports the rest as
   undeclared. *)
let unresolved : (string * Lexing.position) list ref = ref []

(* The formals of the procedure being parsed, with their positions, collected
   before its header is complete. *)
let pending_formals : (string * Lexing.position) list ref = ref []

(* Where each integer literal was written, so a check after parsing can point
   at it. *)
let literals : (Z.t * Lexing.position) list ref = ref []

let reset () =
  scopes := [];
  globals := [];
  formals := [];
  Hashtbl.reset taken;
  unresolved := [];
  pending_formals := [];
  literals := []

let fail fmt = Printf.ksprintf failwith fmt

let fail_at (p : Lexing.position) fmt =
  Printf.ksprintf
    (fun msg ->
      raise (Error { line = p.pos_lnum; col = p.pos_cnum - p.pos_bol + 1; msg }))
    fmt

let add_globals p xs =
  List.iter
    (fun x ->
      if List.mem x !globals then fail_at p "duplicate global '%s'" x;
      globals := !globals @ [ x ])
    xs

let add_formal p x = pending_formals := !pending_formals @ [ (x, p) ]

let literal p n =
  literals := (n, p) :: !literals;
  n

let literal_position n =
  List.find_map
    (fun (m, p) -> if Z.equal m n then Some p else None)
    (List.rev !literals)

let outer_name x = List.mem x !globals || List.mem x !formals

(* The formals are distinct and none of them is a global, as C requires. *)
let enter_proc name =
  let fs = !pending_formals in
  pending_formals := [];
  ignore
    (List.fold_left
       (fun seen (x, p) ->
         if List.mem x seen then
           fail_at p "duplicate formal '%s' of '%s'" x name;
         if List.mem x !globals then
           fail_at p "formal '%s' of '%s' shadows a global" x name;
         x :: seen)
       [] fs);
  formals := List.map fst fs;
  Hashtbl.reset taken;
  unresolved := [];
  scopes := [ [] ]

let push () = scopes := [] :: !scopes

let pop () =
  match !scopes with
  | _ :: rest -> scopes := rest
  | [] -> fail "unbalanced block"

(* A formal shares the body's outermost scope, as in C, so a local there may not
   redeclare it; an inner block may. *)
let declare p x =
  match !scopes with
  | [] -> fail_at p "declaration of '%s' outside a procedure" x
  | inner :: outer ->
      if List.mem_assoc x inner || (outer = [] && List.mem x !formals) then
        fail_at p "redeclaration of '%s'" x;
      (match List.assoc_opt x !unresolved with
      | Some p -> fail_at p "'%s' is used before its declaration" x
      | None -> ());
      let n = Option.value ~default:0 (Hashtbl.find_opt taken x) in
      let shadowed = if outer_name x then 1 else 0 in
      let id =
        if n + shadowed = 0 then x
        else Printf.sprintf "%s#%d" x (n + shadowed + 1)
      in
      Hashtbl.replace taken x (n + 1);
      scopes := ((x, id) :: inner) :: outer;
      id

(* A bare use after its name's declarations have gone out of scope would read
   one of them, so it is rejected. *)
let resolve p x =
  match List.find_map (List.assoc_opt x) !scopes with
  | Some id -> id
  | None when outer_name x -> x
  | None ->
      if Hashtbl.mem taken x then
        fail_at p "'%s' is used outside the scope of its declaration" x;
      if not (List.mem_assoc x !unresolved) then
        unresolved := !unresolved @ [ (x, p) ];
      x

let close_proc () =
  scopes := [];
  match !unresolved with
  | (x, p) :: _ ->
      fail_at p "'%s' is not declared; declare it with a kind, as in 'i32 %s;'"
        x x
  | [] -> ()
