(* C block scoping for local declarations, resolved while parsing.

   A procedure's locals form one flat set of identities (ScopedId proc name), so
   two declarations of the same source name in one procedure must reach the
   verified elaboration under different names. The parser therefore renames each
   declaration whose name is already taken in its procedure -- by a global, a
   formal or an earlier declaration -- to `x#2`, `x#3`, ..., and resolves every
   variable use to the innermost declaration in scope. `#` cannot occur in a
   source identifier, so a renamed local never collides with a written one.

   A declaration's scope starts at its declarator, as in C, and ends with its
   enclosing braces. Resolution happens when the parser reduces a use; an LR
   parser reduces a use before it shifts the closing brace of the block around
   it, so the scope stack is exact at that moment. That this renaming is
   faithful to C's scoping is trusted: no theorem covers the parser. *)

type scope = (string * string) list

(* Innermost scope first. *)
let scopes : scope list ref = ref []
let globals : string list ref = ref []
let formals : string list ref = ref []

(* How many declarations each source name has had in the current procedure. *)
let taken : (string, int) Hashtbl.t = Hashtbl.create 16

(* The names the current procedure used with no declaration in scope and no
   global or formal behind them: implicit locals of an untyped program, or
   undeclared names the typing check rejects in a typed one. *)
let free : string list ref = ref []

let reset () =
  scopes := [];
  globals := [];
  formals := [];
  Hashtbl.reset taken;
  free := []

let fail fmt = Printf.ksprintf failwith fmt
let add_globals xs = globals := !globals @ xs
let outer_name x = List.mem x !globals || List.mem x !formals

let enter_proc fs =
  formals := fs;
  Hashtbl.reset taken;
  free := [];
  scopes := [ [] ]

let push () = scopes := [] :: !scopes

let pop () =
  match !scopes with
  | _ :: rest -> scopes := rest
  | [] -> fail "unbalanced block"

(* A formal shares the body's outermost scope, as in C, so a local there may not
   redeclare it; an inner block may. A name used bare before its declaration
   would share the declaration's identity, so that use is rejected here. *)
let declare x =
  match !scopes with
  | [] -> fail "declaration of '%s' outside a procedure" x
  | inner :: outer ->
      if List.mem_assoc x inner || (outer = [] && List.mem x !formals) then
        fail "redeclaration of '%s'" x;
      if List.mem x !free then fail "'%s' is used before its declaration" x;
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
let resolve x =
  match List.find_map (List.assoc_opt x) !scopes with
  | Some id -> id
  | None when outer_name x -> x
  | None ->
      if Hashtbl.mem taken x then
        fail "'%s' is used outside the scope of its declaration" x;
      if not (List.mem x !free) then free := !free @ [ x ];
      x

let close_proc () = scopes := []
