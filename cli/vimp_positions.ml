(* Source positions for the commands that own a Statement index.

   The parser records into this module rather than into its own %{ %} prelude,
   because Menhir does not export prelude bindings through the generated .mli:
   the recorder has to be reachable from both the parser's semantic actions and
   Vimp_frontend, so it lives in a module both can see.

   Positions are recorded where the parser knows it is building a command. The
   lexer cannot make that call -- a statement-position IDENT and one inside an
   expression are the same token -- which is why this is not the token-stream
   trick check positions use.

   Reductions complete after their parts, so what accumulates here is
   post-order over the command tree, not source order. Vimp_frontend pairs
   these by walking the parsed AST in that same order, structurally, rather
   than relying on any claim about the order Menhir reduces in. *)

let recorded : (int * int) list ref = ref []

let reset () = recorded := []

(* Returns its second argument so a semantic action can wrap its AST value
   without restructuring: `record $startpos (Assign (x, e))`. *)
let record (p : Lexing.position) (c : 'a) : 'a =
  recorded :=
    (p.Lexing.pos_lnum, p.Lexing.pos_cnum - p.Lexing.pos_bol + 1) :: !recorded;
  c

let collected () : (int * int) list = List.rev !recorded
