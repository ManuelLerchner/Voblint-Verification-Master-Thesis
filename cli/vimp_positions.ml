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
   than relying on any claim about the order Menhir reduces in.

   Positions are grouped per definition rather than kept in one flat list.
   Statement indices are allocated procedure by procedure with main compiled
   last, whatever order the definitions appear in, so a flat list would pair
   correctly only for sources that happen to end with main. A function_decl
   reduces once its body is complete and carries its own name, which is
   exactly the boundary needed. *)

type pos = { line : int; column : int; end_line : int; end_column : int }

(* The definition being parsed, in reduction order; reversed. *)
let pending : pos list ref = ref []

(* Completed definitions, most recent first. *)
let closed : (string * pos list) list ref = ref []

let reset () =
  pending := [];
  closed := []

(* Returns its last argument so a semantic action can wrap its AST value without
   restructuring: `record $startpos $endpos (Assign (x, e))`. The end position is
   where the command's own text stops, which is what a node document's endColumn
   needs -- without it a span reads as zero-width. *)
let record (p : Lexing.position) (q : Lexing.position) (c : 'a) : 'a =
  pending :=
    { line = p.Lexing.pos_lnum;
      column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1;
      end_line = q.Lexing.pos_lnum;
      end_column = q.Lexing.pos_cnum - q.Lexing.pos_bol + 1 }
    :: !pending;
  c

(* Closes the current definition's bucket. Called from the function_decl
   action, which reduces after the whole body and before the next definition
   starts recording. *)
let close (name : string) : unit =
  closed := (name, List.rev !pending) :: !closed;
  pending := []

(* Definitions in source order: each function_decl reduces at its own closing
   brace, so they close left to right even though the list production that
   collects them is right-recursive. *)
let definitions () : (string * pos list) list = List.rev !closed
