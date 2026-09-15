(* Unicode for the symbols in a rendered abstract value.

   An Isabelle string literal holds ASCII only, so each domain's printer writes a
   symbol as its Isabelle name between angle brackets -- "1+3<int>" for "1+3ℤ".
   Decoding them once, on the answer run_voblint returns, gives every rendering
   the same text. A token outside the table stays as written. *)

module C = Voblint_CLI.Generated

let table =
  [
    ("bottom", "⊥");
    ("top", "⊤");
    ("int", "ℤ");
    ("infinity", "∞");
    ("le", "≤");
    ("ge", "≥");
    ("and", "∧");
  ]

let decode s =
  let n = String.length s in
  let buf = Buffer.create n in
  let token_at i =
    if s.[i] <> '<' then None
    else
      match String.index_from_opt s i '>' with
      | None -> None
      | Some j ->
          List.assoc_opt (String.sub s (i + 1) (j - i - 1)) table
          |> Option.map (fun glyph -> (glyph, j + 1))
  in
  let rec go i =
    if i < n then
      match token_at i with
      | Some (glyph, next) ->
          Buffer.add_string buf glyph;
          go next
      | None ->
          Buffer.add_char buf s.[i];
          go (i + 1)
  in
  go 0;
  Buffer.contents buf

let decode_answer answer = C.map_analysis_answer decode answer
