(* The plain-text check report: one table of arithmetic diagnostics and one of
   assertion checks. A check row carries its own source position as its label; a
   diagnostic is placed through the statement positions the parser recorded. *)

module C = Voblint_CLI.Generated
module A = Result_text

let node_label = A.point_name
let verdict_label = A.verdict_name

let diagnostic_location positions diagnostic =
  match Voblint_CLI.Generated.diagnostic_point diagnostic with
  | Voblint_CLI.Generated.Statement n ->
      let index = Z.to_int (Voblint_CLI.Generated.integer_of_nat n) in
      Option.map
        (fun (line, column, _, _) -> (line, column))
        (List.assoc_opt index positions)
  | _ -> None

let diagnostic_severity diagnostic =
  match Voblint_CLI.Generated.diagnostic_verdict diagnostic with
  | Voblint_CLI.Generated.Check_Refuted -> "error"
  | _ -> "warning"

(* A check row names its source check by label: the line and column the parser
   wrote for it. Rows are listed in source order. A label shared by two rows
   leaves the lookup a source check needs ambiguous, and the theorem that makes
   a row's verdict the one for its check (run_voblint_labelled_check_sound)
   assumes distinct labels, so a shared label fails rather than printing
   either row at that position. *)
let check_location check =
  let line, column = C.check_label check in
  (A.int_of_nat line, A.int_of_nat column)

let located_checks rows =
  let located = List.map (fun check -> (check, check_location check)) rows in
  let positions = List.map snd located in
  if List.length (List.sort_uniq compare positions) <> List.length positions
  then failwith "two checks share one source label";
  List.stable_sort (fun (_, p) (_, q) -> compare p q) located

(* A row's verdict is lifted, and Bot is the proved-unreachable case: no
   execution reaches the check, so no verdict was computed for it. Goblint
   suppresses such a location entirely; naming it DEAD keeps "proved
   unreachable" distinguishable from "the compiler dropped this check", which
   a suppressed row cannot express. The state slice is dropped alongside the
   verdict -- bottom binds nothing worth printing. *)
let render_table title headers rows =
  let buf = Buffer.create 256 in
  Buffer.add_string buf (title ^ "\n");
  if rows = [] then Buffer.add_string buf "None\n"
  else begin
    let widths = Array.of_list (List.map String.length headers) in
    List.iter
      (List.iteri (fun i cell ->
           widths.(i) <- max widths.(i) (String.length cell)))
      rows;
    let add_row cells =
      let last = List.length cells - 1 in
      List.iteri
        (fun i cell ->
          Buffer.add_string buf cell;
          if i < last then
            Buffer.add_string buf
              (String.make (widths.(i) - String.length cell + 2) ' '))
        cells;
      Buffer.add_char buf '\n'
    in
    add_row headers;
    add_row
      (Array.to_list (Array.map (fun width -> String.make width '-') widths));
    List.iter add_row rows
  end;
  Buffer.contents buf

let render_report path analysis positions result =
  let diagnostics =
    List.map
      (fun diagnostic ->
        let location =
          match diagnostic_location positions diagnostic with
          | Some (line, column) -> Printf.sprintf "%d:%d" line column
          | None -> "-"
        in
        [
          location;
          node_label (Voblint_CLI.Generated.diagnostic_point diagnostic);
          String.uppercase_ascii (diagnostic_severity diagnostic);
          Result_text.diagnostic_message diagnostic;
        ])
      (C.res_diagnostics result)
  in
  let checks =
    List.map
      (fun (check, (line, col)) ->
        let point = C.check_point check and cnd = C.check_exp check in
        let label, state =
          match C.check_verdict check with
          | C.Bot -> ("DEAD", "")
          | C.Lifted v -> (verdict_label v, A.state_slice result point cnd)
        in
        [
          Printf.sprintf "%d:%d" line col;
          node_label point;
          Vimp_printer.string_of_exp cnd;
          label;
          state;
        ])
      (located_checks (C.res_checks result))
  in
  Printf.sprintf "%s [%s]\n\n%s\n%s" path analysis
    (render_table "Arithmetic diagnostics"
       [ "Location"; "Point"; "Severity"; "Message" ]
       diagnostics)
    (render_table "Assertion checks"
       [ "Location"; "Point"; "Condition"; "Verdict"; "State" ]
       checks)
