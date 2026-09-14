(* The JSON payload the browser playground reads: status, timing, the check column,
   diagnostics and the drawn graph, all from one run result. *)

module C = Voblint_CLI.Generated
module A = Result_text

(* -------------------------------------------------------------------------- *)

let json_escape value =
  let buffer = Buffer.create (String.length value + 16) in

  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c -> Buffer.add_char buffer c)
    value;

  Buffer.contents buffer

let json_string value = "\"" ^ json_escape value ^ "\""

let error_json message =
  Printf.sprintf "{\"status\":\"error\",\"message\":%s}" (json_string message)

let parse_error_json ~line ~column message =
  Printf.sprintf "{\"status\":\"error\",\"message\":%s,\"line\":%d,\"column\":%d}"
    (json_string message) line column

let check_json result check =
  let point = C.check_point check and cnd = C.check_exp check in
  let state = match C.check_verdict check with C.Bot -> "" | C.Lifted _ -> A.state_slice result point cnd in
  Printf.sprintf "{\"point\":%s,\"condition\":%s,\"verdict\":%s,\"state\":%s}"
    (json_string (A.point_name point))
    (json_string (Vimp_printer.string_of_exp cnd))
    (json_string (A.contextual_verdict_name (C.check_verdict check)))
    (json_string state)

let diagnostic_json diagnostic =
  Printf.sprintf "{\"severity\":%s,\"message\":%s}"
    (json_string (Render_text.diagnostic_severity diagnostic))
    (json_string (C.diagnostic_message diagnostic))

let result_json analysis_ms program result =
  let checks = C.res_checks result |> List.map (check_json result) |> String.concat "," in
  let diagnostics =
    C.res_diagnostics result |> List.map diagnostic_json |> String.concat ","
  in
  let graph = json_string (Render_dot.render (Context_graph.build program result)) in
  Printf.sprintf
    "{\"status\":\"ok\",\"timing\":{\"analysis_ms\":%.3f},\"checks\":[%s],\"diagnostics\":[%s],\"graph\":%s}"
    analysis_ms checks diagnostics graph
