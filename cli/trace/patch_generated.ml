(* Inserts the solver tracer's hooks into the Isabelle-generated module.

   The build copies codegen/generated/ml/Voblint_CLI.ml into cli/ through this
   program. The hooks are guarded calls into Solver_trace_hook (no-ops unless
   tracing is on) and change no value the solver computes; the export itself and
   the Isabelle sources stay untouched. Each patch names a piece of generated
   text that must occur exactly once (a per-mode patch: once per context mode
   using it): when a regeneration changes it, the build fails here instead of
   silently dropping an event. *)

let guard call = "(if !Solver_trace_hook.enabled then " ^ call ^ ");"

(* A typed decoder for a global-unknown datatype, defined right after it. The
   identity wrapper installs it at the call site that fixes the type, so the
   renderer tells seeds from the analysis global by constructor, not by
   memory layout. *)
let decoder name ty global seed =
  Printf.sprintf
    "\n\n\
     let %s (g : %s) =\n\
    \  Solver_trace_hook.install_global (fun o ->\n\
    \    match (Obj.obj o : %s) with\n\
    \    | %s -> None\n\
    \    | %s (n, c) -> Some (Obj.repr n, Obj.repr c));\n\
    \  g;;"
    name ty ty global seed

(* (description, text to find, replacement) *)
let patches =
  [
    ( "decoder of the global unknowns",
      "type ('a, 'b) global_unknown = Analysis_Global of 'a |\n\
      \  Activation_Seed of cfg_node * 'b;;",
      "type ('a, 'b) global_unknown = Analysis_Global of 'a |\n\
      \  Activation_Seed of cfg_node * 'b;;"
      ^ decoder "trace_global_unknown" "('a, 'b) global_unknown"
          "Analysis_Global _" "Activation_Seed" );
    ( "decoder of the call-string global unknowns",
      "type call_string_gk = Global | Seed of cfg_node * cfg_node list;;",
      "type call_string_gk = Global | Seed of cfg_node * cfg_node list;;"
      ^ decoder "trace_call_string_gk" "call_string_gk" "Global" "Seed" );
    ( "install the call-string decoder",
      "Global (fun a b -> Seed (a, b))",
      "(trace_call_string_gk Global) (fun a b -> Seed (a, b))" );
    ( "export the value printer",
      "  val res_diagnostics : ('a, 'b) run_result_ext -> \
       arithmetic_diagnostic list\n",
      "  val trace_string_of_abstract_value : abstract_value -> string\n\
      \  val res_diagnostics : ('a, 'b) run_result_ext -> \
       arithmetic_diagnostic list\n" );
    ( "define the value printer",
      "end;; (*struct Generated*)",
      "let trace_string_of_abstract_value = string_of_abstract_value;;\n\n\
       end;; (*struct Generated*)" );
    ( "solve: an unstable local unknown is evaluated",
      "      | I (x, (state, ug_state)) ->\n\
      \        (if not (member _A x (stabl state))",
      "      | I (x, (state, ug_state)) ->\n\
      \        (if !Solver_trace_hook.enabled && not (member _A x (stabl \
       state)) then Solver_trace_hook.solve (Obj.repr x));\n\
      \        (if not (member _A x (stabl state))" );
    ( "update of a local unknown",
      "else (let (infl1, stabl1) =",
      "else ("
      ^ guard
          "Solver_trace_hook.update_local (Obj.repr x) (Obj.repr (sigma state1 \
           (Inl x))) (Obj.repr d_newa)"
      ^ " let (infl1, stabl1) =" );
    ( "answer of a right-hand side",
      "      | E (_, (Answer d, (_, (state, ug_state)))) -> Some (d, (state, \
       ug_state))",
      "      | E (trace_x, (Answer d, (_, (state, ug_state)))) -> ("
      ^ guard "Solver_trace_hook.answer (Obj.repr trace_x) (Obj.repr d)"
      ^ " Some (d, (state, ug_state)))" );
    ( "local query",
      "      | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->\n\
      \        bind",
      "      | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->\n\
      \        "
      ^ guard "Solver_trace_hook.query_local (Obj.repr x) (Obj.repr y)"
      ^ "\n        bind" );
    ( "value a local query returned",
      "          (fun (yd, (statea, ug_statea)) ->\n",
      "          (fun (yd, (statea, ug_statea)) ->\n            "
      ^ guard
          "Solver_trace_hook.value_local (Obj.repr x) (Obj.repr y) (Obj.repr \
           yd)"
      ^ "\n" );
    ( "global query",
      "      | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->\n",
      "      | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->\n\
      \        "
      ^ guard
          "Solver_trace_hook.query_global (Obj.repr x) (Obj.repr y) (Obj.repr \
           (sigma state (Inr y)))"
      ^ "\n" );
    ( "side effect",
      "      | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->\n",
      "      | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->\n\
      \        "
      ^ guard "Solver_trace_hook.side (Obj.repr x) (Obj.repr y) (Obj.repr d)"
      ^ "\n" );
    ( "update of a global unknown",
      "            | (Some db, ug_statea) ->\n",
      "            | (Some db, ug_statea) ->\n              "
      ^ guard
          "Solver_trace_hook.update_global (Obj.repr y) (Obj.repr (sigma state \
           (Inr y))) (Obj.repr db)"
      ^ "\n" );
    ( "readers and routing, around the solve",
      "  comp emp rd init_st analysis_global seed route root_ctx solve g p =\n\
      \    (let sol =\n\
      \       solution (_A1, _A2) _C comp init_st analysis_global seed route \
       root_ctx\n\
      \         solve g p\n\
      \       in\n",
      "  comp emp rd init_st analysis_global seed route root_ctx solve g p =\n\
      \    (let trace_read = (fun d -> map_lift (rd g) (canonicalize_lift (emp \
       p) d)) in\n\
      \     let () = Solver_trace_hook.install_readers\n\
      \       ~state_local:(fun o -> Obj.repr (trace_read (dg_local (Obj.obj \
       o))))\n\
      \       ~state_global:(fun o -> Obj.repr (trace_read (dg_global (Obj.obj \
       o))))\n\
      \       ~local_part:(fun o -> Obj.repr (trace_read (Obj.obj o))) in\n\
      \     let route = (fun trace_g u ctx d ca ->\n\
      \       let c = route trace_g u ctx d ca in\n\
      \       "
      ^ guard
          "Solver_trace_hook.route (Obj.repr (u, ctx)) (Obj.repr d) (Obj.repr \
           c)"
      ^ "\n\
        \       c) in\n\
        \     let () = Solver_trace_hook.start_solve () in\n\
        \     let sol =\n\
        \       Stdlib.Fun.protect ~finally:Solver_trace_hook.end_solve (fun \
         () ->\n\
        \       solution (_A1, _A2) _C comp init_st analysis_global seed route \
         root_ctx\n\
        \         solve g p)\n\
        \       in\n" );
    ( "views, where the result is rendered",
      "     let view = map_lift (render vars) in\n",
      "     let view = map_lift (render vars) in\n\
      \     let () = Solver_trace_hook.install_views\n\
      \       ~view:(fun o -> Obj.repr (view (Obj.obj o)))\n\
      \       ~context:(fun o -> Obj.repr (ctx_view (Obj.obj o))) in\n" );
  ]

(* (times, patch): the context modes without call strings each pass the
   analysis global to the solve. *)
let per_mode_patches =
  [
    ( 2,
      ( "install the decoder of the global unknowns",
        "(Analysis_Global ())",
        "(trace_global_unknown (Analysis_Global ()))" ) );
  ]

let occurrences hay needle =
  let n = String.length needle and h = String.length hay in
  let rec go i acc =
    if i + n > h then List.rev acc
    else if String.sub hay i n = needle then go (i + n) (i :: acc)
    else go (i + 1) acc
  in
  go 0 []

let apply ?(times = 1) text (what, find, replace) =
  let found = occurrences text find in
  if List.length found <> times then begin
    Printf.eprintf
      "patch_generated: the anchor for \"%s\" occurs %d times in the generated \
       module (expected %d). The export changed shape; update \
       cli/trace/patch_generated.ml.\n"
      what (List.length found) times;
    exit 2
  end;
  let out = Buffer.create (String.length text + 4096) in
  let rest =
    List.fold_left
      (fun from i ->
        Buffer.add_substring out text from (i - from);
        Buffer.add_string out replace;
        i + String.length find)
      0 found
  in
  Buffer.add_substring out text rest (String.length text - rest);
  Buffer.contents out

let () =
  let path = Sys.argv.(1) in
  let ic = open_in_bin path in
  let text = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let text = List.fold_left (fun t p -> apply t p) text patches in
  print_string
    (List.fold_left
       (fun t (times, p) -> apply ~times t p)
       text per_mode_patches)
