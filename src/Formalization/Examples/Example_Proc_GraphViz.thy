section \<open>Example: interprocedural CFG (compile_prog) as Graphviz\<close>

theory Example_Proc_GraphViz
  imports "Voblint_CFG.CFG_GraphViz" "Voblint_CFG.IMP2_Proc_to_CFG"
begin

text \<open>
  Two @{const compile_prog} demos exported via @{const to_graphviz_regions}
  (procedure clusters from @{const compile_prog_regions}).

  @verbatim\<open>
  Example A (simple):
    proc p { Gx := Gx + 1 }
    main { call p }

  Example B (multi-procedure, conditional calls):
    proc p { Gx := Gx + 1 }
    proc q { Gy := Gy + 1 }
    main {
      if Gx < Gy then call p else call q
    }
  \<close>

  Visual legend (see also docs/GraphViz-improvements.md):
  green double circle = program entry/exit;
  green box = procedure entry (target of @{term EA_Enter});
  red box = procedure exit (middle of a @{term combines} triple);
  purple thick edge = enter; dashed blue = combine.
\<close>

(* -- Example A: single call -------------------------------------- *)

definition proc_p_body :: com where
  "proc_p_body = Assign ''Gx'' (Plus (V ''Gx'') (N 1))"

definition proc_table_a :: proc_table where
  "proc_table_a = ((\<lambda>_. None)(''p'' := Some proc_p_body))"

definition prog_call_p :: com where
  "prog_call_p = Call ''p''"

definition cfg_call_p :: cfg where
  "cfg_call_p = compile_prog proc_table_a [''p''] prog_call_p"

definition regions_call_p :: "graphviz_region list" where
  "regions_call_p = compile_prog_regions proc_table_a [''p''] prog_call_p"

definition proc_entries_call_p :: "pp list" where
  "proc_entries_call_p = enter_targets [(9, EA_Enter, 0)]"

definition proc_exits_call_p :: "pp list" where
  "proc_exits_call_p = combine_exits [(9, 2, 10)]"

(* -- Example B: two procedures + branch -------------------------- *)

definition proc_q_body :: com where
  "proc_q_body = Assign ''Gy'' (Plus (V ''Gy'') (N 1))"

definition proc_table_b :: proc_table where
  "proc_table_b = (proc_table_a(''q'' := Some proc_q_body))"

definition prog_if_calls :: com where
  "prog_if_calls =
     If (Less (V ''Gx'') (V ''Gy'')) (Call ''p'') (Call ''q'')"

definition cfg_if_calls :: cfg where
  "cfg_if_calls = compile_prog proc_table_b [''p'', ''q''] prog_if_calls"

definition regions_if_calls :: "graphviz_region list" where
  "regions_if_calls = compile_prog_regions proc_table_b [''p'', ''q''] prog_if_calls"

definition proc_entries_if_calls :: "pp list" where
  "proc_entries_if_calls = enter_targets [(11, EA_Enter, 0), (13, EA_Enter, 3)]"

definition proc_exits_if_calls :: "pp list" where
  "proc_exits_if_calls = combine_exits [(11, 2, 14), (13, 8, 14)]"

(* -- DOT output -------------------------------------------------- *)

ML \<open>
  fun b x = if x then 1 else 0
  fun gchar (@{code Char} (b0,b1,b2,b3,b4,b5,b6,b7)) =
    Char.chr (    b b0 +   2 * b b1 +   4 * b b2 +   8 * b b3
              + 16 * b b4 +  32 * b b5 +  64 * b b6 + 128 * b b7)
  fun writeln_dot title g regs proc_entries proc_exits =
    (writeln ("--- DOT " ^ title ^ " ---");
     writeln (String.implode
       (map gchar (@{code to_graphviz_regions} g regs proc_entries proc_exits))))

  val _ = writeln_dot "call p" @{code cfg_call_p} @{code regions_call_p}
                        @{code proc_entries_call_p} @{code proc_exits_call_p}
  val _ = writeln_dot "if calls p/q" @{code cfg_if_calls} @{code regions_if_calls}
                        @{code proc_entries_if_calls} @{code proc_exits_if_calls}
\<close>

end
