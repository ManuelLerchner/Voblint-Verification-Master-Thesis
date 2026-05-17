section \<open>Example: visualising CFGs with Graphviz\<close>

theory Example_GraphViz
  imports CFG_GraphViz IMP2_to_CFG
begin

text \<open>
  These examples compile small IMP2 programs to CFGs and dump them as
  Graphviz DOT strings. Paste the printed text into any online
  Graphviz renderer (e.g. \<^url>\<open>https://dreampuf.github.io/GraphvizOnline/\<close>)
  to view the graph.

  The single ML block at the bottom evaluates @{const to_graphviz} via
  the code generator and writelns the clean DOT for each example into
  the Isabelle output panel / build log. Add a program here, then add
  one \<^verbatim>\<open>writeln_dot\<close> line in the ML block at the bottom.
\<close>

(* -- Example 1: straight-line program ------------------------------ *)

text \<open>\<^verbatim>\<open>x := 5; y := x + 1\<close>\<close>

definition prog_straight :: com where
  "prog_straight =
     (''x'' ::= N 5) ;; (''y'' ::= Plus (V ''x'') (N 1))"

(* -- Example 2: branching ------------------------------------------ *)

text \<open>\<^verbatim>\<open>if x < 0 then y := -x else y := x\<close> (absolute value).\<close>

definition prog_if :: com where
  "prog_if =
     IF Less (V ''x'') (N 0)
     THEN ''y'' ::= Minus (N 0) (V ''x'')
     ELSE ''y'' ::= V ''x''"

(* -- Example 3: while loop ----------------------------------------- *)

text \<open>\<^verbatim>\<open>while 0 < n do n := n - 1\<close> (count down to 0).\<close>

definition prog_while :: com where
  "prog_while =
     WHILE Less (N 0) (V ''n'')
     DO (''n'' ::= Minus (V ''n'') (N 1))"

(* -- Example 4: nested loop with branching ------------------------- *)

text \<open>\<^verbatim>\<open>while 0 < n do (if x < n then x := x + 1 else skip); n := n - 1\<close>\<close>

definition prog_nested :: com where
  "prog_nested =
     WHILE Less (N 0) (V ''n'') DO
       ((IF Less (V ''x'') (V ''n'')
         THEN ''x'' ::= Plus (V ''x'') (N 1)
         ELSE SKIP)
        ;;
        (''n'' ::= Minus (V ''n'') (N 1)))"

(* -- DOT output for all examples ---------------------------------- *)

ML \<open>
  fun b x = if x then 1 else 0
  fun gchar (@{code Char} (b0,b1,b2,b3,b4,b5,b6,b7)) =
    Char.chr (    b b0 +   2 * b b1 +   4 * b b2 +   8 * b b3
              + 16 * b b4 +  32 * b b5 +  64 * b b6 + 128 * b b7)
  fun writeln_dot c =
    (writeln "--- DOT ---";
     writeln (String.implode (map gchar (@{code to_graphviz} c))))

  val _ = writeln_dot (@{code to_cfg} @{code prog_straight})
  val _ = writeln_dot (@{code to_cfg} @{code prog_if})
  val _ = writeln_dot (@{code to_cfg} @{code prog_while})
  val _ = writeln_dot (@{code to_cfg} @{code prog_nested})
\<close>

end
