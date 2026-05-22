theory CFG_GraphViz
  imports CFG_Def "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

(*
  Pretty-print a CFG as a Graphviz DOT string.

  The resulting string can be pasted into any online Graphviz viewer,
  e.g. https://dreampuf.github.io/GraphvizOnline/, to visualise the
  compiled control-flow graph of an IMP2 program.

  Recommended use (clean output): the ML helper at the bottom of this
  theory writelns the DOT text into the Isabelle output panel:
     ML_val \<open>CFG_GraphViz.writeln_dot (to_cfg my_program)\<close>

  See Examples/Example_GraphViz.thy for concrete programs.
*)

(* -- Helpers: numbers to strings ----------------------------------- *)

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n =
     (if n < 10 then [char_of (n + 48)]
      else string_of_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i =
     (if i < 0 then ''-'' @ string_of_nat (nat (- i))
      else string_of_nat (nat i))"

(* -- IMP2 expressions to strings ----------------------------------- *)

fun string_of_aexp_hol :: "AExp.aexp \<Rightarrow> string" where
  "string_of_aexp_hol (AExp.N n)      = string_of_int n"
| "string_of_aexp_hol (AExp.V x)      = x"
| "string_of_aexp_hol (AExp.Plus a b) = ''('' @ string_of_aexp_hol a @ ''+'' @ string_of_aexp_hol b @ '')''"

fun string_of_aexp :: "aexp \<Rightarrow> string" where
  "string_of_aexp (BaseN a)     = string_of_aexp_hol a"
| "string_of_aexp (Plus  a b)   = ''('' @ string_of_aexp a @ ''+'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Minus a b)   = ''('' @ string_of_aexp a @ ''-'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Times a b)   = ''('' @ string_of_aexp a @ ''*'' @ string_of_aexp b @ '')''"

fun string_of_bexp_hol :: "BExp.bexp \<Rightarrow> string" where
  "string_of_bexp_hol (BExp.Bc True)    = ''true''"
| "string_of_bexp_hol (BExp.Bc False)   = ''false''"
| "string_of_bexp_hol (BExp.Not b)      = ''!('' @ string_of_bexp_hol b @ '')''"
| "string_of_bexp_hol (BExp.And b1 b2)  = ''('' @ string_of_bexp_hol b1 @ ''&&'' @ string_of_bexp_hol b2 @ '')''"
| "string_of_bexp_hol (BExp.Less a1 a2) = string_of_aexp_hol a1 @ ''<'' @ string_of_aexp_hol a2"

fun string_of_bexp :: "bexp \<Rightarrow> string" where
  "string_of_bexp (BaseB b)     = string_of_bexp_hol b"
| "string_of_bexp (Not b)       = ''!('' @ string_of_bexp b @ '')''"
| "string_of_bexp (And b1 b2)   = ''('' @ string_of_bexp b1 @ ''&&'' @ string_of_bexp b2 @ '')''"
| "string_of_bexp (Or  b1 b2)   = ''('' @ string_of_bexp b1 @ ''||'' @ string_of_bexp b2 @ '')''"
| "string_of_bexp (Less a1 a2)  = string_of_aexp a1 @ ''<''  @ string_of_aexp a2"
| "string_of_bexp (Eq   a1 a2)  = string_of_aexp a1 @ ''=='' @ string_of_aexp a2"

fun string_of_action :: "edge_action \<Rightarrow> string" where
  "string_of_action EA_Nop            = ''nop''"
| "string_of_action (EA_Assign x a)   = x @ '' := '' @ string_of_aexp a"
| "string_of_action (EA_Assume b)     = ''[''  @ string_of_bexp b @ '']''"
| "string_of_action (EA_AssumeNot b)  = ''![''  @ string_of_bexp b @ '']''"

(* -- DOT building blocks ------------------------------------------- *)

definition dq :: string where "dq = [CHR 0x22]"   (* double quote *)
definition nl :: string where "nl = [CHR 0x0A]"   (* newline      *)

definition edge_to_dot :: "pp \<times> edge_action \<times> pp \<Rightarrow> string" where
  "edge_to_dot e =
     (case e of (u, a, v) \<Rightarrow>
        ''  '' @ string_of_nat u @ '' -> '' @ string_of_nat v
              @ '' [label='' @ dq @ string_of_action a @ dq @ ''];'' @ nl)"

(* -- Main entry point ---------------------------------------------- *)

definition to_graphviz :: "cfg \<Rightarrow> string" where
  "to_graphviz g =
       ''digraph CFG {'' @ nl
     @ ''  rankdir=TB;'' @ nl
     @ ''  node [shape=circle];'' @ nl
     @ ''  '' @ string_of_nat (cfg_entry g)
            @ '' [shape=doublecircle,color=green,label=''
            @ dq @ ''entry pp'' @ string_of_nat (cfg_entry g) @ dq
            @ ''];'' @ nl
     @ ''  '' @ string_of_nat (cfg_exit g)
            @ '' [shape=doublecircle,color=red,label=''
            @ dq @ ''exit pp''  @ string_of_nat (cfg_exit g)  @ dq
            @ ''];'' @ nl
     @ concat (sorted_list_of_set (edge_to_dot ` edges g))
     @ ''}'' @ nl"

(*
  -- ML output recipe -----------------------------------------------

  Isabelle's `value` prints a string as a [CHR ''d'', CHR ''i'', ...]
  chain that's awkward to copy. To get clean text, use one ML block
  per theory that bundles the decoder with every call site
  (every `@{code ...}` antiquotation compiles its own generated-code
  snapshot, so the decoder must share its block with the calls).

  Pattern (see Examples/Example_GraphViz.thy):

    ML \<open>
      fun b x = if x then 1 else 0
      fun gchar (@{code Char} (b0,b1,b2,b3,b4,b5,b6,b7)) =
        Char.chr (   b b0 +   2 * b b1 +   4 * b b2 +   8 * b b3
                + 16 * b b4 +  32 * b b5 +  64 * b b6 + 128 * b b7)
      fun writeln_dot c =
        writeln (String.implode (map gchar (@{code to_graphviz} c)))

      val _ = writeln_dot (@{code to_cfg} @{code my_program})
      ...
    \<close>
*)

end
