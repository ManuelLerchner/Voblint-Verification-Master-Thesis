section \<open>Example: recursive interprocedural CFG as Graphviz\<close>

theory Example_Proc_GraphViz_Recursion
  imports
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_Analysis.Analysis_GraphViz"
begin

definition dot_main_name :: pname where
  "dot_main_name = ''main''"

text \<open>
  This example exports the interprocedural CFG of a recursive factorial
  procedure through @{const raw_cfg_dot_lit}.

  Green double circles mark procedure entries.
  Red double circles mark procedure results.
  Purple solid edges enter callees.
  Dashed blue edges resume callers.
\<close>

subsection \<open>Recursive factorial program\<close>

definition factorial_program :: imp_prog where
  "factorial_program = program {

     void fac(n) {
       if (n < 2) {
         return 1
       } else {
         tmp := fac(n - 1);
         return n * tmp
       }
     }

     void main() {
       N := 8;
       r := fac(N)
     }
   }"

subsection \<open>Compiled CFG\<close>

definition factorial_cfg :: cfg where
  "factorial_cfg =
     compile_prog
       (prog_table factorial_program)
       (prog_procs factorial_program)
       dot_main_name
       (prog_main factorial_program)"

subsection \<open>DOT output\<close>

definition factorial_dot :: String.literal where
  "factorial_dot =
     raw_cfg_dot_lit
       (prog_table factorial_program)
       (prog_procs factorial_program)
       dot_main_name
       (prog_main factorial_program)"

ML_val \<open>
  writeln (@{code factorial_dot})
\<close>

end