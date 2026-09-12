theory Example_Sign_Unit_Assembly
  imports "Voblint_Analysis_Sign.Sign_Checks" "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>The assembled Sign pipeline, run\<close>

text \<open>
  The witness that Sign's instance of the shared unit-context assembly is
  executable and not merely definable: a procedure writes a global, the caller
  checks its sign afterwards, and the assembled report decides the check. A
  code-generation defect in the assembly --- a locale constant reaching the
  generator without a code equation, or a specification left folded --- fails
  here.

  What this checks is Isabelle's own evaluation of the assembled definitions. It
  is not a check of the OCaml export, nor of the handwritten consumers that
  compile against it; those need a regenerated \<open>codegen/generated\<close> and its own
  compile step.
\<close>

definition sign_assembly_demo_prog :: imp_prog where
  "sign_assembly_demo_prog = program { global Gx;
     fun f() { Gx = 1; }
     fun main() { Gx = 0; f(); __voblint_check(0 < Gx); } }"

text \<open>
  The check is \<^const>\<open>Check_Proved\<close>, not \<^const>\<open>Check_Unknown\<close>, because the
  callee's write to the global reaches the caller through the local unknown
  rather than a flow-insensitive shared summary: \<open>Gx := 0\<close> and \<open>Gx := 1\<close> never
  join.
\<close>

lemma sign_assembly_demo_report:
  "set (analyse_sign_report sign_assembly_demo_prog)
     = {(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved)}"
  by eval

text \<open>
  The state-carrying and globals-carrying readings of the same solve run too,
  which is what exercises the assembly's combined output.
\<close>

lemma sign_assembly_demo_report_with_state_verdicts:
  "map (\<lambda>(v, c, r, unreachable, _). (v, c, r, unreachable))
     (analyse_sign_report_with_state sign_assembly_demo_prog)
     = [(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved, False)]"
  by eval

lemma sign_assembly_demo_terminates:
  "sign_conf_terminates_prog (declared_global sign_assembly_demo_prog)
     sign_assembly_demo_prog"
  by (rule sign_conf_terminates_prog_via_solve_c) eval

lemma sign_assembly_demo_cover:
  "vars_cover_exec (prog_cfg sign_assembly_demo_prog)
     (fst (sign_conf_sol_prog (declared_global sign_assembly_demo_prog)
             sign_assembly_demo_prog))"
  by eval

end
