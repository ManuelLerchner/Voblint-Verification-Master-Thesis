theory Example_Side_Execute
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Running the certified sign analyzer on \<open>x := 1\<close>\<close>

text \<open>
  The smallest end-to-end witness: compile \<open>x := 1\<close>, run the actual vendored
  solver via @{const sign_exec_raw}, and read the certified soundness off the
  program-parametric theorems in @{theory Voblint_Analysis.Sign_Exec_Sound}.  The
  @{command value} / \<open>eval\<close> evaluates at build time, so a green build is the
  execution proof.
\<close>

definition x1_prog :: imp_prog where
  "x1_prog = \<lbrakk> void main() { x := 1 } \<rbrakk>"

abbreviation x1_pt   :: proc_table where "x1_pt   \<equiv> prog_table x1_prog"
abbreviation x1_main :: com        where "x1_main \<equiv> prog_main  x1_prog"

abbreviation x1_exit :: pp where
  "x1_exit \<equiv> cfg_exit (compile_prog x1_pt [] x1_main)"

text \<open>
  Querying the computed abstract state at the exit (these @{command value} calls
  evaluate at build time): \<open>x\<close> is \<open>SPos\<close>, an untouched \<open>y\<close> stays \<open>STop\<close>.
\<close>

value "sign_exec x1_pt [] x1_main ''x''"
value "sign_exec x1_pt [] x1_main ''y''"

text \<open>The solver computes \<open>x \<mapsto> SPos\<close> at the exit, captured as a theorem
  by code reflection.\<close>

lemma x1_computes_x_pos:
  "sign_exec x1_pt [] x1_main ''x'' = SPos"
  by eval

text \<open>
  Termination is not assumed but proved: the executable side solver returns a
  result on this program (@{method eval}), so by
  @{thm sign_exec_terminates_via_solve_c} the program lies in the solver's domain.
\<close>

lemma x1_terminates: "sign_exec_terminates x1_pt [] x1_main"
  by (rule sign_exec_terminates_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: the computed result over-approximates the
  interprocedural collecting semantics at the exit from any input store -- so
  after \<open>x := 1\<close>, \<open>x\<close> is positive.  An instance of the program-parametric
  @{thm sign_exec_sound_collecting}, with termination discharged by execution.
\<close>

corollary x1_certified_sound:
  "cfg_collect_ip (compile_prog x1_pt [] x1_main) UNIV x1_exit
   \<le> sign_domain.gamma_state (sign_exec x1_pt [] x1_main)"
  by (rule sign_exec_sound_collecting[OF x1_terminates])

end

