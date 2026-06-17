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

text \<open>
  Querying the computed abstract state at the exit (these @{command value} calls
  evaluate at build time): \<open>x\<close> is \<open>SPos\<close>, an untouched \<open>y\<close> stays \<open>STop\<close>.
\<close>

value "sign_exec_prog x1_prog ''x''"
value "sign_exec_prog x1_prog ''y''"

text \<open>The solver computes \<open>x \<mapsto> SPos\<close> at the exit, captured as a theorem
  by code reflection.\<close>

lemma x1_computes_x_pos:
  "sign_exec_prog x1_prog ''x'' = SPos"
  by eval

lemma x1_y_top:
  "sign_exec_prog x1_prog ''y'' = STop"
  by eval

text \<open>
  Termination is not assumed but proved: the executable side solver returns a
  result on this program (@{method eval}), so by
  @{thm sign_terminates_prog_via_solve_c} the program lies in the solver's domain.
\<close>

lemma x1_terminates: "sign_terminates_prog x1_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: the computed result over-approximates the
  interprocedural collecting semantics at the exit from any input store -- so
  after \<open>x := 1\<close>, \<open>x\<close> is positive.  An instance of the program-parametric
  @{thm sign_exec_prog_sound_collecting}, with termination discharged by execution.
\<close>

corollary x1_certified_sound:
  "cfg_collect_ip (prog_cfg x1_prog) cinit_stores (cfg_exit (prog_cfg x1_prog))
   \<le> sign_domain.gamma_state (sign_exec_prog x1_prog)"
  by (rule sign_exec_prog_sound_collecting[OF x1_terminates])

subsection \<open>Annotated CFG visualisation\<close>

text \<open>
  One-command DOT export via @{const sign_annotated_dot_prog_lit}: the CFG
  with per-program-point sign abstract states on each node label.
\<close>

ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} @{code x1_prog})
\<close>

end

