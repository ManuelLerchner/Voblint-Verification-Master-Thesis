theory Example_Side_Branch_Calls
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Certified sign analyzer on a branching, repeatedly-called procedure\<close>

text \<open>
  A richer end-to-end witness than the single-statement \<^verbatim>\<open>Example_Side_Execute\<close>:
  a procedure \<open>compute\<close> with an \<open>if\<close>/\<open>else\<close> on a global input, called twice from
  \<open>main\<close> with different inputs, followed by an arithmetic use of the result.  In C:

  \begin{verbatim}
  int Ginput; int Gresult;            // globals (G-prefixed)
  void compute() {
      int x = 1;                      // local
      if (Ginput > 0) x = x + 1;
      else            x = x + 2;
      Gresult = x;
  }
  int main() {
      Ginput = 5;   compute();
      Ginput = -3;  compute();
      Gout = 100 * Gresult;           // language has no '/', so use '*'
  }
  \end{verbatim}

  Two modelling notes.  The expression language @{type aexp} has \<open>Plus\<close> /
  \<open>Minus\<close> / \<open>Times\<close> but no division, so \<open>100 / Gresult\<close> is written as the
  multiplication \<open>100 * Gresult\<close>.  Variables whose name starts with \<open>G\<close> are
  global (@{const is_global}); \<open>x\<close> is local to \<open>compute\<close> and lives only inside
  its scope.
\<close>

definition branch_prog :: imp_prog where
  "branch_prog = \<lbrakk>
     int Ginput, Gresult, Gout;

     void compute() {
       x := 1;
       if (0 < Ginput) { x := x + 1 } else { x := x + 2 };
       Gresult := x
     }
     void main() {
       Ginput := 5;
       compute();
       Ginput := 0 - 3;
       compute();
       Gout := 100 * Gresult
     }
   \<rbrakk>"

text \<open>
  The computed abstract state at the exit.  With C-faithful seeding
  (\<open>cinit_sign_st\<close>: globals start at \<open>SZero\<close>, locals at \<open>STop\<close>), the
  7-element lattice can give tighter global bounds: \<open>SZero \<squnion> SPos = SNonNeg\<close>
  instead of \<open>STop\<close>.  Concretely, both branches of \<open>compute\<close> assign
  a positive \<open>x\<close> to \<open>Gresult\<close>; joined against the zero initial value the
  result is \<open>SNonNeg\<close> (\<open>\<ge> 0\<close>), not \<open>STop\<close>.
\<close>

value "sign_exec_prog branch_prog ''Gresult''"
value "sign_exec_prog branch_prog ''Gout''"

lemma ec_result_nonnneg:
  "sign_exec_prog branch_prog ''Gresult'' = SNonNeg"
  by eval

text \<open>Termination is proved, not assumed: the executable side solver returns a
  result, so by @{thm sign_terminates_prog_via_solve_c} the program is in the
  solver's domain.\<close>

lemma ec_terminates: "sign_terminates_prog branch_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: from any input store, every store reaching
  the exit under the interprocedural collecting semantics is over-approximated
  by the computed result -- across the \<open>if\<close>/\<open>else\<close> and both calls to \<open>compute\<close>.
  An instance of the program-parametric @{thm sign_exec_prog_sound_collecting}.
\<close>

corollary ec_certified_sound:
  "cfg_collect_ip (prog_cfg branch_prog) cinit_stores (cfg_exit (prog_cfg branch_prog))
   \<le> sign_domain.gamma_state (sign_exec_prog branch_prog)"
  by (rule sign_exec_prog_sound_collecting[OF ec_terminates])

text \<open>
  The same bound against the underlying interprocedural \<open>trace\<close> semantics: the
  last store of \<^emph>\<open>any\<close> C-faithful trace reaching the exit is over-approximated
  by the computed result.
\<close>

corollary ec_certified_sound_trace:
  assumes "tr \<in> cfg_collect_trace_ip (prog_cfg branch_prog) cinit_stores (cfg_exit (prog_cfg branch_prog))"
  shows "last tr \<in> sign_domain.gamma_state (sign_exec_prog branch_prog)"
  using assms by (rule sign_exec_prog_sound_trace[OF ec_terminates])

text \<open>
  Flow-insensitive global analysis: concrete values of every global at the exit.
  The analysis joins all writes to a global across the entire program against the
  C-faithful initialisation seed (\<open>SZero\<close> for globals).
\<close>

value "sign_exec_prog branch_prog ''Ginput''"

text \<open>
  \<open>Ginput\<close> is assigned \<open>5\<close> (positive) and \<open>-3\<close> (negative) in \<open>main\<close>.  Both
  writes are joined: \<open>SZero \<squnion> SPos \<squnion> SNeg = SZero \<squnion> STop = STop\<close>.
  Opposite-sign writes still collapse to \<open>STop\<close> regardless of the seed.
\<close>

lemma ec_ginput_top:
  "sign_exec_prog branch_prog ''Ginput'' = STop"
  by eval

value "sign_exec_prog branch_prog ''Gout''"

text \<open>
  \<open>Gout\<close> is computed as \<open>100 * Gresult\<close>.  With \<open>Gresult = SNonNeg\<close>
  (see @{thm ec_result_nonnneg}), the product \<open>SPos * SNonNeg = SNonNeg\<close>
  joined against the zero seed gives \<open>SZero \<squnion> SNonNeg = SNonNeg\<close>.
\<close>

lemma ec_gout_nonnneg:
  "sign_exec_prog branch_prog ''Gout'' = SNonNeg"
  by eval

text \<open>
  Precision summary.

  \<^bold>\<open>What the analysis now computes (C-faithful seed + 7-element lattice):\<close>

  \<^item> \<open>Ginput = STop\<close>: writes \<open>5\<close> and \<open>-3\<close> have opposite signs; their join is
    \<open>STop\<close> regardless of the seed.

  \<^item> \<open>Gresult = SNonNeg\<close>: both branches of \<open>compute\<close> assign a positive \<open>x\<close>
    (\<open>1+1\<close> and \<open>1+2\<close>).  The write \<open>SPos\<close> is joined against the \<open>SZero\<close> seed:
    \<open>SZero \<squnion> SPos = SNonNeg\<close>.  The 5-element flat lattice would have given
    \<open>STop\<close> here; the 7-element lattice gives \<open>SNonNeg\<close>.

  \<^item> \<open>Gout = SNonNeg\<close>: \<open>SPos * SNonNeg = SNonNeg\<close>, joined against \<open>SZero\<close>.

  \<^bold>\<open>Remaining precision gap:\<close>

  \<open>SNonNeg\<close> includes \<open>0\<close>, so the analysis cannot certify \<open>Gresult \<noteq> 0\<close> -- the
  check needed to justify the original \<open>100 / Gresult\<close>.  That would require
  knowing \<open>Gresult\<close> is strictly positive (\<open>SPos\<close>), which in turn requires
  knowing the initial write of \<open>0\<close> is overwritten before the exit (flow
  sensitivity on globals, not modelled here).

  \<^bold>\<open>What stays precise:\<close>

  The local variable \<open>x\<close> inside @{term compute} is analysed flow-sensitively.
  On the then-branch \<open>x = 1 + 1 = 2\<close> and on the else-branch \<open>x = 1 + 2 = 3\<close>;
  both are \<open>SPos\<close>.  This precision is preserved inside the procedure body.
\<close>

end
