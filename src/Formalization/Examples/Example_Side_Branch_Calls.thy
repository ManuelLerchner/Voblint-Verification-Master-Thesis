theory Example_Side_Branch_Calls
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Certified sign analyzer on a branching, repeatedly-called procedure\<close>

text \<open>
  A richer end-to-end witness than \<^verbatim>\<open>Example_Side_Execute_Proc\<close>:
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

abbreviation ec_pt   :: proc_table   where "ec_pt   \<equiv> prog_table branch_prog"
abbreviation ec_ps   :: "pname list" where "ec_ps   \<equiv> prog_procs branch_prog"
abbreviation ec_main :: com          where "ec_main \<equiv> prog_main  branch_prog"

abbreviation ec_exit :: pp where
  "ec_exit \<equiv> cfg_exit (compile_prog ec_pt ec_ps ec_main)"

text \<open>
  The computed abstract state at the exit (these @{command value} calls evaluate
  at build time).  The concrete \<open>x\<close> is positive on both branches (\<open>1+1\<close> and
  \<open>1+2\<close>), but that does not survive to the exit: \<open>x\<close> is local, and \<open>Gresult\<close>
  (hence \<open>Gout\<close>) is a flow-insensitive global unknown joined against the \<open>STop\<close>
  entry seed, so every global reads back \<open>STop\<close>.  The bound is sound; the sign
  domain is simply too coarse on globals to certify \<open>Gresult \<noteq> 0\<close> -- the check
  a client would need to justify the original \<open>100 / Gresult\<close>.
\<close>

value "sign_exec ec_pt ec_ps ec_main ''Gresult''"
value "sign_exec ec_pt ec_ps ec_main ''Gout''"

lemma ec_result_top:
  "sign_exec ec_pt ec_ps ec_main ''Gresult'' = STop"
  by eval

text \<open>Termination is proved, not assumed: the executable side solver returns a
  result, so by @{thm sign_exec_terminates_via_solve_c} the program is in the
  solver's domain.\<close>

lemma ec_terminates: "sign_exec_terminates ec_pt ec_ps ec_main"
  by (rule sign_exec_terminates_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: from any input store, every store reaching
  the exit under the interprocedural collecting semantics is over-approximated
  by the computed result -- across the \<open>if\<close>/\<open>else\<close> and both calls to \<open>compute\<close>.
  An instance of the program-parametric @{thm sign_exec_sound_collecting}.
\<close>

corollary ec_certified_sound:
  "cfg_collect_ip (compile_prog ec_pt ec_ps ec_main) UNIV ec_exit
   \<le> sign_domain.gamma_state (sign_exec ec_pt ec_ps ec_main)"
  by (rule sign_exec_sound_collecting[OF ec_terminates])

text \<open>
  Flow-insensitive global analysis: concrete values of every global at the exit.
  The analysis joins all writes to a global across the entire program (both call
  sites of @{term compute} and the surrounding @{term ec_main}) against the
  \<open>STop\<close> initialisation seed.
\<close>

value "sign_exec ec_pt ec_ps ec_main ''Ginput''"

text \<open>
  @{term Ginput} is assigned the literal \<open>5\<close> (positive) and \<open>-3\<close> (negative)
  in @{term ec_main}.  Because globals are treated flow-insensitively, both
  writes are joined: \<open>SPos \<squnion> SNeg = STop\<close>.
\<close>

lemma ec_ginput_top:
  "sign_exec ec_pt ec_ps ec_main ''Ginput'' = STop"
  by eval

value "sign_exec ec_pt ec_ps ec_main ''Gout''"

text \<open>
  @{term Gout} is computed as \<open>100 * Gresult\<close>.  Since @{term Gresult} is
  already \<open>STop\<close> (see @{thm ec_result_top}), the product \<open>SPos * STop = STop\<close>
  propagates the imprecision.
\<close>

lemma ec_gout_top:
  "sign_exec ec_pt ec_ps ec_main ''Gout'' = STop"
  by eval

text \<open>
  Precision summary.  Tracing the analysis step by step reveals where precision
  is lost and what a hypothetical more-precise analysis would need.

  \<^bold>\<open>What the analysis computes:\<close>

  \<^item> \<open>Ginput = STop\<close>: two writes with opposite signs (\<open>5\<close> positive, \<open>-3\<close>
    negative) join to the top element.  The analysis cannot distinguish the
    two call contexts.

  \<^item> \<open>Gresult = STop\<close>: the assignment \<open>result = x\<close> inside @{term compute}
    writes a locally positive \<open>x\<close> (\<open>1 + 1\<close> and \<open>1 + 2\<close>, both positive), but
    that write is joined against the \<open>STop\<close> initialisation seed.  Joining
    \<open>SPos\<close> with the seed \<open>STop\<close> gives \<open>STop\<close>.

  \<^item> \<open>Gout = STop\<close>: \<open>100 * STop = STop\<close>; the imprecision propagates.

  \<^bold>\<open>What flow-sensitive global analysis would yield:\<close>

  A fully flow-sensitive analysis seeding globals at \<open>SBot\<close> (\(\bot\)) would
  compute \<open>Gresult = SPos\<close> (both branches write a positive \<open>x\<close>) and in turn
  certify \<open>Gresult \<noteq> 0\<close>, ruling out division-by-zero in the original
  \<open>100 / result\<close>.  The sign domain is sufficiently precise for that goal;
  only the flow-insensitive treatment of globals blocks the certification.

  \<^bold>\<open>What stays precise:\<close>

  The local variable \<open>x\<close> inside @{term compute} is analysed flow-sensitively.
  On the then-branch \<open>x = 1 + 1 = 2\<close> (positive) and on the else-branch
  \<open>x = 1 + 2 = 3\<close> (positive); both are \<open>SPos\<close>.  This flow-sensitive precision
  is preserved inside the procedure body --- it is only the global write that
  loses information when the result is stored in @{term Gresult}.
\<close>

end
