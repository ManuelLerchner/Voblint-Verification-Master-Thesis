theory Example_Side_Branch_Calls
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Certified sign analyzer on a branching, repeatedly-called procedure\<close>

text \<open>
  A richer end-to-end witness than the single-statement \<^verbatim>\<open>Example_Side_Execute\<close>:
  a procedure \<open>compute\<close> with an \<open>if\<close>/\<open>else\<close> on a global input, called twice from
  \<open>main\<close> with different inputs, followed by an arithmetic use of the result.  In C:

  \begin{verbatim}
  int input_val; int result_val; int out_val;   // globals, no naming hint
  void compute() {
      int Glocal = 1;                 // local, G-prefixed but not global
      if (input_val > 0) Glocal = Glocal + 1;
      else                Glocal = Glocal + 2;
      result_val = Glocal;
  }
  int main() {
      int r = 0;                      // local call counter
      input_val = 5;   compute();  r = r + 1;
      input_val = -3;  compute();  r = r + 1;
      out_val = 100 * result_val;           // language has no '/', so use '*'
  }
  \end{verbatim}

  Two modelling notes.  The expression language @{type exp} has \<open>Plus\<close> /
  \<open>Minus\<close> / \<open>Times\<close> but no division, so \<open>100 / result_val\<close> is written as the
  multiplication \<open>100 * result_val\<close>.  \<open>input_val\<close>, \<open>result_val\<close>, and \<open>out_val\<close> are
  declared \<open>global\<close> in the source below despite carrying no naming hint;
  @{text "Glocal"} is local to @{text "compute"} despite the classic \<open>G\<close>
  prefix, and @{text "r"} to @{text "main"} -- \<^const>\<open>declared_global\<close> reads
  storage off the declaration list, never off spelling (see
  \<open>branch_prog_glocal_not_global\<close> below).
\<close>


definition branch_prog :: imp_prog where
  "branch_prog = program {
     global input_val, result_val, out_val;

     void compute() {
       Glocal := 1;
       if (0 < input_val) { Glocal := Glocal + 1 } else { Glocal := Glocal + 2 };
       result_val := Glocal
     }
     void main() {
       r := 0;
       input_val := 5;
       compute();
       r := r + 1;
       input_val := 0 - 3;
       compute();
       r := r + 1;
       out_val := 100 * result_val
     }
   }"

abbreviation branch_prog_gs :: "vname \<Rightarrow> bool" where
  "branch_prog_gs \<equiv> declared_global branch_prog"

lemma branch_prog_declared_global_vars [simp]:
  "declared_global_vars branch_prog = [(STR ''input_val''), (STR ''result_val''), (STR ''out_val'')]"
  by (simp add: branch_prog_def)

lemma branch_prog_glocal_not_global [simp]: "\<not> branch_prog_gs (STR ''Glocal'')"
  by simp

lemma branch_prog_result_val_global [simp]: "branch_prog_gs (STR ''result_val'')"
  by simp

text \<open>
  The computed abstract state at the exit.  With C-faithful seeding
  (\<open>cinit_sign_st\<close>: globals start at \<open>SZero\<close>, locals at \<open>STop\<close>), the
  7-element lattice can give tighter global bounds: \<open>SZero \<squnion> SPos = SNonNeg\<close>
  instead of \<open>STop\<close>.  Concretely, both branches of \<open>compute\<close> assign
  a positive \<open>Glocal\<close> to \<open>result_val\<close>; joined against the zero initial value
  the result is \<open>SNonNeg\<close> (\<open>\<ge> 0\<close>), not \<open>STop\<close>.
\<close>

text \<open>
  \<open>sign_exec_prog\<close> now returns a reachability-lifted \<^typ>\<open>sign abs_state lifted\<close>
  (\<open>#113\<close>): \<open>branch_prog_env\<close> unwraps it to the raw environment
  \<^const>\<open>case_lifted\<close> reads off directly, since \<open>branch_prog\<close>'s exit is reachable
  and this witness is only ever used as a function of a vname below.
\<close>

definition branch_prog_env :: "vname \<Rightarrow> sign" where
  "branch_prog_env = case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog branch_prog_gs (STR ''main'') branch_prog)"

lemma ec_result_nonnneg:
  "branch_prog_env (STR ''result_val'') = SNonNeg"
  by (simp add: branch_prog_env_def) eval

text \<open>Termination is proved, not assumed: the executable side solver returns a
  result, so by @{thm sign_terminates_prog_via_solve_c} the program is in the
  solver's domain.\<close>

lemma ec_terminates: "sign_terminates_prog branch_prog_gs (STR ''main'') branch_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

text \<open>
  Certified sound, unconditionally: from any input store, every store reaching
  the exit under the interprocedural collecting semantics is over-approximated
  by the computed result -- across the \<open>if\<close>/\<open>else\<close> and both calls to \<open>compute\<close>.
  An instance of the program-parametric @{thm sign_exec_prog_sound_collecting}.
\<close>

corollary ec_certified_sound:
  "ltr_collect branch_prog_gs (prog_cfg (STR ''main'') branch_prog) (cinit_stores branch_prog_gs) (cfg_exit (prog_cfg (STR ''main'') branch_prog))
   \<le> gamma_state_lift (sign_exec_prog branch_prog_gs (STR ''main'') branch_prog)"
  by (rule sign_exec_prog_sound_collecting[OF refl ec_terminates])

text \<open>
  The store-level reading: \<^emph>\<open>any\<close> store reaching the exit under the
  interprocedural collecting semantics is over-approximated by the computed
  result.
\<close>

corollary ec_certified_sound_store:
  assumes "s \<in> ltr_collect branch_prog_gs (prog_cfg (STR ''main'') branch_prog) (cinit_stores branch_prog_gs) (cfg_exit (prog_cfg (STR ''main'') branch_prog))"
  shows "s \<in> gamma_state_lift (sign_exec_prog branch_prog_gs (STR ''main'') branch_prog)"
  using assms ec_certified_sound by blast

text \<open>
  Flow-insensitive global analysis: concrete values of every global at the exit.
  The analysis joins all writes to a global across the entire program against the
  C-faithful initialisation seed (\<open>SZero\<close> for globals).
\<close>

text \<open>
  \<open>input_val\<close> is assigned \<open>5\<close> (positive) and \<open>-3\<close> (negative) in \<open>main\<close>.  Both
  writes are joined: \<open>SZero \<squnion> SPos \<squnion> SNeg = SZero \<squnion> STop = STop\<close>.
  Opposite-sign writes still collapse to \<open>STop\<close> regardless of the seed.
\<close>

lemma ec_ginput_top:
  "branch_prog_env (STR ''input_val'') = STop"
  by (simp add: branch_prog_env_def) eval

text \<open>
  \<open>out_val\<close> is computed as \<open>100 * result_val\<close>.  With \<open>result_val = SNonNeg\<close>
  (see @{thm ec_result_nonnneg}), the product \<open>SPos * SNonNeg = SNonNeg\<close>
  joined against the zero seed gives \<open>SZero \<squnion> SNonNeg = SNonNeg\<close>.
\<close>

lemma ec_gout_nonnneg:
  "branch_prog_env (STR ''out_val'') = SNonNeg"
  by (simp add: branch_prog_env_def) eval

lemma ec_r_pos:
  "branch_prog_env (STR ''r'') = SPos"
  by (simp add: branch_prog_env_def) eval

text \<open>
  Precision summary.

  \<^bold>\<open>Computed result with the concrete-faithful seed and seven-element lattice:\<close>

  \<^item> \<open>input_val = STop\<close>: writes \<open>5\<close> and \<open>-3\<close> have opposite signs; their join is
    \<open>STop\<close> regardless of the seed.

  \<^item> \<open>result_val = SNonNeg\<close>: both branches of \<open>compute\<close> assign a positive
    \<open>Glocal\<close> (\<open>1+1\<close> and \<open>1+2\<close>).  The write \<open>SPos\<close> is joined against the \<open>SZero\<close> seed:
    \<open>SZero \<squnion> SPos = SNonNeg\<close>.  The 5-element flat lattice would have given
    \<open>STop\<close> here; the 7-element lattice gives \<open>SNonNeg\<close>.

  \<^item> \<open>out_val = SNonNeg\<close>: \<open>SPos * SNonNeg = SNonNeg\<close>, joined against \<open>SZero\<close>.

  \<^bold>\<open>Precision limitation:\<close>

  \<open>SNonNeg\<close> includes \<open>0\<close>, so the analysis cannot certify \<open>result_val \<noteq> 0\<close> -- the
  check needed to justify a division such as \<open>100 / result_val\<close>.  That would require
  knowing \<open>result_val\<close> is strictly positive (\<open>SPos\<close>), which in turn requires
  knowing the initial write of \<open>0\<close> is overwritten before the exit (flow
  sensitivity on globals, not modelled here).

  \<^bold>\<open>Local precision:\<close>

  The local variable @{text "Glocal"} inside @{term compute} is analysed
  flow-sensitively despite its \<open>G\<close> prefix -- \<^const>\<open>declared_global\<close> never
  consults spelling. On the then-branch @{text "Glocal = 1 + 1 = 2"} and on the
  else-branch @{text "Glocal = 1 + 2 = 3"}; both are @{term SPos}.  In
  @{text "main"}, @{text "r"} counts procedure calls
  (@{text "r := 0"} then two @{text "r := r + 1"}); at exit @{thm ec_r_pos}.
\<close>

end


