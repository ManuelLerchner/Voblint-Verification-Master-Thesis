theory Example_Side_Branch_Calls
  imports "Voblint_CLI.Sign_Entry" "Voblint_VIMP.VIMP_Notation"
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
  The computed abstract state at the exit, read out of the routed solved table
  the production report also reads.  Seeding is C-faithful (\<open>cinit_sign_st\<close>:
  globals start at \<open>SZero\<close>, locals at \<open>STop\<close>), and the 7-element lattice keeps
  a positive global apart from a non-negative one: both branches of \<open>compute\<close>
  assign a positive \<open>Glocal\<close> to \<open>result_val\<close>, and every path to the exit runs
  \<open>compute\<close>, so at the exit \<open>result_val\<close> is \<open>SPos\<close>.
\<close>

text \<open>Termination is proved, not assumed: the executable routed solver returns
  a result, so the program is in the solver's domain. The three closure facts
  are computed the same way; this program really does have call edges, so they
  are not vacuous.\<close>

lemma ec_reserved: "reserved_ret_var branch_prog_gs"
  unfolding reserved_ret_var_def branch_prog_def by (simp add: ret_var_def)

lemma ec_terminates: "sctx_terminates_prog branch_prog_gs prog_main_name branch_prog"
  by (rule sctx_terminates_prog_via_solve_c) eval

lemma ec_entry_cov:
  "(cfg_entry (prog_cfg prog_main_name branch_prog), ())
     \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
  by eval

lemma ec_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg prog_main_name branch_prog).
     (u, ()) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog) \<longrightarrow>
     (w, ()) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
  by eval

lemma ec_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
    and "(u, a, w) \<in> intra (prog_cfg prog_main_name branch_prog)"
  shows "(w, ctx) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
  using assms ec_fwd_ok_ball by (cases ctx) auto

lemma ec_calls_cov_ball:
  "\<forall>(u, ca, ce, k) \<in> calls (prog_cfg prog_main_name branch_prog).
     (case ce of FunctionEntry q \<Rightarrow>
        (FunctionEntry q, ()) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)
      | _ \<Rightarrow> True)
     \<and> ((k, ()) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog))"
  by eval

lemma ec_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name branch_prog)"
  shows "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
  using assms ec_calls_cov_ball by fastforce

lemma ec_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name branch_prog)"
  shows "(k, c1) \<in> fst (sctx_sol_prog branch_prog_gs prog_main_name branch_prog)"
  using assms ec_calls_cov_ball by (cases c1) fastforce

lemma ec_node_sound:
  "ltr_collect branch_prog_gs (prog_cfg prog_main_name branch_prog) (cinit_stores branch_prog_gs) v
     \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for branch_prog_gs branch_prog) v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
  by (rule analyse_sign_result_node_sound_for
        [OF ec_reserved ec_terminates ec_entry_cov
            ec_fwd_ok ec_call_fwd_ok ec_comb_fwd_ok])

text \<open>The computed environment at the exit, read out of the routed solved
  table the production report also reads.\<close>

definition branch_prog_env :: "vname \<Rightarrow> sign" where
  "branch_prog_env =
     (case lookup_context (analyse_sign_result_for branch_prog_gs branch_prog)
             (cfg_exit (prog_cfg prog_main_name branch_prog)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

text \<open>
  Certified sound, unconditionally: from any input store, every store reaching
  the exit under the interprocedural collecting semantics is over-approximated
  by the computed result -- across the \<open>if\<close>/\<open>else\<close> and both calls to \<open>compute\<close>.
\<close>

corollary ec_certified_sound:
  "ltr_collect branch_prog_gs (prog_cfg (STR ''main'') branch_prog) (cinit_stores branch_prog_gs) (cfg_exit (prog_cfg (STR ''main'') branch_prog))
   \<le> \<lbrakk>branch_prog_env\<rbrakk>"
  unfolding branch_prog_env_def
  using ec_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

text \<open>
  The store-level reading: \<^emph>\<open>any\<close> store reaching the exit under the
  interprocedural collecting semantics is over-approximated by the computed
  result.
\<close>

corollary ec_certified_sound_store:
  assumes "s \<in> ltr_collect branch_prog_gs (prog_cfg (STR ''main'') branch_prog) (cinit_stores branch_prog_gs) (cfg_exit (prog_cfg (STR ''main'') branch_prog))"
  shows "s \<in> \<lbrakk>branch_prog_env\<rbrakk>"
  using assms ec_certified_sound by blast

lemma ec_result_pos:
  "branch_prog_env (STR ''result_val'') = SPos"
  by (simp add: branch_prog_env_def) eval

text \<open>
  \<open>input_val\<close> is assigned \<open>5\<close> (positive) and \<open>-3\<close> (negative) in \<open>main\<close>.  Both
  writes are joined: \<open>SPos \<squnion> SNeg = STop\<close>.  Opposite-sign writes collapse to
  \<open>STop\<close> whatever the initialisation seed contributes.
\<close>

lemma ec_ginput_top:
  "branch_prog_env (STR ''input_val'') = STop"
  by (simp add: branch_prog_env_def) eval

text \<open>
  \<open>out_val\<close> is computed as \<open>100 * result_val\<close>.  With \<open>result_val = SPos\<close>
  (@{thm ec_result_pos}), the product is \<open>SPos * SPos = SPos\<close>.
\<close>

lemma ec_gout_pos:
  "branch_prog_env (STR ''out_val'') = SPos"
  by (simp add: branch_prog_env_def) eval

lemma ec_r_pos:
  "branch_prog_env (STR ''r'') = SPos"
  by (simp add: branch_prog_env_def) eval

text \<open>
  Precision summary at the exit.

  \<^item> \<open>input_val = STop\<close>: the writes \<open>5\<close> and \<open>-3\<close> have opposite signs, so no
    single sign element covers both.

  \<^item> \<open>result_val = SPos\<close>: both branches of \<open>compute\<close> assign a positive
    \<open>Glocal\<close> (\<open>1+1\<close> and \<open>1+2\<close>), and every path reaching the exit has run
    \<open>compute\<close>, so the zero initial value is not live there.  Exact.

  \<^item> \<open>out_val = SPos\<close>: \<open>SPos * SPos = SPos\<close>.  Exact.

  \<^item> \<open>r = SPos\<close>: \<open>r := 0\<close> followed by two increments.  Exact.

  Since \<open>result_val\<close> is \<open>SPos\<close> and not merely \<open>\<ge> 0\<close>, the analysis certifies
  \<open>result_val \<noteq> 0\<close> -- the check a division such as \<open>100 / result_val\<close> needs.

  \<^bold>\<open>Local precision:\<close>

  The local variable @{text "Glocal"} inside @{term compute} is analysed
  flow-sensitively despite its \<open>G\<close> prefix -- \<^const>\<open>declared_global\<close> never
  consults spelling. On the then-branch @{text "Glocal = 1 + 1 = 2"} and on the
  else-branch @{text "Glocal = 1 + 2 = 3"}; both are @{term SPos}.  In
  @{text "main"}, @{text "r"} counts procedure calls
  (@{text "r := 0"} then two @{text "r := r + 1"}); at exit @{thm ec_r_pos}.
\<close>

end
