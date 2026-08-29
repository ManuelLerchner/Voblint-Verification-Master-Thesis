section \<open>Example: Procedure Calls --- Increment and Square\<close>

theory Example_Proc_Call
  imports
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.CFG_Prune"

    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Analysis_GraphViz"
begin

definition main_cfg_name :: pname where
  "main_cfg_name = (STR ''main'')"

text \<open>
  Two parameterless procedures communicate through the global variable
  @{term \<open>(STR ''Gx'')\<close>}.  \<open>proc_call_gs\<close> is this program's explicit storage
  classifier: \<open>Gx\<close> is global by declaration, not by its leading letter, so it
  survives call-frame restore while locals are reset to zero.

  \<^item> \<open>inc\<close>: adds 1 to \<open>Gx\<close>.
  \<^item> \<open>sqr\<close>: replaces \<open>Gx\<close> with its square.

  Main program: \<open>Gx := 4; call inc; call sqr\<close>
  terminates with \<open>Gx = 25\<close> since \<open>(4 + 1)^2 = 25\<close>.
\<close>

definition proc_call_gs :: "vname \<Rightarrow> bool" where
  "proc_call_gs x \<longleftrightarrow> x = (STR ''Gx'')"

definition inc_body :: "VIMP_Proc.com" where
  "inc_body = imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition sqr_body :: "VIMP_Proc.com" where
  "sqr_body = imp \<lbrakk> Gx := Gx * Gx \<rbrakk>"

definition main_prog :: "VIMP_Proc.com" where
  "main_prog = imp \<lbrakk>
     Gx := 4;
     inc();
     sqr()
   \<rbrakk>"

definition proc_pi :: proc_table where
  "proc_pi = (\<lambda>_. None)((STR ''inc'') := Some (\<lparr>formals = [], body = inc_body\<rparr>),
                          (STR ''sqr'') := Some (\<lparr>formals = [], body = sqr_body\<rparr>),
                          prog_main_name := Some (\<lparr>formals = [], body = main_prog\<rparr>))"

definition main_procs :: "pname list" where
  "main_procs = [(STR ''inc''), (STR ''sqr'')]"

subsection \<open>Concrete run\<close>

text \<open>
  Each call leaves the global incremented or squared; the caller's locals
  are restored by @{const combine_env}.
\<close>

lemma call_inc_result:
  "pcompletes proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>) s (s((STR ''Gx'') := s (STR ''Gx'') + 1))"
proof -
  have run: "pcompletes proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>) s
                (VIMP_Globals.combine_env proc_call_gs s
                  ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') + 1)))"
  proof (rule pcompletes_Call_parameterless[where c = inc_body])
    show "proc_pi (STR ''inc'') = Some (\<lparr>formals = [], body = inc_body\<rparr>)"
      by (simp add: proc_pi_def prog_main_name_def)
    show "pcompletes proc_call_gs proc_pi inc_body (enter_state proc_call_gs s)
             ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') + 1))"
    proof -
      have "pcompletes proc_call_gs proc_pi (imp \<lbrakk> Gx := Gx + 1 \<rbrakk>)
               (enter_state proc_call_gs s)
               ((enter_state proc_call_gs s)
                 ((STR ''Gx'') := aval (Plus (V (STR ''Gx'')) (N 1)) (enter_state proc_call_gs s)))"
        by (rule pcompletes_assign)
      moreover have "aval (Plus (V (STR ''Gx'')) (N 1)) (enter_state proc_call_gs s) = s (STR ''Gx'') + 1"
        by (simp add: enter_state_def proc_call_gs_def)
      ultimately show ?thesis by (simp add: inc_body_def)
    qed
  qed
  moreover have
    "VIMP_Globals.combine_env proc_call_gs s ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') + 1))
       = s((STR ''Gx'') := s (STR ''Gx'') + 1)"
    by (rule ext) (simp add: enter_state_def proc_call_gs_def)
  ultimately show ?thesis by simp
qed

lemma call_sqr_result:
  "pcompletes proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s (s((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx'')))"
proof -
  have run: "pcompletes proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s
                (VIMP_Globals.combine_env proc_call_gs s
                  ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx''))))"
  proof (rule pcompletes_Call_parameterless[where c = sqr_body])
    show "proc_pi (STR ''sqr'') = Some (\<lparr>formals = [], body = sqr_body\<rparr>)"
      by (simp add: proc_pi_def prog_main_name_def)
    show "pcompletes proc_call_gs proc_pi sqr_body (enter_state proc_call_gs s)
             ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx'')))"
    proof -
      have "pcompletes proc_call_gs proc_pi (imp \<lbrakk> Gx := Gx * Gx \<rbrakk>)
               (enter_state proc_call_gs s)
               ((enter_state proc_call_gs s)
                 ((STR ''Gx'') := aval (Times (V (STR ''Gx'')) (V (STR ''Gx''))) (enter_state proc_call_gs s)))"
        by (rule pcompletes_assign)
      moreover have
        "aval (Times (V (STR ''Gx'')) (V (STR ''Gx''))) (enter_state proc_call_gs s) = s (STR ''Gx'') * s (STR ''Gx'')"
        by (simp add: enter_state_def proc_call_gs_def)
      ultimately show ?thesis by (simp add: sqr_body_def)
    qed
  qed
  moreover have
    "VIMP_Globals.combine_env proc_call_gs s
       ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx''))) = s((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx''))"
    by (rule ext) (simp add: enter_state_def proc_call_gs_def)
  ultimately show ?thesis by simp
qed

text \<open>
  @{const main_prog} terminates in @{term \<open>s((STR ''Gx'') := 25)\<close>} for every
  initial store, regardless of @{term \<open>(STR ''Gx'')\<close>}'s starting value.
\<close>
theorem main_prog_result:
  "pcompletes proc_call_gs proc_pi main_prog s (s((STR ''Gx'') := 25))"
proof -
  have step1: "pcompletes proc_call_gs proc_pi (imp \<lbrakk> Gx := 4 \<rbrakk>) s (s((STR ''Gx'') := 4))"
    using pcompletes_assign[where gs = proc_call_gs and \<Pi> = proc_pi and x = "(STR ''Gx'')" and a = "N 4" and s = s]
    by simp
  have step2: "pcompletes proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>) (s((STR ''Gx'') := 4)) (s((STR ''Gx'') := 5))"
    using call_inc_result[where s = "s((STR ''Gx'') := 4)"]
    by simp
  have step3: "pcompletes proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>) (s((STR ''Gx'') := 5)) (s((STR ''Gx'') := 25))"
    using call_sqr_result[where s = "s((STR ''Gx'') := 5)"]
    by simp
  show ?thesis
    unfolding main_prog_def
    by (rule pcompletes_Seq[OF pcompletes_Seq[OF step1 step2] step3])
qed

subsection \<open>Interprocedural CFG\<close>

text \<open>
  Compile @{const main_prog} together with its two procedure bodies.
  @{const compile_prog} first lays out @{const inc_body} at statements 0--1
  and @{const sqr_body} at statements 2--3, then compiles the main body
  starting at statement 4.  Each procedure is bracketed by its own
  @{const FunctionEntry} / @{const FunctionResult}; each call edge names its callee
  entry and its continuation, so the two calls are
  @{text "5 -> inc, continue at 6"} and @{text "6 -> sqr, continue at 7"}.
\<close>

abbreviation "main_cfg \<equiv> compile_prog proc_pi [(STR ''inc''), (STR ''sqr'')]"

lemma main_cfg_full:
  "main_cfg =
     \<lparr> intra =
         {(FunctionEntry (STR ''inc''), EA_Nop, Statement 0),
          (Statement 0, EA_Assign (STR ''Gx'') (Plus (V (STR ''Gx'')) (N 1)), Statement 1),
          (Statement 1, EA_Ret None (STR ''inc''), FunctionResult (STR ''inc'')),
          (FunctionEntry (STR ''sqr''), EA_Nop, Statement 2),
          (Statement 2, EA_Assign (STR ''Gx'') (Times (V (STR ''Gx'')) (V (STR ''Gx''))), Statement 3),
          (Statement 3, EA_Ret None (STR ''sqr''), FunctionResult (STR ''sqr'')),
          (FunctionEntry (STR ''main''), EA_Nop, Statement 4),
          (Statement 4, EA_Assign (STR ''Gx'') (N 4), Statement 5),
          (Statement 7, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))},
       calls =
         {(Statement 5, CallEdge None [] [], FunctionEntry (STR ''inc''), Statement 6),
          (Statement 6, CallEdge None [] [], FunctionEntry (STR ''sqr''), Statement 7)},
       cfg_entry = FunctionEntry (STR ''main''),
       checks = {} \<rparr>"
  by eval

lemma main_cfg_entry: "cfg_entry main_cfg = FunctionEntry (STR ''main'')"
  by (simp add: main_cfg_full)
lemma main_cfg_exit: "cfg_exit main_cfg = FunctionResult (STR ''main'')"
  by (simp add: main_cfg_full cfg_exit_def)
lemma main_cfg_intra:
  "intra main_cfg =
     {(FunctionEntry (STR ''inc''), EA_Nop, Statement 0),
      (Statement 0, EA_Assign (STR ''Gx'') (Plus (V (STR ''Gx'')) (N 1)), Statement 1),
      (Statement 1, EA_Ret None (STR ''inc''), FunctionResult (STR ''inc'')),
      (FunctionEntry (STR ''sqr''), EA_Nop, Statement 2),
      (Statement 2, EA_Assign (STR ''Gx'') (Times (V (STR ''Gx'')) (V (STR ''Gx''))), Statement 3),
      (Statement 3, EA_Ret None (STR ''sqr''), FunctionResult (STR ''sqr'')),
      (FunctionEntry (STR ''main''), EA_Nop, Statement 4),
      (Statement 4, EA_Assign (STR ''Gx'') (N 4), Statement 5),
      (Statement 7, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  by (simp add: main_cfg_full)
lemma main_cfg_calls:
  "calls main_cfg =
     {(Statement 5, CallEdge None [] [], FunctionEntry (STR ''inc''), Statement 6),
      (Statement 6, CallEdge None [] [], FunctionEntry (STR ''sqr''), Statement 7)}"
  by (simp add: main_cfg_full)

 


text \<open>
  A certified Sign analysis of a shared-global increment call is
  @{text "Example_Side_Proc_Global"};
  this theory's own contribution is the concrete run (@{thm [source]
  main_prog_result [no_vars]}) and the compiled interprocedural CFG above.
\<close>

end
