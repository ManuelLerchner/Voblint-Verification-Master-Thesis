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

definition proc_pi :: proc_table where
  "proc_pi = (\<lambda>_. None)((STR ''inc'') := Some (proc_decl_of [] inc_body), (STR ''sqr'') := Some (proc_decl_of [] sqr_body))"

definition main_prog :: "VIMP_Proc.com" where
  "main_prog = imp \<lbrakk>
     Gx := 4;
     inc();
     sqr()
   \<rbrakk>"

definition main_procs :: "pname list" where
  "main_procs = [(STR ''inc''), (STR ''sqr'')]"

text \<open>The program carries no kind annotations, so every variable is declared at
  \<^const>\<open>I32\<close> and \<^const>\<open>default_tyenv\<close> is the environment the compiler and
  the source semantics both elaborate against.\<close>

lemma proc_call_ik_range_I32 [simp]:
  "(4::int) \<in> ik_range I32" "(5::int) \<in> ik_range I32" "(25::int) \<in> ik_range I32"
  by eval+

subsection \<open>Concrete run\<close>

text \<open>
  Each call leaves the global incremented or squared; the caller's locals
  are restored by @{const combine_env}.
\<close>

text \<open>The two range premises are what make the machine increment agree with
  \<open>+ 1\<close>: without them the assignment writes the wrapped successor.\<close>
lemma call_inc_result:
  assumes ty: "s (STR ''Gx'') \<in> ik_range I32"
      and nov: "s (STR ''Gx'') + 1 \<in> ik_range I32"
  shows "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>) s
           (s((STR ''Gx'') := s (STR ''Gx'') + 1)) rk"
proof -
  have run: "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>) s
                (VIMP_Globals.combine_env proc_call_gs s
                  ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') + 1))) rk"
  proof (rule pcompletes_Call_parameterless[where c = inc_body])
    show "proc_pi (STR ''inc'') = Some (proc_decl_of [] inc_body)"
      by (simp add: proc_pi_def)
    show "pcompletes default_tyenv proc_call_gs proc_pi inc_body (enter_state proc_call_gs s)
             ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') + 1)) I32"
    proof -
      have "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> Gx := Gx + 1 \<rbrakk>)
               (enter_state proc_call_gs s)
               ((enter_state proc_call_gs s)
                 ((STR ''Gx'') := ik_norm (default_tyenv (STR ''Gx''))
                    (taval_syn default_tyenv (Plus (V (STR ''Gx'')) (N 1))
                       (enter_state proc_call_gs s)))) I32"
        by (rule pcompletes_assign)
      moreover have "ik_norm (default_tyenv (STR ''Gx''))
                       (taval_syn default_tyenv (Plus (V (STR ''Gx'')) (N 1))
                          (enter_state proc_call_gs s))
                     = s (STR ''Gx'') + 1"
        using ty nov
        by (simp add: enter_state_def proc_call_gs_def taval_syn_def opk_def default_tyenv_def)
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
  assumes ty: "s (STR ''Gx'') \<in> ik_range I32"
      and nov: "s (STR ''Gx'') * s (STR ''Gx'') \<in> ik_range I32"
  shows "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s
           (s((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx''))) rk"
proof -
  have run: "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s
                (VIMP_Globals.combine_env proc_call_gs s
                  ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx'')))) rk"
  proof (rule pcompletes_Call_parameterless[where c = sqr_body])
    show "proc_pi (STR ''sqr'') = Some (proc_decl_of [] sqr_body)"
      by (simp add: proc_pi_def)
    show "pcompletes default_tyenv proc_call_gs proc_pi sqr_body (enter_state proc_call_gs s)
             ((enter_state proc_call_gs s)((STR ''Gx'') := s (STR ''Gx'') * s (STR ''Gx''))) I32"
    proof -
      have "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> Gx := Gx * Gx \<rbrakk>)
               (enter_state proc_call_gs s)
               ((enter_state proc_call_gs s)
                 ((STR ''Gx'') := ik_norm (default_tyenv (STR ''Gx''))
                    (taval_syn default_tyenv (Times (V (STR ''Gx'')) (V (STR ''Gx'')))
                       (enter_state proc_call_gs s)))) I32"
        by (rule pcompletes_assign)
      moreover have
        "ik_norm (default_tyenv (STR ''Gx''))
           (taval_syn default_tyenv (Times (V (STR ''Gx'')) (V (STR ''Gx'')))
              (enter_state proc_call_gs s))
         = s (STR ''Gx'') * s (STR ''Gx'')"
        using ty nov
        by (simp add: enter_state_def proc_call_gs_def taval_syn_def opk_def default_tyenv_def)
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
  "pcompletes default_tyenv proc_call_gs proc_pi main_prog s (s((STR ''Gx'') := 25)) rk"
proof -
  have step1: "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> Gx := 4 \<rbrakk>) s
                 (s((STR ''Gx'') := 4)) rk"
    using pcompletes_assign[where \<Gamma> = default_tyenv and gs = proc_call_gs and \<Pi> = proc_pi
        and x = "(STR ''Gx'')" and a = "N 4" and s = s and rk = rk]
    by (simp add: pcompletes_def taval_syn_def opk_def default_tyenv_def ik_bounds_pins)
  have step2: "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> inc() \<rbrakk>)
                 (s((STR ''Gx'') := 4)) (s((STR ''Gx'') := 5)) rk"
    using call_inc_result[where s = "s((STR ''Gx'') := 4)"]
    by (simp add: ik_bounds_pins)
  have step3: "pcompletes default_tyenv proc_call_gs proc_pi (imp \<lbrakk> sqr() \<rbrakk>)
                 (s((STR ''Gx'') := 5)) (s((STR ''Gx'') := 25)) rk"
    using call_sqr_result[where s = "s((STR ''Gx'') := 5)"]
    by (simp add: ik_bounds_pins)
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

abbreviation "main_cfg \<equiv>
  compile_prog default_tyenv proc_pi [(STR ''inc''), (STR ''sqr'')] main_cfg_name main_prog"

lemma main_cfg_full:
  "main_cfg =
     \<lparr> intra =
         {(FunctionEntry (STR ''inc''), EA_Nop, Statement 0),
          (Statement 0, EA_Assign (STR ''Gx'')
             (elaborate_to default_tyenv (default_tyenv (STR ''Gx'')) (Plus (V (STR ''Gx'')) (N 1))), Statement 1),
          (Statement 1, EA_Ret None (STR ''inc'') I32, FunctionResult (STR ''inc'')),
          (FunctionEntry (STR ''sqr''), EA_Nop, Statement 2),
          (Statement 2, EA_Assign (STR ''Gx'')
             (elaborate_to default_tyenv (default_tyenv (STR ''Gx''))
                (Times (V (STR ''Gx'')) (V (STR ''Gx'')))), Statement 3),
          (Statement 3, EA_Ret None (STR ''sqr'') I32, FunctionResult (STR ''sqr'')),
          (FunctionEntry (STR ''main''), EA_Nop, Statement 4),
          (Statement 4, EA_Assign (STR ''Gx'') (elaborate_to default_tyenv (default_tyenv (STR ''Gx'')) (N 4)), Statement 5),
          (Statement 7, EA_Ret None (STR ''main'') I32, FunctionResult (STR ''main''))},
       calls =
         {(Statement 5, CallEdge None [] [], FunctionEntry (STR ''inc''), Statement 6),
          (Statement 6, CallEdge None [] [], FunctionEntry (STR ''sqr''), Statement 7)},
       cfg_entry = FunctionEntry (STR ''main''),
       checks = {} \<rparr>"
  by (simp add: main_cfg_name_def) eval

lemma main_cfg_entry: "cfg_entry main_cfg = FunctionEntry (STR ''main'')"
  by (simp add: main_cfg_full)
lemma main_cfg_exit: "cfg_exit main_cfg = FunctionResult (STR ''main'')"
  by (simp add: main_cfg_full cfg_exit_def)
lemma main_cfg_intra:
  "intra main_cfg =
     {(FunctionEntry (STR ''inc''), EA_Nop, Statement 0),
      (Statement 0, EA_Assign (STR ''Gx'')
             (elaborate_to default_tyenv (default_tyenv (STR ''Gx'')) (Plus (V (STR ''Gx'')) (N 1))), Statement 1),
      (Statement 1, EA_Ret None (STR ''inc'') I32, FunctionResult (STR ''inc'')),
      (FunctionEntry (STR ''sqr''), EA_Nop, Statement 2),
      (Statement 2, EA_Assign (STR ''Gx'')
             (elaborate_to default_tyenv (default_tyenv (STR ''Gx''))
                (Times (V (STR ''Gx'')) (V (STR ''Gx'')))), Statement 3),
      (Statement 3, EA_Ret None (STR ''sqr'') I32, FunctionResult (STR ''sqr'')),
      (FunctionEntry (STR ''main''), EA_Nop, Statement 4),
      (Statement 4, EA_Assign (STR ''Gx'') (elaborate_to default_tyenv (default_tyenv (STR ''Gx'')) (N 4)), Statement 5),
      (Statement 7, EA_Ret None (STR ''main'') I32, FunctionResult (STR ''main''))}"
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
