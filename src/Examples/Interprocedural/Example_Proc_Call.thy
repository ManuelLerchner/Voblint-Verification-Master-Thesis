section \<open>Example: Procedure Calls --- Increment and Square\<close>

theory Example_Proc_Call
  imports
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.CFG_Prune"

    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.LTR_Analysis_Sound"
    "Voblint_Analysis.Analysis_GraphViz"
begin

definition main_cfg_name :: pname where
  "main_cfg_name = ''main''"

text \<open>
  Two parameterless procedures communicate through the global variable
  @{term \<open>''Gx''\<close>}.  Variable names starting with \<open>G\<close> are global:
  they survive call-frame restore while locals are reset to zero.

  \<^item> \<open>inc\<close>: adds 1 to \<open>Gx\<close>.
  \<^item> \<open>sqr\<close>: replaces \<open>Gx\<close> with its square.

  Main program: \<open>Gx := 4; call inc; call sqr\<close>
  terminates with \<open>Gx = 25\<close> since \<open>(4 + 1)^2 = 25\<close>.
\<close>

definition inc_body :: "VIMP_Proc.com" where
  "inc_body = imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition sqr_body :: "VIMP_Proc.com" where
  "sqr_body = imp \<lbrakk> Gx := Gx * Gx \<rbrakk>"

definition proc_pi :: proc_table where
  "proc_pi = (\<lambda>_. None)(''inc'' := Some (proc_decl_of [] inc_body), ''sqr'' := Some (proc_decl_of [] sqr_body))"

definition main_prog :: "VIMP_Proc.com" where
  "main_prog = imp \<lbrakk>
     Gx := 4;
     inc();
     sqr()
   \<rbrakk>"

definition main_procs :: "pname list" where
  "main_procs = [''inc'', ''sqr'']"

subsection \<open>Concrete run\<close>

text \<open>
  Each call leaves the global incremented or squared; the caller's locals
  are restored by @{const combine_states}.
\<close>

lemma call_inc_result:
  "pcompletes proc_pi (imp \<lbrakk> inc() \<rbrakk>) s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  have run: "pcompletes proc_pi (imp \<lbrakk> inc() \<rbrakk>) s
                (VIMP_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' + 1)))"
  proof (rule pcompletes_Call_parameterless[where c = inc_body])
    show "proc_pi ''inc'' = Some (proc_decl_of [] inc_body)"
      by (simp add: proc_pi_def)
    show "pcompletes proc_pi inc_body (enter_state s)
             ((enter_state s)(''Gx'' := s ''Gx'' + 1))"
    proof -
      have "pcompletes proc_pi (imp \<lbrakk> Gx := Gx + 1 \<rbrakk>)
               (enter_state s)
               ((enter_state s)(''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state s)))"
        by (rule pcompletes_assign)
      moreover have "aval (Plus (V ''Gx'') (N 1)) (enter_state s) = s ''Gx'' + 1"
        by (simp add: enter_state_def is_global_def)
      ultimately show ?thesis by (simp add: inc_body_def)
    qed
  qed
  moreover have "VIMP_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' + 1)) = s(''Gx'' := s ''Gx'' + 1)"
    by (rule ext) (simp add: enter_state_def is_global_def)
  ultimately show ?thesis by simp
qed

lemma call_sqr_result:
  "pcompletes proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s (s(''Gx'' := s ''Gx'' * s ''Gx''))"
proof -
  have run: "pcompletes proc_pi (imp \<lbrakk> sqr() \<rbrakk>) s
                (VIMP_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx'')))"
  proof (rule pcompletes_Call_parameterless[where c = sqr_body])
    show "proc_pi ''sqr'' = Some (proc_decl_of [] sqr_body)"
      by (simp add: proc_pi_def)
    show "pcompletes proc_pi sqr_body (enter_state s)
             ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx''))"
    proof -
      have "pcompletes proc_pi (imp \<lbrakk> Gx := Gx * Gx \<rbrakk>)
               (enter_state s)
               ((enter_state s)(''Gx'' := aval (Times (V ''Gx'') (V ''Gx'')) (enter_state s)))"
        by (rule pcompletes_assign)
      moreover have "aval (Times (V ''Gx'') (V ''Gx'')) (enter_state s) = s ''Gx'' * s ''Gx''"
        by (simp add: enter_state_def is_global_def)
      ultimately show ?thesis by (simp add: sqr_body_def)
    qed
  qed
  moreover have "VIMP_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx'')) = s(''Gx'' := s ''Gx'' * s ''Gx'')"
    by (rule ext) (simp add: enter_state_def is_global_def)
  ultimately show ?thesis by simp
qed

text \<open>
  @{const main_prog} terminates in @{term \<open>s(''Gx'' := 25)\<close>} for every
  initial store, regardless of @{term \<open>''Gx''\<close>}'s starting value.
\<close>
theorem main_prog_result:
  "pcompletes proc_pi main_prog s (s(''Gx'' := 25))"
proof -
  have step1: "pcompletes proc_pi (imp \<lbrakk> Gx := 4 \<rbrakk>) s (s(''Gx'' := 4))"
    using pcompletes_assign[where \<Pi> = proc_pi and x = "''Gx''" and a = "N 4" and s = s]
    by (simp add: pcompletes_def)
  have step2: "pcompletes proc_pi (imp \<lbrakk> inc() \<rbrakk>) (s(''Gx'' := 4)) (s(''Gx'' := 5))"
    using call_inc_result[where s = "s(''Gx'' := 4)"]
    by simp
  have step3: "pcompletes proc_pi (imp \<lbrakk> sqr() \<rbrakk>) (s(''Gx'' := 5)) (s(''Gx'' := 25))"
    using call_sqr_result[where s = "s(''Gx'' := 5)"]
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

abbreviation "main_cfg \<equiv> compile_prog proc_pi [''inc'', ''sqr''] main_cfg_name main_prog"

lemma main_cfg_full:
  "main_cfg =
     \<lparr> intra =
         {(FunctionEntry ''inc'', EA_Nop, Statement 0),
          (Statement 0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), Statement 1),
          (Statement 1, EA_Ret None ''inc'', FunctionResult ''inc''),
          (FunctionEntry ''sqr'', EA_Nop, Statement 2),
          (Statement 2, EA_Assign ''Gx'' (Times (V ''Gx'') (V ''Gx'')), Statement 3),
          (Statement 3, EA_Ret None ''sqr'', FunctionResult ''sqr''),
          (FunctionEntry ''main'', EA_Nop, Statement 4),
          (Statement 4, EA_Assign ''Gx'' (N 4), Statement 5),
          (Statement 7, EA_Ret None ''main'', FunctionResult ''main'')},
       calls =
         {(Statement 5, CallEdge None [] [], FunctionEntry ''inc'', Statement 6),
          (Statement 6, CallEdge None [] [], FunctionEntry ''sqr'', Statement 7)},
       cfg_entry = FunctionEntry ''main'' \<rparr>"
  by (simp add: main_cfg_name_def) eval

lemma main_cfg_entry: "cfg_entry main_cfg = FunctionEntry ''main''"
  by (simp add: main_cfg_full)
lemma main_cfg_exit: "cfg_exit main_cfg = FunctionResult ''main''"
  by (simp add: main_cfg_full cfg_exit_def)
lemma main_cfg_intra:
  "intra main_cfg =
     {(FunctionEntry ''inc'', EA_Nop, Statement 0),
      (Statement 0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), Statement 1),
      (Statement 1, EA_Ret None ''inc'', FunctionResult ''inc''),
      (FunctionEntry ''sqr'', EA_Nop, Statement 2),
      (Statement 2, EA_Assign ''Gx'' (Times (V ''Gx'') (V ''Gx'')), Statement 3),
      (Statement 3, EA_Ret None ''sqr'', FunctionResult ''sqr''),
      (FunctionEntry ''main'', EA_Nop, Statement 4),
      (Statement 4, EA_Assign ''Gx'' (N 4), Statement 5),
      (Statement 7, EA_Ret None ''main'', FunctionResult ''main'')}"
  by (simp add: main_cfg_full)
lemma main_cfg_calls:
  "calls main_cfg =
     {(Statement 5, CallEdge None [] [], FunctionEntry ''inc'', Statement 6),
      (Statement 6, CallEdge None [] [], FunctionEntry ''sqr'', Statement 7)}"
  by (simp add: main_cfg_full)

 


subsection \<open>Abstract interval post-fixpoint\<close>

text \<open>
  The initial abstract state maps every variable to the full interval.
\<close>
definition main_prog_s0 :: "ivl abs_state" where
  "main_prog_s0 = (\<lambda>_. Ivl MinInf PlusInf)"

text \<open>
  Abstract environment: each program point is assigned an interval state.
  The assignment propagates @{text "Gx = [4,4]"} after @{text "Gx := 4"},
  @{text "Gx = [5,5]"} after @{text "inc"} executes, and
  @{text "Gx = [25,25]"} after @{text "sqr"} executes.
  All local variables remain unconstrained throughout.

  Node groupings:
  @{text "4"} -- main body entry, before @{text "Gx := 4"};
  @{text "5"} -- after @{text "Gx := 4"}, which is also the call site to inc;
  @{text "0"} -- inc body entry (reached through the call edge from 5);
  @{text "1"} -- inc body exit, feeding @{term \<open>FunctionResult ''inc''\<close>};
  @{text "6"} -- continuation after inc, which is also the call site to sqr;
  @{text "2"}, @{text "3"} -- sqr body entry and exit;
  @{text "7"} -- continuation after sqr, feeding @{term \<open>FunctionResult ''main''\<close>}.
\<close>

definition main_prog_env :: "pp \<Rightarrow> ivl abs_state" where
  "main_prog_env v x =
     (if v \<in> {Statement 5, FunctionEntry ''inc'', Statement 0} \<and> x = ''Gx''
        then Ivl (Fin 4) (Fin 4)
      else if v \<in> {Statement 1, FunctionResult ''inc'', Statement 6,
                   FunctionEntry ''sqr'', Statement 2} \<and> x = ''Gx''
        then Ivl (Fin 5) (Fin 5)
      else if v \<in> {Statement 3, FunctionResult ''sqr'', Statement 7,
                   FunctionResult ''main''} \<and> x = ''Gx''
        then Ivl (Fin 25) (Fin 25)
      else Ivl MinInf PlusInf)"

lemma main_prog_postfix:
  "is_post_fixpoint main_cfg ivl_tf (\<squnion>) bot main_prog_s0 main_prog_env"
  unfolding is_post_fixpoint_def
proof (rule allI)
  fix v
  let ?I = "(\<lambda>(u, a). apply_tf ivl_tf a (main_prog_env u)) ` intra_predecessors main_cfg v"
  let ?E = "(\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> tf_enter ivl_tf fs as (main_prog_env c))
              ` entry_calls main_cfg v"
  let ?R = "(\<lambda>(c, dst, ex). tf_combine_collect_abs ivl_tf dst (main_prog_env c) (main_prog_env ex))
              ` return_calls main_cfg v"
  have fin: "finite (?I \<union> ?E \<union> ?R)"
    using finite_intra_predecessors[of main_cfg v] finite_entry_calls[of main_cfg v]
          finite_return_calls[of main_cfg v]
    by (simp add: main_cfg_intra main_cfg_calls)
  \<comment> \<open>one bounded \<open>auto\<close> per constraint source: a single sweep over all three blows up
     on the nested \<^const>\<open>main_prog_env\<close> conditionals\<close>
  have leI: "\<And>t. t \<in> ?I \<Longrightarrow> t \<le> main_prog_env v"
  proof -
    fix t assume "t \<in> ?I"
    then obtain u a where e: "(u, a, v) \<in> intra main_cfg"
      and t: "t = apply_tf ivl_tf a (main_prog_env u)"
      by (auto simp: intra_predecessors_def)
    from e[unfolded main_cfg_intra] show "t \<le> main_prog_env v"
      unfolding t
      by (elim insertE emptyE)
         (simp_all add: main_prog_env_def ivl_tf_def assign_ivl_def times_ivl_def
                        normalize_ivl_def less_eq_ivl_def le_fun_def)
  qed
  have leE: "\<And>t. t \<in> ?E \<Longrightarrow> t \<le> main_prog_env v"
    by (auto split: if_splits
             simp: entry_calls_def main_cfg_calls main_prog_env_def ivl_tf_def
                   enter_ivl_def enter_frame_ivl_def enter_D_def enter_frame_D_def
                   ivl_top_def bind_formals_abs_def less_eq_ivl_def le_fun_def
                   is_global_def)
  have leR: "\<And>t. t \<in> ?R \<Longrightarrow> t \<le> main_prog_env v"
    by (auto split: if_splits
             simp: return_calls_def main_cfg_calls main_prog_env_def
                   tf_combine_collect_abs_def ivl_tf_def combine_abs_def normalize_ivl_def
                   less_eq_ivl_def le_fun_def is_global_def)
  have le: "\<And>t. t \<in> ?I \<union> ?E \<union> ?R \<Longrightarrow> t \<le> main_prog_env v"
    using leI leE leR by blast
  show "rhs main_cfg ivl_tf (\<squnion>) bot main_prog_s0 main_prog_env v \<le> main_prog_env v"
  proof (cases "v = cfg_entry main_cfg")
    case True
    have s0: "main_prog_s0 \<le> main_prog_env v"
      using True by (simp add: main_cfg_entry main_prog_s0_def main_prog_env_def le_fun_def)
    have "abs_join_set (\<squnion>) bot (insert main_prog_s0 (?I \<union> ?E \<union> ?R)) \<le> main_prog_env v"
    proof (rule abs_join_set_le)
      show "finite (insert main_prog_s0 (?I \<union> ?E \<union> ?R))" using fin by simp
      show "\<And>s. s \<in> insert main_prog_s0 (?I \<union> ?E \<union> ?R) \<Longrightarrow> s \<le> main_prog_env v"
        using s0 le by blast
    qed
    thus ?thesis unfolding rhs_def Let_def using True by simp
  next
    case False
    have "abs_join_set (\<squnion>) bot (?I \<union> ?E \<union> ?R) \<le> main_prog_env v"
      by (rule abs_join_set_le) (use fin le in blast)+
    thus ?thesis unfolding rhs_def Let_def using False by simp
  qed
qed

lemma main_prog_gx_exit_ivl:
  "main_prog_env (cfg_exit main_cfg) ''Gx'' = Ivl (Fin 25) (Fin 25)"
  by (simp add: main_prog_env_def main_cfg_exit)


subsection \<open>Interval analysis soundness\<close>

text \<open>
  For any store that reaches the program exit in the collecting semantics and
  whose initial store is in the concretisation of @{const main_prog_s0},
  the value of @{term \<open>''Gx''\<close>} lies in @{term \<open>Ivl (Fin 25) (Fin 25)\<close>}.


  The proof applies the generic trace-native post-fixpoint theorem to the exhibited
  post-fixpoint @{thm [source] main_prog_postfix [no_vars]}.
\<close>

theorem main_prog_interval_analysis:
  assumes S_sound: "S \<le> \<lbrakk>main_prog_s0\<rbrakk>"
  assumes s: "s \<in> ltr_collect main_cfg S (cfg_exit main_cfg)"
  shows "s ''Gx'' \<in> gamma_ivl (Ivl (Fin 25) (Fin 25))"
proof -
  have fin_e: "finite (intra main_cfg)" by (simp add: main_cfg_intra)
  have fin_c: "finite (calls main_cfg)" by (simp add: main_cfg_calls)
  have le: "ltr_collect main_cfg S (cfg_exit main_cfg)
              \<le> \<lbrakk>main_prog_env (cfg_exit main_cfg)\<rbrakk>"
    using sound_transfer.unified_ltr_post_fixpoint_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c main_prog_postfix S_sound]
    by blast
  from s le have "s \<in> \<lbrakk>main_prog_env (cfg_exit main_cfg)\<rbrakk>" by blast
  then have "s ''Gx'' \<in> gamma (main_prog_env (cfg_exit main_cfg) ''Gx'')"
    unfolding gamma_state_def by blast
  then show ?thesis by (simp add: main_prog_env_def main_cfg_exit)
qed


subsection \<open>DOT output\<close>

text \<open>
  @{const raw_cfg_dot_lit} emits the procedural CFG through the canonical
  graph model and DOT backend.  Annotated interval DOT is not yet
  wired; the exhibited post-fixpoint gives @{thm [source] main_prog_gx_exit_ivl}
  at exit.
\<close>

ML_val \<open>
  writeln (@{code raw_cfg_dot_lit}
              @{code proc_pi} @{code main_procs} @{code main_cfg_name} @{code main_prog})
\<close>

end
