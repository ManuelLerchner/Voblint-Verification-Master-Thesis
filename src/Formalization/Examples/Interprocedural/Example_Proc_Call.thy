section \<open>Example: Procedure Calls --- Increment and Square\<close>

theory Example_Proc_Call
  imports
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_IMP2.IMP2_Bridge"
    "Voblint_CFG.CFG_Prune"
    "Voblint_CFG.CFG_Collect"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Constraint_System_Sound"
    Trace_Analysis_Sound
    "Voblint_Analysis.Analysis_GraphViz"
begin

no_notation Syntax.Assign (\<open>_ ::= _\<close> [1000, 61] 61)
hide_const (open) Syntax.N Syntax.V Syntax.Assign Semantics.aval Semantics.bval
hide_const phase.N

text \<open>
  Two parameterless procedures communicate through the global variable
  @{term \<open>''Gx''\<close>}.  Variable names starting with \<open>G\<close> are global:
  they survive call-frame restore while locals are reset to zero.

  \<^item> \<open>inc\<close>: adds 1 to \<open>Gx\<close>.
  \<^item> \<open>sqr\<close>: replaces \<open>Gx\<close> with its square.

  Main program: \<open>Gx := 4; call inc; call sqr\<close>
  terminates with \<open>Gx = 25\<close> since \<open>(4 + 1)^2 = 25\<close>.
\<close>

definition inc_body :: "IMP2_Proc.com" where
  "inc_body = \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition sqr_body :: "IMP2_Proc.com" where
  "sqr_body = \<lbrakk> Gx := Gx * Gx \<rbrakk>"

definition proc_pi :: proc_table where
  "proc_pi = (\<lambda>_. None)(''inc'' := Some inc_body, ''sqr'' := Some sqr_body)"

definition main_prog :: "IMP2_Proc.com" where
  "main_prog = \<lbrakk>
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
  "pcompletes proc_pi (Call ''inc'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  have run: "pcompletes proc_pi (Call ''inc'') s
                (IMP2_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' + 1)))"
  proof (rule pcompletes_Call[where c = inc_body])
    show "proc_pi ''inc'' = Some inc_body"
      by (simp add: proc_pi_def)
    show "pcompletes proc_pi inc_body (enter_state s)
             ((enter_state s)(''Gx'' := s ''Gx'' + 1))"
    proof -
      have "pcompletes proc_pi (Assign ''Gx'' (Plus (V ''Gx'') (N 1)))
               (enter_state s)
               ((enter_state s)(''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state s)))"
        by (rule pcompletes_assign)
      moreover have "aval (Plus (V ''Gx'') (N 1)) (enter_state s) = s ''Gx'' + 1"
        by (simp add: enter_state_def is_global_def)
      ultimately show ?thesis by (simp add: inc_body_def)
    qed
  qed
  moreover have "IMP2_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' + 1)) = s(''Gx'' := s ''Gx'' + 1)"
    by (rule ext) (simp add: enter_state_def is_global_def)
  ultimately show ?thesis by simp
qed

lemma call_sqr_result:
  "pcompletes proc_pi (Call ''sqr'') s (s(''Gx'' := s ''Gx'' * s ''Gx''))"
proof -
  have run: "pcompletes proc_pi (Call ''sqr'') s
                (IMP2_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx'')))"
  proof (rule pcompletes_Call[where c = sqr_body])
    show "proc_pi ''sqr'' = Some sqr_body"
      by (simp add: proc_pi_def)
    show "pcompletes proc_pi sqr_body (enter_state s)
             ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx''))"
    proof -
      have "pcompletes proc_pi (Assign ''Gx'' (Times (V ''Gx'') (V ''Gx'')))
               (enter_state s)
               ((enter_state s)(''Gx'' := aval (Times (V ''Gx'') (V ''Gx'')) (enter_state s)))"
        by (rule pcompletes_assign)
      moreover have "aval (Times (V ''Gx'') (V ''Gx'')) (enter_state s) = s ''Gx'' * s ''Gx''"
        by (simp add: enter_state_def is_global_def)
      ultimately show ?thesis by (simp add: sqr_body_def)
    qed
  qed
  moreover have "IMP2_Globals.combine_states s ((enter_state s)(''Gx'' := s ''Gx'' * s ''Gx'')) = s(''Gx'' := s ''Gx'' * s ''Gx'')"
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
  have step1: "pcompletes proc_pi (Assign ''Gx'' (N 4)) s (s(''Gx'' := 4))"
    using pcompletes_assign[where \<Pi> = proc_pi and x = "''Gx''" and a = "N 4" and s = s]
    by (simp add: pcompletes_def)
  have step2: "pcompletes proc_pi (Call ''inc'') (s(''Gx'' := 4)) (s(''Gx'' := 5))"
    using call_inc_result[where s = "s(''Gx'' := 4)"]
    by simp
  have step3: "pcompletes proc_pi (Call ''sqr'') (s(''Gx'' := 5)) (s(''Gx'' := 25))"
    using call_sqr_result[where s = "s(''Gx'' := 5)"]
    by simp
  show ?thesis
    unfolding main_prog_def
    by (rule pcompletes_Seq[OF pcompletes_Seq[OF step1 step2] step3])
qed

subsection \<open>Interprocedural CFG\<close>

text \<open>
  Compile @{const main_prog} together with its two procedure bodies.
  @{const compile_prog} first lays out @{const inc_body} at nodes 0--1
  and @{const sqr_body} at nodes 2--3, then compiles the main body
  starting at node 4.  Each call site owns a distinct return node, so the
  two combine triples are @{text "(6, 1, 7)"} (return from @{text inc}) and
  @{text "(8, 3, 9)"} (return from @{text sqr}).
\<close>

abbreviation "main_cfg \<equiv> compile_prog proc_pi [''inc'', ''sqr''] main_prog"

lemma main_cfg_full:
  "main_cfg = mk_cfg 4 9
     {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
      (2, EA_Assign ''Gx'' (Times (V ''Gx'') (V ''Gx'')), 3),
      (4, EA_Assign ''Gx'' (N 4), 5),
      (5, EA_Nop, 6),
      (6, EA_Enter, 0),
      (7, EA_Nop, 8),
      (8, EA_Enter, 2)}
     {(6, 1, 7), (8, 3, 9)}"
  by (simp add: proc_pi_def inc_body_def sqr_body_def main_prog_def
      compile_prog_def compile_prog_with_regions_def compile_procs_list_def Let_def eval_nat_numeral;
      blast)

lemma main_cfg_entry:   "cfg_entry main_cfg = 4"                    by (simp add: main_cfg_full)
lemma main_cfg_exit:    "cfg_exit  main_cfg = 9"                    by (simp add: main_cfg_full)
lemma main_cfg_edges:
  "edges main_cfg =
     {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
      (2, EA_Assign ''Gx'' (Times (V ''Gx'') (V ''Gx'')), 3),
      (4, EA_Assign ''Gx'' (N 4), 5),
      (5, EA_Nop, 6),
      (6, EA_Enter, 0),
      (7, EA_Nop, 8),
      (8, EA_Enter, 2)}"
  by (simp add: main_cfg_full)
lemma main_cfg_combines: "combines main_cfg = {(6, 1, 7), (8, 3, 9)}"
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
  @{text "0"} -- inc body entry (after EA_Enter from node 6);
  @{text "5"} -- after @{text "Gx := 4"};
  @{text "6"} -- call site to inc (after EA_Nop from node 5).
  @{text "1"} -- inc body exit;
  @{text "2"} -- sqr body entry;
  @{text "7"} -- return from inc;
  @{text "8"} -- call site to sqr;
  @{text "3"} -- sqr body exit;
  @{text "9"} -- program exit (combine from sqr return).
\<close>

definition main_prog_env :: "pp \<Rightarrow> ivl abs_state" where
  "main_prog_env v x =
     (if (v = 0 \<or> v = 5 \<or> v = 6) \<and> x = ''Gx'' then Ivl (Fin 4) (Fin 4)
      else if (v = 1 \<or> v = 2 \<or> v = 7 \<or> v = 8) \<and> x = ''Gx'' then Ivl (Fin 5) (Fin 5)
      else if (v = 3 \<or> v = 9) \<and> x = ''Gx'' then Ivl (Fin 25) (Fin 25)
      else Ivl MinInf PlusInf)"

lemma main_prog_postfix:
  "is_post_fixpoint main_cfg ivl_tf (\<squnion>) bot main_prog_s0 main_prog_env"
  unfolding is_post_fixpoint_def
proof (rule allI)
  fix v
  show "rhs main_cfg ivl_tf (\<squnion>) bot main_prog_s0 main_prog_env v
          \<le> main_prog_env v"
    apply (simp only: rhs_def Let_def main_cfg_entry main_cfg_edges main_cfg_combines)
    apply (rule abs_join_set_le)
     apply (rule finite_subset[where B =
             "insert main_prog_s0
               ((\<lambda>(u, a). apply_tf ivl_tf a (main_prog_env u)) `
                  {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1))),
                   (2, EA_Assign ''Gx'' (Times (V ''Gx'') (V ''Gx''))),
                   (4, EA_Assign ''Gx'' (N 4)),
                   (5, EA_Nop), (6, EA_Enter), (7, EA_Nop), (8, EA_Enter)})
             \<union>
             ((\<lambda>(c, e). \<langle>main_prog_env c|main_prog_env e\<rangle>) `
                  {(6, 1), (8, 3)})"])
    by (auto split: if_splits
              simp: main_prog_env_def main_prog_s0_def ivl_tf_def assign_ivl_def
                    times_ivl_def less_eq_ivl_def le_fun_def
                    enter_ivl_def combine_abs_def is_global_def)
qed

lemma main_prog_gx_exit_ivl:
  "main_prog_env (cfg_exit main_cfg) ''Gx'' = Ivl (Fin 25) (Fin 25)"
  by (simp add: main_prog_env_def main_cfg_exit)


subsection \<open>Interval analysis soundness\<close>

text \<open>
  For any interprocedural trace that reaches the program exit and whose
  initial store is in the concretisation of @{const main_prog_s0},
  the value of @{term \<open>''Gx''\<close>} at the end of the trace lies in
  @{term \<open>Ivl (Fin 25) (Fin 25)\<close>}.

  The proof applies the generic interprocedural post-fixpoint soundness
  theorem (@{thm [source] Trace_Analysis_Sound.sound_transfer.reaching_global_read_sound})
  to the exhibited post-fixpoint @{thm [source] main_prog_postfix [no_vars]}.
\<close>

theorem main_prog_interval_analysis:
  assumes S_sound: "S \<le> \<lbrakk>main_prog_s0\<rbrakk>"
  assumes tr: "tr \<in> cfg_collect_trace main_cfg S (cfg_exit main_cfg)"
  shows "(last tr) ''Gx'' \<in> gamma_ivl (Ivl (Fin 25) (Fin 25))"
proof -
  have fin_e: "finite (edges main_cfg)" by (simp add: main_cfg_edges)
  have fin_c: "finite (combines main_cfg)" by (simp add: main_cfg_combines)
  have s0_conv: "S \<le> \<lbrakk>main_prog_s0\<rbrakk>"
    using S_sound by simp
  have "(last tr) ''Gx'' \<in> gamma (main_prog_env (cfg_exit main_cfg) ''Gx'')"
    by (rule Trace_Analysis_Sound.sound_transfer.reaching_global_read_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c main_prog_postfix s0_conv tr])
  then show ?thesis by (simp add: main_prog_env_def main_cfg_exit)
qed


subsection \<open>DOT output\<close>

text \<open>
  @{const plain_dot_of_prog_lit} emits the procedural CFG with procedure
  clusters and entry/exit highlighting.  Annotated interval DOT is not yet
  wired; the exhibited post-fixpoint gives @{thm [source] main_prog_gx_exit_ivl}
  at exit.
\<close>

ML_val \<open>
  writeln (@{code plain_dot_of_prog_lit}
             @{code proc_pi} @{code main_procs} @{code main_prog})
\<close>

end

