theory Example_IMP2_Coverage
  imports Voblint_CFG.CFG_Prune "Voblint_CFG.CFG_Collect_Unified"
    "Voblint_Analysis.Sign_Domain" "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_IMP2.IMP2_Notation" "Voblint_IMP2.IMP2_Bridge" Trace_IP_Analysis_Sound
begin

(* Suppress AFP/IMP2 Syntax names that shadow our IMP2_Syntax abbreviations. *)
no_notation Syntax.Assign (\<open>_ ::= _\<close> [1000, 61] 61)
hide_const (open) Syntax.N Syntax.V Syntax.Bc

(*
  Coverage witness: the analyzer yields a sound safety invariant on a
  *non-terminating* program, where AFP IMP2's terminating-run big-step (and
  hence its total-correctness VCG) has no final state to range over.

  Program:  x := 1; while (true) { x := x + 1 }

  Claim (carefully phrased -- NOT "the VCG cannot prove x > 0"):
    * There is no terminating run, so big_step relates no final state and a
      total-correctness goal is vacuous (loop_no_terminating_run).
    * The sign analyzer still proves x > 0 at the loop head over every reaching
      trace (loop_head_x_pos), via a post-fixpoint and trace_ip_analysis_sound.

  Only the sign domain is used in this witness (interval coverage lives in
  @{theory Voblint_Formalization.Example_Interval_Loop_Coverage}), so the
  property is x > 0 (SPos), not x >= 0.
*)

definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = \<lbrakk>
     x := 1;
     while (true) { x := x + 1 }
   \<rbrakk>"

(* -- No terminating run --------------------------------------------------- *)

(* while (true) never reaches a final state. *)
lemma while_true_no_bigstep:
  "Semantics.big_step \<pi> (cmd, s) t \<Longrightarrow> cmd = Syntax.While (Syntax.Bc True) c \<Longrightarrow> False"
proof (induction arbitrary: c rule: big_step_induct)
  case (WhileFalse b s')
  then show ?case by auto
next
  case (WhileTrue b s1 cm s2 s3)
  then show ?case by auto
qed auto

(* Hence the translated program has no terminating AFP IMP2 run, for any start
   state -- so a total-correctness big-step/VCG result is vacuous. *)
lemma loop_no_terminating_run:
  "\<not> Semantics.big_step (to_imp2_pi \<Pi>) (to_imp2_com loop_prog, s) t"
proof
  assume "Semantics.big_step (to_imp2_pi \<Pi>) (to_imp2_com loop_prog, s) t"
  then have "Semantics.big_step (to_imp2_pi \<Pi>)
     (Syntax.Seq (Syntax.AssignIdx ''x'' (Syntax.N 0) (Syntax.N 1))
        (Syntax.While (Syntax.Bc True)
           (Syntax.AssignIdx ''x'' (Syntax.N 0)
              (Syntax.Binop (+) (Syntax.Vidx ''x'' (Syntax.N 0)) (Syntax.N 1)))), s) t"
    by (simp add: loop_prog_def)
  then obtain s2 where
    "Semantics.big_step (to_imp2_pi \<Pi>)
       (Syntax.While (Syntax.Bc True)
          (Syntax.AssignIdx ''x'' (Syntax.N 0)
             (Syntax.Binop (+) (Syntax.Vidx ''x'' (Syntax.N 0)) (Syntax.N 1))), s2) t"
    by (auto elim: Semantics.SeqE)
  thus False using while_true_no_bigstep by blast
qed

(* -- The analyzer side: a sign post-fixpoint proving x > 0 ---------------- *)

abbreviation "loop_cfg \<equiv> compile_prog Map.empty [] loop_prog"

lemma loop_cfg_full:
  "loop_cfg = mk_cfg 0 5
     {(0, EA_Assign ''x'' (N 1), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Bc True), 3),
      (2, EA_AssumeNot (Bc True), 5),
      (3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), 4),
      (4, EA_Nop, 2)}
     {}"
  by (simp add: compile_eval_simps loop_prog_def; blast)

lemma loop_cfg_entry:   "cfg_entry loop_cfg = 0" by (simp add: loop_cfg_full)
lemma loop_cfg_exit:    "cfg_exit  loop_cfg = 5" by (simp add: loop_cfg_full)
lemma loop_cfg_combines: "combines loop_cfg = {}" by (simp add: loop_cfg_full)
lemma loop_cfg_edges:
  "edges loop_cfg =
     {(0, EA_Assign ''x'' (N 1), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Bc True), 3),
      (2, EA_AssumeNot (Bc True), 5),
      (3, EA_Assign ''x'' (Plus (V ''x'') (N 1)), 4),
      (4, EA_Nop, 2)}"
  by (simp add: loop_cfg_full)


(* The exhibited sign solution: x is positive everywhere inside the loop;
   the entry keeps x at STop (it must, since rhs(entry) = s0). *)
definition loop_s0 :: "sign abs_state" where
  "loop_s0 = (\<lambda>_. STop)"

definition loop_env :: "pp \<Rightarrow> sign abs_state" where
  "loop_env v = (if v \<in> {1,2,3,4,5} then (\<lambda>_. STop)(''x'' := SPos) else (\<lambda>_. STop))"

lemma loop_postfix:
  "is_post_fixpoint loop_cfg sign_tf (\<squnion>) bot loop_s0 loop_env"
  unfolding is_post_fixpoint_def
proof (rule allI)
  fix v
  show "rhs loop_cfg sign_tf (\<squnion>) bot loop_s0 loop_env v \<le> loop_env v"
    apply (simp only: rhs_def Let_def loop_cfg_entry loop_cfg_edges loop_cfg_combines)
    apply (rule abs_join_set_le)
    apply (rule finite_subset[where B=
            "insert loop_s0 ((\<lambda>(u,a). apply_tf sign_tf a (loop_env u)) `
               {(0, EA_Assign ''x'' (N 1)),
                (1, EA_Nop),
                (2, EA_Assume (Bc True)),
                (2, EA_AssumeNot (Bc True)),
                (3, EA_Assign ''x'' (Plus (V ''x'') (N 1))),
                (4, EA_Nop)})"])
    by (auto split: if_splits
               simp: loop_env_def loop_s0_def sign_tf_def assign_sign_def
                     less_eq_sign_def le_fun_def)

qed

(* -- Soundness: x > 0 at the loop head ------------------------------------- *)

(* The loop head is the assume node where we check Bc True. *)
abbreviation "loop_head \<equiv> 2"

lemma loop_head_x_pos:
  assumes S_sound: "S \<subseteq> sign_domain.gamma_state loop_s0"
  assumes tr: "tr \<in> cfg_collect_trace loop_cfg S loop_head"
  shows "(last tr) ''x'' > 0"
proof -
  have fin_e: "finite (edges loop_cfg)"
    by (simp add: loop_cfg_edges)
  have fin_c: "finite (combines loop_cfg)"
    by (simp add: loop_cfg_combines)
  have s0_conv: "S \<subseteq> sound_domain.gamma_state gamma_sign loop_s0"
    using S_sound
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have "(last tr) ''x'' \<in> gamma_sign (loop_env loop_head ''x'')"
    by (rule Trace_IP_Analysis_Sound.sound_transfer.reaching_global_read_sound
          [OF sign_sound_tf.sound_transfer_axioms fin_e fin_c loop_postfix s0_conv tr])
  then show ?thesis
    by (auto simp: loop_env_def gamma_sign.simps)
qed

end
