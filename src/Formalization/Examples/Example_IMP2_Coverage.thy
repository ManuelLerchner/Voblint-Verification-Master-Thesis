theory Example_IMP2_Coverage
  imports Goblint_CFG.CFG_Prune "Goblint_CFG.CFG_Collect_Unified"
    "Goblint_Analysis.Sign_Domain" "Goblint_Analysis.Constraint_System_Sound"
    "Goblint_IMP2.IMP2_Bridge" Trace_IP_Analysis_Sound
begin

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

  Only the sign domain lives in this repo (interval/ln was extracted), so the
  property is x > 0 (SPos), not x >= 0.
*)

definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog =
     IMP2_Proc.com.Seq
       (IMP2_Proc.com.Assign ''x'' (BaseN (AExp.N 1)))
       (IMP2_Proc.com.While (BaseB (BExp.Bc True))
          (IMP2_Proc.com.Assign ''x''
             (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1)))))"

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
  "\<not> Semantics.big_step (to_imp2_pi pi) (to_imp2_com loop_prog, s) t"
proof
  assume "Semantics.big_step (to_imp2_pi pi) (to_imp2_com loop_prog, s) t"
  then have "Semantics.big_step (to_imp2_pi pi)
     (Syntax.Seq (Syntax.AssignIdx ''x'' (Syntax.N 0) (Syntax.N 1))
        (Syntax.While (Syntax.Bc True)
           (Syntax.AssignIdx ''x'' (Syntax.N 0)
              (Syntax.Binop (+) (Syntax.Vidx ''x'' (Syntax.N 0)) (Syntax.N 1)))), s) t"
    by (simp add: loop_prog_def)
  then obtain s2 where
    "Semantics.big_step (to_imp2_pi pi)
       (Syntax.While (Syntax.Bc True)
          (Syntax.AssignIdx ''x'' (Syntax.N 0)
             (Syntax.Binop (+) (Syntax.Vidx ''x'' (Syntax.N 0)) (Syntax.N 1))), s2) t"
    by (auto elim: Semantics.SeqE)
  thus False using while_true_no_bigstep by blast
qed

(* -- The analyzer side: a sign post-fixpoint proving x > 0 ---------------- *)

abbreviation "loop_cfg \<equiv> compile_prog Map.empty [] loop_prog"

lemma loop_cfg_entry: "cfg_entry loop_cfg = 0"
  by (simp add: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def)

lemma loop_cfg_combines: "combines loop_cfg = {}"
  by (simp add: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def)

lemma loop_cfg_edges:
  "edges loop_cfg =
     {(0, EA_Assign ''x'' (BaseN (AExp.N 1)), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (BaseB (BExp.Bc True)), 3),
      (2, EA_AssumeNot (BaseB (BExp.Bc True)), 5),
      (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), 4),
      (4, EA_Nop, 2)}"
  by (auto simp: compile_prog_def compile_prog_with_regions_def loop_prog_def Let_def
             eval_nat_numeral)

(* LUB characterization: the abstract join is below X iff every member is. *)
lemma abs_join_set_le:
  fixes X :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes fin: "finite S" and le: "\<And>s. s \<in> S \<Longrightarrow> s \<le> X"
  shows "abs_join_set (\<squnion>) bot S \<le> X"
proof -
  have "abs_join_set (\<squnion>) bot S = Sup_fin (insert bot S)"
    unfolding abs_join_set_def using fin by (simp add: Sup_fin.eq_fold)
  also have "\<dots> \<le> X" using fin le by (intro Sup_fin.boundedI) auto
  finally show ?thesis .
qed

(* The exhibited sign solution: x is positive everywhere inside the loop;
   the entry keeps x at STop (it must, since rhs(entry) = s0). *)
definition loop_s0 :: "sign abs_state" where
  "loop_s0 = (\<lambda>_. STop)"

definition loop_env :: "pp \<Rightarrow> sign abs_state" where
  "loop_env v = (if v \<in> {1,2,3,4,5} then (\<lambda>_. STop)(''x'' := SPos) else (\<lambda>_. STop))"

lemma loop_postfix:
  "is_post_fixpoint_ip loop_cfg sign_tf (\<squnion>) bot loop_s0 loop_env"
  unfolding is_post_fixpoint_ip_def
proof (rule allI)
  fix v
  show "rhs_ip loop_cfg sign_tf (\<squnion>) bot loop_s0 loop_env v \<le> loop_env v"
    apply (simp only: rhs_ip_eq_rhs_if_no_combines[OF loop_cfg_combines]
                      rhs_def Let_def loop_cfg_entry loop_cfg_edges)
    apply (rule abs_join_set_le)
    apply (rule finite_subset[where B=
            "insert loop_s0 ((\<lambda>(u,a). apply_tf sign_tf a (loop_env u)) `
               {(0, EA_Assign ''x'' (BaseN (AExp.N 1))),
                (1, EA_Nop),
                (2, EA_Assume (BaseB (BExp.Bc True))),
                (2, EA_AssumeNot (BaseB (BExp.Bc True))),
                (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1)))),
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
  assumes tr: "tr \<in> cfg_collect_trace_ip loop_cfg S loop_head"
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
