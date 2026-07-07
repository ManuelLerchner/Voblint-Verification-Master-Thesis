theory Example_Trace_Digest_ReachingCompat
  imports "Voblint_CFG.CFG_Collect_Trace" "Voblint_Analysis.Sign_Domain"
          "Voblint_IMP2.IMP2_Notation"
begin

(*
  Reader-side digest filtering (reaching_compat): two writes to global Gg under
  different lock contexts (ghost local ''ls''), followed by an actual reader
  statement x := Gg.

  Flat collecting at the read point joins both reader outcomes, so x is forced
  to STop in the sign domain.  Filtering the reaching traces by the reader's
  lockset digest keeps only the L-compatible write history, so x is SPos.
*)

section \<open>Compiled program\<close>

definition reaching_program :: imp_prog where
  "reaching_program = \<lbrakk>
     int Gg;
     void main() {
       if (flag < 0) { ls := 1; Gg := 1 } else { ls := 2; Gg := -1 };
       x := Gg
     }
   \<rbrakk>"

definition reaching_pi :: proc_table where
  "reaching_pi = prog_table reaching_program"

lemma reaching_program_parts:
  shows "prog_procs reaching_program = []"
    and "prog_table reaching_program = (\<lambda>_. None)"
    and "prog_main reaching_program =
        Seq
          (If (Less (V ''flag'') (N 0))
            (Seq (Assign ''ls'' (N 1)) (Assign ''Gg'' (N 1)))
            (Seq (Assign ''ls'' (N 2)) (Assign ''Gg'' (N (-1)))))
          (Assign ''x'' (V ''Gg''))"
  by (simp_all add: reaching_program_def)

definition reaching_g :: cfg where
  "reaching_g = compile_prog (prog_table reaching_program)
                         (prog_procs reaching_program) (prog_main reaching_program)"

lemma reaching_g_eq_compile:
  "reaching_g = compile_prog reaching_pi [] (prog_main reaching_program)"
  by (simp add: reaching_g_def reaching_pi_def reaching_program_parts)

lemma reaching_g_full:
  "reaching_g = mk_cfg 0 11
     {(0, EA_Assume (Less (V ''flag'') (N 0)), 1),
      (0, EA_AssumeNot (Less (V ''flag'') (N 0)), 5),
      (1, EA_Assign ''ls'' (N 1), 2),
      (2, EA_Nop, 3),
      (3, EA_Assign ''Gg'' (N 1), 4),
      (4, EA_Nop, 9),
      (5, EA_Assign ''ls'' (N 2), 6),
      (6, EA_Nop, 7),
      (7, EA_Assign ''Gg'' (N (-1)), 8),
      (8, EA_Nop, 9),
      (9, EA_Nop, 10),
      (10, EA_Assign ''x'' (V ''Gg''), 11)}
     {}"
  by (simp add: reaching_g_def reaching_program_def compile_eval_simps Let_def; auto)

lemma reaching_g_structure:
  shows "cfg_entry reaching_g = 0"
    and "cfg_exit reaching_g = 11"
    and "combines reaching_g = {}"
  by (simp_all add: reaching_g_full)

definition read_pp :: pp where "read_pp = cfg_exit reaching_g"

lemma read_pp_11[simp]: "read_pp = 11"
  by (simp add: read_pp_def reaching_g_full)

section \<open>Stores and traces\<close>

definition s0 :: store where "s0 = (\<lambda>_. 0)"

definition s_L :: store where "s_L = s0(''flag'' := - 1)"
definition s_M :: store where "s_M = s0"

definition s_ls_L :: store where "s_ls_L = s_L(''ls'' := 1)"
definition s_ls_M :: store where "s_ls_M = s_M(''ls'' := 2)"

definition s_wr_L :: store where "s_wr_L = s_ls_L(''Gg'' := 1)"
definition s_wr_M :: store where "s_wr_M = s_ls_M(''Gg'' := - 1)"

definition s_read_L :: store where "s_read_L = s_wr_L(''x'' := 1)"
definition s_read_M :: store where "s_read_M = s_wr_M(''x'' := - 1)"

definition S0 :: "store set" where "S0 = {s_L, s_M}"

lemma s_L_flag[simp]: "s_L ''flag'' = - 1" by (simp add: s_L_def s0_def)
lemma s_M_flag[simp]: "s_M ''flag'' = 0" by (simp add: s_M_def s0_def)
lemma s_wr_L_g[simp]: "s_wr_L ''Gg'' = 1" by (simp add: s_wr_L_def)
lemma s_wr_M_g[simp]: "s_wr_M ''Gg'' = - 1" by (simp add: s_wr_M_def)
lemma s_read_L_x[simp]: "s_read_L ''x'' = 1" by (simp add: s_read_L_def)
lemma s_read_M_x[simp]: "s_read_M ''x'' = - 1" by (simp add: s_read_M_def)
lemma s_read_L_ls[simp]: "s_read_L ''ls'' = 1" by (simp add: s_read_L_def s_wr_L_def s_ls_L_def)
lemma s_read_M_ls[simp]: "s_read_M ''ls'' = 2" by (simp add: s_read_M_def s_wr_M_def s_ls_M_def)

lemma bval_flag_lt_L[simp]: "bval (Less (V ''flag'') (N 0)) s_L"
  by (simp add: s_L_def s0_def)

lemma bval_flag_lt_M[simp]: "\<not> bval (Less (V ''flag'') (N 0)) s_M"
  by (simp add: s_M_def s0_def)

definition tau_L :: CFG_Collect_Trace.trace where
  "tau_L = [s_L, s_L, s_ls_L, s_ls_L, s_wr_L, s_wr_L, s_wr_L, s_read_L]"

definition tau_M :: CFG_Collect_Trace.trace where
  "tau_M = [s_M, s_M, s_ls_M, s_ls_M, s_wr_M, s_wr_M, s_wr_M, s_read_M]"

lemma tau_L_path: "trace_edges reaching_g 0 tau_L read_pp"
proof -
  have p0: "trace_edges reaching_g 0 [s_L] 0"
    by (rule trace_edges.single)
  have p1: "trace_edges reaching_g 0 [s_L, s_L] 1"
    using trace_edges.step[OF p0, of "EA_Assume (Less (V ''flag'') (N 0))" 1 s_L]
    by (simp add: reaching_g_full edge_step.simps)
  have p2: "trace_edges reaching_g 0 [s_L, s_L, s_ls_L] 2"
    using trace_edges.step[OF p1, of "EA_Assign ''ls'' (N 1)" 2 s_ls_L]
    by (simp add: reaching_g_full edge_step.simps s_ls_L_def)
  have p3: "trace_edges reaching_g 0 [s_L, s_L, s_ls_L, s_ls_L] 3"
    using trace_edges.step[OF p2, of EA_Nop 3 s_ls_L]
    by (simp add: reaching_g_full edge_step.simps)
  have p4: "trace_edges reaching_g 0 [s_L, s_L, s_ls_L, s_ls_L, s_wr_L] 4"
    using trace_edges.step[OF p3, of "EA_Assign ''Gg'' (N 1)" 4 s_wr_L]
    by (simp add: reaching_g_full edge_step.simps s_wr_L_def)
  have p5: "trace_edges reaching_g 0 [s_L, s_L, s_ls_L, s_ls_L, s_wr_L, s_wr_L] 9"
    using trace_edges.step[OF p4, of EA_Nop 9 s_wr_L]
    by (simp add: reaching_g_full edge_step.simps)
  have p6: "trace_edges reaching_g 0 [s_L, s_L, s_ls_L, s_ls_L, s_wr_L, s_wr_L, s_wr_L] 10"
    using trace_edges.step[OF p5, of EA_Nop 10 s_wr_L]
    by (simp add: reaching_g_full edge_step.simps)
  have p7: "trace_edges reaching_g 0 tau_L 11"
    unfolding tau_L_def
    using trace_edges.step[OF p6, of "EA_Assign ''x'' (V ''Gg'')" 11 s_read_L]
    by (simp add: reaching_g_full edge_step.simps s_read_L_def)
  show ?thesis using p7 by simp
qed

lemma tau_M_path: "trace_edges reaching_g 0 tau_M read_pp"
proof -
  have p0: "trace_edges reaching_g 0 [s_M] 0"
    by (rule trace_edges.single)
  have p1: "trace_edges reaching_g 0 [s_M, s_M] 5"
    using trace_edges.step[OF p0, of "EA_AssumeNot (Less (V ''flag'') (N 0))" 5 s_M]
    by (simp add: reaching_g_full edge_step.simps)
  have p2: "trace_edges reaching_g 0 [s_M, s_M, s_ls_M] 6"
    using trace_edges.step[OF p1, of "EA_Assign ''ls'' (N 2)" 6 s_ls_M]
    by (simp add: reaching_g_full edge_step.simps s_ls_M_def)
  have p3: "trace_edges reaching_g 0 [s_M, s_M, s_ls_M, s_ls_M] 7"
    using trace_edges.step[OF p2, of EA_Nop 7 s_ls_M]
    by (simp add: reaching_g_full edge_step.simps)
  have p4: "trace_edges reaching_g 0 [s_M, s_M, s_ls_M, s_ls_M, s_wr_M] 8"
    using trace_edges.step[OF p3, of "EA_Assign ''Gg'' (N (-1))" 8 s_wr_M]
    by (simp add: reaching_g_full edge_step.simps s_wr_M_def)
  have p5: "trace_edges reaching_g 0 [s_M, s_M, s_ls_M, s_ls_M, s_wr_M, s_wr_M] 9"
    using trace_edges.step[OF p4, of EA_Nop 9 s_wr_M]
    by (simp add: reaching_g_full edge_step.simps)
  have p6: "trace_edges reaching_g 0 [s_M, s_M, s_ls_M, s_ls_M, s_wr_M, s_wr_M, s_wr_M] 10"
    using trace_edges.step[OF p5, of EA_Nop 10 s_wr_M]
    by (simp add: reaching_g_full edge_step.simps)
  have p7: "trace_edges reaching_g 0 tau_M 11"
    unfolding tau_M_def
    using trace_edges.step[OF p6, of "EA_Assign ''x'' (V ''Gg'')" 11 s_read_M]
    by (simp add: reaching_g_full edge_step.simps s_read_M_def)
  show ?thesis using p7 by simp
qed

lemma tau_L_witness: "trace_witness reaching_g S0 read_pp tau_L"
  using tau_L_path
  by (rule trace_witness_edges) (simp_all add: reaching_g_structure tau_L_def S0_def)

lemma tau_M_witness: "trace_witness reaching_g S0 read_pp tau_M"
  using tau_M_path
  by (rule trace_witness_edges) (simp_all add: reaching_g_structure tau_M_def S0_def)

lemma reaching_edges_cases:
  assumes "(u, a, v) \<in> edges reaching_g"
  obtains
    "u = 0" "a = EA_Assume (Less (V ''flag'') (N 0))" "v = 1"
  | "u = 0" "a = EA_AssumeNot (Less (V ''flag'') (N 0))" "v = 5"
  | "u = 1" "a = EA_Assign ''ls'' (N 1)" "v = 2"
  | "u = 2" "a = EA_Nop" "v = 3"
  | "u = 3" "a = EA_Assign ''Gg'' (N 1)" "v = 4"
  | "u = 4" "a = EA_Nop" "v = 9"
  | "u = 5" "a = EA_Assign ''ls'' (N 2)" "v = 6"
  | "u = 6" "a = EA_Nop" "v = 7"
  | "u = 7" "a = EA_Assign ''Gg'' (N (-1))" "v = 8"
  | "u = 8" "a = EA_Nop" "v = 9"
  | "u = 9" "a = EA_Nop" "v = 10"
  | "u = 10" "a = EA_Assign ''x'' (V ''Gg'')" "v = 11"
  using assms unfolding reaching_g_full by force

lemma trace_witness_reaching_inv:
  assumes "trace_witness reaching_g S0 v tr"
  shows
    "(v = 0 \<longrightarrow> tr = [s_L] \<or> tr = [s_M]) \<and>
     (v = 1 \<longrightarrow> tr = [s_L, s_L]) \<and>
     (v = 2 \<longrightarrow> tr = [s_L, s_L, s_ls_L]) \<and>
     (v = 3 \<longrightarrow> tr = [s_L, s_L, s_ls_L, s_ls_L]) \<and>
     (v = 4 \<longrightarrow> tr = [s_L, s_L, s_ls_L, s_ls_L, s_wr_L]) \<and>
     (v = 5 \<longrightarrow> tr = [s_M, s_M]) \<and>
     (v = 6 \<longrightarrow> tr = [s_M, s_M, s_ls_M]) \<and>
     (v = 7 \<longrightarrow> tr = [s_M, s_M, s_ls_M, s_ls_M]) \<and>
     (v = 8 \<longrightarrow> tr = [s_M, s_M, s_ls_M, s_ls_M, s_wr_M]) \<and>
     (v = 9 \<longrightarrow> tr = [s_L, s_L, s_ls_L, s_ls_L, s_wr_L, s_wr_L] \<or>
                       tr = [s_M, s_M, s_ls_M, s_ls_M, s_wr_M, s_wr_M]) \<and>
     (v = 10 \<longrightarrow> tr = [s_L, s_L, s_ls_L, s_ls_L, s_wr_L, s_wr_L, s_wr_L] \<or>
                        tr = [s_M, s_M, s_ls_M, s_ls_M, s_wr_M, s_wr_M, s_wr_M]) \<and>
     (v = 11 \<longrightarrow> tr = tau_L \<or> tr = tau_M)"
  using assms
proof (induction rule: trace_witness.induct)
  case (entry v s)
  then show ?case by (auto simp: reaching_g_full S0_def)
next
  case (proc_entry v s)
  then show ?case by (auto simp: reaching_g_full)
next
  case (edge u a v tr s')
  from \<open>(u, a, v) \<in> edges reaching_g\<close> show ?case
    apply (cases rule: reaching_edges_cases)
    using edge.IH edge.hyps s_ls_L_def s_wr_L_def s_ls_M_def s_wr_M_def
          s_read_L_def s_read_M_def tau_L_def tau_M_def
    by auto
next
  case (combine c ex v tau rho)
  then show ?case by (auto simp: reaching_g_full)
qed

lemma trace_witness_read_inv:
  assumes w: "trace_witness reaching_g S0 read_pp tr"
  shows "tr = tau_L \<or> tr = tau_M"
  using w trace_witness_reaching_inv unfolding read_pp_11 by blast

lemma read_traces:
  "cfg_collect_trace reaching_g S0 read_pp = {tau_L, tau_M}"
proof
  show "{tau_L, tau_M} \<subseteq> cfg_collect_trace reaching_g S0 read_pp"
    unfolding cfg_collect_trace_def using tau_L_witness tau_M_witness by auto
next
  show "cfg_collect_trace reaching_g S0 read_pp \<subseteq> {tau_L, tau_M}"
    unfolding cfg_collect_trace_def using trace_witness_read_inv by auto
qed

section \<open>Digest: reader lockset\<close>

definition dg_ls where
  "dg_ls (tr::store list) = (last tr) ''ls''"

lemma dg_ls_tau[simp]:
  "dg_ls tau_L = 1" "dg_ls tau_M = 2"
  by (simp_all add: dg_ls_def tau_L_def tau_M_def)

lemma alpha_last_empty[simp]: "alpha_last {} = {}" unfolding alpha_last_def by simp
lemma alpha_last_single: "alpha_last {t} = {last t}" unfolding alpha_last_def by auto

lemma reaching_compat_read_L:
  "reaching_compat dg_ls (=) 1 reaching_g S0 read_pp = {tau_L}"
  unfolding reaching_compat_def read_traces by auto

lemma reaching_compat_read_M:
  "reaching_compat dg_ls (=) 2 reaching_g S0 read_pp = {tau_M}"
  unfolding reaching_compat_def read_traces by auto

lemma alpha_last_read_flat:
  "alpha_last (cfg_collect_trace reaching_g S0 read_pp) = {s_read_L, s_read_M}"
  unfolding alpha_last_def read_traces by (simp add: tau_L_def tau_M_def)

lemma alpha_last_read_L:
  "alpha_last (reaching_compat dg_ls (=) 1 reaching_g S0 read_pp) = {s_read_L}"
  unfolding alpha_last_def reaching_compat_read_L by (simp add: tau_L_def)

lemma alpha_last_read_subset_collect:
  "alpha_last (reaching_compat dg_ls (=) 1 reaching_g S0 read_pp)
   \<subseteq> cfg_collect reaching_g S0 read_pp"
  by (rule alpha_last_reaching_compat_le)

section \<open>Sign domain: flat read forces top; filtered read is precise\<close>

definition envd where
  "envd v d =
     (if v = read_pp then
        if d = 1 then (\<lambda>y. if y = ''x'' then SPos else STop)
        else if d = 2 then (\<lambda>y. if y = ''x'' then SNeg else STop)
        else (\<lambda>_. STop)
      else (\<lambda>_. STop))"

lemma sign_pos_neg_top:
  "1 \<in> gamma_sign sv \<Longrightarrow> - 1 \<in> gamma_sign sv \<Longrightarrow> sv = STop"
  by (cases sv) auto

lemma s_read_L_in_envd_L: "s_read_L \<in> \<lbrakk>envd read_pp 1\<rbrakk>"
  unfolding gamma_state_def envd_def s_read_L_def s_wr_L_def s_ls_L_def by auto


lemma flat_join_forces_top:
  assumes flat: "alpha_last (cfg_collect_trace reaching_g S0 read_pp) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (envf ''x'') = UNIV"
proof -
  have L: "s_read_L \<in> \<lbrakk>envf\<rbrakk>"
    using flat alpha_last_read_flat by auto
  have M: "s_read_M \<in> \<lbrakk>envf\<rbrakk>"
    using flat alpha_last_read_flat by auto
  have L_all: "\<forall>y. s_read_L y \<in> gamma_sign (envf y)"
    using L unfolding gamma_state_def by simp
  from L_all[rule_format, of "''x''"] have pos: "1 \<in> gamma_sign (envf ''x'')"
    by simp
  have M_all: "\<forall>y. s_read_M y \<in> gamma_sign (envf y)"
    using M unfolding gamma_state_def by simp
  from M_all[rule_format, of "''x''"] have neg: "- 1 \<in> gamma_sign (envf ''x'')"
    by simp
  have "envf ''x'' = STop"
    using sign_pos_neg_top[OF pos neg] .
  thus ?thesis by simp
qed

lemma digest_env_sound_read_L:
  "alpha_last (reaching_compat dg_ls (=) 1 reaching_g S0 read_pp) \<subseteq> \<lbrakk>envd read_pp 1\<rbrakk>"
  unfolding alpha_last_read_L using s_read_L_in_envd_L by auto

lemma digest_read_x_pos:
  "envd read_pp 1 ''x'' = SPos"
  by (simp add: envd_def)

lemma digest_strictly_more_precise:
  assumes flat: "alpha_last (cfg_collect_trace reaching_g S0 read_pp) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (envd read_pp 1 ''x'') \<subset> gamma_sign (envf ''x'')"
proof -
  have flat_top: "gamma_sign (envf ''x'') = UNIV"
    by (rule flat_join_forces_top[OF flat])
  have not_univ: "gamma_sign (envd read_pp 1 ''x'') \<noteq> UNIV"
  proof
    assume "gamma_sign (envd read_pp 1 ''x'') = UNIV"
    moreover have "0 \<notin> gamma_sign (envd read_pp 1 ''x'')"
      by (simp add: envd_def)
    ultimately show False by blast
  qed
  show ?thesis
    using flat_top not_univ by auto
qed

theorem reaching_compat_beats_flat:
  assumes flat: "alpha_last (cfg_collect_trace reaching_g S0 read_pp) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (envd read_pp 1 ''x'') \<subset> gamma_sign (envf ''x'')
       \<and> alpha_last (reaching_compat dg_ls (=) 1 reaching_g S0 read_pp)
          \<subseteq> \<lbrakk>envd read_pp 1\<rbrakk>"
  using digest_strictly_more_precise[OF flat] digest_env_sound_read_L by auto

section \<open>What this example shows\<close>

text \<open>
  The program writes global @{term "''Gg''"} under two ghost locksets and then
  executes the reader statement x := Gg.  Plain collecting reaches the read
  point with x equal to both 1 and -1; any sound flat sign abstraction must use
  @{term STop} for x.

  @{term reaching_compat} keeps the semantics fixed and filters the reaching
  traces by the reader digest.  For digest 1 only @{term tau_L} remains, so the
  digest-indexed environment proves x as @{term SPos}.  The final theorem states
  the verification payoff: filtered reads are strictly more precise than every
  sound flat abstraction at this program point.
\<close>

end

