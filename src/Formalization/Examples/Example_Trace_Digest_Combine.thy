theory Example_Trace_Digest_Combine
  imports "Voblint_CFG.CFG_Collect_Trace" "Voblint_Analysis.Sign_Domain"
          "Voblint_IMP2.IMP2_Notation"
begin

(*
  Combine-side digest filtering (fully compiled): three initial stores carry
  distinct caller path ids (local tag); callee f branches on global Gpath.
  Each caller gets exactly one combine-valid return trace.  cmp_pair blocks
  path 3 with callee tag 2, so digest collecting keeps two traces while plain
  collecting still admits the third.
*)

section \<open>Compiled program\<close>

definition combine_program :: imp_prog where
  "combine_program = \<lbrakk>
     int Gx, Gpath;
     void f() {
       if (Gpath == 1) { tag := 1 } else { tag := 2 }
     }
     void main() { f() }
   \<rbrakk>"

definition combine_pi :: proc_table where
  "combine_pi = prog_table combine_program"

definition b_gpath_eq_1 :: bexp where
  "b_gpath_eq_1 = Eq (V ''Gpath'') (N 1)"

lemma combine_program_parts:
  shows "prog_procs combine_program = [''f'']"
    and "prog_table combine_program =
        (\<lambda>_. None)(''f'' := Some
          (If b_gpath_eq_1 (Assign ''tag'' (N 1)) (Assign ''tag'' (N 2))))"
    and "prog_main combine_program = Call ''f''"
  by (simp_all add: combine_program_def b_gpath_eq_1_def)

definition combine_g :: cfg where
  "combine_g = compile_prog (prog_table combine_program)
                     (prog_procs combine_program) (prog_main combine_program)"

lemma combine_g_eq_compile:
  "combine_g = compile_prog combine_pi [''f''] (Call ''f'')"
  by (simp add: combine_g_def combine_pi_def combine_program_parts)

lemma combine_g_full:
  "combine_g = mk_cfg 6 7
     {(0, EA_Assume b_gpath_eq_1, 1),
      (0, EA_AssumeNot b_gpath_eq_1, 3),
      (1, EA_Assign ''tag'' (N 1), 2),
      (2, EA_Nop, 5),
      (3, EA_Assign ''tag'' (N 2), 4),
      (4, EA_Nop, 5),
      (6, EA_Enter, 0)}
     {(6, 5, 7)}"
  by (simp add: combine_g_def combine_program_def b_gpath_eq_1_def
            compile_eval_simps Let_def; blast)

lemma combine_g_structure:
  shows "cfg_entry combine_g = 6"
    and "cfg_exit combine_g = 7"
    and "combines combine_g = {(6, 5, 7)}"
  by (simp_all add: combine_g_full)

definition call_pp :: pp where "call_pp = cfg_entry combine_g"
definition callee_exit_pp :: pp where "callee_exit_pp = 5"

lemma call_pp_6[simp]: "call_pp = 6"
  by (simp add: call_pp_def combine_g_full)

lemma callee_exit_pp_5[simp]: "callee_exit_pp = 5"
  by (simp add: callee_exit_pp_def)

section \<open>Stores\<close>

definition s_base :: store where
  "s_base = (\<lambda>_. 0)(''Gx'' := 7)"

definition s1 :: store where "s1 = s_base(''Gpath'' := 1, ''tag'' := 1)"
definition s2 :: store where "s2 = s_base(''Gpath'' := 2, ''tag'' := 2)"
definition s3 :: store where "s3 = s_base(''Gpath'' := 3, ''tag'' := - 1)"

definition S0 :: "store set" where "S0 = {s1, s2, s3}"

definition ent1 :: store where "ent1 = enter_state s1"
definition ent2 :: store where "ent2 = enter_state s2"
definition ent3 :: store where "ent3 = enter_state s3"

definition body1 :: store where "body1 = ent1(''tag'' := 1)"
definition body2 :: store where "body2 = ent2(''tag'' := 2)"
definition body3 :: store where "body3 = ent3(''tag'' := 2)"

lemma s1_gpath[simp]: "s1 ''Gpath'' = 1" by (simp add: s1_def s_base_def)
lemma s2_gpath[simp]: "s2 ''Gpath'' = 2" by (simp add: s2_def s_base_def)
lemma s3_gpath[simp]: "s3 ''Gpath'' = 3" by (simp add: s3_def s_base_def)
lemma s1_tag[simp]: "s1 ''tag'' = 1" by (simp add: s1_def)
lemma s2_tag[simp]: "s2 ''tag'' = 2" by (simp add: s2_def)
lemma s3_tag[simp]: "s3 ''tag'' = - 1" by (simp add: s3_def)

lemma ent1_gpath[simp]: "ent1 ''Gpath'' = 1"
  by (simp add: ent1_def enter_state_def s1_def s_base_def is_global_def)
lemma ent2_gpath[simp]: "ent2 ''Gpath'' = 2"
  by (simp add: ent2_def enter_state_def s2_def s_base_def is_global_def)
lemma ent3_gpath[simp]: "ent3 ''Gpath'' = 3"
  by (simp add: ent3_def enter_state_def s3_def s_base_def is_global_def)

lemma ent1_tag[simp]: "ent1 ''tag'' = 0"
  by (simp add: ent1_def enter_state_def is_global_def)
lemma ent2_tag[simp]: "ent2 ''tag'' = 0"
  by (simp add: ent2_def enter_state_def is_global_def)
lemma ent3_tag[simp]: "ent3 ''tag'' = 0"
  by (simp add: ent3_def enter_state_def is_global_def)

lemma body1_tag[simp]: "body1 ''tag'' = 1" by (simp add: body1_def)
lemma body2_tag[simp]: "body2 ''tag'' = 2" by (simp add: body2_def)
lemma body3_tag[simp]: "body3 ''tag'' = 2" by (simp add: body3_def)

lemma ent_s1[simp]: "enter_state s1 = ent1" by (simp add: ent1_def)
lemma ent_s2[simp]: "enter_state s2 = ent2" by (simp add: ent2_def)
lemma ent_s3[simp]: "enter_state s3 = ent3" by (simp add: ent3_def)

lemma bval_gpath_eq_1_ent1[simp]: "bval b_gpath_eq_1 ent1"
  by (simp add: b_gpath_eq_1_def)
lemma bval_gpath_eq_1_ent2[simp]: "\<not> bval b_gpath_eq_1 ent2"
  by (simp add: b_gpath_eq_1_def)
lemma bval_gpath_eq_1_ent3[simp]: "\<not> bval b_gpath_eq_1 ent3"
  by (simp add: b_gpath_eq_1_def)

lemma tag_local[simp]: "\<not> is_global ''tag''"
  by (simp add: is_global_def)

definition ret1 :: store where "ret1 = <s1|body1>"
definition ret2 :: store where "ret2 = <s2|body2>"
definition ret3 :: store where "ret3 = <s3|body3>"

lemma ret1_tag[simp]: "ret1 ''tag'' = 1" by (simp add: ret1_def combine_states_def)
lemma ret2_tag[simp]: "ret2 ''tag'' = 2" by (simp add: ret2_def combine_states_def)
lemma ret3_tag[simp]: "ret3 ''tag'' = - 1" by (simp add: ret3_def combine_states_def)

section \<open>Caller and callee traces\<close>

definition tau1 :: trace where "tau1 = [s1]"
definition tau2 :: trace where "tau2 = [s2]"
definition tau3 :: trace where "tau3 = [s3]"

definition rho1 :: trace where "rho1 = [ent1, ent1, body1, body1]"
definition rho2 :: trace where "rho2 = [ent2, ent2, body2, body2]"
definition rho3 :: trace where "rho3 = [ent3, ent3, body3, body3]"

definition dg_tag where
  "dg_tag tr = (last tr) ''tag''"

definition cmp_pair where
  "cmp_pair p c = (p = c)"


lemma tau1_witness: "trace_witness combine_g S0 call_pp tau1"
  unfolding tau1_def call_pp_def
  by (intro trace_witness.entry) (auto simp: S0_def combine_g_structure)

lemma tau2_witness: "trace_witness combine_g S0 call_pp tau2"
  unfolding tau2_def call_pp_def
  by (intro trace_witness.entry) (auto simp: S0_def combine_g_structure)

lemma tau3_witness: "trace_witness combine_g S0 call_pp tau3"
  unfolding tau3_def call_pp_def
  by (intro trace_witness.entry) (auto simp: S0_def combine_g_structure)

lemma rho1_witness: "trace_witness combine_g S0 callee_exit_pp rho1"
proof -
  have w0: "trace_witness combine_g S0 0 [ent1]"
    by (intro trace_witness.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s1])
  have w1: "trace_witness combine_g S0 1 [ent1, ent1]"
    using trace_witness.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness combine_g S0 2 [ent1, ent1, body1]"
    using trace_witness.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body1_def)
  have w3: "trace_witness combine_g S0 5 [ent1, ent1, body1, body1]"
    using trace_witness.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho1_def callee_exit_pp_def by (simp add: w3)
qed

lemma rho2_witness: "trace_witness combine_g S0 callee_exit_pp rho2"
proof -
  have w0: "trace_witness combine_g S0 0 [ent2]"
    by (intro trace_witness.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s2])
  have w1: "trace_witness combine_g S0 3 [ent2, ent2]"
    using trace_witness.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness combine_g S0 4 [ent2, ent2, body2]"
    using trace_witness.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body2_def)
  have w3: "trace_witness combine_g S0 5 [ent2, ent2, body2, body2]"
    using trace_witness.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho2_def callee_exit_pp_def by (simp add: w3)
qed

lemma rho3_witness: "trace_witness combine_g S0 callee_exit_pp rho3"
proof -
  have w0: "trace_witness combine_g S0 0 [ent3]"
    by (intro trace_witness.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s3])
  have w1: "trace_witness combine_g S0 3 [ent3, ent3]"
    using trace_witness.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness combine_g S0 4 [ent3, ent3, body3]"
    using trace_witness.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body3_def)
  have w3: "trace_witness combine_g S0 5 [ent3, ent3, body3, body3]"
    using trace_witness.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho3_def callee_exit_pp_def by (simp add: w3)
qed

lemma tau1_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau1"
  unfolding tau1_def call_pp_def
  by (intro trace_witness_d.entry) (auto simp: S0_def combine_g_structure)

lemma tau2_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau2"
  unfolding tau2_def call_pp_def
  by (intro trace_witness_d.entry) (auto simp: S0_def combine_g_structure)

lemma tau3_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau3"
  unfolding tau3_def call_pp_def
  by (intro trace_witness_d.entry) (auto simp: S0_def combine_g_structure)

lemma rho1_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 callee_exit_pp rho1"
proof -
  have w0: "trace_witness_d dg_tag cmp_pair combine_g S0 0 [ent1]"
    by (intro trace_witness_d.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s1])
  have w1: "trace_witness_d dg_tag cmp_pair combine_g S0 1 [ent1, ent1]"
    using trace_witness_d.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness_d dg_tag cmp_pair combine_g S0 2 [ent1, ent1, body1]"
    using trace_witness_d.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body1_def)
  have w3: "trace_witness_d dg_tag cmp_pair combine_g S0 5 [ent1, ent1, body1, body1]"
    using trace_witness_d.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho1_def callee_exit_pp_def by (simp add: w3)
qed

lemma rho2_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 callee_exit_pp rho2"
proof -
  have w0: "trace_witness_d dg_tag cmp_pair combine_g S0 0 [ent2]"
    by (intro trace_witness_d.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s2])
  have w1: "trace_witness_d dg_tag cmp_pair combine_g S0 3 [ent2, ent2]"
    using trace_witness_d.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness_d dg_tag cmp_pair combine_g S0 4 [ent2, ent2, body2]"
    using trace_witness_d.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body2_def)
  have w3: "trace_witness_d dg_tag cmp_pair combine_g S0 5 [ent2, ent2, body2, body2]"
    using trace_witness_d.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho2_def callee_exit_pp_def by (simp add: w3)
qed

lemma rho3_witness_d: "trace_witness_d dg_tag cmp_pair combine_g S0 callee_exit_pp rho3"
proof -
  have w0: "trace_witness_d dg_tag cmp_pair combine_g S0 0 [ent3]"
    by (intro trace_witness_d.proc_entry)
      (auto simp: combine_g_full S0_def image_iff intro: rev_image_eqI[where x = s3])
  have w1: "trace_witness_d dg_tag cmp_pair combine_g S0 3 [ent3, ent3]"
    using trace_witness_d.edge[OF _ w0]
    by (auto simp: combine_g_full edge_step.simps b_gpath_eq_1_def)
  have w2: "trace_witness_d dg_tag cmp_pair combine_g S0 4 [ent3, ent3, body3]"
    using trace_witness_d.edge[OF _ w1]
    by (auto simp: combine_g_full edge_step.simps body3_def)
  have w3: "trace_witness_d dg_tag cmp_pair combine_g S0 5 [ent3, ent3, body3, body3]"
    using trace_witness_d.edge[OF _ w2]
    by (auto simp: combine_g_full edge_step.simps)
  show ?thesis unfolding rho3_def callee_exit_pp_def by (simp add: w3)
qed

section \<open>Digest: tag on last store; cmp filters path 3 with callee tag 2\<close>

lemma dg_tag_tau[simp]:
  "dg_tag tau1 = 1" "dg_tag tau2 = 2" "dg_tag tau3 = - 1"
  by (simp_all add: dg_tag_def tau1_def tau2_def tau3_def)

lemma dg_tag_rho[simp]:
  "dg_tag rho1 = 1" "dg_tag rho2 = 2" "dg_tag rho3 = 2"
  by (simp_all add: dg_tag_def rho1_def rho2_def rho3_def)

section \<open>Return traces: tau @ tl rho @ [combine]\<close>

definition tr1 :: trace where "tr1 = tau1 @ tl rho1 @ [ret1]"
definition tr2 :: trace where "tr2 = tau2 @ tl rho2 @ [ret2]"
definition tr3 :: trace where "tr3 = tau3 @ tl rho3 @ [ret3]"

lemma ret1_eq: "ret1 = <last tau1|last rho1>"
  by (simp add: ret1_def tau1_def rho1_def combine_states_def last.simps)

lemma ret2_eq: "ret2 = <last tau2|last rho2>"
  by (simp add: ret2_def tau2_def rho2_def combine_states_def last.simps)

lemma ret3_eq: "ret3 = <last tau3|last rho3>"
  by (simp add: ret3_def tau3_def rho3_def combine_states_def last.simps)

lemma tr1_witness_d:
  "trace_witness_d dg_tag cmp_pair combine_g S0 7 tr1"
proof -
  have w: "trace_witness_d dg_tag cmp_pair combine_g S0 7
            (tau1 @ tl rho1 @ [<last tau1|last rho1>])"
  proof (rule trace_witness_d.combine[where tau = tau1 and \<rho> = rho1])
    show "(call_pp, callee_exit_pp, 7) \<in> combines combine_g"
      by (simp add: combine_g_structure combine_g_full call_pp_def callee_exit_pp_def)
    show "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau1"
      by (rule tau1_witness_d)
    show "trace_witness_d dg_tag cmp_pair combine_g S0 callee_exit_pp rho1"
      by (rule rho1_witness_d)
    show "hd rho1 = enter_state (last tau1)"
      by (simp add: rho1_def tau1_def ent_s1)
    show "cmp_pair (dg_tag tau1) (dg_tag rho1)"
      by (simp add: cmp_pair_def dg_tag_def tau1_def rho1_def)
  qed
  show ?thesis unfolding tr1_def using w by (simp add: ret1_eq)
qed

lemma tr2_witness_d:
  "trace_witness_d dg_tag cmp_pair combine_g S0 7 tr2"
proof -
  have w: "trace_witness_d dg_tag cmp_pair combine_g S0 7
            (tau2 @ tl rho2 @ [<last tau2|last rho2>])"
  proof (rule trace_witness_d.combine[where tau = tau2 and \<rho> = rho2])
    show "(call_pp, callee_exit_pp, 7) \<in> combines combine_g"
      by (simp add: combine_g_structure combine_g_full call_pp_def callee_exit_pp_def)
    show "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau2"
      by (rule tau2_witness_d)
    show "trace_witness_d dg_tag cmp_pair combine_g S0 callee_exit_pp rho2"
      by (rule rho2_witness_d)
    show "hd rho2 = enter_state (last tau2)"
      by (simp add: rho2_def tau2_def ent_s2)
    show "cmp_pair (dg_tag tau2) (dg_tag rho2)"
      by (simp add: cmp_pair_def dg_tag_def tau2_def rho2_def)
  qed
  show ?thesis unfolding tr2_def using w by (simp add: ret2_eq)
qed

lemma not_cmp_pair_tau3_rho3:
  "\<not> cmp_pair (dg_tag tau3) (dg_tag rho3)"
  by (simp add: cmp_pair_def dg_tag_tau dg_tag_rho)

lemma trace_witness_d_call_pp_len:
  assumes "trace_witness_d dg cmp combine_g S call_pp tr"
  shows "length tr = 1"
  using assms
proof (cases rule: trace_witness_d.cases)
  case (entry s)
  then show ?thesis by simp
next
  case (proc_entry s)
  then have False unfolding combine_g_full by auto
  then show ?thesis by simp
next
  case (edge u a tr s')
  then have False unfolding combine_g_full by auto
  then show ?thesis by simp
next
  case (combine c ex tau rho)
  then have False unfolding combine_g_full combine_g_structure by auto
  then show ?thesis by simp
qed

lemma combine_tr3_shape:
  assumes len: "length tau = 1"
  assumes hd: "hd rho = enter_state (last tau)"
  assumes eq: "tau @ tl rho @ [r] = tau3 @ tl rho3 @ [ret3]"
  shows "tau = tau3" "rho = rho3"
proof -
  from len obtain s where tau: "tau = [s]" by (cases tau) auto
  from eq tau have s: "s = s3"
    by (simp add: tau3_def rho3_def ret3_def combine_states_def)
  from eq tau s have tail: "tl rho @ [r] = [ent3, body3, body3, ret3]"
    by (simp add: tau3_def rho3_def ret3_def combine_states_def)
  show "tau = tau3" using tau s by (simp add: tau3_def)
  show "rho = rho3"
  proof (cases rho)
    case Nil
    with tail show ?thesis by simp
  next
    case (Cons x xs)
    from hd Cons tau s have "x = ent3"
      by (simp add: tau3_def ent3_def enter_state_def)
    with Cons tail show ?thesis
      by (auto simp: rho3_def Cons_eq_append_conv)
  qed
qed

lemma tr3_blocked:
  "\<not> trace_witness_d dg_tag cmp_pair combine_g S0 7 tr3"
proof
  assume w: "trace_witness_d dg_tag cmp_pair combine_g S0 7 tr3"
  show False
    using w unfolding tr3_def
  proof (cases rule: trace_witness_d.cases)
    case (entry s)
    then show False using combine_g_structure by auto
  next
    case (proc_entry s)
    then have "(cfg_entry combine_g, EA_Enter, 7) \<in> edges combine_g"
      by simp
    then show False unfolding combine_g_full by simp
  next
    case (edge u a tr s')
    then have "(u, a, 7) \<in> edges combine_g" by simp
    then show False unfolding combine_g_full by simp
  next
    case (combine c ex tau rho)
    then show False
    proof -
      from combine have tw: "trace_witness_d dg_tag cmp_pair combine_g S0 call_pp tau"
        by (auto simp: combine_g_structure combine_g_full call_pp_def)
      have len: "length tau = 1"
        using tw by (rule trace_witness_d_call_pp_len)
      have "tau = tau3" "rho = rho3"
        using combine_tr3_shape[OF len combine(5)] combine(1) by auto
      show False
        using combine(6) not_cmp_pair_tau3_rho3
        using \<open>rho = rho3\<close> \<open>tau = tau3\<close> by blast
    qed
  qed
qed

lemma tr3_witness:
  "trace_witness combine_g S0 7 tr3"
proof -
  have w: "trace_witness combine_g S0 7 (tau3 @ tl rho3 @ [<last tau3|last rho3>])"
  proof (rule trace_witness.combine[where tau = tau3 and \<rho> = rho3])
    show "(call_pp, callee_exit_pp, 7) \<in> combines combine_g"
      by (simp add: combine_g_structure combine_g_full call_pp_def callee_exit_pp_def)
    show "trace_witness combine_g S0 call_pp tau3"
      by (rule tau3_witness)
    show "trace_witness combine_g S0 callee_exit_pp rho3"
      by (rule rho3_witness)
    show "hd rho3 = enter_state (last tau3)"
      by (simp add: rho3_def tau3_def ent_s3)
  qed
  show ?thesis unfolding tr3_def using w by (simp add: ret3_eq)
qed

section \<open>Trace-set cardinality and precision\<close>

lemma tr3_not_in_digest:
  "tr3 \<notin> cfg_collect_trace_d dg_tag cmp_pair combine_g S0 7"
  using tr3_blocked unfolding cfg_collect_trace_d_def by blast

lemma tr1_tr2_in_digest:
  "{tr1, tr2} \<subseteq> cfg_collect_trace_d dg_tag cmp_pair combine_g S0 7"
  unfolding cfg_collect_trace_d_def using tr1_witness_d tr2_witness_d by auto

lemma tr1_tr2_tr3_in_plain:
  "{tr1, tr2, tr3} \<subseteq> cfg_collect_trace combine_g S0 7"
  unfolding cfg_collect_trace_def
  using tr1_witness_d tr2_witness_d tr3_witness trace_witness_d_imp by blast

lemma return_traces_neq:
  "tr1 \<noteq> tr2" "tr1 \<noteq> tr3" "tr2 \<noteq> tr3"
proof -
  have t1: "last tr1 ''tag'' = 1" and t2: "last tr2 ''tag'' = 2" and t3: "last tr3 ''tag'' = - 1"
    by (simp_all add: tr1_def tr2_def tr3_def ret1_tag ret2_tag ret3_tag last.simps)
  show "tr1 \<noteq> tr2"
  proof
    assume "tr1 = tr2"
    with t1 t2 show False by simp
  qed
  show "tr1 \<noteq> tr3"
  proof
    assume "tr1 = tr3"
    with t1 t3 show False by simp
  qed
  show "tr2 \<noteq> tr3"
  proof
    assume "tr2 = tr3"
    with t2 t3 show False by simp
  qed
qed

lemma return_trace_set_two: "card {tr1, tr2} = 2"
  using return_traces_neq by simp

lemma return_trace_set_three: "card {tr1, tr2, tr3} = 3"
  using return_traces_neq by simp

section \<open>Precision: digest witnesses prove a stronger value\<close>

theorem combine_tr3_only_in_plain:
  "tr3 \<in> cfg_collect_trace combine_g S0 7"
  "tr3 \<notin> cfg_collect_trace_d dg_tag cmp_pair combine_g S0 7"
  unfolding cfg_collect_trace_def cfg_collect_trace_d_def
  using tr3_witness tr3_blocked by blast+

theorem combine_digest_two_return_traces:
  "{tr1, tr2} \<subseteq> cfg_collect_trace_d dg_tag cmp_pair combine_g S0 7"
  unfolding cfg_collect_trace_d_def
  using tr1_witness_d tr2_witness_d by auto

theorem combine_digest_filters_tr3:
  "\<not> trace_witness_d dg_tag cmp_pair combine_g S0 7 tr3"
  by (fact tr3_blocked)

theorem combine_unfiltered_admits_tr3:
  "tr3 \<in> cfg_collect_trace combine_g S0 7"
  unfolding cfg_collect_trace_def using tr3_witness by blast

definition env_tag_pos where
  "env_tag_pos = (\<lambda>x. if x = ''tag'' then SPos else STop)"

lemma ret1_ret2_in_env_tag_pos:
  "ret1 \<in> \<lbrakk>env_tag_pos\<rbrakk>" "ret2 \<in> \<lbrakk>env_tag_pos\<rbrakk>"
  unfolding gamma_state_def env_tag_pos_def by auto

lemma alpha_last_digest_witnesses_tag_pos:
  "alpha_last {tr1, tr2} \<subseteq> \<lbrakk>env_tag_pos\<rbrakk>"
  unfolding alpha_last_def tr1_def tr2_def
  using ret1_ret2_in_env_tag_pos by auto

lemma sign_pos_neg_top:
  "1 \<in> gamma_sign sv \<Longrightarrow> - 1 \<in> gamma_sign sv \<Longrightarrow> sv = STop"
  by (cases sv) auto

lemma flat_tag_forces_top:
  assumes flat: "alpha_last (cfg_collect_trace combine_g S0 7) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (envf ''tag'') = UNIV"
proof -
  have plain1: "tr1 \<in> cfg_collect_trace combine_g S0 7"
    using tr1_tr2_tr3_in_plain by blast
  have plain3: "tr3 \<in> cfg_collect_trace combine_g S0 7"
    using tr1_tr2_tr3_in_plain by blast
  have r1: "last tr1 \<in> \<lbrakk>envf\<rbrakk>"
    using flat plain1 unfolding alpha_last_def by blast
  have r3: "last tr3 \<in> \<lbrakk>envf\<rbrakk>"
    using flat plain3 unfolding alpha_last_def by blast
  have r1_all: "\<forall>x. last tr1 x \<in> gamma_sign (envf x)"
    using r1 unfolding gamma_state_def by simp
  from r1_all[rule_format, of "''tag''"] have pos: "1 \<in> gamma_sign (envf ''tag'')"
    by (simp add: tr1_def)
  have r3_all: "\<forall>x. last tr3 x \<in> gamma_sign (envf x)"
    using r3 unfolding gamma_state_def by simp
  from r3_all[rule_format, of "''tag''"] have neg: "- 1 \<in> gamma_sign (envf ''tag'')"
    by (simp add: tr3_def)
  have "envf ''tag'' = STop"
    using sign_pos_neg_top[OF pos neg] .
  thus ?thesis by simp
qed

lemma digest_tag_strictly_more_precise:
  assumes flat: "alpha_last (cfg_collect_trace combine_g S0 7) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (env_tag_pos ''tag'') \<subset> gamma_sign (envf ''tag'')"
proof -
  have flat_top: "gamma_sign (envf ''tag'') = UNIV"
    by (rule flat_tag_forces_top[OF flat])
  have not_univ: "gamma_sign (env_tag_pos ''tag'') \<noteq> UNIV"
  proof
    assume "gamma_sign (env_tag_pos ''tag'') = UNIV"
    moreover have "0 \<notin> gamma_sign (env_tag_pos ''tag'')"
      by (simp add: env_tag_pos_def)
    ultimately show False by blast
  qed
  show ?thesis using flat_top not_univ by auto
qed

theorem combine_digest_payoff_witness:
  assumes flat: "alpha_last (cfg_collect_trace combine_g S0 7) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign (env_tag_pos ''tag'') \<subset> gamma_sign (envf ''tag'')
       \<and> {tr1, tr2} \<subseteq> cfg_collect_trace_d dg_tag cmp_pair combine_g S0 7
       \<and> alpha_last {tr1, tr2} \<subseteq> \<lbrakk>env_tag_pos\<rbrakk>"
  using digest_tag_strictly_more_precise[OF flat]
        combine_digest_two_return_traces
        alpha_last_digest_witnesses_tag_pos
  by auto

section \<open>What this example shows\<close>

text \<open>
  At the interprocedural combine edge, plain trace collecting can join a caller
  prefix with a callee suffix even when their digests disagree.  Here the digest
  is the local tag at the end of each side, and compatibility is equality.

  The plain return witnesses include @{term tr3}, whose caller tag is negative.
  The digest witnesses @{term tr1} and @{term tr2} both have positive return
  tags, while @{term tr3} is blocked by the failed digest comparison.  The final
  theorem states the payoff as a sign-domain fact: every sound flat abstraction
  must use @{term STop} for @{term "''tag''"}, while the admitted digest
  witnesses are soundly covered by @{term SPos}.
\<close>

end

