theory Example_LTR_Collect_Regression
  imports "Voblint_CFG.LTR_Collect"
begin

section \<open>Examples: local-trace collecting semantics\<close>

text \<open>Multiple returns: two distinct intra branches reach \<open>FunctionResult pf\<close>, both states
  occur in \<open>ltr_collect (FunctionResult pf)\<close>, and both resume through the same continuation.
  Built on \<^const>\<open>valid_ltr\<close> witness \<open>multi_return_join\<close>.\<close>
lemma ltr_collect_multi_return:
  "\<exists>s1 s2 r1 r2.
      s1 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)
    \<and> s2 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)
    \<and> r1 \<in> ltr_collect mret_cfg UNIV (Statement 100)
    \<and> r2 \<in> ltr_collect mret_cfg UNIV (Statement 100)"
proof -
  from multi_return_join obtain t1 t2 c1 c2 where
    T1: "t1 \<in> valid_ltr mret_cfg UNIV" and T2: "t2 \<in> valid_ltr mret_cfg UNIV"
    and sn1: "sink_node t1 = FunctionResult pf" and sn2: "sink_node t2 = FunctionResult pf"
    and R1: "Resume c1 t1 (path c1 @ [(Statement 100, combine_collect None (sink_store c1) (sink_store t1))])
               \<in> valid_ltr mret_cfg UNIV"
    and R2: "Resume c2 t2 (path c2 @ [(Statement 100, combine_collect None (sink_store c2) (sink_store t2))])
               \<in> valid_ltr mret_cfg UNIV"
    by blast
  have "sink_store t1 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T1] sn1 by simp
  moreover have "sink_store t2 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T2] sn2 by simp
  moreover have "combine_collect None (sink_store c1) (sink_store t1)
                   \<in> ltr_collect mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R1] by (simp add: sink_node_def sink_store_def)
  moreover have "combine_collect None (sink_store c2) (sink_store t2)
                   \<in> ltr_collect mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R2] by (simp add: sink_node_def sink_store_def)
  ultimately show ?thesis by blast
qed

text \<open>Recursion: two nested activations of \<open>pr\<close> are distinct structural traces; under the
  discriminating context \<open>key (\<lambda>c _. Suc c) 0\<close> (call depth) they receive distinct context
  keys.  Built on \<^const>\<open>valid_ltr\<close> witness \<open>recursion_nesting\<close>.\<close>
lemma ltr_collect_recursion_distinct_ctx:
  "\<exists>outer inner.
      outer \<in> valid_ltr rec_cfg UNIV \<and> inner \<in> valid_ltr rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> key (\<lambda>c _. Suc c) 0 outer \<noteq> key (\<lambda>c _. Suc c) 0 inner"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ltr rec_cfg UNIV" unfolding root_def by (rule valid_ltr.init) simp
  have rt_sn: "sink_node root = FunctionEntry pr" by (simp add: root_def rec_defs)
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    by (simp add: rt_sn rec_defs)
  have stepA: "edge_step (EA_Assume bpos) (sink_store root) = Some (sink_store root)"
    by (simp add: root_def rec_defs s0_def enter_state_def is_global_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ltr rec_cfg UNIV"
    unfolding outer_def by (rule valid_ltr.intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None [] [], FunctionEntry pr, Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, call_enter (CallEdge None [] []) (sink_store outer))]"
  have INNER: "inner \<in> valid_ltr rec_cfg UNIV"
    unfolding inner_def by (rule valid_ltr.call[OF OUTER ecall])
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  have kouter: "key (\<lambda>c _. Suc c) 0 outer = 0" by (simp add: outer_def root_def)
  have kinner: "key (\<lambda>c _. Suc c) 0 inner = Suc 0"
    by (simp add: inner_def outer_def root_def)
  have "key (\<lambda>c _. Suc c) 0 outer \<noteq> key (\<lambda>c _. Suc c) 0 inner"
    using kouter kinner by simp
  then show ?thesis using OUTER INNER neq by blast
qed

text \<open>Flat CFG: for a \<open>calls = {}\<close> graph the collector agrees with ordinary intra
  reachability.  \<open>flat_demo\<close> is a two-edge straight line; both edge targets are collected
  exactly as intra propagation yields, and no call-derived activation exists.\<close>

definition flat_demo :: cfg where
  "flat_demo =
     \<lparr> intra = { (Statement 0, EA_Nop, Statement 1), (Statement 1, EA_Nop, Statement 2) },
       calls = {},
       cfg_entry = Statement 0 \<rparr>"

lemma flat_demo_flat: "flat_cfg flat_demo"
  by (simp add: flat_cfg_def flat_demo_def)

lemma ltr_collect_flat_demo:
  fixes s0 :: store
  shows "s0 \<in> ltr_collect flat_demo {s0} (Statement 0)"
    and "s0 \<in> ltr_collect flat_demo {s0} (Statement 1)"
    and "s0 \<in> ltr_collect flat_demo {s0} (Statement 2)"
proof -
  show c0: "s0 \<in> ltr_collect flat_demo {s0} (Statement 0)"
    using ltr_collect_init[of s0 "{s0}" flat_demo] by (simp add: flat_demo_def)
  have e0: "(Statement 0, EA_Nop, Statement 1) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show c1: "s0 \<in> ltr_collect flat_demo {s0} (Statement 1)"
    using ltr_collect_intra[OF c0 e0] by simp
  have e1: "(Statement 1, EA_Nop, Statement 2) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show "s0 \<in> ltr_collect flat_demo {s0} (Statement 2)"
    using ltr_collect_intra[OF c1 e1] by simp
qed

lemma ltr_collect_flat_demo_no_call:
  "Call caller p \<notin> valid_ltr flat_demo S"
  using valid_ltr_flat_no_call[OF flat_demo_flat] by blast

end
