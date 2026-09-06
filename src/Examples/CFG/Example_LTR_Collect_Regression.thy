theory Example_LTR_Collect_Regression
  imports "Voblint_CFG.LTR_Collect"
begin

section \<open>Examples: local-trace collecting semantics\<close>

text \<open>These witnesses build hand-written CFGs rather than compiling a source program, so
  there is no declared-globals table to read a classifier off; \<open>(STR ''Gx'')\<close> is the only
  store variable any witness below reads or writes, so it is fixed as the sole global.\<close>
abbreviation demo_gs :: "vname \<Rightarrow> bool" where
  "demo_gs \<equiv> (\<lambda>x. x = STR ''Gx'')"

subsection \<open>Shared continuations and converging returns\<close>

text \<open>Procedure \<open>dpf\<close> reaches one result from two nodes and is called from two sites
  that share a continuation.  Result nodes and continuations are join points.\<close>

definition dmain :: pname where "dmain = (STR ''main'')"
definition dpf :: pname where "dpf = (STR ''f'')"

definition demo_cfg :: cfg where
  "demo_cfg =
     \<lparr> intra =
         { (FunctionEntry dpf, EA_Ret None dpf, FunctionResult dpf),
           (Statement 0,      EA_Ret None dpf, FunctionResult dpf) },
       calls =
         { (Statement 10, CallEdge None [] [], FunctionEntry dpf, Statement 99),
           (Statement 20, CallEdge None [] [], FunctionEntry dpf, Statement 99) },
       cfg_entry = FunctionEntry dmain,
       checks = {} \<rparr>"

lemmas demo_defs = demo_cfg_def dmain_def dpf_def

lemma demo_wf: "wf_cfg demo_cfg"
  by (auto simp: wf_cfg_def demo_defs)

text \<open>Two distinct return edges converge into one procedure result.\<close>
lemma demo_returns_converge:
  "(FunctionEntry dpf, EA_Ret None dpf, FunctionResult dpf) \<in> intra demo_cfg"
  "(Statement 0, EA_Ret None dpf, FunctionResult dpf) \<in> intra demo_cfg"
  "FunctionEntry dpf \<noteq> Statement 0"
  by (simp_all add: demo_defs)

text \<open>Two distinct call sites may share one continuation.\<close>
lemma demo_shared_continuation:
  "(Statement 10, CallEdge None [] [], FunctionEntry dpf, Statement 99) \<in> calls demo_cfg"
  "(Statement 20, CallEdge None [] [], FunctionEntry dpf, Statement 99) \<in> calls demo_cfg"
  "Statement 10 \<noteq> Statement 20"
  by (simp_all add: demo_defs)


subsection \<open>Witness: nested returns resume the immediate caller\<close>

text \<open>A two-level program \<open>main -> f -> g\<close> where \<open>g\<close> returns into \<open>f\<close> and \<open>f\<close> returns into
  \<open>main\<close>.  It exercises every rule and shows \<open>g\<close>'s return resumes \<open>f\<close> (the nearest
  activation), while \<open>f\<close>'s return recovers \<open>main\<close> through the resumed \<open>f\<close>.\<close>

definition mn :: pname where "mn = (STR ''main'')"
definition pf :: pname where "pf = (STR ''f'')"
definition pg :: pname where "pg = (STR ''g'')"

definition nest_cfg :: cfg where
  "nest_cfg =
     \<lparr> intra =
         { (FunctionEntry pg, EA_Ret None pg, FunctionResult pg),
           (Statement 200,    EA_Ret None pf, FunctionResult pf) },
       calls =
         { (FunctionEntry mn, CallEdge None [] [], FunctionEntry pf, Statement 100),
           (FunctionEntry pf, CallEdge None [] [], FunctionEntry pg, Statement 200) },
       cfg_entry = FunctionEntry mn,
       checks = {} \<rparr>"

lemmas nest_defs = nest_cfg_def mn_def pf_def pg_def

lemma nested_valid_ltr_example:
  assumes s0: "s0 \<in> S"
  shows "\<exists>main0 f0 g1 f' final.
           g1 \<in> valid_ltr demo_gs nest_cfg S \<and> caller_of g1 = Some f0
         \<and> f' \<in> valid_ltr demo_gs nest_cfg S \<and> caller_of f' = Some main0
         \<and> final \<in> valid_ltr demo_gs nest_cfg S \<and> sink_node final = Statement 100"
proof -
  define main0 where "main0 = Root [(cfg_entry nest_cfg, s0)]"
  have main_mem: "main0 \<in> valid_ltr demo_gs nest_cfg S"
    unfolding main0_def by (rule valid_ltr.init[OF s0])
  have m_sn: "sink_node main0 = FunctionEntry mn"
    by (simp add: main0_def nest_defs)
  have ecall_f: "(sink_node main0, CallEdge None [] [], FunctionEntry pf, Statement 100) \<in> calls nest_cfg"
    by (simp add: m_sn nest_defs)
  define f0 where "f0 = Call main0 [(FunctionEntry pf, call_enter demo_gs (CallEdge None [] []) (sink_store main0))]"
  have f_mem: "f0 \<in> valid_ltr demo_gs nest_cfg S"
    unfolding f0_def by (rule valid_ltr.call[OF main_mem ecall_f])
  have f_sn: "sink_node f0 = FunctionEntry pf" by (simp add: f0_def)
  have ecall_g: "(sink_node f0, CallEdge None [] [], FunctionEntry pg, Statement 200) \<in> calls nest_cfg"
    by (simp add: f_sn nest_defs)
  define g0 where "g0 = Call f0 [(FunctionEntry pg, call_enter demo_gs (CallEdge None [] []) (sink_store f0))]"
  have g_mem: "g0 \<in> valid_ltr demo_gs nest_cfg S"
    unfolding g0_def by (rule valid_ltr.call[OF f_mem ecall_g])
  have g_sn: "sink_node g0 = FunctionEntry pg" by (simp add: g0_def)
  have eRg: "(sink_node g0, EA_Ret None pg, FunctionResult pg) \<in> intra nest_cfg"
    by (simp add: g_sn nest_defs)
  have stRg: "sink_store g0 \<in> edge_step (EA_Ret None pg) (sink_store g0)"
    by simp
  define g1 where "g1 = extend g0 (FunctionResult pg, sink_store g0)"
  have g1_mem: "g1 \<in> valid_ltr demo_gs nest_cfg S"
    unfolding g1_def by (rule valid_ltr.intra[OF g_mem eRg stRg])
  have g1_sn: "sink_node g1 = FunctionResult pg" by (simp add: g1_def)
  have g1_caller: "caller_of g1 = Some f0" by (simp add: g1_def g0_def)
  \<comment> \<open>g returns into f (the immediate caller), not main\<close>
  define f' where
    "f' = Resume f0 g1 (path f0 @ [(Statement 200, combine_collect demo_gs None (sink_store f0) (sink_store g1))])"
  have f'_mem: "f' \<in> valid_ltr demo_gs nest_cfg S"
    unfolding f'_def
    by (rule valid_ltr.ret[OF g1_mem g1_caller g1_sn], simp add: f_sn nest_defs)
  have f'_sn: "sink_node f' = Statement 200" by (simp add: f'_def sink_node_def)
  have f'_caller: "caller_of f' = Some main0" by (simp add: f'_def f0_def)
  have eRf: "(sink_node f', EA_Ret None pf, FunctionResult pf) \<in> intra nest_cfg"
    by (simp add: f'_sn nest_defs)
  have stRf: "sink_store f' \<in> edge_step (EA_Ret None pf) (sink_store f')"
    by simp
  define f2 where "f2 = extend f' (FunctionResult pf, sink_store f')"
  have f2_mem: "f2 \<in> valid_ltr demo_gs nest_cfg S"
    unfolding f2_def by (rule valid_ltr.intra[OF f'_mem eRf stRf])
  have f2_sn: "sink_node f2 = FunctionResult pf" by (simp add: f2_def)
  have f2_caller: "caller_of f2 = Some main0" by (simp add: f2_def f'_def f0_def)
  have ecall_f2: "(sink_node main0, CallEdge None [] [], FunctionEntry pf, Statement 100) \<in> calls nest_cfg"
    by (simp add: m_sn nest_defs)
  define final where
    "final = Resume main0 f2 (path main0 @ [(Statement 100, combine_collect demo_gs None (sink_store main0) (sink_store f2))])"
  have final_mem: "final \<in> valid_ltr demo_gs nest_cfg S"
    unfolding final_def by (rule valid_ltr.ret[OF f2_mem f2_caller f2_sn ecall_f2])
  have final_sn: "sink_node final = Statement 100" by (simp add: final_def sink_node_def)
  from g1_mem g1_caller f'_mem f'_caller final_mem final_sn show ?thesis by blast
qed

subsection \<open>Witness: multiple return paths into one result\<close>

text \<open>Procedure \<open>pf\<close> reaches \<open>FunctionResult pf\<close> through two distinct intra branches;
  \<open>main\<close> calls it with continuation \<open>Statement 100\<close>.  Both branches resume through that same
  continuation.\<close>

definition bpos :: exp where "bpos = Less (N 0) (V (STR ''Gx''))"

definition mret_cfg :: cfg where
  "mret_cfg =
     \<lparr> intra =
         { (FunctionEntry pf, EA_Assume bpos,    Statement 0),
           (Statement 0,      EA_Ret None pf,    FunctionResult pf),
           (FunctionEntry pf, EA_AssumeNot bpos, Statement 1),
           (Statement 1,      EA_Ret None pf,    FunctionResult pf) },
       calls =
         { (FunctionEntry mn, CallEdge None [] [], FunctionEntry pf, Statement 100) },
       cfg_entry = FunctionEntry mn,
       checks = {} \<rparr>"

lemmas mret_defs = mret_cfg_def mn_def pf_def bpos_def

lemma multi_return_join:
  "\<exists>t1 t2 c1 c2.
      t1 \<in> valid_ltr demo_gs mret_cfg UNIV \<and> t2 \<in> valid_ltr demo_gs mret_cfg UNIV \<and> t1 \<noteq> t2
    \<and> sink_node t1 = FunctionResult pf \<and> sink_node t2 = FunctionResult pf
    \<and> caller_of t1 = Some c1 \<and> caller_of t2 = Some c2
    \<and> Resume c1 t1 (path c1 @ [(Statement 100, combine_collect demo_gs None (sink_store c1) (sink_store t1))])
        \<in> valid_ltr demo_gs mret_cfg UNIV
    \<and> Resume c2 t2 (path c2 @ [(Statement 100, combine_collect demo_gs None (sink_store c2) (sink_store t2))])
        \<in> valid_ltr demo_gs mret_cfg UNIV"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)((STR ''Gx'') := 1)"
  define s1 :: store where "s1 = (\<lambda>_. 0)"
  define r0 where "r0 = Root [(cfg_entry mret_cfg, s0)]"
  define r1 where "r1 = Root [(cfg_entry mret_cfg, s1)]"

  \<comment> \<open>positive branch through Statement 0\<close>
  have R0: "r0 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding r0_def by (rule valid_ltr.init) simp
  have m0: "sink_node r0 = FunctionEntry mn" by (simp add: r0_def mret_defs)
  have ec0: "(sink_node r0, CallEdge None [] [], FunctionEntry pf, Statement 100) \<in> calls mret_cfg"
    by (simp add: m0 mret_defs)
  define k0 where "k0 = Call r0 [(FunctionEntry pf, call_enter demo_gs (CallEdge None [] []) (sink_store r0))]"
  have K0: "k0 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding k0_def by (rule valid_ltr.call[OF R0 ec0])
  have k0_sn: "sink_node k0 = FunctionEntry pf" by (simp add: k0_def)
  have k0_ss: "sink_store k0 = enter_state demo_gs s0" by (simp add: k0_def r0_def)
  have eA0: "(sink_node k0, EA_Assume bpos, Statement 0) \<in> intra mret_cfg"
    by (simp add: k0_sn mret_defs)
  have stA0: "sink_store k0 \<in> edge_step (EA_Assume bpos) (sink_store k0)"
    by (simp add: k0_ss s0_def mret_defs enter_state_def)
  define c0 where "c0 = extend k0 (Statement 0, sink_store k0)"
  have C0: "c0 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding c0_def by (rule valid_ltr.intra[OF K0 eA0 stA0])
  have c0_sn: "sink_node c0 = Statement 0" by (simp add: c0_def)
  have eR0: "(sink_node c0, EA_Ret None pf, FunctionResult pf) \<in> intra mret_cfg"
    by (simp add: c0_sn mret_defs)
  have stR0: "sink_store c0 \<in> edge_step (EA_Ret None pf) (sink_store c0)" by simp
  define t1 where "t1 = extend c0 (FunctionResult pf, sink_store c0)"
  have T1: "t1 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding t1_def by (rule valid_ltr.intra[OF C0 eR0 stR0])

  \<comment> \<open>negative branch through Statement 1\<close>
  have R1: "r1 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding r1_def by (rule valid_ltr.init) simp
  have m1: "sink_node r1 = FunctionEntry mn" by (simp add: r1_def mret_defs)
  have ec1: "(sink_node r1, CallEdge None [] [], FunctionEntry pf, Statement 100) \<in> calls mret_cfg"
    by (simp add: m1 mret_defs)
  define k1 where "k1 = Call r1 [(FunctionEntry pf, call_enter demo_gs (CallEdge None [] []) (sink_store r1))]"
  have K1: "k1 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding k1_def by (rule valid_ltr.call[OF R1 ec1])
  have k1_sn: "sink_node k1 = FunctionEntry pf" by (simp add: k1_def)
  have k1_ss: "sink_store k1 = enter_state demo_gs s1" by (simp add: k1_def r1_def)
  have eA1: "(sink_node k1, EA_AssumeNot bpos, Statement 1) \<in> intra mret_cfg"
    by (simp add: k1_sn mret_defs)
  have stA1: "sink_store k1 \<in> edge_step (EA_AssumeNot bpos) (sink_store k1)"
    by (simp add: k1_ss s1_def mret_defs enter_state_def)
  define c1 where "c1 = extend k1 (Statement 1, sink_store k1)"
  have C1: "c1 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding c1_def by (rule valid_ltr.intra[OF K1 eA1 stA1])
  have c1_sn: "sink_node c1 = Statement 1" by (simp add: c1_def)
  have eR1: "(sink_node c1, EA_Ret None pf, FunctionResult pf) \<in> intra mret_cfg"
    by (simp add: c1_sn mret_defs)
  have stR1: "sink_store c1 \<in> edge_step (EA_Ret None pf) (sink_store c1)" by simp
  define t2 where "t2 = extend c1 (FunctionResult pf, sink_store c1)"
  have T2: "t2 \<in> valid_ltr demo_gs mret_cfg UNIV" unfolding t2_def by (rule valid_ltr.intra[OF C1 eR1 stR1])

  have sn1: "sink_node t1 = FunctionResult pf" by (simp add: t1_def)
  have sn2: "sink_node t2 = FunctionResult pf" by (simp add: t2_def)
  have ct1: "caller_of t1 = Some r0" by (simp add: t1_def c0_def k0_def)
  have ct2: "caller_of t2 = Some r1" by (simp add: t2_def c1_def k1_def)

  \<comment> \<open>distinct: the two branches traverse different nodes\<close>
  have neq: "t1 \<noteq> t2"
    by (simp add: t1_def t2_def c0_def c1_def k0_def k1_def)

  have res1: "Resume r0 t1
      (path r0 @ [(Statement 100, combine_collect demo_gs None (sink_store r0) (sink_store t1))])
        \<in> valid_ltr demo_gs mret_cfg UNIV"
    by (rule valid_ltr.ret[OF T1 ct1 sn1 ec0])
  have res2: "Resume r1 t2
      (path r1 @ [(Statement 100, combine_collect demo_gs None (sink_store r1) (sink_store t2))])
        \<in> valid_ltr demo_gs mret_cfg UNIV"
    by (rule valid_ltr.ret[OF T2 ct2 sn2 ec1])

  from T1 T2 neq sn1 sn2 ct1 ct2 res1 res2 show ?thesis by blast
qed

subsection \<open>Witness: recursion nesting\<close>

text \<open>A self-recursive procedure \<open>pr\<close>: at its entry it returns (\<open>Gx <= 0\<close>) or calls itself
  (\<open>Gx > 0\<close>) at continuation \<open>Statement 200\<close>.  Two activations of \<open>pr\<close> are distinct and
  correctly nested via \<^const>\<open>caller_of\<close>.\<close>

definition pr :: pname where "pr = (STR ''r'')"

definition rec_cfg :: cfg where
  "rec_cfg =
     \<lparr> intra =
         { (FunctionEntry pr, EA_AssumeNot bpos, Statement 0),
           (Statement 0,      EA_Ret None pr,    FunctionResult pr),
           (FunctionEntry pr, EA_Assume bpos,    Statement 1) },
       calls =
         { (Statement 1, CallEdge None [] [], FunctionEntry pr, Statement 200) },
       cfg_entry = FunctionEntry pr,
       checks = {} \<rparr>"

lemmas rec_defs = rec_cfg_def pr_def bpos_def

lemma recursion_nesting:
  "\<exists>outer inner.
      outer \<in> valid_ltr demo_gs rec_cfg UNIV \<and> inner \<in> valid_ltr demo_gs rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> caller_of inner = Some outer
    \<and> caller_of outer = None
    \<and> sink_node outer = Statement 1
    \<and> sink_node inner = FunctionEntry pr"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)((STR ''Gx'') := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ltr demo_gs rec_cfg UNIV" unfolding root_def by (rule valid_ltr.init) simp
  have rt_sn: "sink_node root = FunctionEntry pr" by (simp add: root_def rec_defs)
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    by (simp add: rt_sn rec_defs)
  have stepA: "sink_store root \<in> edge_step (EA_Assume bpos) (sink_store root)"
    by (simp add: root_def rec_defs s0_def enter_state_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ltr demo_gs rec_cfg UNIV"
    unfolding outer_def by (rule valid_ltr.intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None [] [], FunctionEntry pr, Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, call_enter demo_gs (CallEdge None [] []) (sink_store outer))]"
  have INNER: "inner \<in> valid_ltr demo_gs rec_cfg UNIV"
    unfolding inner_def by (rule valid_ltr.call[OF OUTER ecall])
  have si: "sink_node inner = FunctionEntry pr" by (simp add: inner_def)
  have ci: "caller_of inner = Some outer" by (simp add: inner_def)
  have co: "caller_of outer = None" by (simp add: outer_def root_def)
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  from OUTER INNER neq ci co so si show ?thesis by blast
qed


text \<open>Multiple returns: two distinct intra branches reach \<open>FunctionResult pf\<close>, both states
  occur in \<open>ltr_collect (FunctionResult pf)\<close>, and both resume through the same continuation.
  Built on \<^const>\<open>valid_ltr\<close> witness \<open>multi_return_join\<close>.\<close>
lemma ltr_collect_multi_return:
  "\<exists>s1 s2 r1 r2.
      s1 \<in> ltr_collect demo_gs mret_cfg UNIV (FunctionResult pf)
    \<and> s2 \<in> ltr_collect demo_gs mret_cfg UNIV (FunctionResult pf)
    \<and> r1 \<in> ltr_collect demo_gs mret_cfg UNIV (Statement 100)
    \<and> r2 \<in> ltr_collect demo_gs mret_cfg UNIV (Statement 100)"
proof -
  from multi_return_join obtain t1 t2 c1 c2 where
    T1: "t1 \<in> valid_ltr demo_gs mret_cfg UNIV" and T2: "t2 \<in> valid_ltr demo_gs mret_cfg UNIV"
    and sn1: "sink_node t1 = FunctionResult pf" and sn2: "sink_node t2 = FunctionResult pf"
    and R1: "Resume c1 t1 (path c1 @ [(Statement 100, combine_collect demo_gs None (sink_store c1) (sink_store t1))])
               \<in> valid_ltr demo_gs mret_cfg UNIV"
    and R2: "Resume c2 t2 (path c2 @ [(Statement 100, combine_collect demo_gs None (sink_store c2) (sink_store t2))])
               \<in> valid_ltr demo_gs mret_cfg UNIV"
    by blast
  have "sink_store t1 \<in> ltr_collect demo_gs mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T1] sn1 by simp
  moreover have "sink_store t2 \<in> ltr_collect demo_gs mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T2] sn2 by simp
  moreover have "combine_collect demo_gs None (sink_store c1) (sink_store t1)
                   \<in> ltr_collect demo_gs mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R1] by (simp add: sink_node_def sink_store_def)
  moreover have "combine_collect demo_gs None (sink_store c2) (sink_store t2)
                   \<in> ltr_collect demo_gs mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R2] by (simp add: sink_node_def sink_store_def)
  ultimately show ?thesis by blast
qed

text \<open>Recursion: two nested activations of \<open>pr\<close> are distinct structural traces; under the
  discriminating context \<open>key (\<lambda>_ c _. Suc c) 0\<close> (call depth) they receive distinct context
  keys.  Built on \<^const>\<open>valid_ltr\<close> witness \<open>recursion_nesting\<close>.\<close>
lemma ltr_collect_recursion_distinct_ctx:
  "\<exists>outer inner.
      outer \<in> valid_ltr demo_gs rec_cfg UNIV \<and> inner \<in> valid_ltr demo_gs rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> key (\<lambda>_ c _. Suc c) 0 outer \<noteq> key (\<lambda>_ c _. Suc c) 0 inner"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)((STR ''Gx'') := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ltr demo_gs rec_cfg UNIV" unfolding root_def by (rule valid_ltr.init) simp
  have rt_sn: "sink_node root = FunctionEntry pr" by (simp add: root_def rec_defs)
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    by (simp add: rt_sn rec_defs)
  have stepA: "sink_store root \<in> edge_step (EA_Assume bpos) (sink_store root)"
    by (simp add: root_def rec_defs s0_def enter_state_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ltr demo_gs rec_cfg UNIV"
    unfolding outer_def by (rule valid_ltr.intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None [] [], FunctionEntry pr, Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, call_enter demo_gs (CallEdge None [] []) (sink_store outer))]"
  have INNER: "inner \<in> valid_ltr demo_gs rec_cfg UNIV"
    unfolding inner_def by (rule valid_ltr.call[OF OUTER ecall])
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  have kouter: "key (\<lambda>_ c _. Suc c) 0 outer = 0" by (simp add: outer_def root_def)
  have kinner: "key (\<lambda>_ c _. Suc c) 0 inner = Suc 0"
    by (simp add: inner_def outer_def root_def)
  have "key (\<lambda>_ c _. Suc c) 0 outer \<noteq> key (\<lambda>_ c _. Suc c) 0 inner"
    using kouter kinner by simp
  then show ?thesis using OUTER INNER neq by blast
qed

text \<open>Flat CFG: for a \<open>calls = {}\<close> graph the collector agrees with ordinary intra
  reachability.  \<open>flat_demo\<close> is a two-edge straight line; both edge targets are collected
  exactly as intra propagation yields, and no call-derived activation exists.\<close>

definition flat_cfg :: "cfg \<Rightarrow> bool" where
  "flat_cfg g \<longleftrightarrow> calls g = {}"

text \<open>When \<open>calls g = {}\<close>, every valid trace is a \<^const>\<open>Root\<close>: no \<^const>\<open>Call\<close> or
  \<^const>\<open>Resume\<close> can arise.\<close>
lemma valid_ltr_flat_root:
  assumes "flat_cfg g" and "t \<in> valid_ltr gs g S"
  shows "\<exists>p. t = Root p"
  using assms(2)
proof (induction rule: valid_ltr.induct)
  case (intra t a v s')
  then obtain p where "t = Root p" by blast
  then show ?case by (cases t) auto
next
  case (call caller dst pars args p cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
next
  case (ret callee caller p dst pars args cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
qed simp

text \<open>Flat reduction: for \<open>calls g = {}\<close>, no call-derived activation exists, so
  collection is exactly the sink stores of root/intra traces.\<close>
lemma valid_ltr_flat_no_call:
  "flat_cfg g \<Longrightarrow> Call caller p \<notin> valid_ltr gs g S"
  using valid_ltr_flat_root by blast

definition flat_demo :: cfg where
  "flat_demo =
     \<lparr> intra = { (Statement 0, EA_Nop, Statement 1), (Statement 1, EA_Nop, Statement 2) },
       calls = {},
       cfg_entry = Statement 0,
       checks = {} \<rparr>"

lemma flat_demo_flat: "flat_cfg flat_demo"
  by (simp add: flat_cfg_def flat_demo_def)

lemma ltr_collect_flat_demo:
  fixes s0 :: store
  shows "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 0)"
    and "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 1)"
    and "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 2)"
proof -
  show c0: "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 0)"
    using ltr_collect_init[of s0 "{s0}" demo_gs flat_demo] by (simp add: flat_demo_def)
  have e0: "(Statement 0, EA_Nop, Statement 1) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show c1: "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 1)"
    using ltr_collect_intra_step[OF c0 e0] by simp
  have e1: "(Statement 1, EA_Nop, Statement 2) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show "s0 \<in> ltr_collect demo_gs flat_demo {s0} (Statement 2)"
    using ltr_collect_intra_step[OF c1 e1] by simp
qed

lemma ltr_collect_flat_demo_no_call:
  "Call caller p \<notin> valid_ltr demo_gs flat_demo S"
  using valid_ltr_flat_no_call[OF flat_demo_flat] by blast

end
