theory Live_Nodes
  imports Procedure_Ownership
begin

section \<open>Every node of a procedure reaches its result\<close>

text \<open>
  A procedure's nodes are the endpoints of its own intra edges and call continuations.
  Every edge out of one of them lands on another (\<open>prog_node_intra\<close>, \<open>prog_node_calls\<close>),
  and every one reaches \<^term>\<open>FunctionResult q\<close> along intra edges and
  call-site-to-continuation steps (\<open>prog_node_reaches\<close>) --- exactly the steps a routed
  equation reads backwards.  Code after a \<^const>\<open>Return\<close> is no exception: it still ends
  at the epilogue, whose return edge \<^const>\<open>compile_proc\<close> always emits.
\<close>

subsection \<open>The whole program\<close>

text \<open>
  Each declared procedure's fragment sits inside the compiled program, so its edges and
  their reachability carry over to the whole graph.
\<close>

lemma compile_prog_proc_frag_sub:
  assumes wf: "wf_compile_input \<G> \<Pi> ps" and decl: "\<Pi> q = Some d"
  obtains m m' Ep Kp where
    "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show thesis
  proof (cases "q = prog_main_name")
    case True
    have dd: "d = \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
      using decl True wf_compile_inputD(2)[OF wf] by simp
    have "(FunctionEntry q, EA_Body q, Statement n1) \<in> intra (compile_prog \<Pi> ps)"
      using EI compile_proc_entry_edge[OF mainc] True by auto
    then show ?thesis using that[of n1 n2 Emain Kmain] mainc True dd EI KC by simp
  next
    case False
    have rin: "q \<in> set ps" using decl wf_compile_inputD(10)[OF wf] False by auto
    from compile_procs_member_frag[OF procs wf_compile_inputD(9)[OF wf] rin decl]
    obtain m m' Ep Kp where cp0: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
        and sub: "Ep \<subseteq> Eprocs" "Kp \<subseteq> Kprocs"
      by blast
    have "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
      using EI sub compile_proc_entry_edge[OF cp0] by auto
    then show ?thesis using that cp0 sub EI KC by blast
  qed
qed


subsection \<open>Call targets are declared\<close>

text \<open>
  A call edge of a well-formed program enters only a declared procedure, so every callee
  has a fragment.
\<close>

lemma compile_calls_target_declared:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> wf_source_com \<Pi> c
   \<Longrightarrow> (u, ca, FunctionEntry q, k') \<in> K \<Longrightarrow> \<exists>d. \<Pi> q = Some d"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] Seq.prems(2,3) K by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] If.prems(2,3) K by auto
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and K: "K = K1"
    by (rule compile_WhileE)
  show ?case using While.IH[OF c1] While.prems(2,3) K by auto
qed (auto split: option.splits)

lemma compile_prog_calls_target_declared:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "\<exists>d. \<Pi> q = Some d"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  from e KC consider (P) "(u, ca, FunctionEntry q, k) \<in> Kprocs"
    | (M) "(u, ca, FunctionEntry q, k) \<in> Kmain"
    by auto
  then show ?thesis
  proof cases
    case P
    from compile_procs_calls_origin[OF procs P] obtain r decl m m' Ep Kp where
        decl: "\<Pi> r = Some decl" and cp: "compile_proc \<Pi> r decl m = (m', Ep, Kp)"
      and eK: "(u, ca, FunctionEntry q, k) \<in> Kp"
      by blast
    from cp obtain Eb where
        cb: "compile \<Pi> r (body decl) (Statement (m + csize (body decl))) m
               = (m + csize (body decl), Statement m, Eb, Kp)"
      by (rule compile_procE)
    have "wf_source_com \<Pi> (body decl)"
      using wf_compile_inputD(5)[OF wf decl] by (simp add: wf_proc_decl_def)
    from compile_calls_target_declared[OF cb this eK] show ?thesis .
  next
    case M
    from mainc obtain Eb where
        cb: "compile \<Pi> prog_main_name (main_body \<Pi>) (Statement (n1 + csize (main_body \<Pi>))) n1
               = (n1 + csize (main_body \<Pi>), Statement n1, Eb, Kmain)"
      by (rule compile_procE) simp
    from compile_calls_target_declared[OF cb wf_compile_inputD(3)[OF wf] M] show ?thesis .
  qed
qed

subsection \<open>Every compiled node reaches the continuation or the result\<close>

text \<open>
  A fragment's nodes all lead out of it: to its continuation or, along an explicit
  \<^const>\<open>Return\<close>, to the procedure result.  The induction needs no case split on
  whether the fragment can fall through.
\<close>

lemma compile_entry_reaches:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
  shows "local_reaches g en k \<or> local_reaches g en (FunctionResult p)"
  using compile_reaches_falls_through[OF assms] compile_reaches_returns[OF assms] by blast

lemma compile_src_reaches:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "(u, a, v) \<in> E \<or> (u, ca, ce, v) \<in> K"
  shows "local_reaches g u k \<or> local_reaches g u (FunctionResult p)"
  using assms
proof (induction c arbitrary: k n n' en E K u a v ca ce)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  have sub: "E1 \<subseteq> intra g" "K1 \<subseteq> calls g" "E2 \<subseteq> intra g" "K2 \<subseteq> calls g"
    using Seq.prems(2,3) E K by auto
  have mid: "local_reaches g (Statement (n + csize c1)) k
             \<or> local_reaches g (Statement (n + csize c1)) (FunctionResult p)"
    by (rule compile_entry_reaches[OF c2 sub(3,4)])
  from Seq.prems(4) E K consider "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    | "(u, a, v) \<in> E2 \<or> (u, ca, ce, v) \<in> K2"
    by blast
  then show ?case
  proof cases
    case 1
    from Seq.IH(1)[OF c1 sub(1,2) 1] mid show ?thesis
      by (blast intro: local_reaches_trans)
  next
    case 2
    from Seq.IH(2)[OF c2 sub(3,4) 2] show ?thesis .
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, if c1 = SKIP then k else Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, if c2 = SKIP then k else Statement (Suc n + csize c1))} \<union> (if c1 = SKIP then {} else E1) \<union> (if c2 = SKIP then {} else E2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  have subK: "K1 \<subseteq> calls g" "K2 \<subseteq> calls g" using If.prems(3) K by auto
  have subE1: "c1 \<noteq> SKIP \<Longrightarrow> E1 \<subseteq> intra g" and subE2: "c2 \<noteq> SKIP \<Longrightarrow> E2 \<subseteq> intra g"
    using If.prems(2) E by auto
  have K1_skip: "c1 = SKIP \<Longrightarrow> K1 = {}" using c1 by auto
  have K2_skip: "c2 = SKIP \<Longrightarrow> K2 = {}" using c2 by auto
  have e1: "c1 \<noteq> SKIP \<Longrightarrow> local_reaches g (Statement (Suc n)) k
             \<or> local_reaches g (Statement (Suc n)) (FunctionResult p)"
    using compile_entry_reaches[OF c1 subE1 subK(1)] by blast
  have e2: "c2 \<noteq> SKIP \<Longrightarrow> local_reaches g (Statement (Suc n + csize c1)) k
             \<or> local_reaches g (Statement (Suc n + csize c1)) (FunctionResult p)"
    using compile_entry_reaches[OF c2 subE2 subK(2)] by blast
  have head: "local_reaches g (Statement n) k \<or> local_reaches g (Statement n) (FunctionResult p)"
  proof (cases "c1 = SKIP")
    case True
    then show ?thesis using If.prems(2) E by (auto intro: local_reaches_intra_step)
  next
    case False
    have "(Statement n, EA_Assume b, Statement (Suc n)) \<in> intra g"
      using If.prems(2) E False by auto
    with e1[OF False] show ?thesis by (blast intro: local_reaches_intra_step)
  qed
  from If.prems(4) E K consider "u = Statement n"
    | "c1 \<noteq> SKIP" "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    | "c2 \<noteq> SKIP" "(u, a, v) \<in> E2 \<or> (u, ca, ce, v) \<in> K2"
    using K1_skip K2_skip by (auto split: if_splits)
  then show ?case
  proof cases
    case 1 then show ?thesis using head by simp
  next
    case 2 from If.IH(1)[OF c1 subE1[OF 2(1)] subK(1) 2(2)] show ?thesis .
  next
    case 3 from If.IH(2)[OF c2 subE2[OF 3(1)] subK(2) 3(2)] show ?thesis .
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = K1"
    by (rule compile_WhileE)
  have sub: "E1 \<subseteq> intra g" "K1 \<subseteq> calls g" using While.prems(2,3) E K by auto
  have exit: "local_reaches g (Statement n) k"
    using While.prems(2) E by (auto intro: local_reaches_intra_step)
  from While.prems(4) E K consider "u = Statement n" | "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    by blast
  then show ?case
  proof cases
    case 1 then show ?thesis using exit by simp
  next
    case 2
    from While.IH[OF c1 sub 2] exit show ?thesis by (blast intro: local_reaches_trans)
  qed
qed (auto split: option.splits intro: local_reaches_intra_step local_reaches_comb_step)

lemma compile_entry_src:
  assumes "compile \<Pi> p c k n = (n', en, E, K)"
  shows "(\<exists>a w. (Statement n, a, w) \<in> E) \<or> (\<exists>ca ce w. (Statement n, ca, ce, w) \<in> K)"
  using assms
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from Seq.IH(1)[OF c1] E K show ?case by blast
qed (auto simp: Let_def split: prod.splits option.splits)

lemma compile_tgt_src:
  assumes "compile \<Pi> p c k n = (n', en, E, K)"
    and "(u, a, v) \<in> E \<or> (u, ca, ce, v) \<in> K"
  shows "v = k \<or> v = FunctionResult p
         \<or> (\<exists>a' w. (v, a', w) \<in> E) \<or> (\<exists>ca' ce' w. (v, ca', ce', w) \<in> K)"
  using assms
proof (induction c arbitrary: k n n' en E K u a v ca ce)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from Seq.prems(2) E K consider "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    | "(u, a, v) \<in> E2 \<or> (u, ca, ce, v) \<in> K2"
    by blast
  then show ?case
  proof cases
    case 1
    from Seq.IH(1)[OF c1 1] compile_entry_src[OF c2] E K show ?thesis by blast
  next
    case 2
    from Seq.IH(2)[OF c2 2] E K show ?thesis by blast
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, if c1 = SKIP then k else Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, if c2 = SKIP then k else Statement (Suc n + csize c1))} \<union> (if c1 = SKIP then {} else E1) \<union> (if c2 = SKIP then {} else E2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  have K1_skip: "c1 = SKIP \<Longrightarrow> K1 = {}" using c1 by auto
  have K2_skip: "c2 = SKIP \<Longrightarrow> K2 = {}" using c2 by auto
  have s1:
    "c1 \<noteq> SKIP \<Longrightarrow> (\<exists>a w. (Statement (Suc n), a, w) \<in> E) \<or> (\<exists>ca ce w. (Statement (Suc n), ca, ce, w) \<in> K)"
    using compile_entry_src[OF c1] E K by auto
  have s2: "c2 \<noteq> SKIP \<Longrightarrow> (\<exists>a w. (Statement (Suc n + csize c1), a, w) \<in> E)
              \<or> (\<exists>ca ce w. (Statement (Suc n + csize c1), ca, ce, w) \<in> K)"
    using compile_entry_src[OF c2] E K by auto
  from If.prems(2) E K consider
      "u = Statement n" "v = (if c1 = SKIP then k else Statement (Suc n))"
    | "u = Statement n" "v = (if c2 = SKIP then k else Statement (Suc n + csize c1))"
    | "c1 \<noteq> SKIP" "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    | "c2 \<noteq> SKIP" "(u, a, v) \<in> E2 \<or> (u, ca, ce, v) \<in> K2"
    using K1_skip K2_skip by (auto split: if_splits)
  then show ?case
  proof cases
    case 1 then show ?thesis using s1 by (auto split: if_splits)
  next
    case 2 then show ?thesis using s2 by (auto split: if_splits)
  next
    case 3 from If.IH(1)[OF c1 3(2)] E K 3(1) show ?thesis by auto
  next
    case 4 from If.IH(2)[OF c2 4(2)] E K 4(1) show ?thesis by auto
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = K1"
    by (rule compile_WhileE)
  have s1: "(\<exists>a w. (Statement (Suc n), a, w) \<in> E) \<or> (\<exists>ca ce w. (Statement (Suc n), ca, ce, w) \<in> K)"
    using compile_entry_src[OF c1] E K by auto
  from While.prems(2) E K consider "u = Statement n" "v = Statement (Suc n)"
    | "u = Statement n" "v = k" | "(u, a, v) \<in> E1 \<or> (u, ca, ce, v) \<in> K1"
    by blast
  then show ?case
  proof cases
    case 1 then show ?thesis using s1 by simp
  next
    case 2 then show ?thesis by simp
  next
    case 3 from While.IH[OF c1 3] E K show ?thesis by blast
  qed
qed (auto split: option.splits)

subsection \<open>A procedure's nodes\<close>

text \<open>
  The endpoints of a procedure's own intra edges and call continuations.  Sources reach
  the continuation or the result by \<open>compile_src_reaches\<close>; a target is the
  continuation, the result, or itself a source (\<open>compile_tgt_src\<close>); and the
  continuation of a procedure body is the epilogue, whose return edge is unconditional.
\<close>

definition proc_nodes ::
  "(cfg_node \<times> edge_action \<times> cfg_node) set
   \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set \<Rightarrow> cfg_node set"
where
  "proc_nodes E K =
     {u. \<exists>a v. (u, a, v) \<in> E} \<union> {v. \<exists>u a. (u, a, v) \<in> E}
   \<union> {u. \<exists>ca ce k. (u, ca, ce, k) \<in> K} \<union> {k. \<exists>u ca ce. (u, ca, ce, k) \<in> K}"

lemma compile_proc_node_reaches:
  assumes cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and Ep: "Ep \<subseteq> intra g" and Kp: "Kp \<subseteq> calls g"
    and x: "x \<in> proc_nodes Ep Kp"
  shows "local_reaches g x (FunctionResult q)"
proof -
  let ?r = "Statement (m + csize (body d))"
  from cp obtain Eb where
      cb: "compile \<Pi> q (body d) ?r m = (m + csize (body d), Statement m, Eb, Kp)"
    and E: "Ep = insert (FunctionEntry q, EA_Body q, Statement m)
                  (insert (?r, EA_Ret None q, FunctionResult q) Eb)"
    by (rule compile_procE)
  have Eb: "Eb \<subseteq> intra g" using E Ep by auto
  have epi: "local_reaches g ?r (FunctionResult q)"
    using E Ep by (auto intro: local_reaches_intra_step)
  have srcE: "local_reaches g u (FunctionResult q)" if "(u, a, v) \<in> Eb" for u a v
    using compile_src_reaches[OF cb Eb Kp, of u a v] that epi local_reaches_trans by blast
  have srcK: "local_reaches g u (FunctionResult q)" if "(u, ca, ce, v) \<in> Kp" for u ca ce v
    using compile_src_reaches[OF cb Eb Kp, of u _ v ca ce] that epi local_reaches_trans by blast
  have src_of: "local_reaches g v (FunctionResult q)"
    if
      "v = ?r \<or> v = FunctionResult q \<or> (\<exists>a' w. (v, a', w) \<in> Eb) \<or> (\<exists>ca' ce' w. (v, ca', ce', w) \<in> Kp)"
    for v
    using that epi srcE srcK by auto
  have tgtE: "local_reaches g v (FunctionResult q)" if "(u, a, v) \<in> Eb" for u a v
    using compile_tgt_src[OF cb, of u a v] that src_of by blast
  have tgtK: "local_reaches g v (FunctionResult q)" if "(u, ca, ce, v) \<in> Kp" for u ca ce v
    using compile_tgt_src[OF cb, of u _ v ca ce] that src_of by blast
  have body: "local_reaches g (Statement m) (FunctionResult q)"
    using compile_entry_src[OF cb] srcE srcK by blast
  have ent: "local_reaches g (FunctionEntry q) (FunctionResult q)"
    by (rule compile_proc_reaches_result[OF cp Ep Kp])
  from x show ?thesis
    unfolding proc_nodes_def E using srcE srcK tgtE tgtK epi body ent by auto
qed

lemma proc_nodes_pfn:
  assumes cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)" and x: "x \<in> proc_nodes Ep Kp"
  shows "x \<in> pfn q m m'"
  using x compile_proc_intra_pfn[OF cp] compile_proc_calls_pfn[OF cp]
  unfolding proc_nodes_def by blast

definition prog_node :: "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "prog_node \<Pi> ps q x \<longleftrightarrow>
     (\<exists>d m m' Ep Kp. \<Pi> q = Some d \<and> compile_proc \<Pi> q d m = (m', Ep, Kp)
        \<and> (FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)
        \<and> Ep \<subseteq> intra (compile_prog \<Pi> ps) \<and> Kp \<subseteq> calls (compile_prog \<Pi> ps)
        \<and> x \<in> proc_nodes Ep Kp)"

lemma prog_node_entry:
  assumes wf: "wf_compile_input \<G> \<Pi> ps" and decl: "\<Pi> q = Some d"
  shows "prog_node \<Pi> ps q (FunctionEntry q)"
proof -
  from compile_prog_proc_frag_sub[OF wf decl] obtain m m' Ep Kp where
      cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    by blast
  have "FunctionEntry q \<in> proc_nodes Ep Kp"
    using compile_proc_entry_edge[OF cp] unfolding proc_nodes_def by blast
  then show ?thesis unfolding prog_node_def using decl cp ent sub by blast
qed

lemma prog_node_result:
  "prog_node \<Pi> ps q x \<Longrightarrow> prog_node \<Pi> ps q (FunctionResult q)"
proof -
  assume "prog_node \<Pi> ps q x"
  then obtain d m m' Ep Kp where
      decl: "\<Pi> q = Some d" and cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    unfolding prog_node_def by auto
  from cp have "(Statement (m + csize (body d)), EA_Ret None q, FunctionResult q) \<in> Ep"
    by (rule compile_procE) simp
  then have "FunctionResult q \<in> proc_nodes Ep Kp" unfolding proc_nodes_def by blast
  then show ?thesis unfolding prog_node_def using decl cp ent sub by blast
qed

lemma prog_node_reaches:
  "prog_node \<Pi> ps q x \<Longrightarrow> local_reaches (compile_prog \<Pi> ps) x (FunctionResult q)"
  unfolding prog_node_def using compile_proc_node_reaches by auto

lemma prog_node_intra:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and u: "prog_node \<Pi> ps q u" and e: "(u, a, v) \<in> intra (compile_prog \<Pi> ps)"
  shows "prog_node \<Pi> ps q v"
proof -
  from u obtain d m m' Ep Kp where
      decl: "\<Pi> q = Some d" and cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    and un: "u \<in> proc_nodes Ep Kp"
    unfolding prog_node_def by auto
  have "(u, a, v) \<in> Ep"
    using compile_prog_entry_frag[OF wf decl cp ent] proc_nodes_pfn[OF cp un] e by blast
  then have "v \<in> proc_nodes Ep Kp" unfolding proc_nodes_def by blast
  then show ?thesis unfolding prog_node_def using decl cp ent sub by blast
qed

lemma prog_node_calls:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and u: "prog_node \<Pi> ps q u" and e: "(u, ca, ce, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "prog_node \<Pi> ps q k"
proof -
  from u obtain d m m' Ep Kp where
      decl: "\<Pi> q = Some d" and cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    and un: "u \<in> proc_nodes Ep Kp"
    unfolding prog_node_def by auto
  have "(u, ca, ce, k) \<in> Kp"
    using compile_prog_entry_frag[OF wf decl cp ent] proc_nodes_pfn[OF cp un] e by blast
  then have "k \<in> proc_nodes Ep Kp" unfolding proc_nodes_def by blast
  then show ?thesis unfolding prog_node_def using decl cp ent sub by blast
qed

lemma prog_node_main_entry:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
  shows "prog_node \<Pi> ps prog_main_name (cfg_entry (compile_prog \<Pi> ps))"
  using prog_node_entry[OF wf wf_compile_inputD(2)[OF wf]] by simp

lemma prog_node_callee_entry:
  assumes wf: "wf_compile_input \<G> \<Pi> ps"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "prog_node \<Pi> ps q (FunctionEntry q)"
  using compile_prog_calls_target_declared[OF wf e] prog_node_entry[OF wf] by blast

end
