theory Procedure_Ownership
  imports Compile_Invariants "Voblint_CFG.LTR_Def"
begin

section \<open>Each procedure owns a disjoint block of nodes\<close>

text \<open>
  An activation's own local \<^const>\<open>path\<close> stays inside one compiled procedure fragment.  A
  \<^emph>\<open>fragment\<close> of procedure \<open>r\<close> compiled over \<open>[m, m')\<close> is \<^term>\<open>FunctionEntry r\<close>,
  \<^term>\<open>FunctionResult r\<close>, and the \<^term>\<open>Statement\<close> nodes in that counter range.  Every intra edge
  keeps both endpoints in one fragment, every call edge keeps its source and continuation there
  (the callee \<^term>\<open>FunctionEntry\<close> is the only cross-fragment endpoint), and distinct fragments are
  node-disjoint, so a single activation entered at \<^term>\<open>FunctionEntry p\<close> reaches
  \<^term>\<open>FunctionResult q\<close> only for \<open>p = q\<close>.
\<close>

definition pfn :: "pname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cfg_node set" where
  "pfn r m m' = insert (FunctionEntry r) (insert (FunctionResult r) (Statement ` {m..<m'}))"

lemma pfn_disjoint:
  "p \<noteq> r \<Longrightarrow> mp' \<le> m \<or> m' \<le> mp \<Longrightarrow> x \<in> pfn p mp mp' \<Longrightarrow> x \<notin> pfn r m m'"
  by (auto simp: pfn_def)

subsection \<open>Edges keep endpoints in one fragment\<close>

text \<open>At command level both endpoints lie in the fragment's own node set or are its
  continuation (\<open>compile_E_shape\<close>).  At procedure level the continuation is the epilogue node,
  which is inside the fragment's range, so the extra alternative collapses.\<close>

lemma compile_K_shape:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, ce, tgt, af) \<in> K
   \<Longrightarrow> (\<exists>j. u = Statement j) \<and> (\<exists>q. tgt = FunctionEntry q)
       \<and> (af = k \<or> (\<exists>j. af = Statement j))"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from Seq.prems(2) K show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1)
               = (n2, Statement (Suc n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  from If.prems(2) K show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] by auto
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and K: "K = K1"
    by (rule compile_WhileE)
  from While.prems(2) K show ?case using While.IH[OF c1] by auto
qed (auto split: if_splits option.splits)

lemma compile_intra_pfn:
  assumes cp: "compile \<Pi> p c k n = (n', en, E, K)" and e: "(u, a, v) \<in> E"
  shows "u \<in> insert k (pfn p n n') \<and> v \<in> insert k (pfn p n n')"
proof -
  have rng: "frag_stmts E K \<subseteq> {n..<n'} \<union> kstmt k" using compile_frag_stmts_range[OF cp] .
  from compile_E_shape[OF cp e] obtain ku where u: "u = Statement ku"
    and vshape: "v = k \<or> v = FunctionResult p \<or> (\<exists>kv. v = Statement kv)" by blast
  have "ku \<in> frag_stmts E K" using frag_stmts_E_srcI[of ku a v E] e u by simp
  hence uin: "u \<in> insert k (pfn p n n')" using rng u by (auto simp: pfn_def)
  have vin: "v \<in> insert k (pfn p n n')"
  proof (cases "v = k \<or> v = FunctionResult p")
    case True then show ?thesis by (auto simp: pfn_def)
  next
    case False
    then obtain kv where v: "v = Statement kv" using vshape by blast
    have "kv \<in> frag_stmts E K" using frag_stmts_E_tgtI[of u a kv E] e v by simp
    then show ?thesis using rng v False by (auto simp: pfn_def)
  qed
  from uin vin show ?thesis ..
qed

lemma compile_calls_pfn:
  assumes cp: "compile \<Pi> p c k n = (n', en, E, K)" and e: "(u, ce, tgt, af) \<in> K"
  shows "u \<in> insert k (pfn p n n') \<and> af \<in> insert k (pfn p n n')"
proof -
  have rng: "frag_stmts E K \<subseteq> {n..<n'} \<union> kstmt k" using compile_frag_stmts_range[OF cp] .
  from compile_K_shape[OF cp e] obtain ku where u: "u = Statement ku"
    and afshape: "af = k \<or> (\<exists>kaf. af = Statement kaf)" by blast
  have "ku \<in> frag_stmts E K" using frag_stmts_K_srcI[of ku ce tgt af K E] e u by simp
  hence uin: "u \<in> insert k (pfn p n n')" using rng u by (auto simp: pfn_def)
  have "af \<in> insert k (pfn p n n')"
  proof (cases "af = k")
    case True then show ?thesis by simp
  next
    case False
    then obtain kaf where af: "af = Statement kaf" using afshape by blast
    have "kaf \<in> frag_stmts E K" using frag_stmts_K_tgtI[of u ce tgt kaf K E] e af by simp
    then show ?thesis using rng af False by (auto simp: pfn_def)
  qed
  with uin show ?thesis ..
qed

text \<open>The entry wiring edge targets the first statement index of the fragment, which is what
  identifies a fragment by its start counter alone.\<close>
lemma compile_proc_entry_edge:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
  shows "(FunctionEntry p, EA_Body p, Statement n) \<in> E"
  using cp by auto

lemma compile_proc_intra_pfn:
  assumes cp: "compile_proc \<Pi> r decl n = (n', E, K)" and e: "(u, a, v) \<in> E"
  shows "u \<in> pfn r n n' \<and> v \<in> pfn r n n'"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> r (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry r, EA_Body r, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None r, FunctionResult r) Eb
               else Eb)"
    and n': "n' = Suc (n + csize (body decl))"
    by (rule compile_procE)
  have kin: "Statement (n + csize (body decl)) \<in> pfn r n n'"
    using n' by (auto simp: pfn_def)
  have entryin: "Statement n \<in> pfn r n n'"
    using n' csize_pos[of "body decl"] by (auto simp: pfn_def)
  have inner: "insert (Statement (n + csize (body decl)))
                 (pfn r n (n + csize (body decl))) \<subseteq> pfn r n n'"
    using n' by (auto simp: pfn_def)
  consider "(u, a, v) = (FunctionEntry r, EA_Body r, Statement n)"
    | "(u, a, v) = (Statement (n + csize (body decl)), EA_Ret None r, FunctionResult r)"
    | "(u, a, v) \<in> Eb"
    using e E by (auto split: if_splits)
  then show ?thesis
  proof cases
    case 1 then show ?thesis using entryin by (auto simp: pfn_def)
  next
    case 2 then show ?thesis using kin by (auto simp: pfn_def)
  next
    case 3 then show ?thesis using compile_intra_pfn[OF cb] inner by blast
  qed
qed

lemma compile_proc_calls_pfn:
  assumes cp: "compile_proc \<Pi> r decl n = (n', E, K)" and e: "(u, ce, tgt, af) \<in> K"
  shows "u \<in> pfn r n n' \<and> af \<in> pfn r n n'"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> r (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and n': "n' = Suc (n + csize (body decl))"
    by (rule compile_procE)
  have inner: "insert (Statement (n + csize (body decl)))
                 (pfn r n (n + csize (body decl))) \<subseteq> pfn r n n'"
    using n' by (auto simp: pfn_def)
  show ?thesis using compile_calls_pfn[OF cb e] inner by blast
qed

text \<open>A fragment of another procedure over a disjoint counter range sources none of its edges
  in \<open>pfn r m m'\<close>.\<close>
lemma compile_proc_src_notin_pfn:
  assumes cp: "compile_proc \<Pi> p decl mp = (mp', Ep, Kp)"
    and neq: "p \<noteq> r" and disjoint: "mp' \<le> m \<or> m' \<le> mp"
  shows "(u, a, v) \<in> Ep \<Longrightarrow> u \<notin> pfn r m m'"
    and "(u, ce, tgt, af) \<in> Kp \<Longrightarrow> u \<notin> pfn r m m'"
  using compile_proc_intra_pfn[OF cp] compile_proc_calls_pfn[OF cp] pfn_disjoint[OF neq disjoint]
  by blast+

lemma compile_procs_intra_src_notin_pfn:
  assumes cps: "compile_procs \<Pi> ps n = (n', E, K)" and e: "(u, a, v) \<in> E"
    and absent: "r \<notin> set ps" and disjoint: "n' \<le> m \<or> m' \<le> n"
  shows "u \<notin> pfn r m m'"
proof -
  from compile_procs_intra_origin[OF cps e] obtain p decl mp mp' Ep Kp
    where "p \<in> set ps" and cp: "compile_proc \<Pi> p decl mp = (mp', Ep, Kp)"
      and "n \<le> mp" "mp' \<le> n'" and ep: "(u, a, v) \<in> Ep" by blast
  have "p \<noteq> r" using \<open>p \<in> set ps\<close> absent by blast
  moreover have "mp' \<le> m \<or> m' \<le> mp" using \<open>n \<le> mp\<close> \<open>mp' \<le> n'\<close> disjoint by auto
  ultimately show ?thesis using compile_proc_src_notin_pfn(1)[OF cp _ _ ep] by blast
qed

lemma compile_procs_calls_src_notin_pfn:
  assumes cps: "compile_procs \<Pi> ps n = (n', E, K)" and e: "(u, ce, tgt, af) \<in> K"
    and absent: "r \<notin> set ps" and disjoint: "n' \<le> m \<or> m' \<le> n"
  shows "u \<notin> pfn r m m'"
proof -
  from compile_procs_calls_origin[OF cps e] obtain p decl mp mp' Ep Kp
    where "p \<in> set ps" and cp: "compile_proc \<Pi> p decl mp = (mp', Ep, Kp)"
      and "n \<le> mp" "mp' \<le> n'" and ep: "(u, ce, tgt, af) \<in> Kp" by blast
  have "p \<noteq> r" using \<open>p \<in> set ps\<close> absent by blast
  moreover have "mp' \<le> m \<or> m' \<le> mp" using \<open>n \<le> mp\<close> \<open>mp' \<le> n'\<close> disjoint by auto
  ultimately show ?thesis using compile_proc_src_notin_pfn(2)[OF cp _ _ ep] by blast
qed

subsection \<open>A procedure entry has a unique out-edge\<close>

text \<open>Within a compiled procedure only the entry wiring edge sources from \<^term>\<open>FunctionEntry\<close>
  (bodies source from \<^term>\<open>Statement\<close> nodes by \<open>compile_E_shape\<close>, the exit wiring from the exit
  \<^term>\<open>Statement\<close>), so the source name is the procedure and the target is unique.\<close>
lemma compile_proc_entry_mem:
  assumes cp: "compile_proc \<Pi> q decl n = (n', E, K)" and e: "(FunctionEntry r, a, v) \<in> E"
  shows "r = q"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> q (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry q, EA_Body q, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None q, FunctionResult q) Eb
               else Eb)"
    by (rule compile_procE)
  have "\<And>aa vv. (FunctionEntry r, aa, vv) \<notin> Eb" using compile_E_shape[OF cb] by blast
  then show ?thesis using e E by (auto split: if_splits)
qed

lemma compile_proc_entry_unique:
  assumes cp: "compile_proc \<Pi> q decl n = (n', E, K)"
    and e1: "(FunctionEntry r, a1, v1) \<in> E" and e2: "(FunctionEntry r, a2, v2) \<in> E"
  shows "v1 = v2"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> q (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry q, EA_Body q, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None q, FunctionResult q) Eb
               else Eb)"
    by (rule compile_procE)
  have nb: "\<And>aa vv. (FunctionEntry r, aa, vv) \<notin> Eb" using compile_E_shape[OF cb] by blast
  from e1 E nb have "v1 = Statement n" by (auto split: if_splits)
  moreover from e2 E nb have "v2 = Statement n" by (auto split: if_splits)
  ultimately show ?thesis by simp
qed

lemma compile_procs_entry_mem:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (FunctionEntry r, a, v) \<in> E \<Longrightarrow> r \<in> set ps"
  using compile_procs_intra_origin compile_proc_entry_mem by blast

text \<open>Under \<open>distinct ps\<close> a member's fragment owns every edge of the pass that sources in the
  member's nodes: the other members are compiled over disjoint counter ranges, and their
  edges stay in their own fragments.\<close>
lemma compile_procs_member_frag:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "distinct ps"
    and "r \<in> set ps" and "\<Pi> r = Some decl"
  shows "\<exists>m m' Er Kr. compile_proc \<Pi> r decl m = (m', Er, Kr) \<and> n \<le> m \<and> m' \<le> n'
           \<and> Er \<subseteq> E \<and> Kr \<subseteq> K
           \<and> (\<forall>u a v. (u, a, v) \<in> E \<longrightarrow> u \<in> pfn r m m' \<longrightarrow> (u, a, v) \<in> Er)
           \<and> (\<forall>u ce tgt af. (u, ce, tgt, af) \<in> K \<longrightarrow> u \<in> pfn r m m'
                \<longrightarrow> (u, ce, tgt, af) \<in> Kr)"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" "distinct qs" "r \<in> set qs"
      by auto
    from Cons.IH[OF this Cons.prems(4)] show ?thesis .
  next
    case (Some dq)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
        cp0: "compile_proc \<Pi> q dq n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and n': "n' = n2" and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    have qnotin: "q \<notin> set qs" and dqs: "distinct qs" using Cons.prems(2) by simp_all
    show ?thesis
    proof (cases "r = q")
      case True
      with Cons.prems(4) Some cp0 have cpr: "compile_proc \<Pi> r decl n = (n1, E0, K0)" by simp
      have rnotin: "r \<notin> set qs" using qnotin True by simp
      have tailE: "\<And>u a v. (u, a, v) \<in> E' \<Longrightarrow> u \<notin> pfn r n n1"
        using compile_procs_intra_src_notin_pfn[OF rest _ rnotin] by blast
      have tailK: "\<And>u ce tgt af. (u, ce, tgt, af) \<in> K' \<Longrightarrow> u \<notin> pfn r n n1"
        using compile_procs_calls_src_notin_pfn[OF rest _ rnotin] by blast
      have "\<forall>u a v. (u, a, v) \<in> E \<longrightarrow> u \<in> pfn r n n1 \<longrightarrow> (u, a, v) \<in> E0"
        using E tailE by blast
      moreover have "\<forall>u ce tgt af. (u, ce, tgt, af) \<in> K \<longrightarrow> u \<in> pfn r n n1
                       \<longrightarrow> (u, ce, tgt, af) \<in> K0"
        using K tailK by blast
      moreover have "n1 \<le> n'" using compile_procs_counter_mono[OF rest] n' by simp
      moreover have "E0 \<subseteq> E" "K0 \<subseteq> K" using E K by auto
      ultimately show ?thesis using cpr by blast
    next
      case False
      have rqs: "r \<in> set qs" using Cons.prems(3) False by simp
      from Cons.IH[OF rest dqs rqs Cons.prems(4)] obtain m m' Er Kr where
          cpr: "compile_proc \<Pi> r decl m = (m', Er, Kr)" and bnds: "n1 \<le> m" "m' \<le> n2"
        and sub: "Er \<subseteq> E'" "Kr \<subseteq> K'"
        and ownE: "\<forall>u a v. (u, a, v) \<in> E' \<longrightarrow> u \<in> pfn r m m' \<longrightarrow> (u, a, v) \<in> Er"
        and ownK: "\<forall>u ce tgt af. (u, ce, tgt, af) \<in> K' \<longrightarrow> u \<in> pfn r m m'
                     \<longrightarrow> (u, ce, tgt, af) \<in> Kr"
        by blast
      have qr: "q \<noteq> r" using False by simp
      have headE: "\<And>u a v. (u, a, v) \<in> E0 \<Longrightarrow> u \<notin> pfn r m m'"
        and headK: "\<And>u ce tgt af. (u, ce, tgt, af) \<in> K0 \<Longrightarrow> u \<notin> pfn r m m'"
        using compile_proc_src_notin_pfn[OF cp0 qr] bnds(1) by blast+
      have "\<forall>u a v. (u, a, v) \<in> E \<longrightarrow> u \<in> pfn r m m' \<longrightarrow> (u, a, v) \<in> Er"
        using E ownE headE by blast
      moreover have "\<forall>u ce tgt af. (u, ce, tgt, af) \<in> K \<longrightarrow> u \<in> pfn r m m'
                       \<longrightarrow> (u, ce, tgt, af) \<in> Kr"
        using K ownK headK by blast
      moreover have "n \<le> m" using compile_proc_counter_mono[OF cp0] bnds(1) by simp
      moreover have "m' \<le> n'" using bnds(2) n' by simp
      moreover have "Er \<subseteq> E" "Kr \<subseteq> K" using sub E K by auto
      ultimately show ?thesis using cpr by blast
    qed
  qed
qed

lemma compile_procs_entry_unique:
  assumes cps: "compile_procs \<Pi> ps n = (n', E, K)" and distinct: "distinct ps"
    and e1: "(FunctionEntry r, a1, v1) \<in> E" and e2: "(FunctionEntry r, a2, v2) \<in> E"
  shows "v1 = v2"
proof -
  from compile_procs_intra_origin[OF cps e1] obtain decl
    where rin: "r \<in> set ps" and decl: "\<Pi> r = Some decl"
    using compile_proc_entry_mem by blast
  from compile_procs_member_frag[OF cps distinct rin decl] obtain m m' Er Kr where
      cp: "compile_proc \<Pi> r decl m = (m', Er, Kr)"
    and own: "\<forall>u a v. (u, a, v) \<in> E \<longrightarrow> u \<in> pfn r m m' \<longrightarrow> (u, a, v) \<in> Er" by blast
  have "(FunctionEntry r, a1, v1) \<in> Er" "(FunctionEntry r, a2, v2) \<in> Er"
    using own e1 e2 by (auto simp: pfn_def)
  then show ?thesis by (rule compile_proc_entry_unique[OF cp])
qed

text \<open>In a whole compiled program \<^term>\<open>FunctionEntry r\<close> has a unique out-target: \<open>main\<close> and the
  callees are node-disjoint (\<open>prog_main_name \<notin> set ps\<close>), and each contributes a single entry edge.\<close>
lemma compile_prog_entry_out_unique:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and e1: "(FunctionEntry r, a1, v1) \<in> intra (compile_prog \<Pi> ps)"
    and e2: "(FunctionEntry r, a2, v2) \<in> intra (compile_prog \<Pi> ps)"
  shows "v1 = v2"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  have main_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> Emain \<Longrightarrow> r = prog_main_name"
    using compile_proc_entry_mem[OF mainc] by simp
  have procs_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> Eprocs \<Longrightarrow> r \<in> set ps"
    using compile_procs_entry_mem[OF procs] by simp
  show ?thesis
  proof (cases "r = prog_main_name")
    case True
    have "(FunctionEntry r, a1, v1) \<in> Emain" "(FunctionEntry r, a2, v2) \<in> Emain"
      using e1 e2 EI procs_mem True wf_compile_inputD(11)[OF wf] by auto
    then show ?thesis using compile_proc_entry_unique[OF mainc] by blast
  next
    case False
    have "(FunctionEntry r, a1, v1) \<in> Eprocs" "(FunctionEntry r, a2, v2) \<in> Eprocs"
      using e1 e2 EI main_mem False by auto
    then show ?thesis using compile_procs_entry_unique[OF procs wf_compile_inputD(9)[OF wf]]
      by blast
  qed
qed

subsection \<open>Whole-program edge shapes\<close>

text \<open>Two shape facts a consumer of a compiled graph may use without redoing the
  callee/\<open>main\<close> split: a call edge always leaves a \<^term>\<open>Statement\<close> node, and an entry edge
  names a procedure the table declares.  The first is a range property each pass has on its
  own; the second needs well-formed input, which is what ties the compiled procedure list
  back to the table.\<close>lemma compile_prog_calls_source_stmt:
  assumes "(u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps)"
  shows "\<exists>k. u = Statement k"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  from assms KC show ?thesis
    using compile_procs_calls_source_range[OF procs] compile_proc_calls_source_range[OF mainc]
    by blast
qed

lemma compile_prog_entry_declared:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and e: "(FunctionEntry p, a, v) \<in> intra (compile_prog \<Pi> ps)"
  shows "\<exists>d. \<Pi> p = Some d"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  from e EI consider "(FunctionEntry p, a, v) \<in> Eprocs" | "(FunctionEntry p, a, v) \<in> Emain"
    by auto
  then show ?thesis
  proof cases
    case 1
    then have "p \<in> set ps" using compile_procs_entry_mem[OF procs] by blast
    with wf_compile_inputD(10)[OF wf] show ?thesis by auto
  next
    case 2
    then have "p = prog_main_name" by (rule compile_proc_entry_mem[OF mainc])
    with wf_compile_inputD(2)[OF wf] show ?thesis by blast
  qed
qed

subsection \<open>Edges stay in the activation fragment\<close>

text \<open>The fragment a procedure's entry wiring identifies owns every edge of the program that
  sources in its nodes.  The callee pass and \<open>main\<close> occupy disjoint counter ranges, and inside
  the pass \<open>compile_procs_member_frag\<close> settles ownership; the entry edge pins the start counter
  through \<open>compile_prog_entry_out_unique\<close>.\<close>
lemma compile_prog_entry_frag:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)"
  shows "(\<forall>u a v. (u, a, v) \<in> intra (compile_prog \<Pi> ps) \<longrightarrow> u \<in> pfn r m m'
             \<longrightarrow> (u, a, v) \<in> Ep)
       \<and> (\<forall>u ce tgt af. (u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps)
             \<longrightarrow> u \<in> pfn r m m' \<longrightarrow> (u, ce, tgt, af) \<in> Kp)"
proof -
  let ?g = "compile_prog \<Pi> ps"
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra ?g = Eprocs \<union> Emain" and KC: "calls ?g = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have distinct: "distinct ps" and setps: "set ps = {p. \<Pi> p \<noteq> None} - {prog_main_name}"
    and main_notin: "prog_main_name \<notin> set ps"
    using wf_compile_inputD(9,10,11)[OF wf] by blast+
  show ?thesis
  proof (cases "r = prog_main_name")
    case True
    have dd: "d = \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
      using decl True wf_compile_inputD(2)[OF wf] by simp
    have entmain: "(FunctionEntry prog_main_name, EA_Body prog_main_name, Statement n1) \<in> intra ?g"
      using EI compile_proc_entry_edge[OF mainc] by simp
    have entr: "(FunctionEntry prog_main_name, EA_Body prog_main_name, Statement m) \<in> intra ?g"
      using ent True by simp
    have mn: "m = n1" using compile_prog_entry_out_unique[OF wf entr entmain] by simp
    have mout: "m' = n2" "Ep = Emain" "Kp = Kmain" using cb mainc True dd mn by simp_all
    show ?thesis unfolding True mn mout
      using EI KC compile_procs_intra_src_notin_pfn[OF procs _ main_notin]
        compile_procs_calls_src_notin_pfn[OF procs _ main_notin] by blast
  next
    case False
    have rin: "r \<in> set ps" using decl setps False by auto
    from compile_procs_member_frag[OF procs distinct rin decl] obtain m0 m0' Er Kr where
        cpr: "compile_proc \<Pi> r d m0 = (m0', Er, Kr)" and upper: "m0' \<le> n1"
      and Ersub: "Er \<subseteq> Eprocs"
      and ownE: "\<forall>u a v. (u, a, v) \<in> Eprocs \<longrightarrow> u \<in> pfn r m0 m0' \<longrightarrow> (u, a, v) \<in> Er"
      and ownK: "\<forall>u ce tgt af. (u, ce, tgt, af) \<in> Kprocs \<longrightarrow> u \<in> pfn r m0 m0'
                   \<longrightarrow> (u, ce, tgt, af) \<in> Kr"
      by blast
    have ent0: "(FunctionEntry r, EA_Body r, Statement m0) \<in> intra ?g"
      using EI Ersub compile_proc_entry_edge[OF cpr] by auto
    have mm: "m = m0" using compile_prog_entry_out_unique[OF wf ent ent0] by simp
    have mout: "m' = m0'" "Ep = Er" "Kp = Kr" using cb cpr mm by simp_all
    have neq: "prog_main_name \<noteq> r" using False by simp
    show ?thesis unfolding mm mout
      using EI KC ownE ownK compile_proc_src_notin_pfn[OF mainc neq] upper by blast
  qed
qed

text \<open>Given a genuine procedure fragment (declared body, entry wiring) and a node in it, every
  intra edge leaving that node, and every call leaving it, lands its same-activation successor
  back in the fragment.\<close>
lemma frag_edge_intra:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and uin: "u \<in> pfn r m m'"
    and e: "(u, a, v) \<in> intra (compile_prog \<Pi> ps)"
  shows "v \<in> pfn r m m'"
  using compile_prog_entry_frag[OF wf decl cb ent] compile_proc_intra_pfn[OF cb] uin e by blast

lemma frag_edge_calls:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and uin: "u \<in> pfn r m m'"
    and e: "(u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps)"
  shows "af \<in> pfn r m m'"
  using compile_prog_entry_frag[OF wf decl cb ent] compile_proc_calls_pfn[OF cb] uin e by blast

subsection \<open>Procedure locality of a valid activation\<close>

text \<open>Every declared procedure of a compiled program owns a fragment, identified by the start
  counter its entry wiring edge points at.\<close>
lemma compile_prog_proc_frag:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and decl: "\<Pi> q = Some d"
  obtains m m' Ep Kp where
    "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  show thesis
  proof (cases "q = prog_main_name")
    case True
    have dd: "d = \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
      using decl True wf_compile_inputD(2)[OF wf] by simp
    have "(FunctionEntry q, EA_Body q, Statement n1) \<in> intra (compile_prog \<Pi> ps)"
      using EI compile_proc_entry_edge[OF mainc] True by auto
    then show ?thesis using that[of n1 n2 Emain Kmain] mainc True dd by simp
  next
    case False
    have rin: "q \<in> set ps" using decl wf_compile_inputD(10)[OF wf] False by auto
    obtain m m' Ep Kp where cp0: "compile_proc \<Pi> q d m = (m', Ep, Kp)" and sub: "Ep \<subseteq> Eprocs"
      using compile_procs_member[OF procs rin decl] by blast
    have "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
      using EI sub compile_proc_entry_edge[OF cp0] by auto
    then show ?thesis using that cp0 by blast
  qed
qed

text \<open>\<open>frag_ok u\<close>: the activation \<open>u\<close> either lies wholly inside a genuine procedure fragment
  (declared body, entry wiring, all path nodes in the fragment) or is a single-node activation
  stuck at an undeclared \<^term>\<open>FunctionEntry\<close> --- which can never advance and never reaches a
  \<^term>\<open>FunctionResult\<close>.\<close>
definition frag_ok :: "proc_table \<Rightarrow> pname list \<Rightarrow> ltr \<Rightarrow> bool" where
  "frag_ok \<Pi> ps u \<longleftrightarrow>
     (\<exists>r d m m' Ep Kp. \<Pi> r = Some d
        \<and> compile_proc \<Pi> r d m = (m', Ep, Kp)
        \<and> (FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)
        \<and> fst (hd (path u)) = FunctionEntry r
        \<and> (\<forall>nd \<in> fst ` set (path u). nd \<in> pfn r m m'))
   \<or> (\<exists>p s. path u = [(FunctionEntry p, s)] \<and> \<Pi> p = None)"

lemma frag_okI_frag:
  assumes "\<Pi> r = Some d" "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    "(FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    "fst (hd (path u)) = FunctionEntry r"
    "\<And>nd. nd \<in> fst ` set (path u) \<Longrightarrow> nd \<in> pfn r m m'"
  shows "frag_ok \<Pi> ps u"
  unfolding frag_ok_def using assms by blast

lemma frag_okE [elim]:
  assumes "frag_ok \<Pi> ps u"
  obtains (frag) r d m m' Ep Kp where "\<Pi> r = Some d" "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    "(FunctionEntry r, EA_Body r, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    "fst (hd (path u)) = FunctionEntry r" "\<forall>nd \<in> fst ` set (path u). nd \<in> pfn r m m'"
  | (stub) p s where "path u = [(FunctionEntry p, s)]" "\<Pi> p = None"
  using assms unfolding frag_ok_def by meson

lemma sink_in_path_nodes:
  "t \<in> valid_ltr gs g S \<Longrightarrow> sink_node t \<in> fst ` set (path t)"
  using valid_ltr_path_nonempty by (auto simp: sink_node_def)

text \<open>Every activation in the caller chain of a valid trace is fragment-local.  The property is
  carried over the whole \<^const>\<open>callers\<close> chain so that the return case, which resumes the caller,
  can read the caller's own fragment (\<open>caller \<in> callers callee\<close>).\<close>
lemma valid_ltr_frag_callers:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and t: "t \<in> valid_ltr gs (compile_prog \<Pi> ps) S"
  shows "\<forall>u \<in> callers t. frag_ok \<Pi> ps u"
proof -
  let ?g = "compile_prog \<Pi> ps"
  show ?thesis
  proof (rule caller_chain_closure)
    fix s assume "s \<in> S"
    have main_decl: "\<Pi> prog_main_name = Some \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
      by (rule wf_compile_inputD(2)[OF wf])
    obtain m m' Ep Kp where
      cb: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> m = (m', Ep, Kp)"
      and ent: "(FunctionEntry prog_main_name, EA_Body prog_main_name, Statement m) \<in> intra ?g"
      by (rule compile_prog_proc_frag[OF wf main_decl])
    show "frag_ok \<Pi> ps (Root [(cfg_entry ?g, s)])"
      by (rule frag_okI_frag[OF main_decl cb ent])
         (simp_all add: pfn_def)
  next
    fix t a v s'
    assume ht: "t \<in> valid_ltr gs ?g S" and ch: "\<forall>u \<in> callers t. frag_ok \<Pi> ps u"
      and e: "(sink_node t, a, v) \<in> intra ?g"
    have "frag_ok \<Pi> ps t" using ch callers_refl by blast
    then show "frag_ok \<Pi> ps (extend t (v, s'))"
    proof (cases rule: frag_okE)
      case (frag r d m m' Ep Kp)
      have snk: "sink_node t \<in> pfn r m m'" using sink_in_path_nodes[OF ht] frag(5) by blast
      have v_in: "v \<in> pfn r m m'" using frag_edge_intra[OF wf frag(1,2,3) snk e] .
      have pne: "path t \<noteq> []" using valid_ltr_path_nonempty[OF ht] .
      show ?thesis
        by (rule frag_okI_frag[OF frag(1,2,3)])
           (use frag(4,5) pne v_in in \<open>auto simp: hd_append\<close>)
    next
      case (stub q s)
      have "sink_node t = FunctionEntry q" using stub(1) by (simp add: sink_node_def)
      then have "(FunctionEntry q, a, v) \<in> intra ?g" using e by simp
      from compile_prog_entry_declared[OF wf this] stub(2) show ?thesis by simp
    qed
  next
    fix caller dst pars args p cont
    assume e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    show "frag_ok \<Pi> ps (Call caller
            [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    proof (cases "\<Pi> p")
      case None
      then show ?thesis unfolding frag_ok_def by fastforce
    next
      case (Some d)
      obtain m m' Ep Kp where
        cb: "compile_proc \<Pi> p d m = (m', Ep, Kp)"
        and ent: "(FunctionEntry p, EA_Body p, Statement m) \<in> intra ?g"
        by (rule compile_prog_proc_frag[OF wf Some])
      show ?thesis
        by (rule frag_okI_frag[OF Some cb ent]) (simp_all add: pfn_def)
    qed
  next
    fix callee caller p dst pars args cont
    assume cvcallee: "callee \<in> valid_ltr gs ?g S"
      and ch: "\<forall>u \<in> callers callee. frag_ok \<Pi> ps u"
      and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
      and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    have cin: "caller \<in> callers callee" using cof callers_caller_subset callers_refl by blast
    have cv: "caller \<in> valid_ltr gs ?g S" using valid_ltr_caller_valid[OF cvcallee cof] .
    have "frag_ok \<Pi> ps caller" using ch cin by blast
    then show "frag_ok \<Pi> ps (Resume caller callee (path caller
            @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
    proof (cases rule: frag_okE)
      case (frag r d m m' Ep Kp)
      have snk: "sink_node caller \<in> pfn r m m'" using sink_in_path_nodes[OF cv] frag(5) by blast
      have cont_in: "cont \<in> pfn r m m'" using frag_edge_calls[OF wf frag(1,2,3) snk e] .
      have pne: "path caller \<noteq> []" using valid_ltr_path_nonempty[OF cv] .
      show ?thesis
        by (rule frag_okI_frag[OF frag(1,2,3)])
           (use frag(4,5) pne cont_in in \<open>auto simp: hd_append\<close>)
    next
      case (stub q s)
      have "sink_node caller = FunctionEntry q" using stub(1) by (simp add: sink_node_def)
      then have "(FunctionEntry q, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
        using e by simp
      with compile_prog_calls_source_stmt show ?thesis by blast
    qed
  next
    show "t \<in> valid_ltr gs ?g S" by (rule t)
  qed
qed

text \<open>An activation entered at \<^term>\<open>FunctionEntry p\<close> reaches \<^term>\<open>FunctionResult q\<close> only for
  \<open>p = q\<close>.\<close>
lemma valid_ltr_entry_result_eq:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and t: "t \<in> valid_ltr gs (compile_prog \<Pi> ps) S"
    and en: "fst (hd (path t)) = FunctionEntry p"
    and sk: "sink_node t = FunctionResult q"
  shows "p = q"
proof -
  have "frag_ok \<Pi> ps t"
    using valid_ltr_frag_callers[OF wf t] callers_refl by blast
  then show ?thesis
  proof (cases rule: frag_okE)
    case (frag r d m m' Ep Kp)
    have "sink_node t \<in> pfn r m m'" using sink_in_path_nodes[OF t] frag(5) by blast
    with frag(4) en sk show ?thesis by (auto simp: pfn_def)
  next
    case (stub p' s)
    then have "sink_node t = FunctionEntry p'" by (simp add: sink_node_def)
    with sk show ?thesis by simp
  qed
qed

end
