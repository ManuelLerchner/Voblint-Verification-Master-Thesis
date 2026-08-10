theory Compile_Locality
  imports Compile_Certificate CFG_Local_Trace
begin

section \<open>Procedure locality of a valid activation\<close>

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


subsection \<open>Edge node shapes\<close>

text \<open>The command-level shapes come from the compiler theory: an intra edge sources at a
  \<^term>\<open>Statement\<close> and targets a \<^term>\<open>Statement\<close>, the own \<^term>\<open>FunctionResult p\<close>, or the
  fragment's continuation (\<open>compile_E_shape\<close>).  The continuation alternative is the only
  addition of continuation passing, and it disappears at procedure level, where the
  continuation is the epilogue \<^term>\<open>Statement\<close> node inside the procedure's own range.\<close>

text \<open>A compiled body reaches a result node only through a return action for the same
  procedure --- provided the fragment's continuation is not itself a result node, which holds
  for every procedure body (its continuation is the epilogue).\<close>
lemma compile_result_target:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, a, FunctionResult q) \<in> E
   \<Longrightarrow> \<forall>r. k \<noteq> FunctionResult r \<Longrightarrow> q = p \<and> (\<exists>e. a = EA_Ret e p)"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from Seq.prems(2) E consider "(u, a, FunctionResult q) \<in> E1"
    | "(u, a, FunctionResult q) \<in> E2" by auto
  then show ?case
  proof cases
    case 1 then show ?thesis using Seq.IH(1)[OF c1] by simp
  next
    case 2 then show ?thesis using Seq.IH(2)[OF c2] Seq.prems(3) by simp
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1)
               = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from If.prems(2) E consider "(u, a, FunctionResult q) \<in> E1"
    | "(u, a, FunctionResult q) \<in> E2" by auto
  then show ?case
  proof cases
    case 1 then show ?thesis using If.IH(1)[OF c1] If.prems(3) by simp
  next
    case 2 then show ?thesis using If.IH(2)[OF c2] If.prems(3) by simp
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (rule compile_WhileE)
  from While.prems(2,3) E have "(u, a, FunctionResult q) \<in> E1" by auto
  then show ?case using While.IH[OF c1] by simp
qed (auto split: option.splits)

text \<open>A call edge sources at a \<^term>\<open>Statement\<close>, targets a \<^term>\<open>FunctionEntry\<close>, and continues
  at a \<^term>\<open>Statement\<close> or at the fragment's continuation.\<close>
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
qed (auto split: if_splits)

text \<open>Source well-formedness ensures that every compiled call enters a declared procedure.\<close>
lemma compile_call_target_declared:
  assumes comp: "compile \<Pi> p c k n = (n', en, E, K)"
    and wf: "wf_source_com \<Pi> c"
    and edge: "(u, ce, FunctionEntry q, af) \<in> K"
  shows "\<Pi> q \<noteq> None"
  using comp wf edge
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits option.splits)

subsection \<open>Edges keep endpoints in one fragment\<close>

text \<open>Command level: both endpoints lie in the fragment's own node set or are its
  continuation.  At procedure level (below) the continuation is the epilogue node, which is
  inside the fragment's range, so the extra alternative collapses and the procedure-level
  statements are exactly the fragment-locality ones the activation proofs use.\<close>

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

text \<open>The procedure wrapper keeps its wiring edges (entry \<^term>\<open>EA_Nop\<close>, fall-through
  \<^term>\<open>EA_Ret None\<close>) and body edges in the procedure fragment.\<close>
lemma compile_proc_entry_target:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(FunctionEntry p, EA_Nop, en) \<in> E"
  shows "en = Statement n"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
               else Eb)"

    by (rule compile_procE)
  have body: "\<And>a v. (FunctionEntry p, a, v) \<notin> Eb"
    using compile_E_shape[OF cb] by blast
  from e E body show ?thesis by (auto split: if_splits)

qed

text \<open>The entry wiring edge of a compiled procedure targets the first statement index of its
  fragment.  This is the shape that identifies a fragment by its start counter alone.\<close>
lemma compile_proc_entry_edge:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
  shows "(FunctionEntry p, EA_Nop, Statement n) \<in> E"
proof -
  from cp obtain Eb where
    E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
               else Eb)"

    by (rule compile_procE)
  show ?thesis using E by simp
qed

lemma compile_proc_intra_pfn:
  assumes cp: "compile_proc \<Pi> r decl n = (n', E, K)" and e: "(u, a, v) \<in> E"
  shows "u \<in> pfn r n n' \<and> v \<in> pfn r n n'"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> r (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry r, EA_Nop, Statement n)
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
  consider "(u, a, v) = (FunctionEntry r, EA_Nop, Statement n)"
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

text \<open>The procedure wrapper preserves the body's result discipline and adds the matching
  fall-through return.\<close>
lemma compile_proc_result_target:
  assumes comp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and edge: "(u, a, FunctionResult q) \<in> E"
  shows "q = p \<and> (\<exists>e. a = EA_Ret e p)"
proof -
  from comp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
               else Eb)"
    by (rule compile_procE)
  show ?thesis using edge E compile_result_target[OF cb] by (auto split: if_splits)

qed

lemma compile_proc_call_target_declared:
  assumes comp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and wf: "wf_proc_decl source_global \<Pi> decl"
    and edge: "(u, ce, FunctionEntry q, af) \<in> K"
  shows "\<Pi> q \<noteq> None"
proof -
  from comp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    by (rule compile_procE)
  show ?thesis
    using compile_call_target_declared[OF cb _ edge] wf by (simp add: wf_proc_decl_def)
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

lemma compile_proc_counter_mono: "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> n \<le> n'"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_counter_mono)

subsection \<open>Each declared procedure occupies a sub-range\<close>

text \<open>A declared member of a \<^const>\<open>compile_procs\<close> pass is compiled at some offset inside the
  pass's counter range \<open>[n, n')\<close>, with its edges included.\<close>
lemma compile_procs_member:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> p \<in> set ps \<Longrightarrow> \<Pi> p = Some decl
   \<Longrightarrow> \<exists>m m' Ep Kp. compile_proc \<Pi> p decl m = (m', Ep, Kp)
        \<and> n \<le> m \<and> m' \<le> n' \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems(2,3) have pqs: "p \<in> set qs" by auto
    from None Cons.prems(1) have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this pqs Cons.prems(3)] show ?thesis .
  next
    case (Some declq)
    obtain n1 Eq Kq where cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      by (metis prod_cases3)
    obtain n2 E' K' where crest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      by (metis prod_cases3)
    from Cons.prems(1) Some cq crest
    have EK: "n' = n2" "E = Eq \<union> E'" "K = Kq \<union> K'" by (simp_all add: Let_def)
    have n_n1: "n \<le> n1" using compile_proc_counter_mono[OF cq] .
    have n1_n2: "n1 \<le> n2" using compile_procs_counter_mono[OF crest] .
    show ?thesis
    proof (cases "p = q")
      case True
      with Cons.prems(3) Some have "decl = declq" by simp
      with cq True have "compile_proc \<Pi> p decl n = (n1, Eq, Kq)" by simp
      moreover have "n \<le> n" "n1 \<le> n'" "Eq \<subseteq> E" "Kq \<subseteq> K" using EK n1_n2 by auto
      ultimately show ?thesis by blast
    next
      case False
      with Cons.prems(2) have "p \<in> set qs" by simp
      from Cons.IH[OF crest this Cons.prems(3)] obtain m m' Ep Kp
        where cpm: "compile_proc \<Pi> p decl m = (m', Ep, Kp)"
          and bnds: "n1 \<le> m" "m' \<le> n2" and sub: "Ep \<subseteq> E'" "Kp \<subseteq> K'" by blast
      have "n \<le> m" using n_n1 bnds(1) by simp
      moreover have "m' \<le> n'" using bnds(2) EK by simp
      moreover have "Ep \<subseteq> E" "Kp \<subseteq> K" using sub EK by auto
      ultimately show ?thesis using cpm by blast
    qed
  qed
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
    and E: "E = insert (FunctionEntry q, EA_Nop, Statement n)
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
    and E: "E = insert (FunctionEntry q, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None q, FunctionResult q) Eb
               else Eb)"
    by (rule compile_procE)
  have nb: "\<And>aa vv. (FunctionEntry r, aa, vv) \<notin> Eb" using compile_E_shape[OF cb] by blast
  from e1 E nb have "v1 = Statement n" by (auto split: if_splits)
  moreover from e2 E nb have "v2 = Statement n" by (auto split: if_splits)

  ultimately show ?thesis by simp
qed

text \<open>A \<^const>\<open>compile_procs\<close> pass sources a \<^term>\<open>FunctionEntry r\<close> edge only for a member \<open>r\<close>.\<close>
lemma compile_procs_entry_mem:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (FunctionEntry r, a, v) \<in> E \<Longrightarrow> r \<in> set ps"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems(1) have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this Cons.prems(2)] show ?thesis by simp
  next
    case (Some d)
    obtain n1 Eq Kq where cq: "compile_proc \<Pi> q d n = (n1, Eq, Kq)" by (metis prod_cases3)
    obtain n2 E' K' where cr: "compile_procs \<Pi> qs n1 = (n2, E', K')" by (metis prod_cases3)
    from Cons.prems(1) Some cq cr have E: "E = Eq \<union> E'" by (simp add: Let_def)
    from Cons.prems(2) E consider "(FunctionEntry r, a, v) \<in> Eq" | "(FunctionEntry r, a, v) \<in> E'"
      by auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using compile_proc_entry_mem[OF cq] by simp
    next
      case 2 then show ?thesis using Cons.IH[OF cr] by simp
    qed
  qed
qed

text \<open>Under \<open>distinct ps\<close> each \<^term>\<open>FunctionEntry r\<close> has a unique out-target in the pass.\<close>
lemma compile_procs_entry_unique:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> distinct ps
   \<Longrightarrow> (FunctionEntry r, a1, v1) \<in> E \<Longrightarrow> (FunctionEntry r, a2, v2) \<in> E \<Longrightarrow> v1 = v2"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems(1) have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this _ Cons.prems(3,4)] Cons.prems(2) show ?thesis by simp
  next
    case (Some d)
    obtain n1 Eq Kq where cq: "compile_proc \<Pi> q d n = (n1, Eq, Kq)" by (metis prod_cases3)
    obtain n2 E' K' where cr: "compile_procs \<Pi> qs n1 = (n2, E', K')" by (metis prod_cases3)
    from Cons.prems(1) Some cq cr have E: "E = Eq \<union> E'" by (simp add: Let_def)
    have qnotin: "q \<notin> set qs" using Cons.prems(2) by simp
    have inEq_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> Eq \<Longrightarrow> r = q"
      using compile_proc_entry_mem[OF cq] by simp
    have inE'_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> E' \<Longrightarrow> r \<in> set qs"
      using compile_procs_entry_mem[OF cr] by simp
    from Cons.prems(3) E have r1: "(FunctionEntry r, a1, v1) \<in> Eq \<or> (FunctionEntry r, a1, v1) \<in> E'"
      by auto
    from Cons.prems(4) E have r2: "(FunctionEntry r, a2, v2) \<in> Eq \<or> (FunctionEntry r, a2, v2) \<in> E'"
      by auto
    show ?thesis
    proof (cases "(FunctionEntry r, a1, v1) \<in> Eq")
      case True
      then have rq: "r = q" using inEq_mem by blast
      have "(FunctionEntry r, a2, v2) \<in> Eq"
        using r2 rq qnotin inE'_mem by blast
      with True show ?thesis using compile_proc_entry_unique[OF cq] by blast
    next
      case False
      then have inE1': "(FunctionEntry r, a1, v1) \<in> E'" using r1 by blast
      then have rqs: "r \<in> set qs" using inE'_mem by blast
      have "(FunctionEntry r, a2, v2) \<in> E'"
        using r2 rqs inEq_mem qnotin by blast
      with inE1' show ?thesis using Cons.IH[OF cr _ ] Cons.prems(2) by simp
    qed
  qed
qed

text \<open>Decomposition of a whole compiled program into the callee pass and the \<open>main\<close> fragment.\<close>
lemma compile_prog_intra_split:
  obtains n1 Eprocs Kprocs n2 Emain Kmain where
    "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
proof -
  obtain n1 Eprocs Kprocs where procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (metis prod_cases3)
  obtain n2 Emain Kmain
    where mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain
      \<and> calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    unfolding compile_prog_def by (simp add: procs mainc Let_def)
  with procs mainc show ?thesis using that by blast
qed

text \<open>In a whole compiled program \<^term>\<open>FunctionEntry r\<close> has a unique out-target: \<open>main\<close> and the
  callees are node-disjoint (\<open>mnm \<notin> set ps\<close>), and each contributes a single entry edge.\<close>
lemma compile_prog_entry_out_unique:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and e1: "(FunctionEntry r, a1, v1) \<in> intra (compile_prog \<Pi> ps mnm main)"
    and e2: "(FunctionEntry r, a2, v2) \<in> intra (compile_prog \<Pi> ps mnm main)"
  shows "v1 = v2"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and gi: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  have distinct: "distinct ps" and mnmnotin: "mnm \<notin> set ps"
    using wf unfolding wf_compile_input_def by auto
  have main_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> Emain \<Longrightarrow> r = mnm"
    using compile_proc_entry_mem[OF mainc] by simp
  have procs_mem: "\<And>b w. (FunctionEntry r, b, w) \<in> Eprocs \<Longrightarrow> r \<in> set ps"
    using compile_procs_entry_mem[OF procs] by simp
  show ?thesis
  proof (cases "r = mnm")
    case True
    have "(FunctionEntry r, a1, v1) \<in> Emain" "(FunctionEntry r, a2, v2) \<in> Emain"
      using e1 e2 gi procs_mem True mnmnotin by auto
    then show ?thesis using compile_proc_entry_unique[OF mainc] by blast
  next
    case False
    have "(FunctionEntry r, a1, v1) \<in> Eprocs" "(FunctionEntry r, a2, v2) \<in> Eprocs"
      using e1 e2 gi main_mem False by auto
    then show ?thesis using compile_procs_entry_unique[OF procs distinct] by blast
  qed
qed

subsection \<open>Whole-program edge shapes\<close>

text \<open>No intra edge sources from a \<^term>\<open>FunctionResult\<close>, a call sources from a \<^term>\<open>Statement\<close>,
  and a \<^term>\<open>FunctionEntry\<close> out-edge belongs to a declared procedure.\<close>
lemma compile_proc_no_result_source:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(FunctionResult r, a, v) \<in> E"
  shows False
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
               else Eb)"
    by (rule compile_procE)
  have body: "\<And>b w. (FunctionResult r, b, w) \<notin> Eb"
    using compile_E_shape[OF cb] by blast
  show False using e E body by (auto split: if_splits)

qed

lemma compile_procs_no_result_source:
  assumes cp: "compile_procs \<Pi> ps n = (n', E, K)"
    and e: "(FunctionResult r, a, v) \<in> E"
  shows False
  using cp e
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons.prems have "compile_procs \<Pi> ps n = (n', E, K)" by simp
    then show ?thesis using Cons.IH Cons.prems(2) by blast
  next
    case (Some decl)
    obtain n1 E0 K0 n2 E' K' where cp0: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'"
      using Cons.prems(1) Some by (auto split: prod.splits)
    from Cons.prems(2) E consider "(FunctionResult r, a, v) \<in> E0"
      | "(FunctionResult r, a, v) \<in> E'" by auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using compile_proc_no_result_source[OF cp0] by blast
    next
      case 2 then show ?thesis using Cons.IH[OF rest] by blast
    qed
  qed
qed

lemma compile_procs_result_target:
  assumes comp: "compile_procs \<Pi> ps n = (n', E, K)"
    and edge: "(u, a, FunctionResult q) \<in> E"
  shows "\<exists>e. a = EA_Ret e q"
  using comp edge
  by (induction ps arbitrary: n n' E K)
     (auto split: option.splits prod.splits dest: compile_proc_result_target)

lemma compile_prog_result_target:
  assumes edge: "(u, a, FunctionResult q) \<in> intra (compile_prog \<Pi> ps mnm main)"
  shows "\<exists>e. a = EA_Ret e q"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and E: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  from edge E consider "(u, a, FunctionResult q) \<in> Eprocs"
    | "(u, a, FunctionResult q) \<in> Emain" by auto
  then show ?thesis
  proof cases
    case 1
    show ?thesis by (rule compile_procs_result_target[OF procs 1])
  next
    case 2
    show ?thesis using compile_proc_result_target[OF mainc 2] by blast
  qed
qed

lemma compile_prog_no_result_source:
  "(FunctionResult r, a, v) \<notin> intra (compile_prog \<Pi> ps mnm main)"
proof (rule notI)
  assume e: "(FunctionResult r, a, v) \<in> intra (compile_prog \<Pi> ps mnm main)"
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and E: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  from e E consider "(FunctionResult r, a, v) \<in> Eprocs"
    | "(FunctionResult r, a, v) \<in> Emain" by auto
  then show False
  proof cases
    case 1
    then show False using compile_procs_no_result_source[OF procs] by blast
  next
    case 2
    then show False using compile_proc_no_result_source[OF mainc] by blast
  qed
qed

lemma compile_proc_calls_source_stmt:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(u, ce, tgt, af) \<in> K"
  shows "\<exists>k. u = Statement k"
proof -
  from cp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
           = (n + csize (body decl), Statement n, Eb, K)"
    by (rule compile_procE)
  show ?thesis using compile_K_shape[OF cb e] by blast
qed

(* A calls-source is always a Statement, never FunctionEntry/FunctionResult; downstream
   proofs obtain the witness directly instead of case-splitting on u and reproving the
   two dead cases false each time. *)
lemma compile_proc_calls_source_stmtE:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(u, ce, tgt, af) \<in> K"
  obtains k where "u = Statement k"
  using compile_proc_calls_source_stmt[OF cp e] by blast

lemma compile_procs_calls_source_stmt:
  assumes cp: "compile_procs \<Pi> ps n = (n', E, K)"
    and e: "(u, ce, tgt, af) \<in> K"
  shows "\<exists>k. u = Statement k"
  using cp e
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons.prems have "compile_procs \<Pi> ps n = (n', E, K)" by simp
    then show ?thesis using Cons.IH Cons.prems(2) by blast
  next
    case (Some decl)
    obtain n1 E0 K0 n2 E' K' where cp0: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and K: "K = K0 \<union> K'"
      using Cons.prems(1) Some by (auto split: prod.splits)
    from Cons.prems(2) K consider "(u, ce, tgt, af) \<in> K0" | "(u, ce, tgt, af) \<in> K'" by auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using compile_proc_calls_source_stmt[OF cp0] by blast
    next
      case 2 then show ?thesis using Cons.IH[OF rest] by blast
    qed
  qed
qed

lemma compile_procs_calls_source_stmtE:
  assumes cp: "compile_procs \<Pi> ps n = (n', E, K)"
    and e: "(u, ce, tgt, af) \<in> K"
  obtains k where "u = Statement k"
  using compile_procs_calls_source_stmt[OF cp e] by blast

lemma compile_procs_call_target_declared:
  assumes comp: "compile_procs \<Pi> ps n = (n', E, K)"
    and decls: "!!p decl. \<Pi> p = Some decl ==> wf_proc_decl source_global \<Pi> decl"
    and edge: "(u, ce, FunctionEntry q, af) \<in> K"
  shows "\<Pi> q \<noteq> None"
  using comp edge
  by (induction ps arbitrary: n n' E K)
     (auto split: option.splits prod.splits
       dest: compile_proc_call_target_declared intro: decls)

lemma compile_prog_call_target_declared:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and edge: "(u, ce, FunctionEntry q, af) \<in> calls (compile_prog \<Pi> ps mnm main)"
  shows "\<Pi> q \<noteq> None"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and K: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have decls: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> wf_proc_decl source_global \<Pi> decl"
    by (rule wf_compile_input_decl[OF wf])
  have main_decl: "\<Pi> mnm = Some (proc_decl_of [] main)"
    by (rule wf_compile_input_main_exists[OF wf])
  from edge K consider "(u, ce, FunctionEntry q, af) \<in> Kprocs"
    | "(u, ce, FunctionEntry q, af) \<in> Kmain" by auto
  then show ?thesis
  proof cases
    case 1
    show ?thesis by (rule compile_procs_call_target_declared[OF procs decls 1])
  next
    case 2
    show ?thesis
      by (rule compile_proc_call_target_declared[OF mainc decls[OF main_decl] 2])
  qed
qed

lemma compile_prog_calls_source_stmt:
  "(u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps mnm main) \<Longrightarrow> \<exists>k. u = Statement k"
proof -
  assume e: "(u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps mnm main)"
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and K: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  from e K consider "(u, ce, tgt, af) \<in> Kprocs" | "(u, ce, tgt, af) \<in> Kmain" by auto
  then show "\<exists>k. u = Statement k"
  proof cases
    case 1
    then show ?thesis using compile_procs_calls_source_stmt[OF procs] by blast
  next
    case 2
    then show ?thesis using compile_proc_calls_source_stmt[OF mainc] by blast
  qed
qed

lemma compile_prog_entry_declared:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and e: "(FunctionEntry p, a, v) \<in> intra (compile_prog \<Pi> ps mnm main)"
  shows "\<exists>d. \<Pi> p = Some d"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and E: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  have setps: "set ps = {p. \<Pi> p \<noteq> None} - {mnm}"
    using wf unfolding wf_compile_input_def by auto
  have main: "\<Pi> mnm = Some (proc_decl_of [] main)"
    by (rule wf_compile_input_main_exists[OF wf])
  from e E consider "(FunctionEntry p, a, v) \<in> Eprocs" | "(FunctionEntry p, a, v) \<in> Emain" by auto
  then show ?thesis
  proof cases
    case 1
    then have "p \<in> set ps" using compile_procs_entry_mem[OF procs] by blast
    then have "\<Pi> p \<noteq> None" using setps by auto
    then show ?thesis by (cases "\<Pi> p") auto
  next
    case 2
    then have "p = mnm" using compile_proc_entry_mem[OF mainc] by blast
    with main show ?thesis by blast
  qed
qed


subsection \<open>Edges stay in the activation fragment\<close>

lemma compile_proc_intra_source_range:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(Statement k, a, v) \<in> E"
  shows "k \<in> {n..<n'}"
proof -
  have "k \<in> frag_stmts E K" using frag_stmts_E_srcI[OF e] .
  then show ?thesis using compile_proc_frag_range[OF cp] by blast
qed

lemma compile_proc_calls_source_range:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e: "(Statement k, ce, tgt, af) \<in> K"
  shows "k \<in> {n..<n'}"
proof -
  have "k \<in> frag_stmts E K" using frag_stmts_K_srcI[OF e] .
  then show ?thesis using compile_proc_frag_range[OF cp] by blast
qed

lemma compile_procs_intra_source_range:
  assumes cp: "compile_procs \<Pi> ps n = (n', E, K)"
    and e: "(Statement k, a, v) \<in> E"
  shows "k \<in> {n..<n'}"
proof -
  have "k \<in> frag_stmts E K" using frag_stmts_E_srcI[OF e] .
  then show ?thesis using compile_procs_frag_range[OF cp] by blast
qed

lemma compile_procs_calls_source_range:
  assumes cp: "compile_procs \<Pi> ps n = (n', E, K)"
    and e: "(Statement k, ce, tgt, af) \<in> K"
  shows "k \<in> {n..<n'}"
proof -
  have "k \<in> frag_stmts E K" using frag_stmts_K_srcI[OF e] .
  then show ?thesis using compile_procs_frag_range[OF cp] by blast
qed

text \<open>
  The four lemmas below (\<open>compile_procs_tail_intra_not_head_pfn\<close>,
  \<open>compile_proc_head_intra_not_tail_pfn\<close>, \<open>compile_procs_head_intra_not_tail_pfn\<close>,
  \<open>compile_proc_tail_intra_not_head_pfn\<close>) all discharge the same shape of
  obligation: an edge produced by compiling one fragment (either a single
  procedure via \<^const>\<open>compile_proc\<close> or a list via \<^const>\<open>compile_procs\<close>)
  cannot land in a node claimed by a range-disjoint fragment. The three
  \<^term>\<open>cfg_node\<close> constructors drive genuinely different sub-arguments (an
  entry-ownership clash, an impossible result source, or a counter-range
  clash), so this is not a mechanical per-constructor dispatch to collapse --
  but the four call sites instantiate that same three-way argument with only
  the ownership predicate (\<open>r = q\<close> vs. \<open>r \<in> set ps\<close>) and the
  disjointness direction varying, so that shared argument is factored out
  once here.
\<close>
lemma compile_frag_no_edge_into_other_pfn:
  assumes own_entry: "\<And>r a v. (FunctionEntry r, a, v) \<in> E \<Longrightarrow> P r"
    and own_no_result: "\<And>r a v. (FunctionResult r, a, v) \<in> E \<Longrightarrow> False"
    and own_range: "\<And>k a v. (Statement k, a, v) \<in> E \<Longrightarrow> k \<in> {n..<n'}"
    and not_own: "\<not> P r0"
    and disjoint: "n' \<le> m \<or> m' \<le> n"
    and e: "(u, a, v) \<in> E"
    and uin: "u \<in> pfn r0 m m'"
  shows False
proof (cases u)
  case (FunctionEntry q)
  have "P q" using own_entry e FunctionEntry by simp
  moreover have "q = r0" using uin FunctionEntry by (auto simp: pfn_def)
  ultimately show False using not_own by simp
next
  case (FunctionResult q)
  show False using own_no_result e FunctionResult by simp
next
  case (Statement k)
  have kh: "k \<in> {n..<n'}" using own_range e Statement by simp
  have kt: "k \<in> {m..<m'}" using uin Statement by (auto simp: pfn_def)
  show False using kh kt disjoint by auto
qed

lemma compile_procs_tail_intra_not_head_pfn:
  assumes cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
    and distinct: "distinct (p # ps)"
    and e: "(u, a, v) \<in> E'"
    and uin: "u \<in> pfn p n n1"
  shows False
proof (rule compile_frag_no_edge_into_other_pfn
    [OF compile_procs_entry_mem[OF rest] compile_procs_no_result_source[OF rest]
        compile_procs_intra_source_range[OF rest] _ _ e uin])
  show "p \<notin> set ps" using distinct by simp
  show "n2 \<le> n \<or> n1 \<le> n1" by simp
qed

lemma compile_procs_tail_calls_not_head_pfn:
  assumes cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
    and distinct: "distinct (p # ps)"
    and e: "(u, ce, tgt, af) \<in> K'"
    and uin: "u \<in> pfn p n n1"
  shows False
proof -
  obtain k where u: "u = Statement k" by (rule compile_procs_calls_source_stmtE[OF rest e])
  have e': "(Statement k, ce, tgt, af) \<in> K'" using e u by simp
  have kr: "k \<in> {n1..<n2}" using compile_procs_calls_source_range[OF rest e'] .
  have kh: "k \<in> {n..<n1}" using uin u by (auto simp: pfn_def)
  show False using kr kh by auto
qed

lemma compile_proc_head_intra_not_tail_pfn:
  assumes cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and e: "(u, a, v) \<in> E0"
    and neq: "p \<noteq> r"
    and lower: "n1 \<le> m"
    and uin: "u \<in> pfn r m m'"
  shows False
proof (rule compile_frag_no_edge_into_other_pfn
    [OF compile_proc_entry_mem[OF cp] compile_proc_no_result_source[OF cp]
        compile_proc_intra_source_range[OF cp] _ _ e uin])
  show "r \<noteq> p" using neq by simp
  show "n1 \<le> m \<or> m' \<le> n" using lower by simp
qed

lemma compile_proc_head_calls_not_tail_pfn:
  assumes cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and e: "(u, ce, tgt, af) \<in> K0"
    and lower: "n1 \<le> m"
    and uin: "u \<in> pfn r m m'"
  shows False
proof -
  obtain k where u: "u = Statement k" by (rule compile_proc_calls_source_stmtE[OF cp e])
  have e': "(Statement k, ce, tgt, af) \<in> K0" using e u by simp
  have kh: "k \<in> {n..<n1}" using compile_proc_calls_source_range[OF cp e'] .
  have kt: "k \<in> {m..<m'}" using uin u by (auto simp: pfn_def)
  show False using kh kt lower by auto
qed


lemma compile_procs_intra_owner:
  assumes cps: "compile_procs \<Pi> ps n = (n', E, K)"
    and distinct: "distinct ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Nop, Statement m) \<in> E"
    and uin: "u \<in> pfn r m m'"
    and edge: "(u, a, v) \<in> E"
  shows "v \<in> pfn r m m'"
  using cps distinct decl cb ent uin edge
proof (induction ps arbitrary: n n' E K m m' Ep Kp u a v)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have cps': "compile_procs \<Pi> qs n = (n', E, K)" by simp
    show ?thesis using Cons.IH[OF cps'] Cons.prems None by simp
  next
    case (Some dq)
    obtain n1 E0 K0 n2 E' K' where cp0: "compile_proc \<Pi> q dq n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'"
      using Cons.prems(1) Some by (auto split: prod.splits)
    show ?thesis
    proof (cases "r = q")
      case True
      with Cons.prems(3) Some have dd: "d = dq" by simp
      have ent0: "(FunctionEntry q, EA_Nop, Statement n) \<in> E"
        using E compile_proc_entry_edge[OF cp0] by auto
      have entq: "(FunctionEntry q, EA_Nop, Statement m) \<in> E" using Cons.prems(5) True by simp
      have mn: "m = n"
        using compile_procs_entry_unique[OF Cons.prems(1) Cons.prems(2) entq ent0] by simp
      have mout: "m' = n1" using Cons.prems(4) cp0 True dd mn by simp

      from Cons.prems(7) E consider "(u, a, v) \<in> E0" | "(u, a, v) \<in> E'" by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using compile_proc_intra_pfn[OF cp0] True mn mout by simp
      next
        case 2
        have False using compile_procs_tail_intra_not_head_pfn[OF cp0 rest Cons.prems(2) 2]
          Cons.prems(6) True mn mout by simp
        then show ?thesis ..
      qed
    next
      case False
      have enttail: "(FunctionEntry r, EA_Nop, Statement m) \<in> E'"
      proof -
        from Cons.prems(5) E consider "(FunctionEntry r, EA_Nop, Statement m) \<in> E0"
          | "(FunctionEntry r, EA_Nop, Statement m) \<in> E'" by auto
        then show ?thesis
        proof cases
          case 1
          have "r = q" using compile_proc_entry_mem[OF cp0 1] .
          with False show ?thesis by simp
        next
          case 2 then show ?thesis .
        qed
      qed
      have lower: "n1 \<le> m"
      proof -
        have "m \<in> frag_stmts E' K'"
          using frag_stmts_E_tgtI[OF enttail] .

        then show ?thesis using compile_procs_frag_range[OF rest] by auto
      qed
      have dqs: "distinct qs" using Cons.prems(2) by simp
      from Cons.prems(7) E consider "(u, a, v) \<in> E0" | "(u, a, v) \<in> E'" by auto
      then show ?thesis
      proof cases
        case 1
        have False using compile_proc_head_intra_not_tail_pfn[OF cp0 1 _ lower Cons.prems(6)]
          False by simp
        then show ?thesis ..
      next
        case 2
        show ?thesis using Cons.IH[OF rest dqs Cons.prems(3) Cons.prems(4) enttail Cons.prems(6) 2] .
      qed
    qed
  qed
qed

lemma compile_procs_calls_owner:
  assumes cps: "compile_procs \<Pi> ps n = (n', E, K)"
    and distinct: "distinct ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Nop, Statement m) \<in> E"
    and uin: "u \<in> pfn r m m'"
    and edge: "(u, ce, tgt, af) \<in> K"
  shows "af \<in> pfn r m m'"
  using cps distinct decl cb ent uin edge
proof (induction ps arbitrary: n n' E K m m' Ep Kp u ce tgt af)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have cps': "compile_procs \<Pi> qs n = (n', E, K)" by simp
    show ?thesis using Cons.IH[OF cps'] Cons.prems None by simp
  next
    case (Some dq)
    obtain n1 E0 K0 n2 E' K' where cp0: "compile_proc \<Pi> q dq n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      using Cons.prems(1) Some by (auto split: prod.splits)
    show ?thesis
    proof (cases "r = q")
      case True
      with Cons.prems(3) Some have dd: "d = dq" by simp
      have ent0: "(FunctionEntry q, EA_Nop, Statement n) \<in> E"
        using E compile_proc_entry_edge[OF cp0] by auto
      have entq: "(FunctionEntry q, EA_Nop, Statement m) \<in> E" using Cons.prems(5) True by simp
      have mn: "m = n"
        using compile_procs_entry_unique[OF Cons.prems(1) Cons.prems(2) entq ent0] by simp
      have mout: "m' = n1" using Cons.prems(4) cp0 True dd mn by simp

      from Cons.prems(7) K consider "(u, ce, tgt, af) \<in> K0" | "(u, ce, tgt, af) \<in> K'" by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using compile_proc_calls_pfn[OF cp0] True mn mout by simp
      next
        case 2
        have False using compile_procs_tail_calls_not_head_pfn[OF cp0 rest Cons.prems(2) 2]
          Cons.prems(6) True mn mout by simp
        then show ?thesis ..
      qed
    next
      case False
      have enttail: "(FunctionEntry r, EA_Nop, Statement m) \<in> E'"
      proof -
        from Cons.prems(5) E consider "(FunctionEntry r, EA_Nop, Statement m) \<in> E0"
          | "(FunctionEntry r, EA_Nop, Statement m) \<in> E'" by auto
        then show ?thesis
        proof cases
          case 1
          have "r = q" using compile_proc_entry_mem[OF cp0 1] .
          with False show ?thesis by simp
        next
          case 2 then show ?thesis .
        qed
      qed
      have lower: "n1 \<le> m"
      proof -
        have "m \<in> frag_stmts E' K'"
          using frag_stmts_E_tgtI[OF enttail] .

        then show ?thesis using compile_procs_frag_range[OF rest] by auto
      qed
      have dqs: "distinct qs" using Cons.prems(2) by simp
      from Cons.prems(7) K consider "(u, ce, tgt, af) \<in> K0" | "(u, ce, tgt, af) \<in> K'" by auto
      then show ?thesis
      proof cases
        case 1
        have False using compile_proc_head_calls_not_tail_pfn[OF cp0 1 lower Cons.prems(6)] .
        then show ?thesis ..
      next
        case 2
        show ?thesis using Cons.IH[OF rest dqs Cons.prems(3) Cons.prems(4) enttail Cons.prems(6) 2] .
      qed
    qed
  qed
qed

lemma compile_procs_head_intra_not_tail_pfn:
  assumes procs: "compile_procs \<Pi> ps n = (n1, E0, K0)"
    and e: "(u, a, v) \<in> E0"
    and absent: "r \<notin> set ps"
    and lower: "n1 \<le> m"
    and uin: "u \<in> pfn r m m'"
  shows False
proof (rule compile_frag_no_edge_into_other_pfn
    [OF compile_procs_entry_mem[OF procs] compile_procs_no_result_source[OF procs]
        compile_procs_intra_source_range[OF procs] _ _ e uin])
  show "r \<notin> set ps" using absent .
  show "n1 \<le> m \<or> m' \<le> n" using lower by simp
qed

lemma compile_proc_tail_intra_not_head_pfn:
  assumes cp: "compile_proc \<Pi> mnm decl n1 = (n2, E0, K0)"
    and e: "(u, a, v) \<in> E0"
    and neq: "mnm \<noteq> r"
    and upper: "m' \<le> n1"
    and uin: "u \<in> pfn r m m'"
  shows False
proof (rule compile_frag_no_edge_into_other_pfn
    [OF compile_proc_entry_mem[OF cp] compile_proc_no_result_source[OF cp]
        compile_proc_intra_source_range[OF cp] _ _ e uin])
  show "r \<noteq> mnm" using neq by simp
  show "n2 \<le> m \<or> m' \<le> n1" using upper by simp
qed

lemma compile_procs_head_calls_not_tail_pfn:
  assumes procs: "compile_procs \<Pi> ps n = (n1, E0, K0)"
    and e: "(u, ce, tgt, af) \<in> K0"
    and lower: "n1 \<le> m"
    and uin: "u \<in> pfn r m m'"
  shows False
proof -
  obtain k where u: "u = Statement k" by (rule compile_procs_calls_source_stmtE[OF procs e])
  have e': "(Statement k, ce, tgt, af) \<in> K0" using e u by simp
  have kh: "k \<in> {n..<n1}" using compile_procs_calls_source_range[OF procs e'] .
  have kt: "k \<in> {m..<m'}" using uin u by (auto simp: pfn_def)
  show False using kh kt lower by auto
qed

lemma compile_proc_tail_calls_not_head_pfn:
  assumes cp: "compile_proc \<Pi> mnm decl n1 = (n2, E0, K0)"
    and e: "(u, ce, tgt, af) \<in> K0"
    and upper: "m' \<le> n1"
    and uin: "u \<in> pfn r m m'"
  shows False
proof -
  obtain k where u: "u = Statement k" by (rule compile_proc_calls_source_stmtE[OF cp e])
  have e': "(Statement k, ce, tgt, af) \<in> K0" using e u by simp
  have kh: "k \<in> {n1..<n2}" using compile_proc_calls_source_range[OF cp e'] .
  have kt: "k \<in> {m..<m'}" using uin u by (auto simp: pfn_def)
  show False using kh kt upper by auto
qed

lemma compile_procs_fragment_bounds_from_entry:
  assumes procs: "compile_procs \<Pi> ps n = (n', E, K)"
    and distinct: "distinct ps"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Nop, Statement m) \<in> E"
    and rin: "r \<in> set ps"
  shows "m' \<le> n'"
proof -
  obtain m0 m0' Ep0 Kp0 where cp0: "compile_proc \<Pi> r d m0 = (m0', Ep0, Kp0)"
    and bnds: "n \<le> m0" "m0' \<le> n'" and sub: "Ep0 \<subseteq> E" "Kp0 \<subseteq> K"
    using compile_procs_member[OF procs rin decl] by blast
  have ent0: "(FunctionEntry r, EA_Nop, Statement m0) \<in> E"
    using sub(1) compile_proc_entry_edge[OF cp0] by auto
  have mm: "m = m0"
    using compile_procs_entry_unique[OF procs distinct ent ent0] by simp
  have mout: "m' = m0'" using cb cp0 mm by simp
  show ?thesis using bnds(2) mout by simp
qed


text \<open>Given a genuine procedure fragment (declared body, included edges, entry wiring) and a node
  in it, every intra edge leaving that node, and every call leaving it, lands its
  same-activation successor back in the fragment.\<close>
lemma frag_edge_intra:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
    and uin: "u \<in> pfn r m m'"
    and e: "(u, a, v) \<in> intra (compile_prog \<Pi> ps mnm main)"
  shows "v \<in> pfn r m m'"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    and KC: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have distinct: "distinct ps" and mnmnotin: "mnm \<notin> set ps"
    and setps: "set ps = {p. \<Pi> p \<noteq> None} - {mnm}"
    using wf unfolding wf_compile_input_def by auto
  show ?thesis
  proof (cases "r = mnm")
    case True
    have entmain': "(FunctionEntry mnm, EA_Nop, Statement n1) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using EI compile_proc_entry_edge[OF mainc] by auto
    have dd: "d = proc_decl_of [] main"
      using decl True wf_compile_input_main_exists[OF wf] by simp
    have entr: "(FunctionEntry mnm, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using ent True by simp
    have mn: "m = n1"
      using compile_prog_entry_out_unique[OF wf entr entmain'] by simp
    have mout: "m' = n2" using cb mainc True dd mn by simp

    have uinmain: "u \<in> pfn mnm n1 n2" using uin True mn mout by simp
    from e EI consider "(u, a, v) \<in> Eprocs" | "(u, a, v) \<in> Emain" by auto
    then show ?thesis
    proof cases
      case 1
      have False using compile_procs_head_intra_not_tail_pfn[OF procs 1 mnmnotin _ uinmain] by simp
      then show ?thesis ..
    next
      case 2
      show ?thesis using compile_proc_intra_pfn[OF mainc 2] True mn mout by simp
    qed
  next
    case False
    have rin: "r \<in> set ps" using decl setps False by auto
    have entprocs: "(FunctionEntry r, EA_Nop, Statement m) \<in> Eprocs"
    proof -
      from ent EI consider "(FunctionEntry r, EA_Nop, Statement m) \<in> Eprocs"
        | "(FunctionEntry r, EA_Nop, Statement m) \<in> Emain" by auto

      then show ?thesis
      proof cases
        case 1 then show ?thesis .
      next
        case 2
        have "r = mnm" using compile_proc_entry_mem[OF mainc 2] .
        with False show ?thesis by simp
      qed
    qed
    have upper: "m' \<le> n1"
      using compile_procs_fragment_bounds_from_entry[OF procs distinct decl cb entprocs rin] .
    from e EI consider "(u, a, v) \<in> Eprocs" | "(u, a, v) \<in> Emain" by auto
    then show ?thesis
    proof cases
      case 1
      show ?thesis using compile_procs_intra_owner[OF procs distinct decl cb entprocs uin 1] .
    next
      case 2
      have neq: "mnm \<noteq> r" using False by simp
      have False using compile_proc_tail_intra_not_head_pfn[OF mainc 2 neq upper uin] .
      then show ?thesis ..
    qed
  qed
qed

lemma frag_edge_calls:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and decl: "\<Pi> r = Some d"
    and cb: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry r, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
    and uin: "u \<in> pfn r m m'"
    and e: "(u, ce, tgt, af) \<in> calls (compile_prog \<Pi> ps mnm main)"
  shows "af \<in> pfn r m m'"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    and KC: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have distinct: "distinct ps" and mnmnotin: "mnm \<notin> set ps"
    and setps: "set ps = {p. \<Pi> p \<noteq> None} - {mnm}"
    using wf unfolding wf_compile_input_def by auto
  show ?thesis
  proof (cases "r = mnm")
    case True
    have entmain': "(FunctionEntry mnm, EA_Nop, Statement n1) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using EI compile_proc_entry_edge[OF mainc] by auto
    have dd: "d = proc_decl_of [] main"
      using decl True wf_compile_input_main_exists[OF wf] by simp
    have entr: "(FunctionEntry mnm, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using ent True by simp
    have mn: "m = n1"
      using compile_prog_entry_out_unique[OF wf entr entmain'] by simp
    have mout: "m' = n2" using cb mainc True dd mn by simp

    have uinmain: "u \<in> pfn mnm n1 n2" using uin True mn mout by simp
    from e KC consider "(u, ce, tgt, af) \<in> Kprocs" | "(u, ce, tgt, af) \<in> Kmain" by auto
    then show ?thesis
    proof cases
      case 1
      have False using compile_procs_head_calls_not_tail_pfn[OF procs 1 _ uinmain] by simp
      then show ?thesis ..
    next
      case 2
      show ?thesis using compile_proc_calls_pfn[OF mainc 2] True mn mout by simp
    qed
  next
    case False
    have rin: "r \<in> set ps" using decl setps False by auto
    have entprocs: "(FunctionEntry r, EA_Nop, Statement m) \<in> Eprocs"
    proof -
      from ent EI consider "(FunctionEntry r, EA_Nop, Statement m) \<in> Eprocs"
        | "(FunctionEntry r, EA_Nop, Statement m) \<in> Emain" by auto

      then show ?thesis
      proof cases
        case 1 then show ?thesis .
      next
        case 2
        have "r = mnm" using compile_proc_entry_mem[OF mainc 2] .
        with False show ?thesis by simp
      qed
    qed
    have upper: "m' \<le> n1"
      using compile_procs_fragment_bounds_from_entry[OF procs distinct decl cb entprocs rin] .
    from e KC consider "(u, ce, tgt, af) \<in> Kprocs" | "(u, ce, tgt, af) \<in> Kmain" by auto
    then show ?thesis
    proof cases
      case 1
      show ?thesis using compile_procs_calls_owner[OF procs distinct decl cb entprocs uin 1] .
    next
      case 2
      have False using compile_proc_tail_calls_not_head_pfn[OF mainc 2 upper uin] .
      then show ?thesis ..
    qed
  qed
qed

subsection \<open>Procedure locality of a valid activation\<close>

text \<open>Every declared procedure of a compiled program owns a fragment, identified by the start
  counter its entry wiring edge points at.\<close>
lemma compile_prog_proc_frag:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and decl: "\<Pi> q = Some d"
  obtains m m' Ep Kp where
    "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    "(FunctionEntry q, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    and KC: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show thesis
  proof (cases "q = mnm")
    case True
    have dd: "d = proc_decl_of [] main"
      using decl True wf_compile_input_main_exists[OF wf] by simp
    have "(FunctionEntry q, EA_Nop, Statement n1) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using EI compile_proc_entry_edge[OF mainc] True by auto
    then show ?thesis using that[of n1 n2 Emain Kmain] mainc True dd by simp
  next
    case False
    have setps: "set ps = {p. \<Pi> p \<noteq> None} - {mnm}"
      using wf unfolding wf_compile_input_def by auto
    have rin: "q \<in> set ps" using decl setps False by auto
    obtain m m' Ep Kp where cp0: "compile_proc \<Pi> q d m = (m', Ep, Kp)" and sub: "Ep \<subseteq> Eprocs"
      using compile_procs_member[OF procs rin decl] by blast
    have "(FunctionEntry q, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
      using EI sub compile_proc_entry_edge[OF cp0] by auto
    then show ?thesis using that cp0 by blast
  qed
qed

text \<open>\<open>frag_ok u\<close>: the activation \<open>u\<close> either lies wholly inside a genuine procedure fragment
  (declared body, entry wiring, all path nodes in the fragment) or is a single-node activation
  stuck at an undeclared \<^term>\<open>FunctionEntry\<close> --- which can never advance and never reaches a
  \<^term>\<open>FunctionResult\<close>.\<close>
definition frag_ok :: "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> ltr \<Rightarrow> bool" where
  "frag_ok \<Pi> ps mnm main u \<longleftrightarrow>
     (\<exists>r d m m' Ep Kp. \<Pi> r = Some d
        \<and> compile_proc \<Pi> r d m = (m', Ep, Kp)
        \<and> (FunctionEntry r, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)
        \<and> fst (hd (path u)) = FunctionEntry r
        \<and> (\<forall>nd \<in> fst ` set (path u). nd \<in> pfn r m m'))
   \<or> (\<exists>p s. path u = [(FunctionEntry p, s)] \<and> \<Pi> p = None)"

lemma frag_okI_frag:
  assumes "\<Pi> r = Some d" "compile_proc \<Pi> r d m = (m', Ep, Kp)"
    "(FunctionEntry r, EA_Nop, Statement m) \<in> intra (compile_prog \<Pi> ps mnm main)"
    "fst (hd (path u)) = FunctionEntry r"
    "\<And>nd. nd \<in> fst ` set (path u) \<Longrightarrow> nd \<in> pfn r m m'"
  shows "frag_ok \<Pi> ps mnm main u"
  unfolding frag_ok_def using assms by blast


lemma sink_in_path_nodes:
  "t \<in> valid_ltr gs g S \<Longrightarrow> sink_node t \<in> fst ` set (path t)"
  using valid_ltr_path_nonempty by (auto simp: sink_node_def)

text \<open>Every activation in the caller chain of a valid trace is fragment-local.  The property is
  carried over the whole \<^const>\<open>callers\<close> chain so that the return case, which resumes the caller,
  can read the caller's own fragment (\<open>caller \<in> callers callee\<close>).\<close>
lemma valid_ltr_frag_callers:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and t: "t \<in> valid_ltr gs (compile_prog \<Pi> ps mnm main) S"
  shows "\<forall>u \<in> callers t. frag_ok \<Pi> ps mnm main u"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  show ?thesis
  proof (rule caller_chain_closure)
    fix s assume "s \<in> S"
    have mnmdecl: "\<Pi> mnm = Some (proc_decl_of [] main)"
      by (rule wf_compile_input_main_exists[OF wf])
    obtain m m' Ep Kp where
      cb: "compile_proc \<Pi> mnm (proc_decl_of [] main) m = (m', Ep, Kp)"
      and ent: "(FunctionEntry mnm, EA_Nop, Statement m) \<in> intra ?g"
      by (rule compile_prog_proc_frag[OF wf mnmdecl])
    show "frag_ok \<Pi> ps mnm main (Root [(cfg_entry ?g, s)])"
      by (rule frag_okI_frag[OF mnmdecl cb ent])
         (simp_all add: inv16_entry_is_main pfn_def)
  next
    fix t a v s' assume ht: "t \<in> valid_ltr gs ?g S" and ch: "\<forall>u \<in> callers t. frag_ok \<Pi> ps mnm main u"
      and e: "(sink_node t, a, v) \<in> intra ?g"
    have ft: "frag_ok \<Pi> ps mnm main t" using ch callers_refl by blast
    from ft[unfolded frag_ok_def] show "frag_ok \<Pi> ps mnm main (extend t (v, s'))"
    proof (elim disjE exE conjE)
      fix r d mm mm' Ep Kp
      assume decl: "\<Pi> r = Some d"
        and cb: "compile_proc \<Pi> r d mm = (mm', Ep, Kp)"
        and ent: "(FunctionEntry r, EA_Nop, Statement mm) \<in> intra ?g"
        and hd_r: "fst (hd (path t)) = FunctionEntry r"
        and nodes_t: "\<forall>nd \<in> fst ` set (path t). nd \<in> pfn r mm mm'"
      have snk: "sink_node t \<in> pfn r mm mm'"
        using sink_in_path_nodes[OF ht] nodes_t by blast
      have v_in: "v \<in> pfn r mm mm'"
        using frag_edge_intra[OF wf decl cb ent snk e] .
      have pne: "path t \<noteq> []" using valid_ltr_path_nonempty[OF ht] .
      show "frag_ok \<Pi> ps mnm main (extend t (v, s'))"
        by (rule frag_okI_frag[OF decl cb ent])
           (use hd_r pne nodes_t v_in in \<open>auto simp: hd_append\<close>)
    next
      fix q s assume stub: "path t = [(FunctionEntry q, s)]" and qnone: "\<Pi> q = None"
      have "sink_node t = FunctionEntry q" using stub by (simp add: sink_node_def)
      then have edge: "(FunctionEntry q, a, v) \<in> intra ?g" using e by simp
      have "\<exists>d. \<Pi> q = Some d" using compile_prog_entry_declared[OF wf edge] .
      then show "frag_ok \<Pi> ps mnm main (extend t (v, s'))" using qnone by simp
    qed
  next
    fix caller dst pars args p cont
    assume e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    show "frag_ok \<Pi> ps mnm main
            (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    proof (cases "\<Pi> p")
      case None
      then show ?thesis unfolding frag_ok_def by fastforce
    next
      case (Some d)
      obtain m m' Ep Kp where
        cb: "compile_proc \<Pi> p d m = (m', Ep, Kp)"
        and ent: "(FunctionEntry p, EA_Nop, Statement m) \<in> intra ?g"
        by (rule compile_prog_proc_frag[OF wf Some])
      show ?thesis
        by (rule frag_okI_frag[OF Some cb ent]) (simp_all add: pfn_def)
    qed
  next
    fix callee caller p dst pars args cont
    assume cvcallee: "callee \<in> valid_ltr gs ?g S" and ch: "\<forall>u \<in> callers callee. frag_ok \<Pi> ps mnm main u"
      and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
      and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    have cin: "caller \<in> callers callee" using cof callers_caller_subset callers_refl by blast
    have cv: "caller \<in> valid_ltr gs ?g S" using valid_ltr_caller_valid[OF cvcallee cof] .
    have fc: "frag_ok \<Pi> ps mnm main caller" using ch cin by blast
    from fc[unfolded frag_ok_def]
    show "frag_ok \<Pi> ps mnm main (Resume caller callee
            (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
    proof (elim disjE exE conjE)
      fix r d mm mm' Ep Kp
      assume decl: "\<Pi> r = Some d"
        and cb: "compile_proc \<Pi> r d mm = (mm', Ep, Kp)"
        and ent: "(FunctionEntry r, EA_Nop, Statement mm) \<in> intra ?g"
        and hd_r: "fst (hd (path caller)) = FunctionEntry r"
        and nodes_c: "\<forall>nd \<in> fst ` set (path caller). nd \<in> pfn r mm mm'"
      have snk: "sink_node caller \<in> pfn r mm mm'"
        by (meson cv nodes_c sink_in_path_nodes)
      have cont_in: "cont \<in> pfn r mm mm'"
        using frag_edge_calls[OF wf decl cb ent snk e] .
      have pne: "path caller \<noteq> []" using valid_ltr_path_nonempty[OF cv] .
      show "frag_ok \<Pi> ps mnm main (Resume caller callee
              (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
        by (rule frag_okI_frag[OF decl cb ent])
           (use hd_r pne nodes_c cont_in in \<open>auto simp: hd_append\<close>)
    next
      fix q s assume stub: "path caller = [(FunctionEntry q, s)]" and qnone: "\<Pi> q = None"
      have "sink_node caller = FunctionEntry q" using stub by (simp add: sink_node_def)
      then have "(FunctionEntry q, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
        using e by simp
      with compile_prog_calls_source_stmt
      show "frag_ok \<Pi> ps mnm main (Resume caller callee
              (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
        by blast
    qed
  next
    show "t \<in> valid_ltr gs ?g S" by (rule t)
  qed
qed

text \<open>An activation entered at \<^term>\<open>FunctionEntry p\<close> reaches \<^term>\<open>FunctionResult q\<close> only for
  \<open>p = q\<close>.\<close>
lemma valid_ltr_entry_result_eq:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and t: "t \<in> valid_ltr gs (compile_prog \<Pi> ps mnm main) S"
    and en: "fst (hd (path t)) = FunctionEntry p"
    and sk: "sink_node t = FunctionResult q"
  shows "p = q"
proof -
  have "frag_ok \<Pi> ps mnm main t"
    using valid_ltr_frag_callers[OF wf t] callers_refl by blast
  then show ?thesis unfolding frag_ok_def
  proof (elim disjE exE conjE)
    fix r d m m' Ep Kp
    assume "fst (hd (path t)) = FunctionEntry r"
      and nodes: "\<forall>nd \<in> fst ` set (path t). nd \<in> pfn r m m'"
    have rp: "r = p" using \<open>fst (hd (path t)) = FunctionEntry r\<close> en by simp
    have "sink_node t \<in> pfn r m m'" using sink_in_path_nodes[OF t] nodes by blast
    then have "FunctionResult q \<in> pfn r m m'" using sk by simp
    then have "q = r" by (auto simp: pfn_def)
    with rp show "p = q" by simp
  next
    fix p' s assume "path t = [(FunctionEntry p', s)]"
    then have "sink_node t = FunctionEntry p'" by (simp add: sink_node_def)
    with sk show "p = q" by simp
  qed
qed

end
