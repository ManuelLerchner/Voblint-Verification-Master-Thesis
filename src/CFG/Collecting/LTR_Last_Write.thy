theory LTR_Last_Write
  imports CFG_Local_Trace Compile_Edge_Determinism
begin

section \<open>Trace-derived last-writer specification\<close>

text \<open>
  \<open>last_writer\<close> identifies the most recent \<^const>\<open>Statement\<close> or \<^const>\<open>FunctionResult\<close> node
  along a concrete local path whose incoming edge wrote a given variable.  Section 5 of
  \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> derives this directly from \<^const>\<open>path\<close> and
  \<^const>\<open>intra\<close>, without enriching \<^type>\<open>ltr\<close> with the action that fired at each step,
  contingent on the compiled CFG being edge-action functional (design-gate item 2, resolved by
  \<open>compile_prog_intra_functional\<close> in \<open>Compile_Edge_Determinism\<close>).  This theory supplies that
  derivation and its characterization lemmas; \<open>cfg_intra_functional\<close> is the exact hypothesis
  those lemmas need, stated once here rather than assumed silently.
\<close>

subsection \<open>Which variable an edge action writes\<close>

fun edge_writes :: "edge_action \<Rightarrow> vname \<Rightarrow> bool" where
  "edge_writes (EA_Assign y _) x = (x = y)"
| "edge_writes (EA_Random y) x = (x = y)"
| "edge_writes (EA_Ret _ _) x = (x = ret_var)"
| "edge_writes EA_Nop x = False"
| "edge_writes (EA_Assume _) x = False"
| "edge_writes (EA_AssumeNot _) x = False"

subsection \<open>Edge-action functional CFGs\<close>

text \<open>The hypothesis \<open>last_write_step\<close> needs to read a well-defined variable off a single
  \<open>(u, v)\<close> step: at most one action labels that pair.\<close>

definition cfg_intra_functional :: "cfg \<Rightarrow> bool" where
  "cfg_intra_functional g \<longleftrightarrow> (\<forall>u a1 v a2. (u, a1, v) \<in> intra g \<longrightarrow> (u, a2, v) \<in> intra g \<longrightarrow> a1 = a2)"

lemma compile_prog_intra_cfg_functional:
  "cfg_intra_functional (compile_prog \<Pi> ps mnm main)"
  unfolding cfg_intra_functional_def using compile_prog_intra_functional by blast

subsection \<open>One-step write witness\<close>

definition last_write_step :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> vname \<Rightarrow> bool" where
  "last_write_step g u v x \<longleftrightarrow> (\<exists>a. (u, a, v) \<in> intra g \<and> edge_writes a x)"

text \<open>Under \<open>cfg_intra_functional\<close> a single step writes at most one variable, so a step that
  writes \<open>y\<close> cannot also count as writing a different \<open>x\<close>.\<close>
lemma last_write_step_unique_var:
  assumes fn: "cfg_intra_functional g"
    and wx: "last_write_step g u v x" and wy: "last_write_step g u v y"
  shows "x = y"
proof -
  from wx obtain ax where ax: "(u, ax, v) \<in> intra g" "edge_writes ax x"
    unfolding last_write_step_def by blast
  from wy obtain ay where ay: "(u, ay, v) \<in> intra g" "edge_writes ay y"
    unfolding last_write_step_def by blast
  have "ax = ay" using fn ax(1) ay(1) unfolding cfg_intra_functional_def by blast
  with ax(2) ay(2) show ?thesis by (cases ax) auto
qed

lemma last_write_step_other [dest]:
  "cfg_intra_functional g \<Longrightarrow> last_write_step g u v y \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> last_write_step g u v x"
  using last_write_step_unique_var by blast

subsection \<open>Last writer over a concrete path\<close>

text \<open>\<open>lw_step\<close> folds one \<open>(node, store)\<close> pair of a \<^const>\<open>path\<close> into a running
  \<open>(previous node, current writer)\<close> accumulator.  \<open>last_writer\<close> seeds the fold at the path's
  head with no writer observed yet, exactly \<^const>\<open>entry_store\<close>'s own convention of reading
  the head of \<^const>\<open>path\<close>.\<close>

fun lw_step ::
  "cfg \<Rightarrow> vname \<Rightarrow> (cfg_node \<times> cfg_node option) \<Rightarrow> (cfg_node \<times> store) \<Rightarrow> (cfg_node \<times> cfg_node option)"
where
  "lw_step g x (prev, acc) (v, s) = (v, if last_write_step g prev v x then Some v else acc)"

definition last_writer :: "cfg \<Rightarrow> vname \<Rightarrow> (cfg_node \<times> store) list \<Rightarrow> cfg_node option" where
  "last_writer g x p = snd (foldl (lw_step g x) (fst (hd p), None) (tl p))"

lemma last_writer_single [simp]:
  "last_writer g x [(n, s)] = None"
  by (simp add: last_writer_def)

lemma lw_step_fst:
  "fst (foldl (lw_step g x) (h, acc) xs) = (if xs = [] then h else fst (last xs))"
proof (induction xs arbitrary: h acc)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  obtain v s where y: "y = (v, s)" by (cases y)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis using y by simp
  next
    case False
    have step: "foldl (lw_step g x) (h, acc) (y # ys)
            = foldl (lw_step g x) (v, if last_write_step g h v x then Some v else acc) ys"
      using y by simp
    have "fst (foldl (lw_step g x) (v, if last_write_step g h v x then Some v else acc) ys)
            = fst (last ys)"
      using Cons.IH[of v "if last_write_step g h v x then Some v else acc"] False by simp
    then show ?thesis using step False by simp
  qed
qed

lemma fst_fold_last:
  assumes "p \<noteq> []"
  shows "fst (foldl (lw_step g x) (fst (hd p), None) (tl p)) = fst (last p)"
using assms proof (cases p)
  case (Cons a as)
  then show ?thesis using lw_step_fst[of g x "fst a" None as] by simp
qed simp

text \<open>The characterization lemma: extending a path by one step either sets the writer to the
  newly reached node (if that step wrote \<open>x\<close>) or leaves the previous writer untouched.  This is
  the shape every other characterization lemma below specializes.\<close>
lemma last_writer_snoc:
  assumes "p \<noteq> []"
  shows "last_writer g x (p @ [(v, s')])
           = (if last_write_step g (fst (last p)) v x then Some v else last_writer g x p)"
proof -
  have tl_eq: "tl (p @ [(v, s')]) = tl p @ [(v, s')]" using assms by (cases p) auto
  have hd_eq: "hd (p @ [(v, s')]) = hd p" using assms by (simp add: hd_append)
  obtain pr ac where fold_eq: "foldl (lw_step g x) (fst (hd p), None) (tl p) = (pr, ac)"
    by (cases "foldl (lw_step g x) (fst (hd p), None) (tl p)")
  have pr_eq: "pr = fst (last p)"
    using fst_fold_last[where g = g and x = x and p = p, OF assms] fold_eq by simp
  have ac_eq: "ac = last_writer g x p" using fold_eq unfolding last_writer_def by simp
  show ?thesis
    unfolding last_writer_def hd_eq tl_eq
    by (simp add: fold_eq pr_eq ac_eq)
qed

subsection \<open>Characterization lemmas\<close>

text \<open>(1) A non-writing step preserves the previous writer.\<close>
lemma last_writer_snoc_no_write:
  assumes "p \<noteq> []" and "\<not> last_write_step g (fst (last p)) v x"
  shows "last_writer g x (p @ [(v, s')]) = last_writer g x p"
  using last_writer_snoc[OF assms(1), of g x v s'] assms(2) by simp

text \<open>(2) A step that writes \<open>x\<close> makes its target node the last writer of \<open>x\<close>.\<close>
lemma last_writer_snoc_write:
  assumes "p \<noteq> []" and "last_write_step g (fst (last p)) v x"
  shows "last_writer g x (p @ [(v, s')]) = Some v"
  using last_writer_snoc[OF assms(1), of g x v s'] assms(2) by simp

text \<open>(3) A step that writes a different variable \<open>y\<close> preserves the last writer of \<open>x\<close>, under
  edge-action functionality.\<close>
lemma last_writer_snoc_write_other:
  assumes "p \<noteq> []" and "cfg_intra_functional g"
    and "last_write_step g (fst (last p)) v y" and "x \<noteq> y"
  shows "last_writer g x (p @ [(v, s')]) = last_writer g x p"
proof -
  have "\<not> last_write_step g (fst (last p)) v x"
    using assms(2,3,4) by (rule last_write_step_other)
  from last_writer_snoc_no_write[OF assms(1) this] show ?thesis .
qed

text \<open>(4) The result, if present, names a node actually occurring in the path.\<close>
lemma last_writer_in_path:
  "last_writer g x p = Some w \<Longrightarrow> \<exists>s. (w, s) \<in> set p"
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by (simp add: last_writer_def)
next
  case (snoc z zs)
  obtain v s' where z: "z = (v, s')" by (cases z)
  show ?case
  proof (cases "zs = []")
    case True
    then show ?thesis using snoc.prems z by (simp add: last_writer_def)
  next
    case False
    show ?thesis
    proof (cases "last_write_step g (fst (last zs)) v x")
      case True
      then have "last_writer g x (zs @ [z]) = Some v"
        using last_writer_snoc_write[OF \<open>zs \<noteq> []\<close>] z by simp
      then have "w = v" using snoc.prems by simp
      then show ?thesis using z by auto
    next
      case False
      then have "last_writer g x (zs @ [z]) = last_writer g x zs"
        using last_writer_snoc_no_write[OF \<open>zs \<noteq> []\<close>] z by simp
      then have "last_writer g x zs = Some w" using snoc.prems by simp
      then obtain s where "(w, s) \<in> set zs" using snoc.IH by blast
      then show ?thesis by auto
    qed
  qed
qed


text \<open>(5) \<open>last_writer\<close> is an ordinary total function of its path argument, so its result is
  unique and deterministic by construction --- there is no separate uniqueness obligation to
  discharge once the specification is stated as a function rather than a relation.\<close>
lemmas last_writer_deterministic = last_writer_def

subsection \<open>The activation-local last writer\<close>

definition trace_last_writer :: "cfg \<Rightarrow> vname \<Rightarrow> ltr \<Rightarrow> cfg_node option" where
  "trace_last_writer g x t = last_writer g x (path t)"

text \<open>The trace-level counterpart of \<open>last_writer_snoc_write\<close>, phrased directly against
  \<^const>\<open>valid_ltr\<close>'s \<open>intra\<close> rule: executing a write-to-\<open>x\<close> edge out of a valid trace's sink
  makes the extended trace's last writer of \<open>x\<close> exactly the node just entered.\<close>
theorem trace_last_writer_write:
  assumes t: "t \<in> valid_ltr gs g S"
    and e: "(sink_node t, a, v) \<in> intra g" and s': "s' \<in> edge_step a (sink_store t)"
    and w: "edge_writes a x"
  shows "trace_last_writer g x (extend t (v, s')) = Some v"
proof -
  have nonempty: "path t \<noteq> []" using t by (rule valid_ltr_path_nonempty)
  have lw: "last_write_step g (fst (last (path t))) v x"
    unfolding last_write_step_def using e w by (auto simp: sink_node_def)
  have "path (extend t (v, s')) = path t @ [(v, s')]" by simp
  then show ?thesis
    unfolding trace_last_writer_def
    using last_writer_snoc_write[OF nonempty lw] by simp
qed

text \<open>The trace-level counterpart of \<open>last_writer_snoc_no_write\<close>: an executed step whose
  action does not write \<open>x\<close> preserves the trace's last writer of \<open>x\<close>.\<close>
theorem trace_last_writer_preserved:
  assumes t: "t \<in> valid_ltr gs g S"
    and e: "(sink_node t, a, v) \<in> intra g" and s': "s' \<in> edge_step a (sink_store t)"
    and w: "\<not> edge_writes a x"
    and fn: "cfg_intra_functional g"
  shows "trace_last_writer g x (extend t (v, s')) = trace_last_writer g x t"
proof -
  have nonempty: "path t \<noteq> []" using t by (rule valid_ltr_path_nonempty)
  have "\<not> last_write_step g (fst (last (path t))) v x"
  proof
    assume "last_write_step g (fst (last (path t))) v x"
    then obtain a' where a': "(fst (last (path t)), a', v) \<in> intra g" "edge_writes a' x"
      unfolding last_write_step_def by blast
    have same: "fst (last (path t)) = sink_node t" by (simp add: sink_node_def)
    have "a' = a" using fn a'(1) e unfolding cfg_intra_functional_def same by blast
    with a'(2) w show False by simp
  qed
  then show ?thesis
    unfolding trace_last_writer_def
    using last_writer_snoc_no_write[OF nonempty, of g v x s'] by simp
qed

text \<open>The writer identified for an activation-local trace is a node the activation actually
  reached.\<close>
theorem trace_last_writer_sound:
  assumes "t \<in> valid_ltr gs g S" and "trace_last_writer g x t = Some w"
  shows "\<exists>s. (w, s) \<in> set (path t)"
  using last_writer_in_path assms(2)
  unfolding trace_last_writer_def by simp

text \<open>Combined with \<open>valid_ltr_nodes_in_cfg\<close>, the identified writer is a genuine node
  of the compiled CFG.\<close>
corollary trace_last_writer_sound_cfg_node:
  assumes "t \<in> valid_ltr gs g S" and "trace_last_writer g x t = Some w"
  shows "w \<in> cfg_nodes g"
proof -
  obtain s where "(w, s) \<in> set (path t)"
    using trace_last_writer_sound[OF assms] by blast
  then show ?thesis using valid_ltr_nodes_in_cfg[OF assms(1)] by blast
qed

end
