theory Control_Residual
  imports IMP2_Proc_to_CFG
begin

section \<open>Located control inside a compiled procedure fragment\<close>

text \<open>
  \<open>control_at \<Pi> p c n residual v\<close> locates a runtime residual at node \<open>v\<close> inside the
  fragment compiled from command \<open>c\<close> of procedure \<open>p\<close> at base counter \<open>n\<close>.  The relation
  describes control only; the simulation states store agreement separately.

  A call crosses procedure fragments.  The caller fragment records its call site and
  continuation, while the callee fragment locates the callee body.  The activation stack of
  \<open>cstep\<close> connects both locations.
\<close>

subsection \<open>The compiled entry node is the base counter\<close>

text \<open>Every fragment enters at \<open>Statement n\<close>: base commands emit it directly, and \<^const>\<open>Seq\<close>
  inherits the entry of its left operand.\<close>
lemma compile_entry_node:
  "compile \<Pi> p c n = (n', en, ex, E, K) \<Longrightarrow> en = Statement n"
  by (induction c arbitrary: n n' en ex E K rule: com.induct)
     (auto split: prod.splits)

subsection \<open>Located residuals\<close>

text \<open>
  Residual coverage.  For each source form the located clauses fix which node the residual
  occupies; runtime-only forms are handled as follows.
    \<^item> \<^const>\<open>SKIP\<close>, assignment, sequence (before and after left completion), conditionals,
      loops, call site, entered continuation, and explicit \<^const>\<open>Return\<close> all map to a
      compiled node.
    \<^item> \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> are runtime-only activation markers, not located
      here: once a \<^const>\<open>Return\<close> fires the CFG control is already at \<^term>\<open>FunctionResult p\<close>
      (through the \<^term>\<open>EA_Ret\<close> edge) and the remaining activation return is discharged by the
      located executor \<open>cstep\<close>, not by a fragment node.
\<close>

inductive control_at ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> bool"
  for \<Pi> :: proc_table and p :: pname
where
  Skip:
    "control_at \<Pi> p SKIP n SKIP (Statement n)"
| Assign:
    "control_at \<Pi> p (Assign x a) n (Assign x a) (Statement n)"
| AssignDone:
    "control_at \<Pi> p (Assign x a) n SKIP (Statement (Suc n))"
| SeqLeft:
    "control_at \<Pi> p c1 n r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) n (Seq r c2) v"
| SeqRight:
    "compile \<Pi> p c1 n = (n1, en1, ex1, E1, K1) \<Longrightarrow>
     control_at \<Pi> p c2 n1 r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) n r v"
| IfHead:
    "control_at \<Pi> p (If b c1 c2) n (If b c1 c2) (Statement n)"
| IfLeft:
    "control_at \<Pi> p c1 (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) n r v"
| IfRight:
    "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1) \<Longrightarrow>
     control_at \<Pi> p c2 n1 r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) n r v"
| IfDone:
    "compile \<Pi> p (If b c1 c2) n = (n', en, ex, E, K) \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) n SKIP ex"
| WhileHead:
    "control_at \<Pi> p (While b c) n (While b c) (Statement n)"
| WhileUnfolded:
    "control_at \<Pi> p (While b c) n
       (If b (Seq c (While b c)) SKIP) (Statement n)"
| WhileBody:
    "control_at \<Pi> p c (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (While b c) n (Seq r (While b c)) v"
| WhileDone:
    "compile \<Pi> p (While b c) n = (n', en, ex, E, K) \<Longrightarrow>
     control_at \<Pi> p (While b c) n SKIP ex"
| CallHead:
    "control_at \<Pi> p (Call dst q actuals) n (Call dst q actuals) (Statement n)"
| CallDone:
    "control_at \<Pi> p (Call dst q actuals) n SKIP (Statement (Suc n))"
| ReturnHead:
    "control_at \<Pi> p (Return e) n (Return e) (Statement n)"

subsection \<open>Initial location\<close>

text \<open>A source command is initially located at its entry node \<open>Statement n\<close>.\<close>
lemma control_at_initial:
  "source_com c \<Longrightarrow> control_at \<Pi> p c n c (Statement n)"
proof (induction c arbitrary: n)
  case SKIP show ?case by (rule control_at.Skip)
next
  case (Assign x a) show ?case by (rule control_at.Assign)
next
  case (Seq c1 c2)
  have "control_at \<Pi> p c1 n c1 (Statement n)"
    by (rule Seq.IH(1)) (use Seq.prems in simp)
  from control_at.SeqLeft[OF this] show ?case .
next
  case (If b c1 c2) show ?case by (rule control_at.IfHead)
next
  case (While b c) show ?case by (rule control_at.WhileHead)
next
  case (Call dst q actuals) show ?case by (rule control_at.CallHead)
next
  case (Return e) show ?case by (rule control_at.ReturnHead)
next
  case Restore then show ?case by simp
next
  case Unwind then show ?case by simp
qed

subsection \<open>Located nodes are statement nodes\<close>

text \<open>Every located node is a \<^term>\<open>Statement\<close> node: located control never sits on a
  \<^term>\<open>FunctionEntry\<close> or \<^term>\<open>FunctionResult\<close> node --- crossing those is the job of
  the located executor \<open>cstep\<close>, not of within-fragment location.\<close>
lemma control_at_node_stmt:
  "control_at \<Pi> p c n r v \<Longrightarrow> \<exists>k. v = Statement k"
  by (induction rule: control_at.induct)
     (auto simp del: compile.simps dest: compile_entry_exit_stmt)

subsection \<open>Normal completion is located at the fragment exit\<close>

text \<open>A falling-through assignment reduced to \<^const>\<open>SKIP\<close> is located at the fragment's
  normal-exit node.  Composite commands use the path characterization below.\<close>
lemma control_at_done_Assign:
  "control_at \<Pi> p (Assign x a) n SKIP (Statement (Suc n))"
  by (rule control_at.AssignDone)

text \<open>
  A completed residual may remain at a taken branch's exit, one \<^const>\<open>EA_Nop\<close> edge before
  the fragment join.  It reaches the normal exit through store-preserving join edges, so the
  store agrees at both ends of the path.
\<close>

lemma compile_control_at_SKIP_exit_path:
  "control_at \<Pi> p c0 n SKIP v \<Longrightarrow> compile \<Pi> p c0 n = (n', en, ex, E, K)
   \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> intra_path g (v, s) (ex, s)"
proof (induction c0 n "SKIP :: com" v arbitrary: n' en ex E K rule: control_at.induct)
  case (Skip n)
  then show ?case by (auto intro: star.refl)
next
  case (AssignDone x a n)
  then show ?case by (simp add: star.refl)
next
  case (CallDone dst q actuals n)
  then show ?case by (simp add: star.refl)
next
  case (IfDone b c1 c2 n n0 en0 ex0 E0 K0)
  then show ?case by (simp add: star.refl)
next
  case (WhileDone b c n n0 en0 ex0 E0 K0)
  then show ?case by (simp add: star.refl)
next
  case (SeqRight c1 n n1 en1 ex1 E1 K1 c2 v)
  obtain n2 en2 ex2 E2 K2 where c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (cases "compile \<Pi> p c2 n1") auto
  from SeqRight.prems(1) SeqRight.hyps(1) c2
  have ex: "ex = ex2" and Esub: "E2 \<subseteq> E" by (auto simp: Let_def)
  show ?case unfolding ex
    by (rule SeqRight.hyps(3)[OF c2]) (use Esub SeqRight.prems(2) in blast)
next
  case (IfLeft c1 n v b c2)
  obtain n1 en1 ex1 E1 K1 where c1: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    by (cases "compile \<Pi> p c1 (Suc n)") auto
  obtain n2 en2 ex2 E2 K2 where c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (cases "compile \<Pi> p c2 n1") auto
  from IfLeft.prems(1) c1 c2
  have ex: "ex = Statement n2" and Esub: "E1 \<subseteq> E" and join: "(ex1, EA_Nop, Statement n2) \<in> E"
    by (auto simp: Let_def)
  have p1: "intra_path g (v, s) (ex1, s)"
    by (rule IfLeft.hyps(2)[OF c1]) (use Esub IfLeft.prems(2) in blast)
  have p2: "intra_path g (ex1, s) (Statement n2, s)"
    by (rule intra_path_nop) (use join IfLeft.prems(2) in blast)
  show ?case unfolding ex by (rule star_trans[OF p1 p2])
next
  case (IfRight c1 n n1 en1 ex1 E1 K1 c2 v b)
  obtain n2 en2 ex2 E2 K2 where c2: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (cases "compile \<Pi> p c2 n1") auto
  from IfRight.prems(1) IfRight.hyps(1) c2
  have ex: "ex = Statement n2" and Esub: "E2 \<subseteq> E" and join: "(ex2, EA_Nop, Statement n2) \<in> E"
    by (auto simp: Let_def)
  have p1: "intra_path g (v, s) (ex2, s)"
    by (rule IfRight.hyps(3)[OF c2]) (use Esub IfRight.prems(2) in blast)
  have p2: "intra_path g (ex2, s) (Statement n2, s)"
    by (rule intra_path_nop) (use join IfRight.prems(2) in blast)
  show ?case unfolding ex by (rule star_trans[OF p1 p2])
qed

subsection \<open>Located residuals remain source commands\<close>

lemma control_at_source_com:
  assumes "control_at \<Pi> p c0 n r v" and "source_com c0"
  shows "source_com r"
  using assms
  by (induction rule: control_at.induct) auto

lemma source_com_no_Restore:
  "source_com c \<Longrightarrow> c \<noteq> Restore"
  by (cases c) auto

lemma source_com_no_Unwind:
  "source_com c \<Longrightarrow> c \<noteq> Unwind"
  by (cases c) auto

end

