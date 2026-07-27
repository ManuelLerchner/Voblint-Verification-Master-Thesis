theory Control_Residual
  imports IMP2_Proc_to_CFG
begin

section \<open>Located control inside a compiled procedure fragment\<close>

text \<open>
  \<open>control_at \<Pi> p c k n residual v\<close> locates a runtime residual at node \<open>v\<close> inside the
  fragment compiled from command \<open>c\<close> of procedure \<open>p\<close> at base counter \<open>n\<close> with continuation
  \<open>k\<close>.  The relation describes control only; the simulation states store agreement separately.

  The continuation is the node a completed fragment occupies.  A command that has run to
  \<^const>\<open>SKIP\<close> is therefore located at \<open>k\<close> itself rather than at a private exit node, which
  is why the \<open>Done\<close> rules below name no fragment node.

  A call crosses procedure fragments.  The caller fragment records its call site and
  continuation, while the callee fragment locates the callee body.  The activation stack of
  \<open>cstep\<close> connects both locations.
\<close>

subsection \<open>The compiled entry node is the base counter\<close>

text \<open>Every fragment enters at \<open>Statement n\<close>: base commands emit it directly, and \<^const>\<open>Seq\<close>
  inherits the entry of its left operand.\<close>
lemmas compile_entry_node = compile_entry

subsection \<open>Located residuals\<close>

text \<open>
  Residual coverage.  For each source form the located clauses fix which node the residual
  occupies; runtime-only forms are handled as follows.
    \<^item> \<^const>\<open>SKIP\<close>, assignment, sequence (before and after left completion), conditionals,
      loops, call site, entered continuation, and explicit \<^const>\<open>Return\<close> all map to a
      compiled node or to the continuation.
    \<^item> \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> are runtime-only activation markers, not located
      here: once a \<^const>\<open>Return\<close> fires the CFG control is already at \<^term>\<open>FunctionResult p\<close>
      (through the \<^term>\<open>EA_Ret\<close> edge) and the remaining activation return is discharged by the
      located executor \<open>cstep\<close>, not by a fragment node.
\<close>

inductive control_at ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> bool"
  for \<Pi> :: proc_table and p :: pname
where
  Skip:
    "control_at \<Pi> p SKIP k n SKIP (Statement n)"
| Assign:
    "control_at \<Pi> p (Assign x a) k n (Assign x a) (Statement n)"
| AssignDone:
    "control_at \<Pi> p (Assign x a) k n SKIP k"
| SeqLeft:
    "control_at \<Pi> p c1 (Statement (n + csize c1)) n r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n (Seq r c2) v"
| SeqRight:
    "control_at \<Pi> p c2 k (n + csize c1) r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n r v"
| IfHead:
    "control_at \<Pi> p (If b c1 c2) k n (If b c1 c2) (Statement n)"
| IfLeft:
    "control_at \<Pi> p c1 k (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfRight:
    "control_at \<Pi> p c2 k (Suc n + csize c1) r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfDone:
    "control_at \<Pi> p (If b c1 c2) k n SKIP k"
| WhileHead:
    "control_at \<Pi> p (While b c) k n (While b c) (Statement n)"
| WhileUnfolded:
    "control_at \<Pi> p (While b c) k n
       (If b (Seq c (While b c)) SKIP) (Statement n)"
| WhileBody:
    "control_at \<Pi> p c (Statement n) (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (While b c) k n (Seq r (While b c)) v"
| WhileDone:
    "control_at \<Pi> p (While b c) k n SKIP k"
| CallHead:
    "control_at \<Pi> p (Call dst q actuals) k n (Call dst q actuals) (Statement n)"
| CallDone:
    "control_at \<Pi> p (Call dst q actuals) k n SKIP k"
| ReturnHead:
    "control_at \<Pi> p (Return e) k n (Return e) (Statement n)"

subsection \<open>Initial location\<close>

text \<open>A source command is initially located at its entry node \<open>Statement n\<close>.\<close>
lemma control_at_initial:
  "source_com c \<Longrightarrow> control_at \<Pi> p c k n c (Statement n)"
proof (induction c arbitrary: k n)
  case SKIP show ?case by (rule control_at.Skip)
next
  case (Assign x a) show ?case by (rule control_at.Assign)
next
  case (Seq c1 c2)
  have "control_at \<Pi> p c1 (Statement (n + csize c1)) n c1 (Statement n)"
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

text \<open>Every located node is a \<^term>\<open>Statement\<close> node, provided the continuation is one.  Located
  control never sits on a \<^term>\<open>FunctionEntry\<close> or \<^term>\<open>FunctionResult\<close> node --- crossing
  those is the job of the located executor \<open>cstep\<close>, not of within-fragment location.  At
  procedure level the continuation is the epilogue node, so the hypothesis is immediate.\<close>
lemma control_at_node_stmt:
  "control_at \<Pi> p c k n r v \<Longrightarrow> \<exists>j. k = Statement j \<Longrightarrow> \<exists>j. v = Statement j"
  by (induction rule: control_at.induct) auto

subsection \<open>Normal completion is located at the continuation\<close>

text \<open>A falling-through assignment reduced to \<^const>\<open>SKIP\<close> is located at the continuation
  itself.\<close>
lemma control_at_done_Assign:
  "control_at \<Pi> p (Assign x a) k n SKIP k"
  by (rule control_at.AssignDone)

text \<open>
  A completed residual is at the continuation already, except for a source \<^const>\<open>SKIP\<close>,
  whose own node still carries one store-preserving \<^const>\<open>EA_Nop\<close> edge to it.  The
  branch-join hops of the previous layout are gone: both branches of a conditional are
  compiled with the same continuation, so a completed branch is at \<open>k\<close> directly.
\<close>

lemma compile_control_at_SKIP_exit_path:
  "control_at \<Pi> p c0 k n SKIP v \<Longrightarrow> compile \<Pi> p c0 k n = (n', en, E, K)
   \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> intra_path g (v, s) (k, s)"
proof (induction c0 k n "SKIP :: com" v arbitrary: n' en E K rule: control_at.induct)
  case (Skip k n)
  then have "(Statement n, EA_Nop, k) \<in> intra g" by auto
  then show ?case by (rule intra_path_nop)
next
  case (AssignDone x a k n)
  then show ?case by (simp add: star.refl)
next
  case (CallDone dst q actuals k n)
  then show ?case by (simp add: star.refl)
next
  case (IfDone b c1 c2 k n)
  then show ?case by (simp add: star.refl)
next
  case (WhileDone b c k n)
  then show ?case by (simp add: star.refl)
next
  case (SeqRight c2 k n c1 v)
  obtain n2 en2 E2 K2 where c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    by (cases "compile \<Pi> p c2 k (n + csize c1)") auto
  from SeqRight.prems(1) c2 have Esub: "E2 \<subseteq> E" by (auto simp: Let_def split: prod.splits)
  show ?case by (rule SeqRight.hyps(2)[OF c2]) (use Esub SeqRight.prems(2) in blast)
next
  case (IfLeft c1 k n v b c2)
  obtain n1 en1 E1 K1 where c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    by (cases "compile \<Pi> p c1 k (Suc n)") auto
  from IfLeft.prems(1) c1 have Esub: "E1 \<subseteq> E" by (auto simp: Let_def split: prod.splits)
  show ?case by (rule IfLeft.hyps(2)[OF c1]) (use Esub IfLeft.prems(2) in blast)
next
  case (IfRight c2 k n c1 v b)
  obtain n1 en1 E1 K1 where c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    by (cases "compile \<Pi> p c1 k (Suc n)") auto
  have n1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] by simp
  obtain n2 en2 E2 K2 where c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, en2, E2, K2)"
    by (cases "compile \<Pi> p c2 k (Suc n + csize c1)") auto
  from IfRight.prems(1) c1 c2 n1 have Esub: "E2 \<subseteq> E"
    by (auto simp: Let_def split: prod.splits)
  show ?case by (rule IfRight.hyps(2)[OF c2]) (use Esub IfRight.prems(2) in blast)
qed
subsection \<open>Located residuals remain source commands\<close>

lemma control_at_source_com:
  assumes "control_at \<Pi> p c0 k n r v" and "source_com c0"
  shows "source_com r"  using assms
  by (induction rule: control_at.induct) auto

lemma source_com_no_Restore:
  "source_com c \<Longrightarrow> c \<noteq> Restore"
  by (cases c) auto

lemma source_com_no_Unwind:
  "source_com c \<Longrightarrow> c \<noteq> Unwind"
  by (cases c) auto

end

