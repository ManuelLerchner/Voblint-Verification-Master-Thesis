theory Control_Residual
  imports IMP2_Proc_to_CFG
begin

section \<open>Located control inside a compiled procedure fragment\<close>

text \<open>
  \<open>control_at \<Pi> p c n residual v\<close> relates a source runtime residual command to the CFG node
  it currently sits at, inside the fragment obtained by \<open>compile \<Pi> p c n\<close> (procedure \<open>p\<close>,
  source original command \<open>c\<close>, base counter \<open>n\<close>).  It is a pure control relation: it fixes the
  node, not the store; store agreement is a separate simulation-stage concern.

  The relation covers one activation's control.  A \<^const>\<open>Call\<close> crosses into a different
  procedure fragment; \<open>control_at\<close> for the call fragment records only the call site and the
  post-return continuation node, while the callee body is located by \<open>control_at\<close> for the
  callee, tied to the caller through the activation stack of the located executor \<open>cstep\<close>.
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

text \<open>A source command whose body can fall through (contains no \<^const>\<open>Return\<close> on the
  completing path) is, once reduced to \<^const>\<open>SKIP\<close>, located at the fragment's normal-exit
  node.  The lemma is stated for the shapes the fall-through example needs.\<close>
lemma control_at_done_Assign:
  "control_at \<Pi> p (Assign x a) n SKIP (Statement (Suc n))"
  by (rule control_at.AssignDone)

end

