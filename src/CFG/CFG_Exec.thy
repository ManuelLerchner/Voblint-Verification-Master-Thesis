theory CFG_Exec
  imports CFG_Transfer
begin

section \<open>How a control-flow graph runs\<close>

text \<open>
  \<open>cstep\<close> executes an arbitrary CFG over a node, a store, and a stack of suspended
  activations.  Each \<open>cframe\<close> records where to resume, which variable receives the
  result, and the caller's store.  There are three rules, one per graph phenomenon:
  follow an \<open>intra\<close> edge and apply its transfer; follow a \<open>calls\<close> edge, enter the callee
  and push a frame; at a \<^term>\<open>FunctionResult\<close>, pop the top frame and combine the
  callee's store into the caller's.

  A return follows no edge.  The stack supplies the continuation, so one
  \<^term>\<open>FunctionResult\<close> node serves every caller of a procedure and recursion needs no
  duplicated nodes.  Nothing here mentions the compiler: this is the execution of any
  graph, just as \<open>valid_ltr\<close> is the trace semantics of any graph.
\<close>
type_synonym cframe = "cfg_node \<times> vname option \<times> store"
type_synonym cconf = "cfg_node \<times> store \<times> cframe list"

inductive cstep :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for gs and g where
  Intra:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow>
     cstep gs g (u, s, stk) (v, s', stk)"
| Call:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     cstep gs g (u, s, stk)
       (FunctionEntry q, call_enter gs (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return:
    "cstep gs g (FunctionResult q, t, (cont, dst, caller) # stk)
       (cont, combine_collect gs dst caller t, stk)"

declare cstep.intros [intro]

text \<open>One inversion rule, because the three clauses are told apart by the edge taken rather
  than by the shape of the configuration.  It stays plain \<open>[elim]\<close> so the classical reasoner
  does not split every \<open>cstep\<close> hypothesis three ways before trying anything else.\<close>
inductive_cases cstep_E [elim]: "cstep gs g (u, s, stk) y"

subsection \<open>Single-step and small-step lemmas\<close>

lemma cstep_nop:
  assumes "(u, EA_Nop, v) \<in> intra g"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assign:
  assumes "(u, EA_Assign x a, v) \<in> intra g"
  shows "cstep gs g (u, s, stk) (v, s(x := aval a s), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assume:
  assumes "(u, EA_Assume b, v) \<in> intra g" and "truthy (aval b s)"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (use assms(2) in simp)

lemma cstep_assume_not:
  assumes "(u, EA_AssumeNot b, v) \<in> intra g" and "\<not> truthy (aval b s)"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (use assms(2) in simp)

lemma cstep_ret:
  assumes "(u, EA_Ret e q, v) \<in> intra g"
  shows "cstep gs g (u, s, stk)
     (v, s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_check:
  assumes "(u, EA_Check c, v) \<in> intra g"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms]) simp

subsection \<open>Intra-only paths as stack-preserving runs\<close>

text \<open>An \<^const>\<open>intra_path\<close> is a \<open>cstep\<close> run at any stack: every \<^const>\<open>cfg_intra_step\<close> is a
  \<open>cstep.Intra\<close>, which passes the stack through untouched.  Callers that only need to move
  along local edges can therefore reason on \<open>(node, store)\<close> pairs and lift the result here.\<close>
lemma intra_path_imp_cstep_star:
  "intra_path g x y \<Longrightarrow> star (cstep gs g) (fst x, snd x, stk) (fst y, snd y, stk)"
proof (induction rule: star.induct)
  case (refl a) show ?case by simp
next
  case (step a b c)
  obtain ua sa where a: "a = (ua, sa)" by (cases a)
  obtain ub sb where b: "b = (ub, sb)" by (cases b)
  from step.hyps(1) a b obtain e where "(ua, e, ub) \<in> intra g" "sb \<in> edge_step e sa" by auto
  hence "cstep gs g (ua, sa, stk) (ub, sb, stk)" by (rule cstep.Intra)
  with step.IH a b show ?case by (auto intro: star.step)
qed

subsection \<open>Activation-stack matching\<close>

text \<open>Both stacks record procedure activations.  \<open>act_frames\<close> removes the CFG-only
  continuation component and retains the caller store and destination used by the source.\<close>

fun act_frames :: "frame list \<Rightarrow> (store \<times> vname option) list" where
  "act_frames [] = []"
| "act_frames (Frame s d # frs) = (s, d) # act_frames frs"

definition cframe_act :: "cframe \<Rightarrow> store \<times> vname option" where
  "cframe_act cf = (case cf of (cont, d, s) \<Rightarrow> (s, d))"

text \<open>\<open>frames_match\<close> ties a source frame stack to a CFG activation stack: the activation
  frames agree, in order, on caller store and destination (the continuation node is the CFG's
  own bookkeeping and is not visible to the source).\<close>
definition frames_match :: "frame list \<Rightarrow> cframe list \<Rightarrow> bool" where
  "frames_match frs stk = (act_frames frs = map cframe_act stk)"

lemma frames_match_Nil [simp]: "frames_match [] []"
  by (simp add: frames_match_def)

text \<open>An activation frame matches the top CFG activation on caller store and destination.\<close>
lemma frames_match_activation:
  "frames_match (Frame s d # frs) ((cont, d, s) # stk)
     = frames_match frs stk"
  by (simp add: frames_match_def cframe_act_def)

text \<open>Call entry creates exactly one child activation on top of the preserved caller stack.\<close>
lemma frames_match_call:
  "frames_match frs stk \<Longrightarrow>
   frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  by (simp add: frames_match_activation)


end

