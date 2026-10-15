theory CFG_Exec
  imports CFG_Transfer
begin

section \<open>How a control-flow graph runs\<close>

text \<open>
  \<open>gcstep\<close> executes an arbitrary CFG over a node, a store, and a stack of suspended
  activations.  Each \<open>gcframe\<close> records where to resume, which variable receives the
  result, and the caller's store.  There are three rules, one per graph phenomenon:
  follow an \<open>intra\<close> edge and apply its transfer; follow a \<open>calls\<close> edge, enter the callee
  and push a frame; at a \<^term>\<open>FunctionResult\<close>, pop the top frame and combine the
  callee's store into the caller's.

  A return follows no edge.  The stack supplies the continuation, so one
  \<^term>\<open>FunctionResult\<close> node serves every caller of a procedure and recursion needs no
  duplicated nodes.  Nothing here mentions the compiler: this is the execution of any
  graph, just as \<open>gvalid_activation_trace\<close> is the activation-trace semantics of any graph.
\<close>
type_synonym 'v gcframe = "cfg_node \<times> 'v option \<times> ('v \<Rightarrow> int)"
type_synonym 'v gcconf = "cfg_node \<times> ('v \<Rightarrow> int) \<times> 'v gcframe list"

text \<open>Graph execution is generic in the language like the edge and transfer semantics it
  runs.\<close>

locale cfg_exec_sem = cfg_transfer_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int" and glob :: "'v \<Rightarrow> bool"
begin

inductive gcstep :: "('v, 'e) gcfg \<Rightarrow> 'v gcconf \<Rightarrow> 'v gcconf \<Rightarrow> bool" for g where
  Intra [intro]:
    "(u, a, v) \<in> intra g \<Longrightarrow> s' \<in> gedge_step a s \<Longrightarrow> gcstep g (u, s, stk) (v, s', stk)"
| Call [intro]:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     gcstep g (u, s, stk)
       (FunctionEntry q, gcall_enter (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return [intro]:
    "gcstep g (FunctionResult q, t, (cont, dst, caller) # stk)
       (cont, gcombine_collect dst caller t, stk)"

text \<open>One inversion rule, because the three clauses are told apart by the edge taken rather
  than by the shape of the configuration.  It stays plain \<open>[elim]\<close> so the classical reasoner
  does not split every \<open>gcstep\<close> hypothesis three ways before trying anything else.\<close>
inductive_cases cstep_E [elim]: "gcstep g (u, s, stk) y"

end

subsection \<open>Single-step and small-step lemmas\<close>

text \<open>
  Introduction lemmas for the store-preserving edge actions the simulation steps
  through: body, assume and assume-not.
\<close>

context cfg_exec_sem
begin

lemma cstep_body:
  assumes "(u, EA_Body p, v) \<in> intra g"
  shows "gcstep g (u, s, stk) (v, s, stk)"
  by (rule gcstep.Intra[OF assms]) simp

lemma cstep_assume:
  assumes "(u, EA_Assume b, v) \<in> intra g" and "truthy (ev b s)"
  shows "gcstep g (u, s, stk) (v, s, stk)"
  by (rule gcstep.Intra[OF assms(1)]) (use assms(2) in simp)

lemma cstep_assume_not:
  assumes "(u, EA_AssumeNot b, v) \<in> intra g" and "\<not> truthy (ev b s)"
  shows "gcstep g (u, s, stk) (v, s, stk)"
  by (rule gcstep.Intra[OF assms(1)]) (use assms(2) in simp)

text \<open>An intra path is a \<open>gcstep\<close> run at any stack: every \<^const>\<open>cfg_edge_sem.gcfg_intra_step\<close> is a
  \<open>gcstep.Intra\<close>, which passes the stack through untouched.  Callers that only need to move
  along local edges can therefore reason on \<open>(node, store)\<close> pairs and lift the result here.\<close>
lemma intra_path_imp_cstep_star:
  "star (gcfg_intra_step g) x y \<Longrightarrow> star (gcstep g) (fst x, snd x, stk) (fst y, snd y, stk)"
proof (induction rule: star.induct)
  case (refl a) show ?case by simp
next
  case (step a b c)
  obtain ua sa where a: "a = (ua, sa)" by (cases a)
  obtain ub sb where b: "b = (ub, sb)" by (cases b)
  from step.hyps(1) a b obtain e where "(ua, e, ub) \<in> intra g" "sb \<in> gedge_step e sa" by auto
  hence "gcstep g (ua, sa, stk) (ub, sb, stk)" by (rule gcstep.Intra)
  with step.IH a b show ?case by (auto intro: star.step)
qed

end

subsection \<open>Activation-stack matching\<close>

text \<open>Both stacks record procedure activations.  \<open>act_frames\<close> removes the CFG-only
  continuation component and retains the caller store and destination used by the source.\<close>

fun act_frames :: "'v gframe list \<Rightarrow> (('v \<Rightarrow> int) \<times> 'v option) list" where
  "act_frames [] = []"
| "act_frames (Frame s d # frs) = (s, d) # act_frames frs"

definition cframe_act :: "'v gcframe \<Rightarrow> ('v \<Rightarrow> int) \<times> 'v option" where
  "cframe_act cf = (case cf of (cont, d, s) \<Rightarrow> (s, d))"

text \<open>\<open>frames_match\<close> ties a source frame stack to a CFG activation stack: the activation
  frames agree, in order, on caller store and destination (the continuation node is the CFG's
  own bookkeeping and is not visible to the source).\<close>
definition frames_match :: "'v gframe list \<Rightarrow> 'v gcframe list \<Rightarrow> bool" where
  "frames_match frs stk = (act_frames frs = map cframe_act stk)"

lemma frames_match_Nil [simp]: "frames_match [] []"
  by (simp add: frames_match_def)

text \<open>An activation frame matches the top CFG activation on caller store and destination.\<close>
lemma frames_match_activation:
  "frames_match (Frame s d # frs) ((cont, d, s) # stk)
     = frames_match frs stk"
  by (simp add: frames_match_def cframe_act_def)

end
