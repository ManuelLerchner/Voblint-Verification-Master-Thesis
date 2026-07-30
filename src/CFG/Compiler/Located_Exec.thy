theory Located_Exec
  imports Control_Residual
begin

section \<open>Located CFG execution\<close>

text \<open>
  \<open>cstep\<close> is the concrete execution of the two-relation procedure-aware CFG, in the
  activation-stack shape that mirrors the source \<^const>\<open>pstep\<close> and drives the located
  simulation.  A \<open>cconf\<close> pairs the current node with a store and a stack of pending
  activations; each \<open>cframe\<close> records the continuation node, the caller destination, and the
  saved caller store --- exactly the payload the resume transfer \<^const>\<open>combine_collect\<close>
  needs.

  There are three transitions, one per graph phenomenon:
    \<^item> intra flow follows an \<^const>\<open>intra\<close> edge and applies \<^const>\<open>edge_step\<close> (covering
      \<^term>\<open>EA_Nop\<close>, assignment, both assume forms, and \<^term>\<open>EA_Ret\<close> into
      \<^term>\<open>FunctionResult\<close>); the stack is unchanged;
    \<^item> a call follows a \<^const>\<open>calls\<close> edge, applies the caller-side \<^const>\<open>call_enter\<close>, moves to
      the callee \<^term>\<open>FunctionEntry\<close>, and pushes one activation carrying the continuation;
    \<^item> a return/resume fires at \<^term>\<open>FunctionResult\<close>, pops the top activation, and lands at its
      recorded continuation with the combined store \<^const>\<open>combine_collect\<close>.

  A return does not use a \<open>FunctionResult p --> cont\<close> intra edge.  The activation stack
  supplies the continuation, so one \<^term>\<open>FunctionResult\<close> node serves every caller and
  the stack contains one entry per call.
\<close>

type_synonym cframe = "cfg_node \<times> vname option \<times> store"
type_synonym cconf = "cfg_node \<times> store \<times> cframe list"

inductive cstep :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for gs and g where
  Intra:
    "(u, a, v) \<in> intra g \<Longrightarrow> edge_step a s = Some s' \<Longrightarrow>
     cstep gs g (u, s, stk) (v, s', stk)"
| Call:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     cstep gs g (u, s, stk)
       (FunctionEntry q, call_enter gs (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return:
    "cstep gs g (FunctionResult q, t, (cont, dst, caller) # stk)
       (cont, combine_collect gs dst caller t, stk)"

subsection \<open>Single-step and small-step lemmas\<close>

lemma cstep_star_single: "cstep gs g cf cf' \<Longrightarrow> star (cstep gs g) cf cf'"
  by (rule star.step[OF _ star.refl])

lemma cstep_nop:
  assumes "(u, EA_Nop, v) \<in> intra g"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assign:
  assumes "(u, EA_Assign x a, v) \<in> intra g"
  shows "cstep gs g (u, s, stk) (v, s(x := aval a s), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assume:
  assumes "(u, EA_Assume b, v) \<in> intra g" and "bval b s"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (simp add: assms(2))

lemma cstep_assume_not:
  assumes "(u, EA_AssumeNot b, v) \<in> intra g" and "\<not> bval b s"
  shows "cstep gs g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (simp add: assms(2))

lemma cstep_ret:
  assumes "(u, EA_Ret e q, v) \<in> intra g"
  shows "cstep gs g (u, s, stk)
     (v, s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_call:
  "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
   cstep gs g (u, s, stk)
     (FunctionEntry q, call_enter gs (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
  by (rule cstep.Call)

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

