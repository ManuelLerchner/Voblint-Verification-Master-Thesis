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

  A return does not use any \<open>FunctionResult p --> cont\<close> intra edge (there is none): the
  continuation is recovered from the activation stack, so a single \<^term>\<open>FunctionResult\<close> node
  serves every caller.  Lexical scope frames create no activation --- they are flattened into
  intra flow --- so the stack holds one entry per \<^emph>\<open>call\<close>, never per scope.
\<close>

type_synonym cframe = "cfg_node \<times> vname option \<times> store"
type_synonym cconf = "cfg_node \<times> store \<times> cframe list"

inductive cstep :: "cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for g where
  Intra:
    "(u, a, v) \<in> intra g \<Longrightarrow> edge_step a s = Some s' \<Longrightarrow>
     cstep g (u, s, stk) (v, s', stk)"
| Call:
    "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     cstep g (u, s, stk)
       (FunctionEntry q, call_enter (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
| Return:
    "cstep g (FunctionResult q, t, (cont, dst, caller) # stk)
       (cont, combine_collect dst caller t, stk)"

subsection \<open>Single-step and small-step lemmas\<close>

lemma cstep_star_single: "cstep g cf cf' \<Longrightarrow> star (cstep g) cf cf'"
  by (rule star.step[OF _ star.refl])

lemma cstep_nop:
  assumes "(u, EA_Nop, v) \<in> intra g"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assign:
  assumes "(u, EA_Assign x a, v) \<in> intra g"
  shows "cstep g (u, s, stk) (v, s(x := aval a s), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_assume:
  assumes "(u, EA_Assume b, v) \<in> intra g" and "bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (simp add: assms(2))

lemma cstep_assume_not:
  assumes "(u, EA_AssumeNot b, v) \<in> intra g" and "\<not> bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF assms(1)]) (simp add: assms(2))

lemma cstep_ret:
  assumes "(u, EA_Ret e q, v) \<in> intra g"
  shows "cstep g (u, s, stk)
     (v, s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)), stk)"
  by (rule cstep.Intra[OF assms]) simp

lemma cstep_call:
  "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
   cstep g (u, s, stk)
     (FunctionEntry q, call_enter (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"
  by (rule cstep.Call)

lemma cstep_return:
  "cstep g (FunctionResult q, t, (cont, dst, caller) # stk)
     (cont, combine_collect dst caller t, stk)"
  by (rule cstep.Return)

lemma cstep_star_nop_right:
  "star (cstep g) cf (u, s, stk) \<Longrightarrow> (u, EA_Nop, v) \<in> intra g \<Longrightarrow>
   star (cstep g) cf (v, s, stk)"
  by (meson star_trans cstep_star_single cstep_nop)

subsection \<open>Activation-stack matching\<close>

text \<open>The source frame stack carries both lexical (scope) and activation (call) frames; only
  activation frames cross a procedure boundary and thus appear on the CFG stack.  \<open>act_frames\<close>
  projects a source stack to its activation frames, recording caller store and destination.\<close>

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

subsection \<open>Fragment edge lemmas\<close>

text \<open>A located call site corresponds to a concrete call edge carrying the callee's declared
  formals; the continuation is the node immediately after the call site.  This is the unique
  call edge the compiler emits for the call (see \<open>compile_Call_calls\<close>).\<close>
lemma compile_seq_call_edge:
  assumes "\<Pi> pin = Some decl"
      and "compile \<Pi> pout (Seq (Call (Some rin) pin actuals) after) n = (n', en, ex, E, K)"
  shows "(Statement n, CallEdge (Some rin) (formals decl) actuals, FunctionEntry pin,
          Statement (Suc n)) \<in> K"
  using assms by (auto split: prod.splits)

text \<open>An early \<^const>\<open>Return\<close> in a sequence compiles to an \<^term>\<open>EA_Ret\<close> edge from the
  return's node straight to \<^term>\<open>FunctionResult p\<close> --- located returns target the enclosing
  function result.  The dead code after the return sits behind a separate node the return
  edge bypasses.\<close>
lemma compile_seq_return_edge:
  "compile \<Pi> p (Seq (Return (Some e)) dead) n = (n', en, ex, E, K) \<Longrightarrow>
   (Statement n, EA_Ret (Some e) p, FunctionResult p) \<in> E"
  by (auto split: prod.splits)

subsection \<open>Regression example: early return skips dead code\<close>

text \<open>
  A configuration inside \<^term>\<open>Seq (Return (Some e)) dead\<close> is located at the return's
  node, and a single \<^const>\<open>cstep\<close> along the compiled \<^term>\<open>EA_Ret\<close> edge reaches
  \<^term>\<open>FunctionResult p\<close> --- publishing \<open>e\<close> into \<^const>\<open>ret_var\<close> --- without ever locating the
  dead code (\<^term>\<open>FunctionResult p\<close> is not a \<^term>\<open>Statement\<close> node, so it is disjoint from the
  \<open>dead\<close> fragment).
\<close>
theorem example_early_return_skips_dead:
  assumes comp: "compile \<Pi> p (Seq (Return (Some e)) dead) n = (n', en, ex, E, K)"
      and sub: "E \<subseteq> intra g"
  shows "control_at \<Pi> p (Seq (Return (Some e)) dead) n
           (Seq (Return (Some e)) dead) (Statement n)"
    and "cstep g (Statement n, s, stk)
           (FunctionResult p, s(ret_var := aval e s), stk)"
    and "\<forall>k. FunctionResult p \<noteq> Statement k"
proof -
  show "control_at \<Pi> p (Seq (Return (Some e)) dead) n
          (Seq (Return (Some e)) dead) (Statement n)"
    by (rule control_at.SeqLeft[OF control_at.ReturnHead])
  have "(Statement n, EA_Ret (Some e) p, FunctionResult p) \<in> intra g"
    using compile_seq_return_edge[OF comp] sub by blast
  from cstep_ret[OF this]
  show "cstep g (Statement n, s, stk) (FunctionResult p, s(ret_var := aval e s), stk)"
    by simp
  show "\<forall>k. FunctionResult p \<noteq> Statement k" by simp
qed

subsection \<open>Regression example: nested call preserves the outer activation\<close>

text \<open>
  With the outer procedure body \<^term>\<open>Seq (Call (Some rin) pin actuals) after\<close>, the located
  state before the inner call is at the call site with the outer activation \<open>outer\<close> on the
  stack.  Firing the inner call moves to \<^term>\<open>FunctionEntry pin\<close> and pushes exactly one child
  activation recording the inner continuation \<^term>\<open>Statement (Suc n)\<close>; the outer activation
  \<open>outer\<close> is preserved directly beneath it.
\<close>
theorem example_nested_call_preserves_outer:
  assumes p: "\<Pi> pin = Some decl"
      and comp: "compile \<Pi> pout (Seq (Call (Some rin) pin actuals) after) n = (n', en, ex, E, K)"
      and sub: "K \<subseteq> calls g"
  shows "cstep g (Statement n, s, outer # stk)
           (FunctionEntry pin,
            call_enter (CallEdge (Some rin) (formals decl) actuals) s,
            (Statement (Suc n), Some rin, s) # outer # stk)"
proof -
  have "(Statement n, CallEdge (Some rin) (formals decl) actuals, FunctionEntry pin,
         Statement (Suc n)) \<in> calls g"
    using compile_seq_call_edge[OF p comp] sub by blast
  from cstep_call[OF this] show ?thesis .
qed

text \<open>The frame bookkeeping of the nested call: the child activation sits on top and the outer
  activation is unchanged beneath it.\<close>
lemma example_nested_call_frames:
  "frames_match frs stk \<Longrightarrow>
   frames_match (Frame caller (Some rin) # frs)
     ((Statement (Suc n), Some rin, caller) # stk)"
  by (rule frames_match_call)

subsection \<open>Regression example: normal fall-through\<close>

text \<open>
  A procedure whose body completes normally is, once the body is reduced to \<^const>\<open>SKIP\<close>,
  located immediately before the generated fall-through \<^term>\<open>EA_Ret\<close> edge that publishes the
  declared result into \<^term>\<open>FunctionResult p\<close>.  Shown here for a single-assignment body, whose
  normal exit is \<^term>\<open>Statement (Suc n)\<close>.
\<close>
theorem example_normal_fallthrough:
  assumes comp: "compile_proc \<Pi> p decl n = (n', E, K)"
      and body: "body decl = Assign x a"
  shows "control_at \<Pi> p (body decl) n SKIP (Statement (Suc n))"
    and "(Statement (Suc n), EA_Ret (result decl) p, FunctionResult p) \<in> E"
proof -
  show "control_at \<Pi> p (body decl) n SKIP (Statement (Suc n))"
    unfolding body by (rule control_at.AssignDone)
  show "(Statement (Suc n), EA_Ret (result decl) p, FunctionResult p) \<in> E"
    using comp by (auto simp: compile_proc_def Let_def body split: prod.splits)
qed

end

