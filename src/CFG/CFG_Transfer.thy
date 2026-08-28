theory CFG_Transfer
  imports CFG_Def
begin

section \<open>What each kind of edge does to the store\<close>

text \<open>
  Three transfers, one per thing an edge can do.  \<open>edge_collect\<close> runs an ordinary edge on a
  whole set of stores at once, by lifting the single-store \<^const>\<open>edge_step\<close> pointwise ---
  derived from the concrete step rather than restated, so the two cannot drift apart.
  \<open>call_enter\<close> builds the callee's opening store: evaluate the actuals in the caller,
  reset the locals, bind the formals.  \<open>combine_collect\<close> does the reverse at a return:
  keep the callee's globals, restore the caller's locals, and write the callee's return
  value into the destination.

  All the payload comes from the edge itself, so none of these needs the procedure table.
\<close>

definition edge_collect :: "edge_action \<Rightarrow> store set \<Rightarrow> store set" where
  "edge_collect a S = {t. \<exists>s\<in>S. t \<in> edge_step a s}"

lemma edge_collect_simps [simp]:
  "edge_collect EA_Nop S = S"
  "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s \<in> S}"
  "edge_collect (EA_Special sc x) S = {t. \<exists>s\<in>S. t \<in> special_step sc x s}"
  "edge_collect (EA_Assume b) S = {s. s \<in> S \<and> truthy (aval b s)}"
  "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> truthy (aval b s)}"
  "edge_collect (EA_Ret e p) S =
     {s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) | s. s \<in> S}"
  "edge_collect (EA_Check c) S = S"
  unfolding edge_collect_def by (auto split: if_splits)

lemma edge_collect_single:
  "edge_collect a {s} = edge_step a s"
  by (cases a) (auto split: if_splits)

lemma edge_collect_empty_set [simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

subsection \<open>Return-value transfer\<close>

text \<open>Return-value rehydration at the caller: write the callee's \<open>ret_var\<close> into the
  destination over the combined store (callee globals, caller locals).  It is fixed by the
  call's destination \<open>dst\<close>, which the \<open>CallEdge\<close> already records --- no side lookup.\<close>

definition combine_collect :: "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect gs dst s t = combine_assign dst (t ret_var) (combine_env gs s t)"

lemma combine_collect_None: "combine_collect gs None s t = combine_env gs s t"
  by (simp add: combine_collect_def)

subsection \<open>Call-entry transfer\<close>

text \<open>Caller-side entry transfer at a call.  The actuals are evaluated in the caller store,
  the callee locals are reset (\<^const>\<open>enter_state\<close>, globals preserved), and the resulting
  values are bound to the callee formals.  All payload comes from the \<open>CallEdge\<close>, so the
  transfer needs no procedure table.  This is exactly the callee-entry store produced by the
  source \<^const>\<open>pstep\<close> \<open>Call\<close> rule.\<close>

definition call_enter :: "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> store \<Rightarrow> store" where
  "call_enter gs ca s =
     (case ca of CallEdge dst pars actuals \<Rightarrow>
        bind_formals pars (map (\<lambda>e. aval e s) actuals) (enter_state gs s))"

lemma call_enter_CallEdge:
  "call_enter gs (CallEdge dst pars actuals) s
     = bind_formals pars (map (\<lambda>e. aval e s) actuals) (enter_state gs s)"
  by (simp add: call_enter_def)

text \<open>A parameterless call is exactly \<^const>\<open>enter_state\<close>: no actuals to evaluate and no
  formals to bind.\<close>
lemma call_enter_Nil [simp]:
  "call_enter gs (CallEdge dst [] []) s = enter_state gs s"
  by (simp add: call_enter_CallEdge)

end
