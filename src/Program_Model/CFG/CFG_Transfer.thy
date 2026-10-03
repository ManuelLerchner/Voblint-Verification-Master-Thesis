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
  "edge_collect (EA_Assign x a) S = {s(x := \<lbrakk>a\<rbrakk>\<^sub>e s) | s. s \<in> S}"
  "edge_collect (EA_Special sc x) S = {t. \<exists>s\<in>S. t \<in> special_step sc x s}"
  "edge_collect (EA_Assume b) S = {s. s \<in> S \<and> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
  "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
  "edge_collect (EA_Body p) S = S"
  "edge_collect (EA_Ret e p) S =
     {s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s)) | s. s \<in> S}"
  "edge_collect (EA_Check l c) S = S"
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
  "combine_collect \<G> dst s t = combine_assign dst (t ret_var) (combine_env \<G> s t)"

subsection \<open>Call-entry transfer\<close>

text \<open>Caller-side entry transfer at a call.  The actuals are evaluated in the caller store,
  the callee locals are reset (\<^const>\<open>enter_state\<close>, globals preserved), and the resulting
  values are bound to the callee formals.  All payload comes from the \<open>CallEdge\<close>, so the
  transfer needs no procedure table.  This is exactly the callee-entry store produced by the
  source \<^const>\<open>pstep\<close> \<open>Call\<close> rule.\<close>

definition call_enter :: "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> store \<Rightarrow> store" where
  "call_enter \<G> ca s =
     (case ca of CallEdge dst pars actuals \<Rightarrow>
        enter_binding \<G> 0 aval pars actuals s)"

lemma call_enter_CallEdge:
  "call_enter \<G> (CallEdge dst pars actuals) s
     = bind_formals pars (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s)"
  by (simp add: call_enter_def enter_binding_def enter_state_def)

text \<open>A parameterless call is exactly \<^const>\<open>enter_state\<close>: no actuals to evaluate and no
  formals to bind.\<close>
lemma call_enter_Nil [simp]:
  "call_enter \<G> (CallEdge dst [] []) s = enter_state \<G> s"
  by (simp add: call_enter_CallEdge)

subsection \<open>What an edge reads and what it may change\<close>

text \<open>An edge reads the variables of its expressions. It may change only the
  variable it assigns, and a return only its result slot.\<close>

definition edge_reads :: "edge_action \<Rightarrow> vname list" where
  "edge_reads a = sorted_list_of_set (\<Union> (exp_vnames ` set (edge_expressions a)))"

fun edge_writes :: "edge_action \<Rightarrow> vname list" where
  "edge_writes (EA_Assign x a) = [x]"
| "edge_writes (EA_Special sc x) = [x]"
| "edge_writes (EA_Ret e p) = [ret_var]"
| "edge_writes _ = []"

text \<open>The frame each concrete step respects: a name outside its write set keeps
  its value. A call entry may only bind its formals, and a return takes every
  global from the callee except the destination it assigns.\<close>

lemma edge_step_frame:
  "t \<in> edge_step a s \<Longrightarrow> x \<notin> set (edge_writes a) \<Longrightarrow> t x = s x"
  by (cases a) (auto split: if_splits)

lemma call_enter_frame:
  "\<G> x \<Longrightarrow> x \<notin> set pars \<Longrightarrow> call_enter \<G> (CallEdge dst pars args) s x = s x"
  by (simp add: call_enter_CallEdge bind_formals_other enter_state_def)

lemma combine_collect_frame:
  "\<G> x \<Longrightarrow> dst \<noteq> Some x \<Longrightarrow> combine_collect \<G> dst s t x = t x"
  by (cases dst) (auto simp: combine_collect_def)

subsection \<open>Finite global footprints\<close>

text \<open>The declared globals among those names, as duplicate-free lists a
  transfer folds over to read or publish them.\<close>

definition global_names_in :: "(vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> vname list" where
  "global_names_in G xs = remdups (filter G xs)"

lemma set_global_names_in [simp]:
  "set (global_names_in G xs) = {x \<in> set xs. G x}"
  by (simp add: global_names_in_def)

lemma distinct_global_names_in [simp]: "distinct (global_names_in G xs)"
  by (simp add: global_names_in_def)

definition globals_in_exp :: "(vname \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> vname list" where
  "globals_in_exp G e = global_names_in G (sorted_list_of_set (exp_vnames e))"

definition edge_global_reads :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow> vname list" where
  "edge_global_reads G a = global_names_in G (edge_reads a)"

definition edge_global_writes :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow> vname list" where
  "edge_global_writes G a = global_names_in G (edge_writes a)"

definition call_global_reads :: "(vname \<Rightarrow> bool) \<Rightarrow> exp list \<Rightarrow> vname list" where
  "call_global_reads G es = global_names_in G (sorted_list_of_set (\<Union> (exp_vnames ` set es)))"

lemma set_edge_global_writes [simp]:
  "set (edge_global_writes G a) = {x \<in> set (edge_writes a). G x}"
  by (simp add: edge_global_writes_def)

lemma distinct_global_footprints [simp]:
  "distinct (globals_in_exp G e)"
  "distinct (edge_global_reads G a)"
  "distinct (edge_global_writes G a)"
  "distinct (call_global_reads G es)"
  by (simp_all add: globals_in_exp_def edge_global_reads_def edge_global_writes_def
    call_global_reads_def)

end
