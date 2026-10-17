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

definition edge_collect :: "kenv \<Rightarrow> (var_id, exp) gedge_action \<Rightarrow> store set \<Rightarrow> store set" where
  "edge_collect \<kappa> a S = {t. \<exists>s\<in>S. t \<in> edge_step \<kappa> a s}"

lemma edge_collect_simps [simp]:
  "edge_collect \<kappa> EA_Nop S = S"
  "edge_collect \<kappa> (EA_Assign x a) S = {s(x := kind_conv \<kappa> (Some x) (eval a s)) | s. s \<in> S}"
  "edge_collect \<kappa> (EA_Special sc x) S = {t. \<exists>s\<in>S. t \<in> special_step \<kappa> sc x s}"
  "edge_collect \<kappa> (EA_Assume b) S = {s. s \<in> S \<and> truthy (eval b s)}"
  "edge_collect \<kappa> (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> truthy (eval b s)}"
  "edge_collect \<kappa> (EA_Body p) S = S"
  "edge_collect \<kappa> (EA_Ret e p) S =
     {s(ReturnVar := (case e of None \<Rightarrow> s ReturnVar | Some a \<Rightarrow> eval a s)) | s. s \<in> S}"
  "edge_collect \<kappa> (EA_Check l c) S = S"
  unfolding edge_collect_def by (auto split: if_splits)

lemma edge_collect_single:
  "edge_collect \<kappa> a {s} = edge_step \<kappa> a s"
  by (cases a) (auto split: if_splits)

lemma edge_collect_empty_set [simp]: "edge_collect \<kappa> a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect \<kappa> a S \<subseteq> edge_collect \<kappa> a T"
  using assms by (cases a) auto

subsection \<open>Return-value transfer\<close>

text \<open>Return-value rehydration at the caller: write the callee's return slot into the
  destination over the combined store (callee globals, caller locals), converted to the
  destination.  It is fixed by the call's destination \<open>dst\<close>, which the \<open>CallEdge\<close> already
  records --- no side lookup.\<close>

definition combine_collect ::
    "kenv \<Rightarrow> var_id option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect \<kappa> dst s t = combine_assign dst (kind_conv \<kappa> dst (t ReturnVar)) (combine_env is_global s t)"

subsection \<open>Call-entry transfer\<close>

text \<open>Caller-side entry transfer at a call.  The actuals are evaluated in the caller store,
  the callee locals are reset (\<^const>\<open>enter_state\<close>, globals preserved), and the resulting
  values are bound to the callee formals, each converted to its formal.  All payload
  comes from the \<open>CallEdge\<close>, so the transfer needs no procedure table.  This is exactly
  the entered store produced by the source \<^const>\<open>pstep\<close> \<open>Call\<close> rule.\<close>

definition call_enter :: "kenv \<Rightarrow> (var_id, exp) gcall_action \<Rightarrow> store \<Rightarrow> store" where
  "call_enter \<kappa> ca s =
     (case ca of CallEdge dst pars actuals \<Rightarrow>
        bind_formals pars (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) pars (map (\<lambda>e. eval e s) actuals))
          (enter_state is_global s))"

lemma call_enter_CallEdge:
  "call_enter \<kappa> (CallEdge dst pars actuals) s
     = bind_formals pars (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) pars (map (\<lambda>e. eval e s) actuals))
         (enter_state is_global s)"
  by (simp add: call_enter_def)

text \<open>A parameterless call is exactly \<^const>\<open>enter_state\<close>: no actuals to evaluate and no
  formals to bind.\<close>
lemma call_enter_Nil [simp]:
  "call_enter \<kappa> (CallEdge dst [] []) s = enter_state is_global s"
  by (simp add: call_enter_CallEdge)

subsection \<open>What an edge may change\<close>

text \<open>An edge may change only the variable it assigns, and a return only its result slot.\<close>

fun edge_writes :: "(var_id, exp) gedge_action \<Rightarrow> var_id list" where
  "edge_writes (EA_Assign x a) = [x]"
| "edge_writes (EA_Special sc x) = [x]"
| "edge_writes (EA_Ret e p) = [ReturnVar]"
| "edge_writes _ = []"

text \<open>The frame each concrete step respects: a name outside its write set keeps
  its value. A call entry may only bind its formals, and a return takes every
  global from the callee except the destination it assigns.\<close>

lemma edge_step_frame:
  "t \<in> edge_step \<kappa> a s \<Longrightarrow> x \<notin> set (edge_writes a) \<Longrightarrow> t x = s x"
  by (cases a) (auto split: if_splits)

lemma call_enter_frame:
  "is_global x \<Longrightarrow> x \<notin> set pars \<Longrightarrow> call_enter \<kappa> (CallEdge dst pars args) s x = s x"
  by (simp add: call_enter_CallEdge bind_formals_other enter_state_def)

lemma combine_collect_frame:
  "is_global x \<Longrightarrow> dst \<noteq> Some x \<Longrightarrow> combine_collect \<kappa> dst s t x = t x"
  by (cases dst) (auto simp: combine_collect_def)

text \<open>The write set runs in generated code.\<close>

lemmas [code] = edge_writes.simps

subsection \<open>What an edge reads\<close>

text \<open>An edge reads the variables of its expressions.\<close>

definition edge_reads :: "(var_id, exp) gedge_action \<Rightarrow> var_id list" where
  "edge_reads a = sorted_list_of_set (\<Union> (exp_vars ` set (edge_expressions a)))"

subsection \<open>Finite global footprints\<close>

text \<open>The declared globals among those names, as duplicate-free lists a
  transfer folds over to read or publish them.\<close>

definition global_names_in :: "('v \<Rightarrow> bool) \<Rightarrow> 'v list \<Rightarrow> 'v list" where
  "global_names_in G xs = remdups (filter G xs)"

lemma set_global_names_in [simp]:
  "set (global_names_in G xs) = {x \<in> set xs. G x}"
  by (simp add: global_names_in_def)

lemma distinct_global_names_in [simp]: "distinct (global_names_in G xs)"
  by (simp add: global_names_in_def)

definition edge_global_reads :: "(var_id \<Rightarrow> bool) \<Rightarrow> (var_id, exp) gedge_action \<Rightarrow> var_id list" where
  "edge_global_reads G a = global_names_in G (edge_reads a)"

text \<open>The writes are those of the concrete step, so they follow the return slot.\<close>

definition edge_global_writes :: "(var_id \<Rightarrow> bool) \<Rightarrow> (var_id, exp) gedge_action \<Rightarrow> var_id list" where
  "edge_global_writes G a = global_names_in G (edge_writes a)"

definition call_global_reads :: "(var_id \<Rightarrow> bool) \<Rightarrow> exp list \<Rightarrow> var_id list" where
  "call_global_reads G es = global_names_in G (sorted_list_of_set (\<Union> (exp_vars ` set es)))"

lemma set_edge_global_writes [simp]:
  "set (edge_global_writes G a) = {x \<in> set (edge_writes a). G x}"
  by (simp add: edge_global_writes_def)

lemma distinct_global_footprints [simp]:
  "distinct (edge_global_reads G a)"
  "distinct (edge_global_writes G a)"
  "distinct (call_global_reads G es)"
  by (simp_all add: edge_global_reads_def edge_global_writes_def call_global_reads_def)

end
