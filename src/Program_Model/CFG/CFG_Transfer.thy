theory CFG_Transfer
  imports CFG_Def
begin

section \<open>What each kind of edge does to the store\<close>

text \<open>
  Three transfers, one per thing an edge can do.  \<open>gedge_collect\<close> runs an ordinary edge on a
  whole set of stores at once, by lifting the single-store \<^const>\<open>cfg_edge_sem.gedge_step\<close> pointwise ---
  derived from the concrete step rather than restated, so the two cannot drift apart.
  \<open>gcall_enter\<close> builds the callee's opening store: evaluate the actuals in the caller,
  reset the locals, bind the formals.  \<open>gcombine_collect\<close> does the reverse at a return:
  keep the callee's globals, restore the caller's locals, and write the callee's return
  value into the destination.

  All the payload comes from the edge itself, so none of these needs the procedure table.
\<close>

locale cfg_transfer_sem = cfg_edge_sem ev rv conv
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int" +
  fixes glob :: "'v \<Rightarrow> bool"
begin

definition gedge_collect :: "('v, 'e) gedge_action \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> ('v \<Rightarrow> int) set" where
  "gedge_collect a S = {t. \<exists>s\<in>S. t \<in> gedge_step a s}"

lemma edge_collect_simps [simp]:
  "gedge_collect EA_Nop S = S"
  "gedge_collect (EA_Assign x a) S = {s(x := conv (Some x) (ev a s)) | s. s \<in> S}"
  "gedge_collect (EA_Special sc x) S = {t. \<exists>s\<in>S. t \<in> gspecial_step sc x s}"
  "gedge_collect (EA_Assume b) S = {s. s \<in> S \<and> truthy (ev b s)}"
  "gedge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> truthy (ev b s)}"
  "gedge_collect (EA_Body p) S = S"
  "gedge_collect (EA_Ret e p) S =
     {s(rv := (case e of None \<Rightarrow> s rv | Some a \<Rightarrow> ev a s)) | s. s \<in> S}"
  "gedge_collect (EA_Check l c) S = S"
  unfolding gedge_collect_def by (auto split: if_splits)

lemma edge_collect_single:
  "gedge_collect a {s} = gedge_step a s"
  by (cases a) (auto split: if_splits)

lemma edge_collect_empty_set [simp]: "gedge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "gedge_collect a S \<subseteq> gedge_collect a T"
  using assms by (cases a) auto

subsection \<open>Return-value transfer\<close>

text \<open>Return-value rehydration at the caller: write the callee's return slot into the
  destination over the combined store (callee globals, caller locals), converted to the
  destination.  It is fixed by the call's destination \<open>dst\<close>, which the \<open>CallEdge\<close> already
  records --- no side lookup.\<close>

definition gcombine_collect ::
    "'v option \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> ('v \<Rightarrow> int)" where
  "gcombine_collect dst s t = combine_assign dst (conv dst (t rv)) (combine_env glob s t)"

subsection \<open>Call-entry transfer\<close>

text \<open>Caller-side entry transfer at a call.  The actuals are evaluated in the caller store,
  the callee locals are reset (\<^const>\<open>enter_state\<close>, globals preserved), and the resulting
  values are bound to the callee formals, each converted to its formal.  All payload
  comes from the \<open>CallEdge\<close>, so the transfer needs no procedure table.  This is exactly
  the entered store produced by the source \<^const>\<open>vimp_sem.gpstep\<close> \<open>Call\<close> rule.\<close>

definition gcall_enter :: "('v, 'e) gcall_action \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> ('v \<Rightarrow> int)" where
  "gcall_enter ca s =
     (case ca of CallEdge dst pars actuals \<Rightarrow>
        bind_formals pars (map2 (\<lambda>x. conv (Some x)) pars (map (\<lambda>e. ev e s) actuals))
          (enter_state glob s))"

lemma call_enter_CallEdge:
  "gcall_enter (CallEdge dst pars actuals) s
     = bind_formals pars (map2 (\<lambda>x. conv (Some x)) pars (map (\<lambda>e. ev e s) actuals))
         (enter_state glob s)"
  by (simp add: gcall_enter_def)

text \<open>A parameterless call is exactly \<^const>\<open>enter_state\<close>: no actuals to evaluate and no
  formals to bind.\<close>
lemma call_enter_Nil [simp]:
  "gcall_enter (CallEdge dst [] []) s = enter_state glob s"
  by (simp add: call_enter_CallEdge)

subsection \<open>What an edge may change\<close>

text \<open>An edge may change only the variable it assigns, and a return only its result slot.\<close>

fun gedge_writes :: "('v, 'e) gedge_action \<Rightarrow> 'v list" where
  "gedge_writes (EA_Assign x a) = [x]"
| "gedge_writes (EA_Special sc x) = [x]"
| "gedge_writes (EA_Ret e p) = [rv]"
| "gedge_writes _ = []"

text \<open>The frame each concrete step respects: a name outside its write set keeps
  its value. A call entry may only bind its formals, and a return takes every
  global from the callee except the destination it assigns.\<close>

lemma edge_step_frame:
  "t \<in> gedge_step a s \<Longrightarrow> x \<notin> set (gedge_writes a) \<Longrightarrow> t x = s x"
  by (cases a) (auto split: if_splits)

lemma call_enter_frame:
  "glob x \<Longrightarrow> x \<notin> set pars \<Longrightarrow> gcall_enter (CallEdge dst pars args) s x = s x"
  by (simp add: call_enter_CallEdge bind_formals_other enter_state_def)

lemma combine_collect_frame:
  "glob x \<Longrightarrow> dst \<noteq> Some x \<Longrightarrow> gcombine_collect dst s t x = t x"
  by (cases dst) (auto simp: gcombine_collect_def)

end

text \<open>The write set runs in generated code at every language.\<close>

lemmas [code] = cfg_transfer_sem.gedge_writes.simps

subsection \<open>What an edge reads\<close>

text \<open>An edge reads the variables of its expressions, as \<open>evars\<close> names them.\<close>

definition gedge_reads :: "('e \<Rightarrow> 'v::linorder set) \<Rightarrow> ('v, 'e) gedge_action \<Rightarrow> 'v list" where
  "gedge_reads evars a = sorted_list_of_set (\<Union> (evars ` set (edge_expressions a)))"

abbreviation edge_reads :: "edge_action \<Rightarrow> vname list" where
  "edge_reads \<equiv> gedge_reads exp_vnames"

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

definition globals_in_exp :: "(vname \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> vname list" where
  "globals_in_exp G e = global_names_in G (sorted_list_of_set (exp_vnames e))"

definition gedge_global_reads ::
    "('e \<Rightarrow> 'v::linorder set) \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('v, 'e) gedge_action \<Rightarrow> 'v list" where
  "gedge_global_reads evars G a = global_names_in G (gedge_reads evars a)"

text \<open>The writes are those of the concrete step, so they follow the return slot \<open>rv\<close>.\<close>

definition gedge_global_writes :: "'v \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('v, 'e) gedge_action \<Rightarrow> 'v list" where
  "gedge_global_writes rv G a = global_names_in G (cfg_transfer_sem.gedge_writes rv a)"

definition gcall_global_reads ::
    "('e \<Rightarrow> 'v::linorder set) \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> 'v list" where
  "gcall_global_reads evars G es = global_names_in G (sorted_list_of_set (\<Union> (evars ` set es)))"

abbreviation edge_global_reads :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow> vname list" where
  "edge_global_reads \<equiv> gedge_global_reads exp_vnames"

abbreviation edge_global_writes :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow> vname list" where
  "edge_global_writes \<equiv> gedge_global_writes ret_var"

abbreviation call_global_reads :: "(vname \<Rightarrow> bool) \<Rightarrow> exp list \<Rightarrow> vname list" where
  "call_global_reads \<equiv> gcall_global_reads exp_vnames"

lemma set_edge_global_writes [simp]:
  "set (gedge_global_writes rv G a) = {x \<in> set (cfg_transfer_sem.gedge_writes rv a). G x}"
  by (simp add: gedge_global_writes_def)

lemma distinct_global_footprints [simp]:
  "distinct (globals_in_exp G e)"
  "distinct (gedge_global_reads evars G a)"
  "distinct (gedge_global_writes rv G a)"
  "distinct (gcall_global_reads evars G es)"
  by (simp_all add: globals_in_exp_def gedge_global_reads_def gedge_global_writes_def
    gcall_global_reads_def)

end
