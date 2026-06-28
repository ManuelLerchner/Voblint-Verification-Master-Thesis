theory CFG_Collect_Trace
  imports CFG_Collect_Runs "Voblint_IMP2.IMP2_Globals"
begin

section \<open>Trace-valued collecting semantics\<close>

text \<open>
  Trace-valued interprocedural collecting: store sequences (traces) reaching a
  program point, alongside the reachable-state collecting \<open>cfg_collect\<close>
  (CFG_Collect).  Traces are \<open>store list\<close>: the sequence of stores visited
  along a run.  Projecting every trace to its last store (\<open>alpha_last\<close>) lands in
  the state-based collecting (\<open>alpha_last_cfg_collect_trace_le\<close>), so state-based
  soundness carries to the trace foundation by transitivity.

  Trace witness
       |
       v
  cfg_collect_trace
       | alpha_last
       v
  cfg_collect
       |
       v
  abstract interpretation
\<close>

type_synonym trace = "store list"

subsection \<open>Single-store step\<close>

text \<open>
  edge_step is the single-store version of edge_collect: it returns None
  exactly when an assume edge filters the store out, and Some of the updated
  store otherwise.
\<close>
fun edge_step :: "edge_action => store => store option" where
    "edge_step EA_Nop           s = Some s"
  | "edge_step (EA_Assign x a)  s = Some (s(x := aval a s))"
  | "edge_step (EA_Assume b)    s = (if bval b s then Some s else None)"
  | "edge_step (EA_AssumeNot b) s = (if bval b s then None else Some s)"
  | "edge_step EA_Enter           s = Some (enter_state s)"

(* edge_collect on a singleton agrees with edge_step, viewed as an option-set. *)
lemma edge_collect_single:
  "edge_collect a {s} = set_option (edge_step a s)"
  by (cases a) auto

subsection \<open>Last-store projection\<close>

(* Projection: the last store of each trace. *)
definition alpha_last :: "trace set \<Rightarrow> store set" where
  "alpha_last T = last ` T"

lemma alpha_last_mono:
  "A \<subseteq> B \<Longrightarrow> alpha_last A \<subseteq> alpha_last B"
  unfolding alpha_last_def by blast

subsection \<open>Procedure entry points\<close>

definition proc_entry_pps :: "cfg \<Rightarrow> pp set" where
  "proc_entry_pps g = {v. \<exists>u. (u, EA_Enter, v) \<in> edges g}"

lemma proc_entry_ppsI:
  "(u, EA_Enter, v) \<in> edges g \<Longrightarrow> v \<in> proc_entry_pps g"
  unfolding proc_entry_pps_def by blast

subsection \<open>Interprocedural trace witness\<close>

text \<open>
  trace_witness g S v tr : tr is a store sequence reaching v.
  entry   : a singleton [s] for s in the initial set, at the CFG entry.
  proc_entry : callee-relative seed [s] at procedure entry pp when the CFG
            has an enter edge from cfg_entry (call-at-main-entry layout).
  edge    : extend by one CFG edge (covers intra edges AND enter edges, since
            EA_Enter is an ordinary edge_action with edge_step EA_Enter s =
            Some (enter_state s)).
  combine : at a combine triple (c, ex, ret), append the callee body trace to
            the caller trace and then append the restored return store
            combine_states (last tau) (last \<rho>).  The premise hd \<rho> =
            enter_state (last tau) identifies the callee entry store, so tl \<rho>
            avoids recording that call transition twice.
\<close>
inductive trace_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> bool" for g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> trace_witness g S v [s]"
| proc_entry:
    "(cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S \<Longrightarrow> trace_witness g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> trace_witness g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> trace_witness g S v (tr @ [s'])"
| combine: "(c, ex, v) \<in> combines g \<Longrightarrow> trace_witness g S c tau
            \<Longrightarrow> trace_witness g S ex \<rho>
            \<Longrightarrow> hd \<rho> = enter_state (last tau)
            \<Longrightarrow> trace_witness g S v
                  (tau @ tl \<rho> @ [<last tau|last \<rho>>])"

definition cfg_collect_trace :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "cfg_collect_trace g S v = {tr. trace_witness g S v tr}"

subsection \<open>Basic structure\<close>

lemma trace_witness_nonempty:
  "trace_witness g S v tr \<Longrightarrow> tr \<noteq> []"
  by (induction rule: trace_witness.induct) auto

lemma trace_witness_mono_initial:
  assumes "S' \<subseteq> S"
  assumes "trace_witness g S' v tr"
  shows "trace_witness g S v tr"
  using assms(2)
proof (induction rule: trace_witness.induct)
  case (entry v s)
  then show ?case using entry assms(1) by (auto intro!: trace_witness.entry)
next
  case (proc_entry v s)
  then show ?case using proc_entry assms(1) by (auto intro!: trace_witness.proc_entry)
next
  case (edge u a v tr s')
  then show ?case by (auto intro!: trace_witness.intros)
next
  case (combine c ex v tau \<rho>)
  then show ?case by (auto intro!: trace_witness.intros)
qed

lemma proc_entry_pps_mono:
  "edges g' \<subseteq> edges g \<Longrightarrow> proc_entry_pps g' \<subseteq> proc_entry_pps g"
  by (auto simp: proc_entry_pps_def)

lemma trace_witness_ext_edges:
  assumes edge_sub: "edges g' \<subseteq> edges g"
  assumes comb_sub: "combines g' \<subseteq> combines g"
  assumes entry_eq: "cfg_entry g = cfg_entry g'"
  assumes w: "trace_witness g' S v tr"
  shows "trace_witness g S v tr"
  using w
proof (induction rule: trace_witness.induct)
  case (entry v s)
  then show ?case using entry_eq by (auto intro!: trace_witness.entry)
next
  case (proc_entry v s)
  then have enter': "(cfg_entry g', EA_Enter, v) \<in> edges g'" by simp
  have enter: "(cfg_entry g, EA_Enter, v) \<in> edges g"
    using edge_sub enter' entry_eq by auto
  then show ?case using proc_entry.hyps(2) enter
    by (intro trace_witness.proc_entry)
next
  case (edge u a v tr s')
  then show ?case
    using edge_sub edge.hyps(1) edge.IH
    by (auto intro!: trace_witness.intros)
next
  case (combine c ex v tau \<rho>)
  then show ?case
    using comb_sub combine.hyps(1) combine.IH
    by (auto intro!: trace_witness.intros)
qed

lemma trace_witness_assign_from_entry_store:
  fixes g :: cfg and S :: "store set" and ent body :: store and u v :: pp
    and x :: vname and a :: aexp
  assumes ent_in: "ent \<in> S"
  assumes proc_ent: "u = cfg_entry g"
  assumes edge: "(u, EA_Assign x a, v) \<in> edges g"
  assumes body: "body = ent(x := aval a ent)"
  shows "trace_witness g S v [ent, body]"
proof -
  have ent_w: "trace_witness g S (cfg_entry g) [ent]"
    using ent_in by (intro trace_witness.entry) simp
  have ent_w': "trace_witness g S u [ent]"
    using ent_w proc_ent by simp
  show ?thesis
    using body ent_w' local.edge trace_witness.edge by fastforce
qed

lemma trace_witness_assign_from_proc_entry:
  fixes g :: cfg and S :: "store set" and ent body :: store and pe ex :: pp
    and x :: vname and a :: aexp
  assumes ent_in: "ent \<in> enter_state ` S"
  assumes enter_edge: "(cfg_entry g, EA_Enter, pe) \<in> edges g"
  assumes edge: "(pe, EA_Assign x a, ex) \<in> edges g"
  assumes body: "body = ent(x := aval a ent)"
  shows "trace_witness g S ex [ent, body]"
proof -
  have ent_w: "trace_witness g S pe [ent]"
    using ent_in enter_edge by (intro trace_witness.proc_entry) simp
  show ?thesis
    using body ent_w edge trace_witness.edge by fastforce
qed

lemma cfg_collect_trace_entry:
  "s \<in> S \<Longrightarrow> [s] \<in> cfg_collect_trace g S (cfg_entry g)"
  unfolding cfg_collect_trace_def using trace_witness.entry by simp


subsection \<open>Linear edge traces\<close>

inductive trace_edges :: "cfg => pp => trace => pp => bool" for g where
  single: "trace_edges g v [s] v"
| step:
    "trace_edges g u tr v
     ==> (v, a, w) \<in> edges g
     ==> edge_step a (last tr) = Some s'
     ==> trace_edges g u (tr @ [s']) w"

lemma trace_edges_nonempty:
  "trace_edges g u tr v ==> tr \<noteq> []"
  by (induction rule: trace_edges.induct) auto

lemma trace_witness_edges:
  assumes path: "trace_edges g u tr v"
  assumes start: "u = cfg_entry g"
  assumes init: "hd tr \<in> S"
  shows "trace_witness g S v tr"
  using path start init
proof (induction rule: trace_edges.induct)
  case (single v s)
  then show ?case by (intro trace_witness.entry) auto
next
  case (step u tr v a w s')
  have tr_ne: "tr \<noteq> []"
    using step.hyps(1) by (rule trace_edges_nonempty)
  have prev: "trace_witness g S v tr"
    using step.IH step.prems(1,2) tr_ne by simp
  show ?case
    using trace_witness.edge[OF step.hyps(2) prev step.hyps(3)] by simp
qed

lemma trace_witness_proc_edges:
  assumes enter: "(cfg_entry g, EA_Enter, pe) \<in> edges g"
  assumes path: "trace_edges g u tr v"
  assumes start: "u = pe"
  assumes init: "hd tr \<in> enter_state ` S"
  shows "trace_witness g S v tr"
  using path start init
proof (induction rule: trace_edges.induct)
  case (single v s)
  then show ?case using enter by (intro trace_witness.proc_entry) auto
next
  case (step u tr v a w s')
  have tr_ne: "tr \<noteq> []"
    using step.hyps(1) by (rule trace_edges_nonempty)
  have prev: "trace_witness g S v tr"
    using step.IH step.prems(1,2) tr_ne by simp
  show ?case
    using trace_witness.edge[OF step.hyps(2) prev step.hyps(3)] by simp
qed


lemma trace_witness_combineI:
  assumes comb: "(c, ex, v) \<in> combines g"
  assumes caller: "trace_witness g S c tau"
  assumes callee: "trace_witness g S ex rho"
  assumes enter: "hd rho = enter_state (last tau)"
  assumes ret: "r = <last tau|last rho>"
  shows "trace_witness g S v (tau @ tl rho @ [r])"
  using assms trace_witness.combine by fastforce

subsection \<open>Interprocedural projection\<close>

text \<open>
  Every interprocedural trace projects (last store) into the state-based
  interprocedural collecting.  Carries traces through the same lfp post-fixpoint
  steps as cfg_witness_in_cfg_collect (CFG_Collect), projecting with last.
\<close>

lemma enter_state_mem_cfg_collect_proc_entry:
  assumes enter: "(u, EA_Enter, pe) \<in> edges g"
  assumes sub: "S \<subseteq> cfg_collect g S u"
  assumes s: "s \<in> enter_state ` S"
  shows "s \<in> cfg_collect g S pe"
proof -
  obtain s' where s'_in: "s' \<in> S" and s_eq: "s = enter_state s'"
    using s by blast
  have "s' \<in> cfg_collect g S u" using sub s'_in by blast
  have ent_in: "s \<in> edge_collect EA_Enter (cfg_collect g S u)"
    using s_eq `s' \<in> cfg_collect g S u` by force
  show ?thesis using cfg_collect_edge[OF enter ent_in] by simp
qed

lemma enter_state_image_subset_cfg_collect_proc_entry:
  assumes enter: "(cfg_entry g, EA_Enter, pe) \<in> edges g"
  shows "enter_state ` S \<subseteq> cfg_collect g S pe"
proof
  fix s
  assume s_in: "s \<in> enter_state ` S"
  then obtain s' where s'_in: "s' \<in> S" and s_eq: "s = enter_state s'"
    by blast
  show "s \<in> cfg_collect g S pe"
    using enter_state_mem_cfg_collect_proc_entry[OF enter cfg_collect_entry s_in]
    by simp
qed

lemma trace_witness_last_in_cfg_collect:
  assumes "trace_witness g S v tr"
  shows "last tr \<in> cfg_collect g S v"
  using assms
proof (induction rule: trace_witness.induct)
  case (entry v s)
  then show ?case using cfg_collect_entry by auto
next
  case (proc_entry v s)
  then have sub: "enter_state ` S \<subseteq> cfg_collect g S v"
    using enter_state_image_subset_cfg_collect_proc_entry[OF proc_entry.hyps(1)]
    by simp
  then show ?case
    using proc_entry.hyps(2) sub by (auto simp: subset_iff)
next
  case (edge u a v tr s')
  have ih: "last tr \<in> cfg_collect g S u" using edge.IH .
  have e: "(u, a, v) \<in> edges g" using edge.hyps(1) .
  have st: "edge_step a (last tr) = Some s'" using edge.hyps(3) .
  have s'in: "s' \<in> edge_collect a {last tr}"
    using st by (simp add: edge_collect_single)
  have sub: "{last tr} \<subseteq> cfg_collect g S u" using ih by simp
  have "s' \<in> edge_collect a (cfg_collect g S u)"
    using s'in edge_collect_mono[OF sub] by blast
  then have "s' \<in> collect_pp g (cfg_collect g S) v"
    unfolding collect_pp_def using e by auto
  then have "s' \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def by auto
  then have "s' \<in> cfg_collect g S v" using cfg_collect_post by blast
  then show ?case by simp
next
  case (combine c ex v tau \<rho>)
  have ih1: "last tau \<in> cfg_collect g S c" using combine.IH(1) .
  have ih2: "last \<rho> \<in> cfg_collect g S ex" using combine.IH(2) .
  have h: "(c, ex, v) \<in> combines g" using combine.hyps(1) .
  have "<last tau|last \<rho>> \<in> collect_combine_pp g (cfg_collect g S) v"
    using collect_combine_pp_member[OF h refl ih1 ih2] .
  then have "<last tau|last \<rho>> \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def by auto
  then have "<last tau|last \<rho>> \<in> cfg_collect g S v"
    using cfg_collect_post by blast
  then show ?case by (metis last_snoc append_assoc)
qed

theorem alpha_last_cfg_collect_trace_le:
  "alpha_last (cfg_collect_trace g S v) \<subseteq> cfg_collect g S v"
  unfolding alpha_last_def cfg_collect_trace_def
  using trace_witness_last_in_cfg_collect by auto


subsection \<open>Digest-refined interprocedural trace collecting\<close>

text \<open>
  A digest compresses execution history into a finite context, such as call
  strings or locksets.  The only semantic change is an additional compatibility
  check in the combine rule.  Consequently the refined trace semantics is a
  subset of the original one, preserving soundness while enabling more precise
  analyses.
\<close>
inductive trace_witness_d ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> bool"
  for dg :: "trace \<Rightarrow> 'd" and cmp :: "'d \<Rightarrow> 'd \<Rightarrow> bool" and g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> trace_witness_d dg cmp g S v [s]"
| proc_entry:
    "(cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S \<Longrightarrow> trace_witness_d dg cmp g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> trace_witness_d dg cmp g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> trace_witness_d dg cmp g S v (tr @ [s'])"
| combine: "(c, ex, v) \<in> combines g \<Longrightarrow> trace_witness_d dg cmp g S c tau
            \<Longrightarrow> trace_witness_d dg cmp g S ex \<rho>
            \<Longrightarrow> hd \<rho> = enter_state (last tau)
            \<Longrightarrow> cmp (dg tau) (dg \<rho>)
            \<Longrightarrow> trace_witness_d dg cmp g S v
                  (tau @ tl \<rho> @ [<last tau|last \<rho>>])"

definition cfg_collect_trace_d ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "cfg_collect_trace_d dg cmp g S v = {tr. trace_witness_d dg cmp g S v tr}"

lemma trace_witness_d_imp:
  "trace_witness_d dg cmp g S v tr \<Longrightarrow> trace_witness g S v tr"
  by (induction rule: trace_witness_d.induct) (auto intro: trace_witness.intros)

theorem cfg_collect_trace_d_subset:
  "cfg_collect_trace_d dg cmp g S v \<subseteq> cfg_collect_trace g S v"
  unfolding cfg_collect_trace_d_def cfg_collect_trace_def
  using trace_witness_d_imp by blast

theorem alpha_last_cfg_collect_trace_d_le:
  "alpha_last (cfg_collect_trace_d dg cmp g S v) \<subseteq> cfg_collect g S v"
proof -
  have "alpha_last (cfg_collect_trace_d dg cmp g S v)
      \<subseteq> alpha_last (cfg_collect_trace g S v)"
    by (rule alpha_last_mono[OF cfg_collect_trace_d_subset])
  also have "... \<subseteq> cfg_collect g S v"
    by (rule alpha_last_cfg_collect_trace_le)
  finally show ?thesis .
qed

(* Reader-side digest filter: the traces reaching v whose digest is compatible
   with the reading digest d.  The precise (history-sensitive) global read joins
   only over reaching_compat, not over all reaching traces. *)
definition reaching_compat ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "reaching_compat dg cmp d g S v = {tr \<in> cfg_collect_trace g S v. cmp (dg tr) d}"

lemma trace_witness_d_edges:
  assumes path: "trace_edges g u tr v"
  assumes start: "u = cfg_entry g"
  assumes init: "hd tr \<in> S"
  shows "trace_witness_d dg cmp g S v tr"
  using path start init
proof (induction rule: trace_edges.induct)
  case (single v s)
  then show ?case by (intro trace_witness_d.entry) auto
next
  case (step u tr v a w s')
  have tr_ne: "tr \<noteq> []"
    using step.hyps(1) by (rule trace_edges_nonempty)
  have prev: "trace_witness_d dg cmp g S v tr"
    using step.IH step.prems(1,2) tr_ne by simp
  show ?case
    using trace_witness_d.edge[OF step.hyps(2) prev step.hyps(3)] by simp
qed

lemma trace_witness_d_proc_edges:
  assumes enter: "(cfg_entry g, EA_Enter, pe) \<in> edges g"
  assumes path: "trace_edges g u tr v"
  assumes start: "u = pe"
  assumes init: "hd tr \<in> enter_state ` S"
  shows "trace_witness_d dg cmp g S v tr"
  using path start init
proof (induction rule: trace_edges.induct)
  case (single v s)
  then show ?case using enter by (intro trace_witness_d.proc_entry) auto
next
  case (step u tr v a w s')
  have tr_ne: "tr \<noteq> []"
    using step.hyps(1) by (rule trace_edges_nonempty)
  have prev: "trace_witness_d dg cmp g S v tr"
    using step.IH step.prems(1,2) tr_ne by simp
  show ?case
    using trace_witness_d.edge[OF step.hyps(2) prev step.hyps(3)] by simp
qed

lemma trace_witness_d_combineI:
  assumes comb: "(c, ex, v) \<in> combines g"
  assumes caller: "trace_witness_d dg cmp g S c tau"
  assumes callee: "trace_witness_d dg cmp g S ex rho"
  assumes enter: "hd rho = enter_state (last tau)"
  assumes compat: "cmp (dg tau) (dg rho)"
  assumes ret: "r = <last tau|last rho>"
  shows "trace_witness_d dg cmp g S v (tau @ tl rho @ [r])"
  using assms trace_witness_d.combine by fastforce

lemma reaching_compat_subset:
  "reaching_compat dg cmp d g S v \<subseteq> cfg_collect_trace g S v"
  unfolding reaching_compat_def by blast

theorem alpha_last_reaching_compat_le:
  "alpha_last (reaching_compat dg cmp d g S v) \<subseteq> cfg_collect g S v"
proof -
  have "alpha_last (reaching_compat dg cmp d g S v)
      \<subseteq> alpha_last (cfg_collect_trace g S v)"
    by (rule alpha_last_mono[OF reaching_compat_subset])
  also have "... \<subseteq> cfg_collect g S v"
    by (rule alpha_last_cfg_collect_trace_le)
  finally show ?thesis .
qed


end
