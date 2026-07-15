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
  | "edge_step (EA_Enter xs es) s = Some (bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s))"

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
  "proc_entry_pps g = {v. \<exists>u xs es. (u, EA_Enter xs es, v) \<in> edges g}"

lemma proc_entry_ppsI:
  "(u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> v \<in> proc_entry_pps g"
  unfolding proc_entry_pps_def by blast

definition call_enter_store :: "cfg \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "call_enter_store g c s t \<longleftrightarrow>
     (\<exists>pe xs es. (c, EA_Enter xs es, pe) \<in> edges g \<and>
       t = bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s))"

subsection \<open>Interprocedural trace witness\<close>

text \<open>
  trace_witness g S v tr : tr is a store sequence reaching v.
  entry   : a singleton [s] for s in the initial set, at the CFG entry.
  proc_entry : callee-relative seed [s] at procedure entry pp when the CFG
            has an enter edge from cfg_entry.
  edge    : extend by one CFG edge (covers intra edges and enter edges).
  combine : at a combine entry, append the callee body trace to the caller
            trace and then append one store produced by \<open>combine_collect\<close>.
            The callee trace starts at the caller-derived enter store recorded
            by \<open>call_enter_store\<close>, so \<open>tl rho\<close> avoids recording that call
            transition twice.
\<close>
inductive trace_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> bool" for g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> trace_witness g S v [s]"
| proc_entry:
    "(cfg_entry g, EA_Enter xs es, v) \<in> edges g \<Longrightarrow>
     s \<in> edge_collect (EA_Enter xs es) S \<Longrightarrow>
     trace_witness g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> trace_witness g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> trace_witness g S v (tr @ [s'])"
| combine: "(c, ex, v, dst) \<in> combines g \<Longrightarrow> trace_witness g S c tau
            \<Longrightarrow> trace_witness g S ex \<rho>
            \<Longrightarrow> r = combine_collect dst (last tau) (last \<rho>)
            \<Longrightarrow> call_enter_store g c (last tau) (hd \<rho>)
            \<Longrightarrow> trace_witness g S v
                  (tau @ tl \<rho> @ [r])"

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
  case (proc_entry xs es v s)
  have enter: "(cfg_entry g, EA_Enter xs es, v) \<in> edges g"
    using proc_entry.hyps(1) .
  have s_in: "s \<in> edge_collect (EA_Enter xs es) S"
    using proc_entry.hyps(2) assms(1) by (meson edge_collect_mono subsetD)
  show ?case
    by (rule trace_witness.proc_entry[OF enter s_in])
next
  case (edge u a v tr s')
  then show ?case by (auto intro!: trace_witness.intros)
next
  case (combine c ex v dst tau \<rho> r)
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
  case (proc_entry xs es v s)
  have enter: "(cfg_entry g, EA_Enter xs es, v) \<in> edges g"
    using edge_sub entry_eq proc_entry.hyps(1) by auto
  show ?case
    by (rule trace_witness.proc_entry[OF enter proc_entry.hyps(2)])
next
  case (edge u a v tr s')
  then show ?case
    using edge_sub edge.hyps(1) edge.IH
    by (auto intro!: trace_witness.intros)
next
  case (combine c ex v dst tau \<rho> r)
  have enter: "call_enter_store g c (last tau) (hd \<rho>)"
    using edge_sub combine.hyps(5)
    unfolding call_enter_store_def by blast
  then show ?case
    using comb_sub combine.hyps(1,4) combine.IH
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
    and x :: vname and a :: aexp and xs :: "vname list" and es :: "aexp list"
  assumes ent_in: "ent \<in> edge_collect (EA_Enter xs es) S"
  assumes enter_edge: "(cfg_entry g, EA_Enter xs es, pe) \<in> edges g"
  assumes edge: "(pe, EA_Assign x a, ex) \<in> edges g"
  assumes body: "body = ent(x := aval a ent)"
  shows "trace_witness g S ex [ent, body]"
proof -
  have ent_w: "trace_witness g S pe [ent]"
    using ent_in enter_edge by (intro trace_witness.proc_entry)
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
  assumes enter: "(cfg_entry g, EA_Enter xs es, pe) \<in> edges g"
  assumes path: "trace_edges g u tr v"
  assumes start: "u = pe"
  assumes init: "hd tr \<in> edge_collect (EA_Enter xs es) S"
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
  assumes comb: "(c, ex, v, dst) \<in> combines g"
  assumes caller: "trace_witness g S c tau"
  assumes callee: "trace_witness g S ex rho"
  assumes ret: "r = combine_collect dst (last tau) (last rho)"
  assumes enter: "call_enter_store g c (last tau) (hd rho)"
  shows "trace_witness g S v (tau @ tl rho @ [r])"
  using assms trace_witness.combine by blast

subsection \<open>Interprocedural projection\<close>

text \<open>
  Every interprocedural trace projects (last store) into the state-based
  interprocedural collecting.  Carries traces through the same lfp post-fixpoint
  steps as cfg_witness_in_cfg_collect (CFG_Collect), projecting with last.
\<close>

lemma enter_mem_cfg_collect_proc_entry:
  assumes enter: "(u, EA_Enter xs es, pe) \<in> edges g"
  assumes sub: "S \<subseteq> cfg_collect g S u"
  assumes s: "s \<in> edge_collect (EA_Enter xs es) S"
  shows "s \<in> cfg_collect g S pe"
proof -
  have s_in: "s \<in> edge_collect (EA_Enter xs es) (cfg_collect g S u)"
    using s edge_collect_mono[OF sub] by blast
  show ?thesis using cfg_collect_edge[OF enter s_in] by simp
qed

lemma enter_image_subset_cfg_collect_proc_entry:
  assumes enter: "(cfg_entry g, EA_Enter xs es, pe) \<in> edges g"
  shows "edge_collect (EA_Enter xs es) S \<subseteq> cfg_collect g S pe"
proof
  fix s
  assume s_in: "s \<in> edge_collect (EA_Enter xs es) S"
  show "s \<in> cfg_collect g S pe"
    using enter_mem_cfg_collect_proc_entry[OF enter cfg_collect_entry s_in]
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
  case (proc_entry xs es v s)
  then have sub: "edge_collect (EA_Enter xs es) S \<subseteq> cfg_collect g S v"
    using enter_image_subset_cfg_collect_proc_entry[OF proc_entry.hyps(1)]
    by simp
  then show ?case
    using proc_entry.hyps(2) by auto
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
  case (combine c ex v dst tau rho r)
  have ih1: "last tau \<in> cfg_collect g S c" using combine.IH(1) .
  have ih2: "last rho \<in> cfg_collect g S ex" using combine.IH(2) .
  have h: "(c, ex, v, dst) \<in> combines g" using combine.hyps(1) .
  have "r \<in> collect_combine_pp g (cfg_collect g S) v"
    using collect_combine_pp_member[OF h refl ih1 ih2 combine.hyps(4)] .
  then have "r \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def by auto
  then have "r \<in> cfg_collect g S v"
    using cfg_collect_post by blast
  then show ?case by (simp add: last_appendR)
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
    "(cfg_entry g, EA_Enter xs es, v) \<in> edges g \<Longrightarrow>
     s \<in> edge_collect (EA_Enter xs es) S \<Longrightarrow>
     trace_witness_d dg cmp g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> trace_witness_d dg cmp g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> trace_witness_d dg cmp g S v (tr @ [s'])"
| combine: "(c, ex, v, dst) \<in> combines g \<Longrightarrow> trace_witness_d dg cmp g S c tau
            \<Longrightarrow> trace_witness_d dg cmp g S ex rho
            \<Longrightarrow> r = combine_collect dst (last tau) (last rho)
            \<Longrightarrow> call_enter_store g c (last tau) (hd rho)
            \<Longrightarrow> cmp (dg tau) (dg rho)
            \<Longrightarrow> trace_witness_d dg cmp g S v
                  (tau @ tl rho @ [r])"

definition cfg_collect_trace_d ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "cfg_collect_trace_d dg cmp g S v = {tr. trace_witness_d dg cmp g S v tr}"

lemma trace_witness_d_imp:
  "trace_witness_d dg cmp g S v tr \<Longrightarrow> trace_witness g S v tr"
proof (induction rule: trace_witness_d.induct)
  case (entry v s)
  then show ?case by (intro trace_witness.entry) auto
next
  case (proc_entry xs es v s)
  then show ?case by (intro trace_witness.proc_entry) auto
next
  case (edge u a v tr s')
  then show ?case by (intro trace_witness.edge) auto
next
  case (combine c ex v dst tau rho r)
  then show ?case by (intro trace_witness.combine) auto
qed

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
  assumes enter: "(cfg_entry g, EA_Enter xs es, pe) \<in> edges g"
  assumes path: "trace_edges g u tr v"
  assumes start: "u = pe"
  assumes init: "hd tr \<in> edge_collect (EA_Enter xs es) S"
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
  assumes comb: "(c, ex, v, dst) \<in> combines g"
  assumes caller: "trace_witness_d dg cmp g S c tau"
  assumes callee: "trace_witness_d dg cmp g S ex rho"
  assumes ret: "r = combine_collect dst (last tau) (last rho)"
  assumes enter: "call_enter_store g c (last tau) (hd rho)"
  assumes compat: "cmp (dg tau) (dg rho)"
  shows "trace_witness_d dg cmp g S v (tau @ tl rho @ [r])"
  using assms trace_witness_d.combine by blast

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


subsection \<open>Context-indexed collecting semantics (B0)\<close>

text \<open>
  The store collecting at a program point, refined by a context \<open>c\<close>: project to
  their last store only the reaching traces whose digest \<open>dg tr\<close> is compatible
  with \<open>c\<close>.  This is the \<open>(pp, c)\<close>-indexed semantics a context-sensitive solver
  must over-approximate; \<open>alpha_ctx\<close> is the projection, \<open>cfg_collect_ctx\<close> applies
  it to the trace collecting.  With \<open>cmp = (\<lambda>_ _. True)\<close> every reaching trace is
  kept and the context dimension collapses to flat \<open>alpha_last\<close>.
\<close>

definition alpha_ctx ::
  "(trace \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> trace set \<Rightarrow> 'c \<Rightarrow> store set" where
  "alpha_ctx dg cmp T c = {last tr | tr. tr \<in> T \<and> cmp (dg tr) c}"

definition cfg_collect_ctx ::
  "(trace \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> store set" where
  "cfg_collect_ctx dg cmp g S v c = alpha_ctx dg cmp (cfg_collect_trace g S v) c"

text \<open>Bridge to the existing digest infrastructure: context collecting is the
  last-store projection of the digest-compatible reaching traces.\<close>
lemma cfg_collect_ctx_reaching_compat:
  "cfg_collect_ctx dg cmp g S v c = alpha_last (reaching_compat dg cmp c g S v)"
  unfolding cfg_collect_ctx_def alpha_ctx_def alpha_last_def reaching_compat_def
  by auto

text \<open>Adding a context only shrinks the collected stores.\<close>
lemma cfg_collect_ctx_subset_flat:
  "cfg_collect_ctx dg cmp g S v c \<subseteq> alpha_last (cfg_collect_trace g S v)"
  unfolding cfg_collect_ctx_reaching_compat
  by (rule alpha_last_mono[OF reaching_compat_subset])

text \<open>Flat collapse: a trivial compatibility recovers the context-insensitive read.\<close>
lemma cfg_collect_ctx_flat:
  "cfg_collect_ctx dg (\<lambda>_ _. True) g S v c = alpha_last (cfg_collect_trace g S v)"
  unfolding cfg_collect_ctx_def alpha_ctx_def alpha_last_def by auto

text \<open>Context collecting lands in the state-based collecting, as the flat read does.\<close>
theorem cfg_collect_ctx_le:
  "cfg_collect_ctx dg cmp g S v c \<subseteq> cfg_collect g S v"
  unfolding cfg_collect_ctx_reaching_compat
  by (rule alpha_last_reaching_compat_le)


subsection \<open>Incremental context tracking refines the trace digest (B2)\<close>

text \<open>
  A context-sensitive solver indexes unknowns by \<open>(pp, context)\<close> and computes the
  context INCREMENTALLY: seeded at entries, advanced one edge at a time by
  \<open>step_ctx\<close>, combined at returns by \<open>comb_ctx\<close>.  The collecting semantics instead
  filters traces by the WHOLE-trace digest \<open>dg\<close> (\<open>reaching_compat\<close> /
  \<open>cfg_collect_ctx\<close>).  \<open>context_transfer\<close> fixes the incremental transfers with their
  per-step refinement obligations against \<open>dg\<close>; \<open>trace_witness_ctx\<close> threads the
  incremental context along a witness derivation; \<open>context_step_refines_dg\<close> shows
  the incremental context is \<open>dg\<close>-compatible on every witness trace, so the
  context-threaded collecting lands in \<open>cfg_collect_ctx\<close>.  An instance discharges
  only the three local obligations and inherits whole-trace faithfulness.
\<close>

locale context_transfer =
  fixes dg :: "trace \<Rightarrow> 'c"
    and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and seed_ctx :: 'c
    and step_ctx :: "'c \<Rightarrow> edge_action \<Rightarrow> store \<Rightarrow> 'c"
    and comb_ctx :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes seed_ok: "cmp (dg [s]) seed_ctx"
    and step_ok:
      "edge_step a (last tr) = Some s' \<Longrightarrow> cmp (dg tr) c
        \<Longrightarrow> cmp (dg (tr @ [s'])) (step_ctx c a (last tr))"
    and comb_ok:
      "r = combine_collect dst (last tau) (last rho) \<Longrightarrow> cmp (dg tau) c1 \<Longrightarrow> cmp (dg rho) c2
        \<Longrightarrow> cmp (dg (tau @ tl rho @ [r])) (comb_ctx c1 c2)"
begin

inductive trace_witness_ctx ::
  "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> trace \<Rightarrow> bool" for g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> trace_witness_ctx g S v seed_ctx [s]"
| proc_entry:
    "(cfg_entry g, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
      \<Longrightarrow> trace_witness_ctx g S v seed_ctx [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> trace_witness_ctx g S u c tr
      \<Longrightarrow> edge_step a (last tr) = Some s'
      \<Longrightarrow> trace_witness_ctx g S v (step_ctx c a (last tr)) (tr @ [s'])"
| combine: "(cl, ex, v, dst) \<in> combines g \<Longrightarrow> trace_witness_ctx g S cl c1 tau
      \<Longrightarrow> trace_witness_ctx g S ex c2 rho
      \<Longrightarrow> r = combine_collect dst (last tau) (last rho)
      \<Longrightarrow> call_enter_store g cl (last tau) (hd rho)
      \<Longrightarrow> trace_witness_ctx g S v (comb_ctx c1 c2)
            (tau @ tl rho @ [r])"

text \<open>The context-threaded witness forgets to the plain trace witness.\<close>
lemma trace_witness_ctx_imp:
  "trace_witness_ctx g S v c tr \<Longrightarrow> trace_witness g S v tr"
proof (induction rule: trace_witness_ctx.induct)
  case (entry v s)
  then show ?case by (intro trace_witness.entry) auto
next
  case (proc_entry xs es v s)
  then show ?case by (intro trace_witness.proc_entry) auto
next
  case (edge u a v c tr s')
  then show ?case by (intro trace_witness.edge) auto
next
  case (combine cl ex v dst c1 tau c2 rho r)
  then show ?case by (intro trace_witness.combine) auto
qed

text \<open>The incremental context is \<open>dg\<close>-compatible on every witness trace.\<close>
lemma context_step_refines_dg:
  "trace_witness_ctx g S v c tr \<Longrightarrow> cmp (dg tr) c"
proof (induction rule: trace_witness_ctx.induct)
  case (entry v s)
  show ?case by (rule seed_ok)
next
  case (proc_entry xs es v s)
  show ?case by (rule seed_ok)
next
  case (edge u a v c tr s')
  then show ?case by (auto intro: step_ok)
next
  case (combine cl ex v dst c1 tau c2 rho r)
  then show ?case by (auto intro: comb_ok)
qed

text \<open>So the context-threaded collecting is captured by \<open>cfg_collect_ctx\<close> (B0).\<close>
lemma trace_witness_ctx_in_reaching_compat:
  assumes "trace_witness_ctx g S v c tr"
  shows "tr \<in> reaching_compat dg cmp c g S v"
  using assms
  by (auto simp: reaching_compat_def cfg_collect_trace_def dest: trace_witness_ctx_imp context_step_refines_dg)

lemma trace_witness_ctx_last_in_cfg_collect_ctx:
  assumes "trace_witness_ctx g S v c tr"
  shows "last tr \<in> cfg_collect_ctx dg cmp g S v c"
  unfolding cfg_collect_ctx_reaching_compat alpha_last_def
  using trace_witness_ctx_in_reaching_compat[OF assms] by blast

end


end
