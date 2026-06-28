theory CFG_Collect_Trace
  imports CFG_Collect "Voblint_IMP2.IMP2_Globals"
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

subsection \<open>Interprocedural trace witness\<close>

text \<open>
  trace_witness g S v tr : tr is a store sequence reaching v.
  entry   : a singleton [s] for s in the initial set, at the CFG entry.
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

lemma cfg_collect_trace_entry:
  "s \<in> S \<Longrightarrow> [s] \<in> cfg_collect_trace g S (cfg_entry g)"
  unfolding cfg_collect_trace_def using trace_witness.entry by simp

subsection \<open>Interprocedural projection\<close>

text \<open>
  Every interprocedural trace projects (last store) into the state-based
  interprocedural collecting.  Carries traces through the same lfp post-fixpoint
  steps as cfg_witness_in_cfg_collect (CFG_Collect), projecting with last.
\<close>
lemma trace_witness_last_in_cfg_collect:
  assumes "trace_witness g S v tr"
  shows "last tr \<in> cfg_collect g S v"
  using assms
proof (induction rule: trace_witness.induct)
  case (entry v s)
  then show ?case using cfg_collect_entry by auto
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
