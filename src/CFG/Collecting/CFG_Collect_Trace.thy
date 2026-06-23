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
definition alpha_last :: "trace set => store set" where
  "alpha_last T = {last tr | tr. tr \<in> T}"

subsection \<open>Interprocedural trace witness\<close>

text \<open>
  trace_witness g S v tr : tr is a store sequence reaching v.
  entry   : a singleton [s] for s in the initial set, at the CFG entry.
  edge    : extend by one CFG edge (covers intra edges AND enter edges, since
            EA_Enter is an ordinary edge_action with edge_step EA_Enter s =
            Some (enter_state s)).
  combine : at a combine triple (c, ex, ret), splice the callee trace \<rho> (at the
            procedure exit ex) onto the caller trace tau (at the call site c) it
            was entered from, appending the restored return store
            combine_states (last tau) (last \<rho>).
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
                  (tau @ \<rho> @ [<last tau|last \<rho>>])"

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
  A digest abstracts a trace's history (calling context, lockset, ...).  The
  digest-refined witness adds ONE premise to the combine rule: the caller and
  callee digests must be COMPATIBLE (cmp).  Every other rule is unchanged, so the
  refined trace set is a SUBSET of the unrefined one (cfg_collect_trace_d_subset).
  Soundness therefore carries over verbatim (reaching_global_read_sound_d in
  Trace_Analysis_Sound) -- the digest hook only SHRINKS the trace set.  This
  mechanizes the claim that the ''combine_at digest hook preserves soundness'';
  choosing a concrete digest + proving strictly tighter reads is the precision
  payoff (Example_Trace_Digest_Precision).
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
                  (tau @ \<rho> @ [<last tau|last \<rho>>])"

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

(* Reader-side digest filter: the traces reaching v whose digest is compatible
   with the reading digest d.  The precise (history-sensitive) global read joins
   only over reaching_compat, not over all reaching traces. *)
definition reaching_compat ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "reaching_compat dg cmp d g S v = {tr \<in> cfg_collect_trace g S v. cmp (dg tr) d}"


end
