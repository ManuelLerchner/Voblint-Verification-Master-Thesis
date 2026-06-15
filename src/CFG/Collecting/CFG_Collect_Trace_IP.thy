theory CFG_Collect_Trace_IP
  imports CFG_Collect_Trace CFG_Collect_IP
begin

section \<open>Interprocedural trace collecting and the projection lemma\<close>

text \<open>
  cfg_collect_trace (intraprocedural, CFG_Collect_Trace) records the sequence of
  stores along a single CFG path.  cfg_collect_ip (CFG_Collect_IP) is
  state-based with enter edges + combine triples.  This theory forms their
  product: a trace-valued interprocedural collecting whose enter is an ordinary
  edge step and whose combine splices a callee trace (\<rho>) onto the caller trace
  (tau) it returned to, restoring with combine_states (caller locals, callee
  globals).

  The central result is the interprocedural projection (REFINEMENT, not equality):

      alpha_last (cfg_collect_trace_ip g S v)  \<subseteq>  cfg_collect_ip g S v

  Why \<subseteq> and not =:  the state-based cfg_collect_ip over-combines via
  collect_combine_pp -- it pairs EVERY s \<in> \<rho> call with EVERY t \<in> \<rho> exit,
  including caller/callee states that never co-occurred on a real run.  The trace
  combine only splices a callee trace with the caller it actually returned to
  (junction condition hd \<rho> = enter_state (last tau)), so it is strictly more
  precise.  But every matched combine_states (last tau) (last \<rho>) IS produced by
  collect_combine_pp (witness s = last tau \<in> cfg_collect_ip c,
  t = last \<rho> \<in> cfg_collect_ip ex), so the \<subseteq> direction always holds.  This
  lets the state-based soundness (analysis \<supseteq> cfg_collect_ip) carry to the trace
  foundation by transitivity, and the strict cases are the precision payoff.

  cfg_collect_ip = ip.collect (CFG_Collect_Unified, ip_collect_eq), so this lands
  on the unified collecting locale rather than a parallel stack.

  The junction condition is recorded for fidelity (it pins down the genuinely
  reachable interprocedural traces) but is NOT used by the projection: any
  pairing's last store already lands in the over-combining cfg_collect_ip.
\<close>

subsection \<open>Interprocedural trace witness\<close>

text \<open>
  ip_trace_witness g S v tr : tr is a store sequence reaching v.
  entry   : a singleton [s] for s in the initial set, at the CFG entry.
  edge    : extend by one CFG edge (covers intra edges AND enter edges, since
            EA_Enter is an ordinary edge_action with edge_step EA_Enter s =
            Some (enter_state s)).
  combine : at a combine triple (c, ex, ret), splice the callee trace \<rho> (at the
            procedure exit ex) onto the caller trace tau (at the call site c) it
            was entered from, appending the restored return store
            combine_states (last tau) (last \<rho>).
\<close>
inductive ip_trace_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> bool" for g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> ip_trace_witness g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> ip_trace_witness g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> ip_trace_witness g S v (tr @ [s'])"
| combine: "(c, ex, v) \<in> combines g \<Longrightarrow> ip_trace_witness g S c tau
            \<Longrightarrow> ip_trace_witness g S ex \<rho>
            \<Longrightarrow> hd \<rho> = enter_state (last tau)
            \<Longrightarrow> ip_trace_witness g S v
                  (tau @ \<rho> @ [combine_states (last tau) (last \<rho>)])"

definition cfg_collect_trace_ip :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "cfg_collect_trace_ip g S v = {tr. ip_trace_witness g S v tr}"

subsection \<open>Basic structure\<close>

lemma ip_trace_witness_nonempty:
  "ip_trace_witness g S v tr \<Longrightarrow> tr \<noteq> []"
  by (induction rule: ip_trace_witness.induct) auto

lemma cfg_collect_trace_ip_entry:
  "s \<in> S \<Longrightarrow> [s] \<in> cfg_collect_trace_ip g S (cfg_entry g)"
  unfolding cfg_collect_trace_ip_def using ip_trace_witness.entry by simp

subsection \<open>Interprocedural projection\<close>

text \<open>
  Every interprocedural trace projects (last store) into the state-based
  interprocedural collecting.  Near-copy of ip_witness_in_cfg_collect_ip
  (CFG_Collect_IP), carrying traces and projecting with last.
\<close>
lemma ip_trace_witness_last_in_cfg_collect_ip:
  assumes "ip_trace_witness g S v tr"
  shows "last tr \<in> cfg_collect_ip g S v"
  using assms
proof (induction rule: ip_trace_witness.induct)
  case (entry v s)
  then show ?case using cfg_collect_ip_entry by auto
next
  case (edge u a v tr s')
  have ih: "last tr \<in> cfg_collect_ip g S u" using edge.IH .
  have e: "(u, a, v) \<in> edges g" using edge.hyps(1) .
  have st: "edge_step a (last tr) = Some s'" using edge.hyps(3) .
  have s'in: "s' \<in> edge_collect a {last tr}"
    using st by (simp add: edge_collect_single)
  have sub: "{last tr} \<subseteq> cfg_collect_ip g S u" using ih by simp
  have "s' \<in> edge_collect a (cfg_collect_ip g S u)"
    using s'in edge_collect_mono[OF sub] by blast
  then have "s' \<in> collect_pp g (cfg_collect_ip g S) v"
    unfolding collect_pp_def using e by auto
  then have "s' \<in> cfg_collect_ip_F g S (cfg_collect_ip g S) v"
    unfolding cfg_collect_ip_F_def by auto
  then have "s' \<in> cfg_collect_ip g S v" using cfg_collect_ip_post by blast
  then show ?case by simp
next
  case (combine c ex v tau \<rho>)
  have ih1: "last tau \<in> cfg_collect_ip g S c" using combine.IH(1) .
  have ih2: "last \<rho> \<in> cfg_collect_ip g S ex" using combine.IH(2) .
  have h: "(c, ex, v) \<in> combines g" using combine.hyps(1) .
  have "combine_states (last tau) (last \<rho>) \<in> collect_combine_pp g (cfg_collect_ip g S) v"
    using collect_combine_pp_member[OF h refl ih1 ih2] .
  then have "combine_states (last tau) (last \<rho>) \<in> cfg_collect_ip_F g S (cfg_collect_ip g S) v"
    unfolding cfg_collect_ip_F_def by auto
  then have "combine_states (last tau) (last \<rho>) \<in> cfg_collect_ip g S v"
    using cfg_collect_ip_post by blast
  then show ?case by (metis last_snoc append_assoc)
qed

theorem alpha_last_cfg_collect_trace_ip_le:
  "alpha_last (cfg_collect_trace_ip g S v) \<subseteq> cfg_collect_ip g S v"
  unfolding alpha_last_def cfg_collect_trace_ip_def
  using ip_trace_witness_last_in_cfg_collect_ip by auto


subsection \<open>Digest-refined interprocedural trace collecting\<close>

text \<open>
  A digest abstracts a trace's history (calling context, lockset, ...).  The
  digest-refined witness adds ONE premise to the combine rule: the caller and
  callee digests must be COMPATIBLE (cmp).  Every other rule is unchanged, so the
  refined trace set is a SUBSET of the unrefined one (cfg_collect_trace_ip_d_subset).
  Soundness therefore carries over verbatim (reaching_global_read_sound_d in
  Trace_IP_Analysis_Sound) -- the digest hook only SHRINKS the trace set.  This
  mechanizes the claim that the ''combine_at digest hook preserves soundness'';
  choosing a concrete digest + proving strictly tighter reads is the precision
  payoff (Example_Trace_Digest_Precision).
\<close>
inductive ip_trace_witness_d ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> bool"
  for dg :: "trace \<Rightarrow> 'd" and cmp :: "'d \<Rightarrow> 'd \<Rightarrow> bool" and g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> ip_trace_witness_d dg cmp g S v [s]"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> ip_trace_witness_d dg cmp g S u tr
         \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> ip_trace_witness_d dg cmp g S v (tr @ [s'])"
| combine: "(c, ex, v) \<in> combines g \<Longrightarrow> ip_trace_witness_d dg cmp g S c tau
            \<Longrightarrow> ip_trace_witness_d dg cmp g S ex \<rho>
            \<Longrightarrow> hd \<rho> = enter_state (last tau)
            \<Longrightarrow> cmp (dg tau) (dg \<rho>)
            \<Longrightarrow> ip_trace_witness_d dg cmp g S v
                  (tau @ \<rho> @ [combine_states (last tau) (last \<rho>)])"

definition cfg_collect_trace_ip_d ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "cfg_collect_trace_ip_d dg cmp g S v = {tr. ip_trace_witness_d dg cmp g S v tr}"

lemma ip_trace_witness_d_imp:
  "ip_trace_witness_d dg cmp g S v tr \<Longrightarrow> ip_trace_witness g S v tr"
  by (induction rule: ip_trace_witness_d.induct) (auto intro: ip_trace_witness.intros)

theorem cfg_collect_trace_ip_d_subset:
  "cfg_collect_trace_ip_d dg cmp g S v \<subseteq> cfg_collect_trace_ip g S v"
  unfolding cfg_collect_trace_ip_d_def cfg_collect_trace_ip_def
  using ip_trace_witness_d_imp by blast

(* Reader-side digest filter: the traces reaching v whose digest is compatible
   with the reading digest d.  The precise (history-sensitive) global read joins
   only over reaching_compat, not over all reaching traces. *)
definition reaching_compat ::
  "(trace \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace set" where
  "reaching_compat dg cmp d g S v = {tr \<in> cfg_collect_trace_ip g S v. cmp (dg tr) d}"


end
