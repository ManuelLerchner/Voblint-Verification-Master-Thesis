theory CFG_Trace_Collect
  imports CFG_Collecting_Core "Voblint_IMP2.IMP2_Globals"
begin

(*
  Trace-valued collecting semantics, alongside the reachable-state collecting
  of CFG_Collecting_Core.  The central result `lift` shows that projecting
  every trace to its last store recovers `cfg_collect_paths` exactly, so any
  property of the reachable-state collecting transfers to the trace collecting
  through the projection `alpha_last`.

  Traces are encoded as `store list`: the sequence of stores visited along a
  path.  This is all `lift` needs.
*)

type_synonym trace = "store list"

(* \<midarrow>\<midarrow> Single-store step \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  edge_step is the single-store version of edge_collect: it returns None
  exactly when an assume edge filters the store out, and Some of the updated
  store otherwise.
*)
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

(* \<midarrow>\<midarrow> Trace of a single run along an edge path \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Walk an edge path from one start store, recording the sequence of stores
  visited (start store included).  None when some assume kills the run.
*)
fun edges_trace :: "(edge_action * pp) list => store => trace option" where
    "edges_trace [] s = Some [s]"
  | "edges_trace ((a, _) # es) s =
       (case edge_step a s of
          None    => None
        | Some s' => map_option ((#) s) (edges_trace es s'))"

(* Traces are non-empty: the start store is always recorded. *)
lemma edges_trace_nonempty:
  "edges_trace es s = Some tr \<Longrightarrow> tr \<noteq> []"
  by (induction es arbitrary: s tr) (auto split: option.splits)

(*
  The bridge to the existing fold: edges_collect on a singleton keeps exactly
  the last store of the trace (or nothing, when the run is killed).
*)
lemma edges_collect_single:
  "edges_collect es {s} =
     (case edges_trace es s of None \<Rightarrow> {} | Some tr \<Rightarrow> {last tr})"
proof (induction es arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  obtain a p where e: "e = (a, p)" by (cases e) auto
  have step: "edges_collect (e # es) {s} = edges_collect es (edge_collect a {s})"
    unfolding e by simp
  show ?case
  proof (cases "edge_step a s")
    case None
    hence ec: "edge_collect a {s} = {}" by (simp add: edge_collect_single)
    from None have "edges_trace (e # es) s = None" unfolding e by simp
    with step ec show ?thesis by simp
  next
    case (Some s')
    hence ec: "edge_collect a {s} = {s'}" by (simp add: edge_collect_single)
    have tr: "edges_trace (e # es) s = map_option ((#) s) (edges_trace es s')"
      unfolding e using Some by simp
    show ?thesis
    proof (cases "edges_trace es s'")
      case None
      with step ec tr Cons.IH[of s'] show ?thesis by simp
    next
      case (Some tr')
      hence "tr' \<noteq> []" using edges_trace_nonempty by blast
      hence "last (s # tr') = last tr'" by simp
      with step ec tr Some Cons.IH[of s'] show ?thesis by simp
    qed
  qed
qed

(* \<midarrow>\<midarrow> Trace-valued collecting \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  All traces reaching v from some start store in S along some CFG path.
  Mirrors cfg_collect_paths, threading a sequence where a single final store
  used to flow.
*)
definition cfg_collect_trace :: "cfg => store set => pp => trace set" where
  "cfg_collect_trace g S v =
     {tr. \<exists>es s. (g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v) \<and> s \<in> S \<and> edges_trace es s = Some tr}"

(* Projection: the last store of each trace. *)
definition alpha_last :: "trace set => store set" where
  "alpha_last T = {last tr | tr. tr \<in> T}"

(* \<midarrow>\<midarrow> The lift lemma \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Projecting traces to their last store recovers the reachable-state path
  collecting exactly.  Every existing numeric-domain proof composes through
  alpha_last unchanged.
*)
theorem lift:
  "alpha_last (cfg_collect_trace g S v) = cfg_collect_paths g S v"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> alpha_last (cfg_collect_trace g S v)"
  then obtain tr es s where
        es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v" and s: "s \<in> S"
    and et: "edges_trace es s = Some tr" and x: "x = last tr"
    unfolding alpha_last_def cfg_collect_trace_def by auto
  from et x have "x \<in> edges_collect es {s}" by (simp add: edges_collect_single)
  with s have "x \<in> edges_collect es S" using edges_collect_member by blast
  then show "x \<in> cfg_collect_paths g S v"
    unfolding cfg_collect_paths_def using es by auto
next
  fix x assume "x \<in> cfg_collect_paths g S v"
  then obtain es where es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
    and x: "x \<in> edges_collect es S"
    unfolding cfg_collect_paths_def by auto
  from x obtain s where s: "s \<in> S" and xs: "x \<in> edges_collect es {s}"
    using edges_collect_member by blast
  from xs obtain tr where et: "edges_trace es s = Some tr" and xl: "x = last tr"
    by (auto simp: edges_collect_single split: option.splits)
  show "x \<in> alpha_last (cfg_collect_trace g S v)"
    unfolding alpha_last_def cfg_collect_trace_def using es s et xl by auto
qed

(* -- Globals frame lemma -------------------------------------------------- *)
(*
  A global variable that is never assigned along a trace keeps its initial
  value.  This makes the M4 reading precise at the source: an unwritten global
  reads back exactly what it started with.  edge_step preserves any global x
  that the edge does not assign (assignments to other variables, assume/nop, and
  EA_Enter all leave globals untouched -- enter_state keeps globals and zeroes
  only locals).  Lifted along a path: if the CFG never assigns x, every reaching
  trace ends with x at its start value.
*)
lemma edge_step_preserves_global:
  assumes "is_global x"
  assumes "\<forall>e. a \<noteq> EA_Assign x e"
  assumes "edge_step a s = Some s'"
  shows "s' x = s x"
  using assms by (cases a) (auto simp: enter_state_def split: if_splits)

lemma edges_trace_global_frame:
  assumes "is_global x"
  assumes "\<forall>(a, p) \<in> set es. \<forall>e. a \<noteq> EA_Assign x e"
  assumes "edges_trace es s = Some tr"
  shows "(last tr) x = s x"
  using assms
proof (induction es arbitrary: s tr)
  case Nil
  then have "tr = [s]" by auto
  then show ?case by simp
next
  case (Cons ap es)
  obtain a p where ap: "ap = (a, p)" by (cases ap)
  from Cons.prems(3) ap obtain s' where
      step: "edge_step a s = Some s'" and
      rest: "edges_trace es s' = Some (tl tr)" and
      hdtr: "tr = s # tl tr"
    by (auto split: option.splits)
  have notx: "\<forall>e. a \<noteq> EA_Assign x e" using Cons.prems(2) ap by simp
  have tail: "\<forall>(a, p) \<in> set es. \<forall>e. a \<noteq> EA_Assign x e"
    using Cons.prems(2) ap by simp
  have s'x: "s' x = s x"
    by (rule edge_step_preserves_global[OF Cons.prems(1) notx step])
  have nn: "tl tr \<noteq> []" using rest edges_trace_nonempty by blast
  have lt: "last tr = last (tl tr)" using hdtr nn by (metis last_ConsR)
  have "last tr x = s' x" using lt Cons.IH[OF Cons.prems(1) tail rest] by simp
  then show ?case using s'x by simp
qed

lemma cfg_path_actions_in_edges:
  assumes "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "\<forall>(a, w) \<in> set es. \<exists>u'. (u', a, w) \<in> edges g"
  using assms by (induction rule: cfg_path.induct) auto

corollary cfg_collect_trace_global_frame:
  assumes glob: "is_global x"
  assumes unwritten: "\<forall>(u, a, w) \<in> edges g. \<forall>e. a \<noteq> EA_Assign x e"
  assumes tr: "tr \<in> cfg_collect_trace g S v"
  shows "\<exists>s \<in> S. (last tr) x = s x"
proof -
  from tr obtain es s where
      path: "g \<turnstile> cfg_entry g \<longrightarrow>\<^bsub>es\<^esub> v" and s: "s \<in> S"
      and et: "edges_trace es s = Some tr"
    unfolding cfg_collect_trace_def by auto
  have nowrite: "\<forall>(a, p) \<in> set es. \<forall>e. a \<noteq> EA_Assign x e"
    using cfg_path_actions_in_edges[OF path] unwritten by fastforce
  have "(last tr) x = s x"
    by (rule edges_trace_global_frame[OF glob nowrite et])
  thus ?thesis using s by blast
qed

end
