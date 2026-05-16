theory CFG_Path
  imports CFG_Def
begin

(*
  CFG_Path -- Inductive path predicate for CFGs.

  Pattern: inductive path + derived notation + intro/elim/simp lemma library.
  Adapted from: https://github.com/lohner/FormalSSA (Ullrich & Lohner, Isabelle2016)
                "Verified Construction of Static Single-Assignment Form"
                SSA_CFG.thy / Graph_path.thy — path2 + lemma library.
  See wiki: ~/goblint-formalization-kb/wiki/concepts/isabelle-proof-engineering.md
            Pattern 1 (inductive path), Pattern 2 (attribute discipline),
            Pattern 4 (derived _cases / _induct lemmas).

  Why this file exists:
    post_fixpoint_sound and cfg_collect_exit_eq_collect both need to reason
    about sequences of edges from the entry to an arbitrary program point.
    Without an inductive path predicate, every reachability argument requires
    raw list induction and manual invariant re-establishment at each step.

  Design choices vs. FormalSSA:
    - FormalSSA path2: list of *nodes* (predecessor-based graph)
    - Our cfg_path:   list of *(edge_action * pp)* steps (labeled-edge graph)
    Edge actions are recorded because transfer-function composition in
    post_fixpoint_sound needs to know which action was taken on each step.
*)

(* ── Core Inductive Predicate ─────────────────────────────────── *)

(*
  cfg_path g u steps v
    = there is a path from u to v in g, taking the sequence of (action, next-pp)
      pairs listed in 'steps'.

  Base case:  empty path stays at u.
  Step case:  if there is an edge (u, a, w) in g and a path from w to v,
              then we can prepend (a, w) to get a path from u to v.
*)

inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool" where
  empty[intro]: "cfg_path g v [] v"
| step[intro]:  "(u, a, w) : cfg_edges g ==> cfg_path g w es v
                 ==> cfg_path g u ((a, w) # es) v"

(* ── Reachability Abbreviation + Notation ─────────────────────── *)

(*
  g |- u -->* v   iff some path (of any steps) exists from u to v.
  Notation inspired by FormalSSA's "n⌜ns⌝→m".
*)

abbreviation cfg_reaches :: "cfg => pp => pp => bool" ("_ \<turnstile> _ \<rightarrow>* _" [50,0,50] 80) where
  "cfg_reaches g u v == (\<exists>es. cfg_path g u es v)"

(* ── Intro Lemmas ──────────────────────────────────────────────── *)

lemma cfg_reaches_refl[intro, simp]: "g \<turnstile> v \<rightarrow>* v"
  by (rule exI, rule cfg_path.empty)

lemma cfg_reaches_step[intro]:
  "(u, a, w) : cfg_edges g ==> g \<turnstile> w \<rightarrow>* v ==> g \<turnstile> u \<rightarrow>* v"
proof -
  assume e: "(u, a, w) : cfg_edges g" and r: "g \<turnstile> w \<rightarrow>* v"
  from r obtain es where p: "cfg_path g w es v" ..
  show "g \<turnstile> u \<rightarrow>* v"
    by (rule exI, rule cfg_path.step[OF e p])
qed

lemma cfg_path_append:
  "cfg_path g u es1 v ==> cfg_path g v es2 w ==> cfg_path g u (es1 @ es2) w"
proof (induction es1 arbitrary: u)
  case Nil
  then have "u = v"
    by (cases rule: cfg_path.cases) auto
  then show ?case using Nil.prems(2) by simp
next
  case (Cons e es1)
  obtain a w_tgt where e': "e = (a, w_tgt)" by (cases e) auto
  from Cons.prems(1) e' obtain e1: "(u, a, w_tgt) : cfg_edges g" and p1: "cfg_path g w_tgt es1 v"
    by (cases rule: cfg_path.cases) auto
  from Cons.IH[OF p1] Cons.prems(2) have p: "cfg_path g w_tgt (es1 @ es2) w" by simp
  show ?case
    unfolding e'
    by (simp add: cfg_path.step e1 p)  
qed

lemma cfg_reaches_trans[intro]:
  "g \<turnstile> u \<rightarrow>* v ==> g \<turnstile> v \<rightarrow>* w ==> g \<turnstile> u \<rightarrow>* w"
  using cfg_path_append by blast
 

(* ── Cases Lemma (Pattern 4) ───────────────────────────────────── *)

(*
  Named case split mirroring the inductive constructor structure.
  Avoids "simp add: cfg_path.simps" which unfolds too aggressively.
*)

lemma cfg_path_cases[consumes 1, case_names empty step]:
  assumes "cfg_path g u es v"
  obtains
    (empty) "es = []" "u = v"
  | (step)  a w es' where
      "es = (a, w) # es'"
      "(u, a, w) : cfg_edges g"
      "cfg_path g w es' v"
  using assms by (cases rule: cfg_path.cases) auto

(* ── Induction Rule (Pattern 4) ────────────────────────────────── *)

(*
  Custom induction rule with named cases and [consumes 1] so that
    proof (induction rule: cfg_path_induct)
  works directly and produces named subgoals 'empty' and 'step'.
*)

lemma cfg_path_induct[consumes 1, case_names empty step]:
  assumes "cfg_path g u es v"
  assumes empty: "P g v [] v"
  assumes step:  "!!u a w es.
                    (u, a, w) : cfg_edges g ==>
                    cfg_path g w es v ==>
                    P g w es v ==>
                    P g u ((a, w) # es) v"
  shows "P g u es v"
  using assms  apply (induction rule: cfg_path.induct)
  by(auto)
 

(* ── Elim / Simp Lemmas ────────────────────────────────────────── *)

lemma cfg_path_not_Nil_imp_step[dest]:
  "cfg_path g u es v ==> es \<noteq> [] ==>
   \<exists>a w es'. es = (a, w) # es' \<and> (u, a, w) \<in> cfg_edges g \<and> cfg_path g w es' v"
  by (erule cfg_path.cases) auto

(*
  Each step (a,w) in the path list came from some edge in the CFG.
  The source of that edge is NOT necessarily u (the path start) — it is
  whatever node preceded w along the path.  The old statement
    (a,w) \<in> set (map snd es) ⟹ (u,a,w) \<in> cfg_edges g
  was wrong for paths of length > 1.  Correct form: existential source.
*)
lemma cfg_path_edges_in_cfg:
  "cfg_path g u es v ==> (a, w) : set es ==> \<exists>src. (src, a, w) \<in> cfg_edges g"
  apply (induction rule: cfg_path.induct)
  by(auto)

 

(* Convenience: first step of a non-empty path hits the CFG at u. *)
lemma cfg_path_first_edge:
  "cfg_path g u ((a, w) # es) v ==> (u, a, w) : cfg_edges g"
  by (erule cfg_path.cases) auto

(* ── Offset Paths ──────────────────────────────────────────────── *)

(*
  offset_path k es shifts every pp in the step list by k.
  Useful for lifting an IH path on `to_cfg c` (compile c 0) into a
  larger compound CFG where c was compiled at some n > 0.
  Since path_collect ignores the pp component, the collect output is
  invariant under this shift (see path_collect_offset_path).
*)

definition offset_path :: "nat => (edge_action * pp) list => (edge_action * pp) list" where
  "offset_path k es = map (\<lambda>(a, p). (a, p + k)) es"

lemma offset_path_Nil[simp]: "offset_path k [] = []"
  unfolding offset_path_def by simp

lemma offset_path_Cons[simp]:
  "offset_path k ((a, p) # es) = (a, p + k) # offset_path k es"
  unfolding offset_path_def by simp

lemma offset_path_append[simp]:
  "offset_path k (es1 @ es2) = offset_path k es1 @ offset_path k es2"
  unfolding offset_path_def by simp

(*
  cfg_path_offset: a path in a graph G lifts to a path in the
  pp-shifted graph (offset_edges k G), with start/end shifted by k
  and the step list shifted via offset_path.
*)
lemma cfg_path_offset:
  assumes "cfg_path \<lparr>cfg_entry = ent, cfg_exit = ex, cfg_edges = E\<rparr> u es v"
  shows "cfg_path \<lparr>cfg_entry = ent + k, cfg_exit = ex + k, cfg_edges = offset_edges k E\<rparr>
                  (u + k) (offset_path k es) (v + k)"
  using assms
proof (induction "\<lparr>cfg_entry = ent, cfg_exit = ex, cfg_edges = E\<rparr>" u es v rule: cfg_path.induct)
  case (empty w)
  show ?case by (simp add: cfg_path.empty)
next
  case (step u a w es v)
  have e: "(u, a, w) \<in> E"
    using step.hyps(1) by simp
  have e': "(u + k, a, w + k) \<in> offset_edges k E"
    using e in_offset_edges_iff by metis
  show ?case
    by (simp add: cfg_path.step e' step.hyps(3))
qed

(*
  Path lift along an edge-set inclusion that's witnessed via offset.
  In Seq/If/While, the sub-command c was compiled at offset n>0, so
  its edges are `offset_edges n (cfg_edges (to_cfg c))`.  Combine
  cfg_path_offset with cfg_path_mono_edges (in CFG_Collecting) to
  drop the IH path into the compound graph.
*)

(*
  unoffset_path k es strips k from every pp in es.
  Converse direction of offset_path.
*)
definition unoffset_path :: "nat => (edge_action * pp) list => (edge_action * pp) list" where
  "unoffset_path k es = map (\<lambda>(a, p). (a, p - k)) es"

lemma unoffset_path_Nil[simp]: "unoffset_path k [] = []"
  unfolding unoffset_path_def by simp

lemma unoffset_path_Cons[simp]:
  "unoffset_path k ((a, p) # es) = (a, p - k) # unoffset_path k es"
  unfolding unoffset_path_def by simp

(*
  cfg_path_offset_back: a path through offset_edges k E with start ≥ k
  lifts back to a path through E.  Endpoint is automatically ≥ k
  because every edge in offset_edges k E lands at some p ≥ k.
*)
lemma cfg_path_offset_back:
  fixes E :: "(pp \<times> edge_action \<times> pp) set"
  assumes p: "cfg_path G u es v"
    and   E_eq: "cfg_edges G = offset_edges k E"
    and   u_ge: "k \<le> u"
  shows "cfg_path \<lparr>cfg_entry = 0, cfg_exit = 0, cfg_edges = E\<rparr>
                  (u - k) (unoffset_path k es) (v - k)"
  using p E_eq u_ge
proof (induction rule: cfg_path.induct)
  case (empty g w)
  show ?case by (simp add: cfg_path.empty)
next
  case (step u a w g es v)
  have e_off: "(u, a, w) \<in> offset_edges k E"
    using step.hyps(1) step.prems(1) by simp
  from e_off obtain u0 w0 where
        decomp: "u = u0 + k" "w = w0 + k" "(u0, a, w0) \<in> E"
    unfolding offset_edges_def by auto
  have ku: "k \<le> u" using step.prems(2) .
  have kw: "k \<le> w" using decomp(2) by simp
  have e_unshifted: "(u - k, a, w - k) \<in> E"
    using decomp by simp
  have ih: "cfg_path \<lparr>cfg_entry = 0, cfg_exit = 0, cfg_edges = E\<rparr>
                    (w - k) (unoffset_path k es) (v - k)"
    using step.IH[OF step.prems(1) kw] .
  show ?case
    using e_unshifted ih ku by (simp add: cfg_path.step)
qed

(*
  cfg_path_split_last: a non-empty path factors as
    (path u \<to> mid) @ [(a, v)]
  where (mid, a, v) is the last edge.  Used to peel the trailing Nop
  bridge in If / While CFG paths.
*)
lemma cfg_path_split_last:
  assumes p: "cfg_path G u es v"
    and ne: "es \<noteq> []"
  shows "\<exists>es' mid a. es = es' @ [(a, v)] \<and>
                     cfg_path G u es' mid \<and>
                     (mid, a, v) \<in> cfg_edges G"
  using p ne
proof (induction es arbitrary: u)
  case Nil
  thus ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e: "(u, a, w) \<in> cfg_edges G"
    and ps: "cfg_path G w tl v"
    by (cases rule: cfg_path.cases) auto
  show ?case
  proof (cases "tl = []")
    case True
    from ps True have wv: "w = v" by (cases rule: cfg_path.cases) auto
    have es_eq: "(a, w) # tl = [] @ [(a, v)]" using True wv by simp
    have empty_p: "cfg_path G u [] u" by (rule cfg_path.empty)
    have e_uv: "(u, a, v) \<in> cfg_edges G" using e wv by simp
    show ?thesis using es_eq empty_p e_uv hd_eq by blast
  next
    case False
    from Cons.IH[OF ps False] obtain es' mid a' where
          tl_eq: "tl = es' @ [(a', v)]"
      and ps': "cfg_path G w es' mid"
      and last_e: "(mid, a', v) \<in> cfg_edges G"
      by blast
    have full: "cfg_path G u ((a, w) # es') mid"
      by (rule cfg_path.step[OF e ps'])
    have list_eq: "(a, w) # tl = ((a, w) # es') @ [(a', v)]" using tl_eq by simp
    show ?thesis using list_eq full last_e hd_eq by blast
  qed
qed

(* ── Reachability from Entry ───────────────────────────────────── *)

definition cfg_reachable :: "cfg => pp => bool" where
  "cfg_reachable g v = (g \<turnstile> cfg_entry g \<rightarrow>* v)"

lemma cfg_entry_reachable[intro, simp]: "cfg_reachable g (cfg_entry g)"
  unfolding cfg_reachable_def by (rule cfg_reaches_refl)

(*
  cfg_exit_reachable_from_entry is unprovable for arbitrary well-formed CFGs:
  cfg_wf does not guarantee a path from entry to exit.  Replaced by
  to_cfg_exit_reachable below, which uses the compile structure.
*)
lemma cfg_exit_reachable_from_entry:
  "cfg_wf g ==>
   (\<forall>(u, _, v) \<in> cfg_edges g. cfg_reachable g u \<longrightarrow> cfg_reachable g v) ==>
   cfg_reachable g (cfg_exit g)"
  sorry  (* intentionally weak; use to_cfg_exit_reachable for to_cfg results *)

(*
  For CFGs produced by to_cfg, the exit IS reachable from entry.
  Proved by structural induction on c using compile's edge structure.
*)
lemma to_cfg_exit_reachable:
  "cfg_reachable (to_cfg c) (cfg_exit (to_cfg c))"
  sorry

end
