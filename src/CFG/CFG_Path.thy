theory CFG_Path
  imports CFG_Def
begin

(*
  CFG_Path -- Inductive path predicate for CFGs.

  Pattern: inductive path + derived notation + intro/elim/simp lemma library.
  Adapted from: https://github.com/lohner/FormalSSA (Ullrich & Lohner, Isabelle2016)
                "Verified Construction of Static Single-Assignment Form"
                SSA_CFG.thy / Graph_path.thy — path2 + lemma library.
  Pattern 1: inductive path; Pattern 2: attribute discipline;
            Pattern 4: derived _cases / _induct lemmas.

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

(* \<midarrow>\<midarrow> Core Inductive Predicate \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

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

inductive_cases stepE[elim]: "cfg_path g u es v"

(* \<midarrow>\<midarrow> Reachability Abbreviation + Notation \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

(*
  g |- u -->* v   iff some path (of any steps) exists from u to v.
  Notation inspired by FormalSSA's "n⌜ns⌝\<rightarrow>m".
*)

abbreviation cfg_reaches :: "cfg => pp => pp => bool" ("_ \<turnstile> _ \<rightarrow>* _" [50,0,50] 80) where
  "cfg_reaches g u v == (\<exists>es. cfg_path g u es v)"

(* \<midarrow>\<midarrow> Intro Lemmas \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

lemma cfg_reaches_refl[intro, simp]: "g \<turnstile> v \<rightarrow>* v"
  by auto

lemma cfg_reaches_step[intro]:
  "(u, a, w) : cfg_edges g ==> g \<turnstile> w \<rightarrow>* v ==> g \<turnstile> u \<rightarrow>* v"
  by auto

lemma cfg_path_append:
  "cfg_path g u es1 v ==> cfg_path g v es2 w ==> cfg_path g u (es1 @ es2) w"
  apply (induction es1 arbitrary: u)
  by(auto)

lemma cfg_reaches_trans[intro]:
  "g \<turnstile> u \<rightarrow>* v ==> g \<turnstile> v \<rightarrow>* w ==> g \<turnstile> u \<rightarrow>* w"
  using cfg_path_append by blast
 
 

(* \<midarrow>\<midarrow> Offset Paths \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

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
  apply (induction "\<lparr>cfg_entry = ent, cfg_exit = ex, cfg_edges = E\<rparr>" u es v rule: cfg_path.induct)
  by(auto simp add: cfg_path.step in_offset_edges_iff)
 
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
  cfg_path_offset_back: a path through offset_edges k E with start \<ge> k
  lifts back to a path through E.  Endpoint is automatically \<ge> k
  because every edge in offset_edges k E lands at some p \<ge> k.
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

end
