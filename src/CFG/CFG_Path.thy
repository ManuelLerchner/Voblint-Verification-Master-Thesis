theory CFG_Path
  imports CFG_Def
begin

(*
  CFG_Path -- Inductive path predicate for CFGs.

  Pattern: inductive path + derived notation + intro/elim/simp lemma library.
  Adapted from: https://github.com/lohner/FormalSSA (Ullrich & Lohner, Isabelle2016)
                "Verified Construction of Static Single-Assignment Form"
                SSA_CFG.thy / Graph_path.thy path2 + lemma library.

  Design choices vs. FormalSSA:
    - FormalSSA path2: list of *nodes* (predecessor-based graph)
    - Our cfg_path:   list of *(edge_action * pp)* steps (labeled-edge graph)
*)

(* \<midarrow>\<midarrow> Core Inductive Predicate \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool"
                 ("_ \<turnstile> _ \<longrightarrow>\<^bsub>_\<^esub> _" [60, 0, 0, 60] 60) where 
  empty[intro]: "g \<turnstile> v \<longrightarrow>\<^bsub>[]\<^esub> v"
| step[intro]:  "(u, a, w) : edges g ==> g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> v
                ==> g \<turnstile> u \<longrightarrow>\<^bsub>(a, w) # es\<^esub> v"

inductive_cases cfg_emptyE[elim!]: "g \<turnstile> v \<longrightarrow>\<^bsub>[]\<^esub> u"
inductive_cases cfg_stepE[elim]: "g \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> u"


lemma cfg_path_append[intro]:
  "g \<turnstile> u \<longrightarrow>\<^bsub>es1\<^esub> v ==> g \<turnstile> v \<longrightarrow>\<^bsub>es2\<^esub> w ==> g \<turnstile> u \<longrightarrow>\<^bsub>es1 @ es2\<^esub> w"
  apply (induction es1 arbitrary: u) 
  by(auto)

(* First step of a non-empty path reaches its intermediate target. *)
lemma cfg_path_step_target:
  assumes path: "g \<turnstile> u \<longrightarrow>\<^bsub>(a, w) # es\<^esub> v"
  shows "g \<turnstile> u \<longrightarrow>\<^bsub>[(a, w)]\<^esub> w"
proof (rule cfg_path.step)
  show "(u, a, w) \<in> edges g"
    using path by (cases rule: cfg_stepE) auto
  show "g \<turnstile> w \<longrightarrow>\<^bsub>[]\<^esub> w"
    by (rule cfg_path.empty)
qed

(* If x lies on a path from p to v and takes one step toward v, so does w. *)
lemma cfg_path_on_path_step:
  assumes prefix: "g \<turnstile> p \<longrightarrow>\<^bsub>esx\<^esub> x"
  assumes step: "g \<turnstile> x \<longrightarrow>\<^bsub>(a, w) # es'\<^esub> v"
  shows "g \<turnstile> p \<longrightarrow>\<^bsub>esx @ [(a, w)]\<^esub> w"
  using cfg_path_append[OF prefix cfg_path_step_target[OF step]] by simp

(* \<midarrow>\<midarrow> Offset Paths \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

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

lemma cfg_path_offset:
  assumes "mk_cfg ent ex E \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "mk_cfg (ent + k) (ex + k) (offset_edges k E) \<turnstile> (u + k) \<longrightarrow>\<^bsub>offset_path k es\<^esub> (v + k)"
  using assms
  apply (induction "mk_cfg ent ex E" u es v rule: cfg_path.induct)
  by(auto simp add: cfg_path.step in_offset_edges_iff)

lemma cfg_path_split_last:
  assumes p: "G \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
    and ne: "es \<noteq> []"
  shows "\<exists>es' mid a. es = es' @ [(a, v)] \<and>
                      G \<turnstile> u \<longrightarrow>\<^bsub>es'\<^esub> mid \<and>
                      (mid, a, v) \<in> edges G"
using assms proof (induction es arbitrary: u)
  case Nil
  thus ?case by simp
next
  case (Cons hd tl)
  then obtain a w where "hd = (a, w)" and "(u, a, w) \<in> edges G" and "G \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> v"
    by blast
  then show ?case
    using Cons.IH cfg_path.step cfg_path_append empty by fastforce
qed

end