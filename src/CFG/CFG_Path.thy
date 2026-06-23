theory CFG_Path
  imports CFG_Def
begin

section \<open>Inductive path predicate for CFGs\<close>

text \<open>
  Pattern: inductive path + derived notation + intro/elim/simp lemma library.
  Adapted from: https://github.com/lohner/FormalSSA (Ullrich & Lohner, Isabelle2016)
                ''Verified Construction of Static Single-Assignment Form''
                SSA_CFG.thy / Graph_path.thy path2 + lemma library.

  Design choices vs. FormalSSA:
    - FormalSSA path2: list of *nodes* (predecessor-based graph)
    - Our cfg_path:   list of *(edge_action * pp)* steps (labeled-edge graph)
\<close>

subsection \<open>Core inductive predicate\<close>

inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool"
                 ("_ \<turnstile> _ \<rightarrow>\<langle>_\<rangle> _" [60, 0, 0, 60] 60) where
  empty[intro]: "g \<turnstile> v \<rightarrow>\<langle>[]\<rangle> v"
| step[intro]:  "(u, a, w) : edges g ==> g \<turnstile> w \<rightarrow>\<langle>es\<rangle> v
                ==> g \<turnstile> u \<rightarrow>\<langle>(a, w) # es\<rangle> v"

inductive_cases cfg_emptyE[elim!]: "g \<turnstile> v \<rightarrow>\<langle>[]\<rangle> u"

lemma cfg_path_emptyD:
  "g \<turnstile> u \<rightarrow>\<langle>[]\<rangle> v \<Longrightarrow> u = v"
  by auto

inductive_cases cfg_stepE[elim]: "g \<turnstile> v \<rightarrow>\<langle>es\<rangle> u"

lemma cfg_path_ConsD_edge:
  "g \<turnstile> u \<rightarrow>\<langle>(a, w) # es\<rangle> v \<Longrightarrow> (u, a, w) \<in> edges g"
  by (cases rule: cfg_stepE) auto

lemma cfg_path_ConsD_rest:
  "g \<turnstile> u \<rightarrow>\<langle>(a, w) # es\<rangle> v \<Longrightarrow> g \<turnstile> w \<rightarrow>\<langle>es\<rangle> v"
  by (cases rule: cfg_stepE) auto

lemma cfg_path_ne_nil:
  assumes path: "g \<turnstile> u \<rightarrow>\<langle>es\<rangle> v"
    and u_ne: "u \<noteq> v"
  shows "es \<noteq> []"
  using assms cfg_path_emptyD by auto


lemma cfg_path_append[intro]:
  "g \<turnstile> u \<rightarrow>\<langle>es1\<rangle> v ==> g \<turnstile> v \<rightarrow>\<langle>es2\<rangle> w ==> g \<turnstile> u \<rightarrow>\<langle>es1 @ es2\<rangle> w"
  apply (induction es1 arbitrary: u)
  by(auto)

lemma cfg_path_suffix_to_query:
  assumes prefix: "g \<turnstile> p \<rightarrow>\<langle>esx\<rangle> x"
  assumes suffix: "g \<turnstile> x \<rightarrow>\<langle>es'\<rangle> v0"
  shows "g \<turnstile> p \<rightarrow>\<langle>esx @ es'\<rangle> v0"
  using cfg_path_append[OF prefix suffix] .

(* First step of a non-empty path reaches its intermediate target. *)
lemma cfg_path_step_target:
  assumes path: "g \<turnstile> u \<rightarrow>\<langle>(a, w) # es\<rangle> v"
  shows "g \<turnstile> u \<rightarrow>\<langle>[(a, w)]\<rangle> w"
proof (rule cfg_path.step)
  show "(u, a, w) \<in> edges g"
    using path by (cases rule: cfg_stepE) auto
  show "g \<turnstile> w \<rightarrow>\<langle>[]\<rangle> w"
    by (rule cfg_path.empty)
qed

(* If x lies on a path from p to v and takes one step toward v, so does w. *)
lemma cfg_path_on_path_step:
  assumes prefix: "g \<turnstile> p \<rightarrow>\<langle>esx\<rangle> x"
  assumes step: "g \<turnstile> x \<rightarrow>\<langle>(a, w) # es'\<rangle> v"
  shows "g \<turnstile> p \<rightarrow>\<langle>esx @ [(a, w)]\<rangle> w"
  using cfg_path_append[OF prefix cfg_path_step_target[OF step]] by simp

subsection \<open>Offset paths\<close>

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
  assumes "mk_cfg ent ex E {} \<turnstile> u \<rightarrow>\<langle>es\<rangle> v"
  shows "mk_cfg (ent + k) (ex + k) (offset_edges k E) {} \<turnstile> (u + k) \<rightarrow>\<langle>offset_path k es\<rangle> (v + k)"
  using assms
  apply (induction "mk_cfg ent ex E {}" u es v rule: cfg_path.induct)
  by(auto simp add: cfg_path.step in_offset_edges_iff)

lemma cfg_path_split_last:
  assumes p: "G \<turnstile> u \<rightarrow>\<langle>es\<rangle> v"
    and ne: "es \<noteq> []"
  shows "\<exists>es' mid a. es = es' @ [(a, v)] \<and>
                      G \<turnstile> u \<rightarrow>\<langle>es'\<rangle> mid \<and>
                      (mid, a, v) \<in> edges G"
using assms proof (induction es arbitrary: u)
  case Nil
  thus ?case by simp
next
  case (Cons hd tl)
  then obtain a w where "hd = (a, w)" and "(u, a, w) \<in> edges G" and "G \<turnstile> w \<rightarrow>\<langle>tl\<rangle> v"
    by blast
  then show ?case
    using Cons.IH cfg_path.step cfg_path_append empty by fastforce
qed

end