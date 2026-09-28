theory MCP_Spec
  imports "Voblint_Framework.DG_Spec_Sound" "Voblint_Domain.Reachability_Lift"
begin

section \<open>Many cooperating analyses over one state\<close>

text \<open>
  Goblint's \<open>MCP\<close> runs every activated analysis on its own part of one
  combined state (\<open>mCP.ml\<close> at \<open>0dc12d355\<close>). Voblint keeps the combined state
  as one type \<open>'s\<close>, a record with a field per registered analysis, and a
  component as operations on the whole record that touch only its own field.
  The activation list chooses which components run; the fields of inactive
  analyses are never read.

  Every operation of a component receives the query channel of the manager
  Goblint hands it, \<open>man.ask\<close>, as a function \<^typ>\<open>answers\<close> from queries to
  answers: its query handler (\<open>S.query man q\<close>), its edge transfers, its entry
  (\<open>S.enter man\<close>) and both stages of its return. The return stages also receive
  the callee's channel, which Goblint's normal-call transfer in \<open>constraints.ml\<close>
  passes as \<open>f_ask\<close>.
  A handler may therefore ask further queries while it answers, and the channel
  that answers them is the one \<open>ask_rec\<close> below closes over the combined
  state, as Goblint's \<open>MCP.query'\<close> does.

  The channel is a pure function of the state it describes. A component
  therefore neither reads nor publishes globals: the combined state covers
  analyses whose operations are local, and effectful analyses run as
  specifications of their own (\<^const>\<open>dgs_query\<close> is the effectful handler).

  A component holds only what runs. What its states describe, a set of stores,
  is not executable and is supplied beside it wherever soundness is stated,
  as \<^class>\<open>numeric_domain\<close> keeps \<open>gamma\<close> out of \<^class>\<open>executable_domain\<close>.
\<close>

record 's mcp_component =
  mc_qry :: "answers \<Rightarrow> 's \<Rightarrow> answers"
  mc_skip :: "answers \<Rightarrow> 's \<Rightarrow> 's"
  mc_assign :: "answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 's \<Rightarrow> 's"
  mc_special :: "answers \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 's \<Rightarrow> 's"
  mc_branch :: "answers \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's"
  mc_body :: "answers \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  mc_return :: "answers \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  mc_event :: "answers \<Rightarrow> analysis_event \<Rightarrow> 's \<Rightarrow> 's"
  mc_en :: "answers \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  mc_comb_env :: "answers \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  mc_comb_assign :: "answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"

text \<open>
  The edge transfers are separate fields, one per kind of edge, as Goblint's
  \<open>Spec\<close> has \<open>skip\<close>, \<open>assign\<close>, \<open>special\<close>, \<open>branch\<close>, \<open>body\<close>, \<open>return\<close> and
  \<open>event\<close>. A component that overrides one of them updates that field alone. The
  step on an arbitrary edge is derived from them.
\<close>

definition mc_step :: "'s mcp_component \<Rightarrow> answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "mc_step c A = local_spec_step (mc_skip c A) (mc_assign c A) (mc_special c A)
     (mc_branch c A) (mc_body c A) (mc_return c A) (mc_event c A)"

lemma mc_step_simps [simp]:
  "mc_step c A EA_Nop = mc_skip c A"
  "mc_step c A (EA_Assign x e) = mc_assign c A x e"
  "mc_step c A (EA_Special sc x) = mc_special c A sc x"
  "mc_step c A (EA_Assume b) = mc_branch c A b True"
  "mc_step c A (EA_AssumeNot b) = mc_branch c A b False"
  "mc_step c A (EA_Body p) = mc_body c A p"
  "mc_step c A (EA_Ret r p) = mc_return c A r p"
  "mc_step c A (EA_Check l cnd) = mc_event c A (Check_Event l cnd)"
  by (simp_all add: mc_step_def)

lemma mc_step_update_other [simp]:
  "mc_step (c\<lparr>mc_qry := h\<rparr>) = mc_step c"
  "mc_step (c\<lparr>mc_en := e\<rparr>) = mc_step c"
  "mc_step (c\<lparr>mc_comb_env := ce\<rparr>) = mc_step c"
  "mc_step (c\<lparr>mc_comb_assign := ca\<rparr>) = mc_step c"
  by (simp_all add: mc_step_def fun_eq_iff)

text \<open>
  A component whose edge transfers are one function of the edge, such as a
  lens onto a field or a fold over several components, is built from that
  function: each field is the function at its kind of edge.
\<close>

definition make_component ::
  "(answers \<Rightarrow> 's \<Rightarrow> answers) \<Rightarrow> (answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> (answers \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list)
   \<Rightarrow> (answers \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> (answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's mcp_component" where
  "make_component qry st en ce ca = \<lparr>
     mc_qry = qry,
     mc_skip = (\<lambda>A. st A EA_Nop),
     mc_assign = (\<lambda>A x e. st A (EA_Assign x e)),
     mc_special = (\<lambda>A sc x. st A (EA_Special sc x)),
     mc_branch = (\<lambda>A b pol. st A (if pol then EA_Assume b else EA_AssumeNot b)),
     mc_body = (\<lambda>A p. st A (EA_Body p)),
     mc_return = (\<lambda>A r p. st A (EA_Ret r p)),
     mc_event = (\<lambda>A ev. st A (event_action ev)),
     mc_en = en, mc_comb_env = ce, mc_comb_assign = ca \<rparr>"

lemma make_component_sel [simp]:
  "mc_qry (make_component qry st en ce ca) = qry"
  "mc_step (make_component qry st en ce ca) = st"
  "mc_en (make_component qry st en ce ca) = en"
  "mc_comb_env (make_component qry st en ce ca) = ce"
  "mc_comb_assign (make_component qry st en ce ca) = ca"
proof -
  have "mc_step (make_component qry st en ce ca) A a = st A a" for A a
  proof (cases a)
    case (EA_Check l cnd)
    then show ?thesis by (simp add: make_component_def mc_step_def)
  qed (simp_all add: make_component_def mc_step_def)
  then show "mc_step (make_component qry st en ce ca) = st" by (simp add: fun_eq_iff)
qed (simp_all add: make_component_def)

text \<open>
  The return runs in the two stages of Goblint's \<open>combine_env\<close> and
  \<open>combine_assign\<close>, which both receive the callee's channel. Only the first
  receives the caller's: Goblint's \<open>combine_assign\<close> asks about the state
  \<open>combine_env\<close> produced, which describes no concrete store on its own here,
  since soundness and independence speak only about the composite.
\<close>

abbreviation mc_comb ::
  "'s mcp_component \<Rightarrow> answers \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mc_comb c A B ci x de \<equiv> mc_comb_assign c B ci (mc_comb_env c A B ci x de) de"

text \<open>
  A component is sound for a concretization \<open>gamma\<close> when each operation covers the
  concrete behaviour, whatever the other fields of the record hold. Every
  operation is proved against every channel that holds at the stores it is
  asked about, as in \<^locale>\<open>sound_local_dg_spec\<close>: the caller's store for a
  step, an entry, a query and the first stage of a return, and the callee's exit
  store for the callee's channel.
\<close>

definition mcp_component_sound ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('s::order \<Rightarrow> store set) \<Rightarrow> 's mcp_component \<Rightarrow> bool" where
  "mcp_component_sound \<G> gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>A a x. edge_collect a (gm x \<inter> Collect (eval_query.oracle_holds A))
                  \<subseteq> gm (mc_step c A a x))
     \<and> (\<forall>A s ci p. s \<in> gm (fst p) \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          (\<exists>q \<in> set (mc_en c A ci p). s \<in> gm (fst q)
             \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>A B s t ci x de. s \<in> gm x \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          t \<in> gm de \<longrightarrow> eval_query.oracle_holds B t \<longrightarrow>
          combine_collect \<G> (ci_dst ci) s t \<in> gm (mc_comb c A B ci x de))
     \<and> (\<forall>A s x q. s \<in> gm x \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          eval_holds q (mc_qry c A x q) s)"

text \<open>
  A component leaves a concretization alone when none of its operations
  changes what that concretization says. For components that each own one
  field of a record this is the lens law that updating one field leaves the
  others.
\<close>

definition mcp_frame :: "'s mcp_component \<Rightarrow> ('s \<Rightarrow> store set) \<Rightarrow> bool" where
  "mcp_frame c gm \<longleftrightarrow>
     (\<forall>A a x. gm (mc_step c A a x) = gm x)
     \<and> (\<forall>A ci p q. q \<in> set (mc_en c A ci p) \<longrightarrow>
          gm (fst q) = gm (fst p) \<and> gm (snd q) = gm (snd p))
     \<and> (\<forall>A B ci x de. gm (mc_comb c A B ci x de) = gm x)"

text \<open>
  Cooperating analyses come as pairs of a concretization and a component.
  They are independent when each leaves the others' concretizations alone.
\<close>

type_synonym 's certified_component = "('s \<Rightarrow> store set) \<times> 's mcp_component"

fun mcp_independent :: "'s certified_component list \<Rightarrow> bool" where
  "mcp_independent [] \<longleftrightarrow> True"
| "mcp_independent ((g, c) # gcs) \<longleftrightarrow>
     (\<forall>(g', c') \<in> set gcs. mcp_frame c g' \<and> mcp_frame c' g) \<and> mcp_independent gcs"

section \<open>The query channel\<close>

text \<open>
  A handler answers a query given the channel through which it may ask further
  ones. \<open>ask_rec\<close> closes that recursion over one state, as Goblint's
  \<open>MCP.query'\<close> does: a query already being asked answers \<open>\<top>\<close> instead of
  recursing, and every other query is answered by the handler under a channel
  that remembers it. The depth bound plays the role it plays in
  \<^const>\<open>ask_with\<close>: queries range over an infinite type, so cycle detection
  alone does not make the recursion total, and exhausting the bound aborts the
  generated program. Logically the fallback is \<open>\<top>\<close>, so the bound plays no part
  in soundness. Goblint also caches answers per transfer; that changes only how
  often a handler runs.
\<close>

fun ask_rec :: "(answers \<Rightarrow> 's \<Rightarrow> answers) \<Rightarrow> nat \<Rightarrow> query set \<Rightarrow> 's \<Rightarrow> answers" where
  "ask_rec H 0 asked x q =
     Code.abort (STR ''query recursion exceeded query_depth'') (\<lambda>_. \<top>)"
| "ask_rec H (Suc n) asked x q =
     (if q \<in> asked then \<top> else H (ask_rec H n (insert q asked) x) x q)"

text \<open>
  A handler that answers soundly under every sound channel makes the closed
  channel sound: by induction on the depth, each level's channel holds, so the
  handler's answer under it holds.
\<close>

lemma ask_rec_sound:
  assumes "\<And>A q. eval_query.oracle_holds A s \<Longrightarrow> eval_holds q (H A x q) s"
  shows "eval_query.oracle_holds (ask_rec H n asked x) s"
proof (induction n arbitrary: asked)
  case 0
  then show ?case by (simp add: eval_query.oracle_holds_def)
next
  case (Suc n)
  then show ?case
    using assms by (auto simp: eval_query.oracle_holds_def)
qed

text \<open>A handler that never asks answers through the closed channel as it is.\<close>

lemma ask_rec_const: "ask_rec (\<lambda>A x. h x) (Suc n) {} x = h x"
  by (simp add: fun_eq_iff)

definition mc_channel :: "'s mcp_component \<Rightarrow> 's \<Rightarrow> answers" where
  "mc_channel c x = ask_rec (mc_qry c) query_depth {} x"

lemma mc_channel_sound:
  assumes "mcp_component_sound \<G> gm c" and "s \<in> gm x"
  shows "eval_query.oracle_holds (mc_channel c x) s"
  unfolding mc_channel_def
  by (rule ask_rec_sound) (use assms in \<open>simp add: mcp_component_sound_def\<close>)

lemma mc_channel_const: "mc_qry c = (\<lambda>A x. h x) \<Longrightarrow> mc_channel c = h"
  by (simp add: mc_channel_def query_depth_def fun_eq_iff eval_nat_numeral)

section \<open>The combined operations\<close>

text \<open>
  The combined operations run the active components in turn. Soundness needs
  only \<^const>\<open>mcp_frame\<close>: a component keeps what the other components'
  states describe, not their representation, so the soundness proof says
  nothing about the order of the fold. A component that updates only its own
  field of a product does leave the other fields unchanged, and for those the
  order does not matter; Goblint runs every component on the predecessor's
  part of the state, which is the same computation. Every component gets the
  same channel, as every Goblint component gets the same \<open>man.ask\<close>.
\<close>

definition mcp_step :: "'s mcp_component list \<Rightarrow> answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_step cs A a x = fold (\<lambda>c y. mc_step c A a y) cs x"

definition mcp_en_from ::
  "'s mcp_component list \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> 's enter_result list" where
  "mcp_en_from cs A ci p = fold (\<lambda>c ps. concat (map (mc_en c A ci) ps)) cs [p]"

definition mcp_comb ::
  "'s mcp_component list \<Rightarrow> answers \<Rightarrow> answers \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_comb cs A B ci x de = fold (\<lambda>c y. mc_comb c A B ci y de) cs x"

text \<open>
  The combined handler meets every component's answer, each given the same
  channel, as \<open>MCP.query'\<close> meets the results of all analyses.
\<close>

definition mcp_qry :: "'s mcp_component list \<Rightarrow> answers \<Rightarrow> 's \<Rightarrow> answers" where
  "mcp_qry cs A x q = fold (\<lambda>c r. r \<sqinter> mc_qry c A x q) cs \<top>"

definition mcp_gamma :: "('s \<Rightarrow> store set) list \<Rightarrow> 's \<Rightarrow> store set" where
  "mcp_gamma gs x = (\<Inter>g \<in> set gs. g x)"

section \<open>Soundness of the combination\<close>

lemma mcp_gamma_Cons [simp]: "mcp_gamma (g # gs) x = g x \<inter> mcp_gamma gs x"
  by (simp add: mcp_gamma_def)

lemma mcp_gamma_Nil [simp]: "mcp_gamma [] x = UNIV"
  by (simp add: mcp_gamma_def)

text \<open>Components a fold runs leave an independent concretization as it was.\<close>

lemma gamma_fold_step:
  "(\<forall>c \<in> set cs. mcp_frame c g) \<Longrightarrow> g (fold (\<lambda>c y. mc_step c A a y) cs x) = g x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma gamma_fold_comb:
  "(\<forall>c \<in> set cs. mcp_frame c g) \<Longrightarrow> g (fold (\<lambda>c y. mc_comb c A B ci y de) cs x) = g x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma mcp_gamma_frame:
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (mc_step c A a x) = mcp_gamma gs x"
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (mc_comb c A B ci x de) = mcp_gamma gs x"
  by (auto simp: mcp_gamma_def mcp_frame_def intro!: INF_cong)

lemma mcp_independent_Cons_frames:
  assumes "mcp_independent ((g, c) # gcs)"
  shows "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
  using assms by auto

lemma mcp_step_sound:
  assumes "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" and "mcp_independent gcs"
  shows "edge_collect a (mcp_gamma (map fst gcs) x \<inter> Collect (eval_query.oracle_holds A))
           \<subseteq> mcp_gamma (map fst gcs) (mcp_step (map snd gcs) A a x)"
  using assms
proof (induction gcs arbitrary: x)
  case Nil
  then show ?case by (simp add: mcp_step_def)
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  let ?O = "Collect (eval_query.oracle_holds A)"
  let ?x1 = "mc_step c A a x"
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  have own: "edge_collect a (g x \<inter> ?O) \<subseteq> g ?x1"
    using Cons.prems(1) unfolding gc by (simp add: mcp_component_sound_def)
  have own_kept: "g (mcp_step (map snd gcs) A a ?x1) = g ?x1"
    unfolding mcp_step_def by (rule gamma_fold_step) (use frames in auto)
  have rest: "edge_collect a (mcp_gamma (map fst gcs) ?x1 \<inter> ?O)
      \<subseteq> mcp_gamma (map fst gcs) (mcp_step (map snd gcs) A a ?x1)"
    by (rule Cons.IH) (use Cons.prems(1) frames in auto)
  have rest_eq: "mcp_gamma (map fst gcs) ?x1 = mcp_gamma (map fst gcs) x"
    by (rule mcp_gamma_frame(1)) (use frames in auto)
  have "edge_collect a (mcp_gamma (map fst (gc # gcs)) x \<inter> ?O)
          \<subseteq> edge_collect a (g x \<inter> ?O) \<inter> edge_collect a (mcp_gamma (map fst gcs) ?x1 \<inter> ?O)"
    unfolding gc by (intro Int_greatest edge_collect_mono) (auto simp: rest_eq)
  also have "\<dots> \<subseteq> mcp_gamma (map fst (gc # gcs)) (mcp_step (map snd (gc # gcs)) A a x)"
    using own own_kept rest unfolding gc by (auto simp: mcp_step_def)
  finally show ?case .
qed

lemma mcp_comb_sound:
  assumes "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" and "mcp_independent gcs"
    and "s \<in> mcp_gamma (map fst gcs) x" and "eval_query.oracle_holds A s"
    and "t \<in> mcp_gamma (map fst gcs) de" and "eval_query.oracle_holds B t"
  shows "combine_collect \<G> (ci_dst ci) s t
           \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) A B ci x de)"
  using assms
proof (induction gcs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  let ?x1 = "mc_comb c A B ci x de"
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  have own: "combine_collect \<G> (ci_dst ci) s t \<in> g ?x1"
    using Cons.prems(1,3-6) unfolding gc by (simp add: mcp_component_sound_def)
  have own_kept: "g (mcp_comb (map snd gcs) A B ci ?x1 de) = g ?x1"
    unfolding mcp_comb_def by (rule gamma_fold_comb) (use frames in auto)
  have rest_eq: "mcp_gamma (map fst gcs) ?x1 = mcp_gamma (map fst gcs) x"
    by (rule mcp_gamma_frame(2)) (use frames in auto)
  have rest: "combine_collect \<G> (ci_dst ci) s t
      \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) A B ci ?x1 de)"
    by (rule Cons.IH) (use Cons.prems frames rest_eq gc in auto)
  show ?case
    using own own_kept rest unfolding gc by (simp add: mcp_comb_def)
qed

text \<open>
  Entry threads a list of pairs through the components. The invariant carries
  the concretizations of the components already run (\<open>ds\<close>), whose fields are
  set in both halves, and the components still to run (\<open>gcs\<close>), whose fields
  are still the caller's.
\<close>

lemma mcp_en_fold_sound:
  assumes "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" and "mcp_independent gcs"
    and "\<forall>c \<in> snd ` set gcs. \<forall>d \<in> set ds. mcp_frame c d"
    and "\<exists>p \<in> set ps. s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma ds (fst p)
                       \<and> E \<in> mcp_gamma ds (snd p)"
    and A: "eval_query.oracle_holds A s"
    and E: "E = call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s"
  shows "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c A ci) ps)) (map snd gcs) ps).
           s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma ds (fst p)
           \<and> E \<in> mcp_gamma (map fst gcs) (snd p) \<and> E \<in> mcp_gamma ds (snd p)"
  using assms(1-4)
proof (induction gcs arbitrary: ps ds)
  case Nil
  then show ?case by simp
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  obtain p where p: "p \<in> set ps" "s \<in> g (fst p)" "s \<in> mcp_gamma (map fst gcs) (fst p)"
      "s \<in> mcp_gamma ds (fst p)" "E \<in> mcp_gamma ds (snd p)"
    using Cons.prems(4) unfolding gc by auto
  have "mcp_component_sound \<G> g c" using Cons.prems(1) unfolding gc by simp
  then obtain q where q: "q \<in> set (mc_en c A ci p)" "s \<in> g (fst q)" "E \<in> g (snd q)"
    using p(2) A unfolding E mcp_component_sound_def by meson
  have keep: "d (fst q) = d (fst p) \<and> d (snd q) = d (snd p)"
    if "d \<in> fst ` set gcs \<union> set ds" for d
  proof -
    have "mcp_frame c d" using that frames(1) Cons.prems(3) unfolding gc by auto
    then show ?thesis using q(1) unfolding mcp_frame_def by blast
  qed
  have q_in: "q \<in> set (concat (map (mc_en c A ci) ps))"
    using p(1) q(1) by auto
  have "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c A ci) ps)) (map snd gcs)
                 (concat (map (mc_en c A ci) ps))).
          s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma (g # ds) (fst p)
          \<and> E \<in> mcp_gamma (map fst gcs) (snd p) \<and> E \<in> mcp_gamma (g # ds) (snd p)"
  proof (rule Cons.IH)
    show "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" using Cons.prems(1) by simp
    show "mcp_independent gcs" by (fact frames(3))
    show "\<forall>c' \<in> snd ` set gcs. \<forall>d \<in> set (g # ds). mcp_frame c' d"
      using frames(2) Cons.prems(3) unfolding gc by auto
    show "\<exists>p \<in> set (concat (map (mc_en c A ci) ps)).
            s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma (g # ds) (fst p)
            \<and> E \<in> mcp_gamma (g # ds) (snd p)"
    proof (rule bexI[OF _ q_in])
      show "s \<in> mcp_gamma (map fst gcs) (fst q) \<and> s \<in> mcp_gamma (g # ds) (fst q)
              \<and> E \<in> mcp_gamma (g # ds) (snd q)"
      proof -
        have "mcp_gamma (map fst gcs) (fst q) = mcp_gamma (map fst gcs) (fst p)"
            "mcp_gamma ds (fst q) = mcp_gamma ds (fst p)"
            "mcp_gamma ds (snd q) = mcp_gamma ds (snd p)"
          using keep by (auto simp: mcp_gamma_def intro!: INF_cong)
        then show ?thesis using p(3-5) q(2,3) by simp
      qed
    qed
  qed
  then show ?case unfolding gc by (auto simp: mcp_gamma_def)
qed

lemma mcp_qry_fold_sound:
  "s \<in> mcp_gamma (map fst gcs) x \<Longrightarrow> eval_query.oracle_holds A s
   \<Longrightarrow> \<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c
   \<Longrightarrow> eval_holds q r s
   \<Longrightarrow> eval_holds q (fold (\<lambda>c r. r \<sqinter> mc_qry c A x q) (map snd gcs) r) s"
proof (induction gcs arbitrary: r)
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  have "eval_holds q (mc_qry c A x q) s"
    using Cons.prems unfolding gc by (simp add: mcp_component_sound_def)
  with Cons.prems(4) have "eval_holds q (r \<sqinter> mc_qry c A x q) s"
    by (rule eval_query.inf_sound)
  then show ?case
    using Cons.IH[of "r \<sqinter> mc_qry c A x q"] Cons.prems(1-3) unfolding gc by simp
qed simp

section \<open>A component as a specification\<close>

text \<open>
  A component runs as the local specification whose fields are its own
  operations, each given the component's closed channel on the state it is
  asked about. The specification names no questions of its own: its channel is
  a pure function of the state, so a transfer asks it whatever it needs while it
  runs, as a Goblint transfer asks \<open>man.ask\<close>. Entry starts both halves at the
  caller's record.
\<close>

definition component_spec :: "'s mcp_component \<Rightarrow> ('x,'k,'v,'s::bot,'G) dg_spec" where
  "component_spec c = local_dg_spec (\<lambda>_ _. []) (mc_channel c)
     (\<lambda>_ d. mc_step c (mc_channel c d) EA_Nop d)
     (\<lambda>_ x e d. mc_step c (mc_channel c d) (EA_Assign x e) d)
     (\<lambda>_ sc x d. mc_step c (mc_channel c d) (EA_Special sc x) d)
     (\<lambda>_ b pol d. mc_step c (mc_channel c d) (if pol then EA_Assume b else EA_AssumeNot b) d)
     (\<lambda>_ p d. mc_step c (mc_channel c d) (EA_Body p) d)
     (\<lambda>_ e p d. mc_step c (mc_channel c d) (EA_Ret e p) d)
     (\<lambda>ci d. mc_en c (mc_channel c d) ci (d, d))
     (\<lambda>_ ev d. mc_step c (mc_channel c d) (event_action ev) d)
     (\<lambda>ci dc de. mc_comb_env c (mc_channel c dc) (mc_channel c de) ci dc de)
     (\<lambda>ci dc de. mc_comb_assign c (mc_channel c de) ci dc de)"

text \<open>The step a component takes on an edge, with its own channel.\<close>

definition component_step :: "'s mcp_component \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "component_step c a d = mc_step c (mc_channel c d) a d"

lemma local_spec_step_component_spec:
  "local_spec_step (\<lambda>d. mc_step c (mc_channel c d) EA_Nop d)
     (\<lambda>x e d. mc_step c (mc_channel c d) (EA_Assign x e) d)
     (\<lambda>sc x d. mc_step c (mc_channel c d) (EA_Special sc x) d)
     (\<lambda>b pol d. mc_step c (mc_channel c d) (if pol then EA_Assume b else EA_AssumeNot b) d)
     (\<lambda>p d. mc_step c (mc_channel c d) (EA_Body p) d)
     (\<lambda>e p d. mc_step c (mc_channel c d) (EA_Ret e p) d)
     (\<lambda>ev d. mc_step c (mc_channel c d) (event_action ev) d) a
   = component_step c a"
  by (cases a) (simp_all add: component_step_def fun_eq_iff)

theorem component_local_spec:
  assumes sound: "mcp_component_sound \<G> gm c"
  shows "sound_local_dg_spec (mc_channel c)
     (\<lambda>_ d. mc_step c (mc_channel c d) EA_Nop d)
     (\<lambda>_ x e d. mc_step c (mc_channel c d) (EA_Assign x e) d)
     (\<lambda>_ sc x d. mc_step c (mc_channel c d) (EA_Special sc x) d)
     (\<lambda>_ b pol d. mc_step c (mc_channel c d) (if pol then EA_Assume b else EA_AssumeNot b) d)
     (\<lambda>_ p d. mc_step c (mc_channel c d) (EA_Body p) d)
     (\<lambda>_ e p d. mc_step c (mc_channel c d) (EA_Ret e p) d)
     (\<lambda>ci d. mc_en c (mc_channel c d) ci (d, d))
     (\<lambda>_ ev d. mc_step c (mc_channel c d) (event_action ev) d)
     (\<lambda>ci dc de. mc_comb_env c (mc_channel c dc) (mc_channel c de) ci dc de)
     (\<lambda>ci dc de. mc_comb_assign c (mc_channel c de) ci dc de)
     gm \<G>"
proof (unfold_locales, goal_cases)
  case (1 d d')
  then show ?case using sound unfolding mcp_component_sound_def by metis
next
  case (2 a d A)
  have "gm d \<subseteq> Collect (eval_query.oracle_holds (mc_channel c d))"
    using mc_channel_sound[OF sound] by blast
  then have "edge_collect a (gm d \<inter> Collect (eval_query.oracle_holds A))
      \<subseteq> edge_collect a (gm d \<inter> Collect (eval_query.oracle_holds (mc_channel c d)))"
    by (intro edge_collect_mono) blast
  also have "\<dots> \<subseteq> gm (mc_step c (mc_channel c d) a d)"
    using sound unfolding mcp_component_sound_def by blast
  finally show ?case
    by (simp only: local_spec_step_component_spec component_step_def)
next
  case (3 s d ci)
  then obtain q where "q \<in> set (mc_en c (mc_channel c d) ci (d, d))" "s \<in> gm (fst q)"
      "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gm (snd q)"
    using sound mc_channel_sound[OF sound 3] unfolding mcp_component_sound_def
    by (metis fst_conv)
  then show ?case
    by (intro entry_pairs_coverI[of "fst q" "snd q"]) simp_all
next
  case (4 s dc t de ci)
  then show ?case
    using sound mc_channel_sound[OF sound 4(1)] mc_channel_sound[OF sound 4(2)]
    unfolding mcp_component_sound_def by blast
next
  case (5 s d q)
  then show ?case
    using mc_channel_sound[OF sound 5] by (simp add: eval_query.oracle_holdsD)
qed

theorem component_contract:
  assumes "mcp_component_sound \<G> gm c"
  shows "analysis_contract (component_spec c) (\<lambda>d g. gm d) \<G>"
  unfolding component_spec_def
  by (rule sound_local_dg_spec.local_spec_contract[OF component_local_spec[OF assms]])

section \<open>Several components as one\<close>

text \<open>
  The combination of several components is itself a component. One
  component is its own combination, so a single analysis and an \<open>MCP\<close> of one
  analysis are the same specification. Several components run their returns
  one after the other, each through both of its stages: the combination's env
  stage runs every component's composite, and its assign stage keeps the state
  it is handed. Running every env stage before every assign stage would need the
  stages of different components to commute, which independence of their
  concretizations does not give. The composite needs the caller's channel, which
  only the env stage receives.
\<close>

fun mcp_combine :: "'s mcp_component list \<Rightarrow> 's mcp_component" where
  "mcp_combine [c] = c"
| "mcp_combine cs =
     make_component (mcp_qry cs) (mcp_step cs) (mcp_en_from cs) (mcp_comb cs) (\<lambda>B ci dc de. dc)"

text \<open>Components that answer nothing combine to a state that answers nothing.\<close>

lemma mcp_qry_top: "(\<And>c. c \<in> set cs \<Longrightarrow> mc_qry c A x q = \<top>) \<Longrightarrow> mcp_qry cs A x q = \<top>"
  unfolding mcp_qry_def by (induction cs) auto

lemma mcp_combine_qry_top:
  "(\<And>c. c \<in> set cs \<Longrightarrow> mc_qry c A x q = \<top>) \<Longrightarrow> mc_qry (mcp_combine cs) A x q = \<top>"
  by (cases cs rule: mcp_combine.cases) (auto intro!: mcp_qry_top)

definition mcp_spec :: "'s mcp_component list \<Rightarrow> ('x,'k,'v,'s::bot,'G) dg_spec" where
  "mcp_spec cs = component_spec (mcp_combine cs)"

theorem mcp_combine_sound:
  assumes sound: "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c"
    and indep: "mcp_independent gcs" and ne: "gcs \<noteq> []"
  shows "mcp_component_sound \<G> (mcp_gamma (map fst gcs)) (mcp_combine (map snd gcs))"
proof (cases "\<exists>gc. gcs = [gc]")
  case True
  then obtain g c where "gcs = [(g, c)]" by fastforce
  then show ?thesis using sound by (simp add: mcp_component_sound_def mcp_gamma_def)
next
  case False
  have comb: "mcp_combine (map snd gcs) =
     make_component (mcp_qry (map snd gcs)) (mcp_step (map snd gcs))
       (mcp_en_from (map snd gcs)) (mcp_comb (map snd gcs)) (\<lambda>B ci dc de. dc)"
    using False ne by (cases "map snd gcs" rule: mcp_combine.cases) (auto simp: Cons_eq_map_conv)
  have enter: "\<exists>q \<in> set (mcp_en_from (map snd gcs) A ci p).
                 s \<in> mcp_gamma (map fst gcs) (fst q)
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> mcp_gamma (map fst gcs) (snd q)"
    if "s \<in> mcp_gamma (map fst gcs) (fst p)" "eval_query.oracle_holds A s" for A s ci p
    using mcp_en_fold_sound[OF sound indep, of "[]" "[p]" s _ A ci] that
    by (auto simp: mcp_en_from_def)
  have mono: "\<forall>x y. x \<le> y \<longrightarrow> mcp_gamma (map fst gcs) x \<subseteq> mcp_gamma (map fst gcs) y"
    using sound by (fastforce simp: mcp_gamma_def mcp_component_sound_def)
  have qry: "\<forall>A s x q. s \<in> mcp_gamma (map fst gcs) x \<longrightarrow> eval_query.oracle_holds A s
               \<longrightarrow> eval_holds q (mcp_qry (map snd gcs) A x q) s"
    unfolding mcp_qry_def using mcp_qry_fold_sound[OF _ _ sound] by simp
  show ?thesis
    unfolding comb mcp_component_sound_def
    using mono mcp_step_sound[OF sound indep] mcp_comb_sound[OF sound indep] enter qry
    by simp
qed

theorem mcp_contract:
  assumes "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" and "mcp_independent gcs"
    and "gcs \<noteq> []"
  shows "analysis_contract (mcp_spec (map snd gcs)) (\<lambda>d g. mcp_gamma (map fst gcs) d) \<G>"
  unfolding mcp_spec_def by (rule component_contract[OF mcp_combine_sound[OF assms]])

section \<open>A local specification as a component\<close>

text \<open>
  A registered analysis is a local specification over its own carrier \<open>'c\<close>.
  A lens \<open>get\<close>/\<open>put\<close> places that carrier in one field of the combined record,
  and \<open>lens_component\<close> runs the specification on that field, as Goblint's
  \<open>inner_man\<close> hands a component its own part of the \<open>MCP\<close> state. Its
  concretization reads that field. A local specification's handler answers from
  its own value and asks nothing, and its entry and return take no answers, so
  only its edge transfers consult the channel.
\<close>

definition lens_component ::
  "('s \<Rightarrow> 'c) \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> 's) \<Rightarrow> ('c \<Rightarrow> answers)
   \<Rightarrow> (answers \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (answers \<Rightarrow> pname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c enter_result list)
   \<Rightarrow> (answers \<Rightarrow> analysis_event \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> 's mcp_component"
where
  "lens_component get put qry sk asn sp br bd rt en ev ce ca = make_component
     (\<lambda>A x. qry (get x))
     (\<lambda>A a x. put x (local_spec_step (sk A) (asn A) (sp A) (br A) (bd A) (rt A) (ev A)
                       a (get x)))
     (\<lambda>A ci p. map (\<lambda>(c, e). (put (fst p) c, put (snd p) e)) (en ci (get (fst p))))
     (\<lambda>A B ci x de. put x (ce ci (get x) (get de)))
     (\<lambda>B ci x de. put x (ca ci (get x) (get de)))"

theorem lens_component_sound:
  assumes spec: "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "mcp_component_sound \<G> (\<lambda>x. gammaD (get x))
           (lens_component get put qry sk asn sp br bd rt en ev ce ca)"
proof -
  interpret S: sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G> by (fact spec)
  have enter: "\<exists>q \<in> set (map (\<lambda>(c, e). (put (fst p) c, put (snd p) e)) (en ci (get (fst p)))).
                 s \<in> gammaD (get (fst q))
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> gammaD (get (snd q))"
    if s_in: "s \<in> gammaD (get (fst p))" for s ci p
  proof -
    obtain c e where "(c, e) \<in> set (en ci (get (fst p)))" "s \<in> gammaD c"
        "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gammaD e"
      using S.enter_sound_local[OF s_in, of ci] unfolding entry_pairs_cover_def by blast
    then show ?thesis
      by (intro bexI[of _ "(put (fst p) c, put (snd p) e)"]) (auto simp: get_put)
  qed
  show ?thesis
    unfolding mcp_component_sound_def lens_component_def
    using S.gammaD_mono get_mono S.step_sound_local S.combine_sound_local S.qry_sound enter
    by (simp add: get_put)
qed

theorem lens_frame:
  assumes "\<And>x v. get2 (put1 x v) = get2 x"
  shows "mcp_frame (lens_component get1 put1 qry1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1)
                   (\<lambda>x. g2 (get2 x))"
  unfolding mcp_frame_def lens_component_def by (auto simp: assms)

subsection \<open>A local specification over the whole state\<close>

text \<open>
  Through the identity lens a local specification is a component over its own
  carrier. Its handler asks nothing, so its channel is the handler itself, and
  the component runs as the specification it came from with every transfer
  given the handler's answers.
\<close>

abbreviation local_component where
  "local_component \<equiv> lens_component id (\<lambda>_ v. v)"

lemma local_spec_step_event_action [simp]:
  "local_spec_step sk asn sp br bd rt ev (event_action e) = ev e"
  by (cases e) simp

lemma mc_channel_local_component [simp]:
  "mc_channel (local_component qry sk asn sp br bd rt en ev ce ca) = qry"
  by (rule mc_channel_const) (simp add: lens_component_def)

theorem component_spec_local_component:
  "component_spec (local_component qry sk asn sp br bd rt en ev ce ca)
   = local_dg_spec (\<lambda>_ _. []) qry
       (\<lambda>_ d. sk (qry d) d) (\<lambda>_ x e d. asn (qry d) x e d) (\<lambda>_ c x d. sp (qry d) c x d)
       (\<lambda>_ b pol d. br (qry d) b pol d) (\<lambda>_ p d. bd (qry d) p d) (\<lambda>_ e p d. rt (qry d) e p d)
       en (\<lambda>_ v d. ev (qry d) v d) ce ca"
proof -
  have en: "(\<lambda>ci d. map (\<lambda>(c, e). (c, e)) (en ci d)) = en"
    by (simp add: fun_eq_iff case_prod_beta)
  have br: "(\<lambda>_ b pol d. local_spec_step (sk (qry d)) (asn (qry d)) (sp (qry d)) (br (qry d))
               (bd (qry d)) (rt (qry d)) (ev (qry d)) (if pol then EA_Assume b else EA_AssumeNot b) d)
          = (\<lambda>_ b pol d. br (qry d) b pol d)"
    by (intro ext) (simp split: if_split)
  show ?thesis
    unfolding component_spec_def mc_channel_local_component
    by (simp add: lens_component_def en br)
qed

theorem local_component_sound:
  assumes "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
  shows "mcp_component_sound \<G> gammaD (local_component qry sk asn sp br bd rt en ev ce ca)"
proof -
  have "mcp_component_sound \<G> (\<lambda>x. gammaD (id x))
          (local_component qry sk asn sp br bd rt en ev ce ca)"
    by (rule lens_component_sound[OF assms]) simp_all
  then show ?thesis by simp
qed

section \<open>A component on one field of a larger state\<close>

text \<open>
  A component over its own carrier \<open>'c\<close> runs on one field of the combined
  state through a lens: every operation reads the field, and writes back only
  the field. This is \<^const>\<open>lens_component\<close> for a component that already
  exists rather than for the operations of a local specification. The channel
  passes through unchanged: it describes the stores of the whole state, which
  are the stores the field describes as well.
\<close>

definition lens_of :: "('s \<Rightarrow> 'c) \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> 's) \<Rightarrow> 'c mcp_component \<Rightarrow> 's mcp_component"
where
  "lens_of get put c = make_component
     (\<lambda>A x. mc_qry c A (get x))
     (\<lambda>A a x. put x (mc_step c A a (get x)))
     (\<lambda>A ci p. map (\<lambda>(q, e). (put (fst p) q, put (snd p) e))
                (mc_en c A ci (get (fst p), get (snd p))))
     (\<lambda>A B ci x de. put x (mc_comb_env c A B ci (get x) (get de)))
     (\<lambda>B ci x de. put x (mc_comb_assign c B ci (get x) (get de)))"

lemma get_mc_comb_lens_of:
  assumes "\<And>x v. get (put x v) = v"
  shows "get (mc_comb (lens_of get put c) A B ci x de) = mc_comb c A B ci (get x) (get de)"
  by (simp add: lens_of_def assms)

theorem lens_of_sound:
  assumes sound: "mcp_component_sound \<G> g c"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "mcp_component_sound \<G> (\<lambda>x. g (get x)) (lens_of get put c)"
proof -
  have enter: "\<exists>q \<in> set (mc_en (lens_of get put c) A ci p).
                 s \<in> g (get (fst q))
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> g (get (snd q))"
    if s_in: "s \<in> g (get (fst p))" and A: "eval_query.oracle_holds A s" for A s ci p
  proof -
    have "s \<in> g (fst (get (fst p), get (snd p)))" using s_in by simp
    then obtain q where "q \<in> set (mc_en c A ci (get (fst p), get (snd p)))" "s \<in> g (fst q)"
        "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound A unfolding mcp_component_sound_def by metis
    then show ?thesis
      by (intro bexI[of _ "(put (fst p) (fst q), put (snd p) (snd q))"])
         (auto simp: lens_of_def get_put)
  qed
  show ?thesis
    using sound get_mono enter
    unfolding mcp_component_sound_def get_mc_comb_lens_of[of get put, OF get_put]
    by (simp add: lens_of_def get_put)
qed

theorem lens_of_frame:
  assumes "\<And>x v. get2 (put1 x v) = get2 x"
  shows "mcp_frame (lens_of get1 put1 c) (\<lambda>x. g2 (get2 x))"
  unfolding mcp_frame_def lens_of_def by (auto simp: assms)

section \<open>Replacing a component's handler\<close>

text \<open>
  The handler is the only operation that neither changes a state nor is framed,
  so any other handler that answers soundly for the same states may replace it.
  This is how an analysis written without a query handler becomes a provider
  once it runs in the combined state.
\<close>

definition with_qry :: "(answers \<Rightarrow> 's \<Rightarrow> answers) \<Rightarrow> 's mcp_component \<Rightarrow> 's mcp_component" where
  "with_qry h c = c\<lparr>mc_qry := h\<rparr>"

theorem with_qry_sound:
  assumes "mcp_component_sound \<G> gm c"
    and "\<And>A s x q. s \<in> gm x \<Longrightarrow> eval_query.oracle_holds A s \<Longrightarrow> eval_holds q (h A x q) s"
  shows "mcp_component_sound \<G> gm (with_qry h c)"
  using assms unfolding mcp_component_sound_def with_qry_def by simp

lemma with_qry_frame: "mcp_frame c g \<Longrightarrow> mcp_frame (with_qry h c) g"
  by (simp add: mcp_frame_def with_qry_def)

section \<open>Normalizing what a component produces\<close>

text \<open>
  A normalization \<open>k\<close> that keeps a state's concretization may be applied to
  what a component produces: each step, the entered half of each entry, and
  the return after its second stage. The caller half of an entry is the
  caller's state and stays as it is. The first stage of a return is left
  alone, because the component's soundness speaks only about the composite.
  The combined state of several analyses uses this to become unreachable as
  soon as one active analysis is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close>.
\<close>

definition map_component :: "('s \<Rightarrow> 's) \<Rightarrow> 's mcp_component \<Rightarrow> 's mcp_component" where
  "map_component k c = make_component (mc_qry c)
     (\<lambda>A a x. k (mc_step c A a x))
     (\<lambda>A ci p. map (\<lambda>(q, e). (q, k e)) (mc_en c A ci p))
     (mc_comb_env c)
     (\<lambda>B ci x de. k (mc_comb_assign c B ci x de))"

theorem map_component_sound:
  assumes sound: "mcp_component_sound \<G> g c"
    and keep: "\<And>x. g (k x) = g x"
  shows "mcp_component_sound \<G> g (map_component k c)"
proof -
  have enter: "\<exists>q \<in> set (mc_en (map_component k c) A ci p).
                 s \<in> g (fst q)
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
    if s_in: "s \<in> g (fst p)" and A: "eval_query.oracle_holds A s" for A s ci p
  proof -
    obtain q where "q \<in> set (mc_en c A ci p)" "s \<in> g (fst q)"
        "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound s_in A unfolding mcp_component_sound_def by metis
    then show ?thesis
      by (intro bexI[of _ "(fst q, k (snd q))"]) (auto simp: map_component_def keep)
  qed
  show ?thesis
    using sound enter unfolding mcp_component_sound_def
    by (simp add: map_component_def keep)
qed

section \<open>Components whose entry answers once\<close>

text \<open>
  An entry that answers a single alternative, paired with the caller's own
  state, is what the routed pipeline consumes. Lenses, combination and
  normalization keep that shape.
\<close>

definition single_entry :: "'s mcp_component \<Rightarrow> bool" where
  "single_entry c \<longleftrightarrow> (\<forall>A ci p. \<exists>e. mc_en c A ci p = [(fst p, e)])"

lemma single_entryD:
  "single_entry c \<Longrightarrow> mc_en c A ci p = [(fst p, snd (hd (mc_en c A ci p)))]"
  unfolding single_entry_def by (metis list.sel(1) snd_conv)

lemma single_entry_lens_of:
  assumes single: "single_entry c" and put_get: "\<And>x. put x (get x) = x"
  shows "single_entry (lens_of get put c)"
  unfolding single_entry_def
proof (intro allI)
  fix A ci p
  obtain e where "mc_en c A ci (get (fst p), get (snd p)) = [(get (fst p), e)]"
    using single unfolding single_entry_def by (metis fst_conv)
  then show "\<exists>e. mc_en (lens_of get put c) A ci p = [(fst p, e)]"
    by (simp add: lens_of_def put_get)
qed

lemma single_entry_map_component:
  assumes "single_entry c"
  shows "single_entry (map_component k c)"
  unfolding single_entry_def
proof (intro allI)
  fix A ci p
  obtain e where "mc_en c A ci p = [(fst p, e)]"
    using assms unfolding single_entry_def by blast
  then show "\<exists>e. mc_en (map_component k c) A ci p = [(fst p, e)]"
    by (simp add: map_component_def)
qed

lemma single_entry_with_qry: "single_entry c \<Longrightarrow> single_entry (with_qry h c)"
  by (simp add: single_entry_def with_qry_def)

lemma single_entry_mcp_en_fold:
  assumes "\<forall>c \<in> set cs. single_entry c"
  shows "\<exists>e. fold (\<lambda>c ps. concat (map (mc_en c A ci) ps)) cs [(d, e0)] = [(d, e)]"
  using assms
proof (induction cs arbitrary: e0)
  case (Cons c cs)
  obtain e1 where "mc_en c A ci (d, e0) = [(d, e1)]"
    using Cons.prems unfolding single_entry_def by (metis fst_conv list.set_intros(1))
  then show ?case using Cons.IH[of e1] Cons.prems by simp
qed simp

lemma single_entry_mcp_combine:
  assumes single: "\<forall>c \<in> set cs. single_entry c" and ne: "cs \<noteq> []"
  shows "single_entry (mcp_combine cs)"
proof (cases "\<exists>c. cs = [c]")
  case True
  then show ?thesis using single by auto
next
  case False
  then have "mc_en (mcp_combine cs) = mcp_en_from cs"
    using ne by (cases cs rule: mcp_combine.cases) auto
  then show ?thesis
    unfolding single_entry_def mcp_en_from_def
    using single_entry_mcp_en_fold[OF single] by (metis prod.collapse)
qed

section \<open>One field of a reachability-lifted record\<close>

text \<open>
  The combined state is a record of fields under one reachability lift, whose
  \<^const>\<open>Bot\<close> is the state no analysis can reach. Each field has a bottom of
  its own: a reachability-lifted field's is \<^const>\<open>Bot\<close>, and a carrier with an
  unreachable element of its own uses that. A field's lens reads the field's
  bottom from the unreachable state, and writing any other value into it starts
  from the record whose fields are all at bottom. Writing bottom into the
  unreachable state leaves it unreachable, so writing back what was read
  changes nothing.
\<close>

definition lift_get :: "('r \<Rightarrow> 'c::bot) \<Rightarrow> 'r lifted \<Rightarrow> 'c" where
  "lift_get f x = (case x of Bot \<Rightarrow> \<bottom> | Lifted r \<Rightarrow> f r)"

definition lift_put :: "('r \<Rightarrow> 'c::bot \<Rightarrow> 'r) \<Rightarrow> 'r::bot lifted \<Rightarrow> 'c \<Rightarrow> 'r lifted" where
  "lift_put u x v =
     (case x of
        Bot \<Rightarrow> (if v = \<bottom> then Bot else Lifted (u \<bottom> v))
      | Lifted r \<Rightarrow> Lifted (u r v))"

lemma lift_get_simps [simp]:
  "lift_get f Bot = \<bottom>" "lift_get f (Lifted r) = f r"
  by (simp_all add: lift_get_def)

lemma lift_get_put:
  assumes "\<And>r v. f (u r v) = v" and "f \<bottom> = \<bottom>"
  shows "lift_get f (lift_put u x v) = v"
  using assms by (cases x) (simp_all add: lift_put_def)

lemma lift_put_get:
  assumes "\<And>r. u r (f r) = r"
  shows "lift_put u x (lift_get f x) = x"
  using assms by (cases x) (simp_all add: lift_put_def)

lemma lift_get_mono:
  fixes f :: "'r::semilattice_sup \<Rightarrow> 'c::order_bot"
  assumes "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "x \<le> y \<Longrightarrow> lift_get f x \<le> lift_get f y"
  using assms by (cases x; cases y) simp_all

lemma lift_get_put_other:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = \<bottom>"
  shows "lift_get f2 (lift_put u1 x v) = lift_get f2 x"
  using assms by (cases x) (simp_all add: lift_put_def)

text \<open>
  Components that each own a distinct field are independent: a list of
  distinct analyses, each run on its own field, satisfies
  \<^const>\<open>mcp_independent\<close> as soon as every one leaves every other field alone.
\<close>

lemma mcp_independent_map:
  assumes "distinct as"
    and "\<And>a b. a \<in> set as \<Longrightarrow> b \<in> set as \<Longrightarrow> a \<noteq> b \<Longrightarrow> mcp_frame (c a) (g b)"
  shows "mcp_independent (map (\<lambda>a. (g a, c a)) as)"
  using assms by (induction as) auto

end
