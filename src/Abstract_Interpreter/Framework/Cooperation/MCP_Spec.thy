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

  A component's operations are those of a local specification, with one
  change that lets components be chained over one record: its entry transfer
  takes the pair of records built so far and sets its own field in both
  halves. A single analysis is a component too, and runs as the specification
  \<open>component_spec\<close> builds from it.

  A component holds only what runs. What its states describe, a set of stores,
  is not executable and is supplied beside it wherever soundness is stated,
  as \<^class>\<open>numeric_domain\<close> keeps \<open>gamma\<close> out of \<^class>\<open>executable_domain\<close>.
\<close>

record 's mcp_component =
  mc_qry :: "'s \<Rightarrow> answers"
  mc_qs :: "edge_action \<Rightarrow> 's \<Rightarrow> query list"
  mc_step :: "answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's"
  mc_en :: "call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  mc_comb_env :: "call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  mc_comb_assign :: "call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"

text \<open>
  The return runs in the two stages of Goblint's \<open>combine_env\<close> and
  \<open>combine_assign\<close>. Soundness and independence speak about their composite.
\<close>

abbreviation mc_comb :: "'s mcp_component \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mc_comb c ci x de \<equiv> mc_comb_assign c ci (mc_comb_env c ci x de) de"

text \<open>
  A component is sound for a concretization \<open>gamma\<close> when each operation covers the
  concrete behaviour, whatever the other fields of the record hold. The step
  is proved against every answer function that holds at the start store, as
  in \<^locale>\<open>sound_local_dg_spec\<close>.
\<close>

definition mcp_component_sound ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('s::order \<Rightarrow> store set) \<Rightarrow> 's mcp_component \<Rightarrow> bool" where
  "mcp_component_sound \<G> gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>A a x. edge_collect a (gm x \<inter> Collect (eval_query.oracle_holds A))
                  \<subseteq> gm (mc_step c A a x))
     \<and> (\<forall>s ci p. s \<in> gm (fst p) \<longrightarrow>
          (\<exists>q \<in> set (mc_en c ci p). s \<in> gm (fst q)
             \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>s t ci x de. s \<in> gm x \<longrightarrow> t \<in> gm de \<longrightarrow>
          combine_collect \<G> (ci_dst ci) s t \<in> gm (mc_comb c ci x de))
     \<and> (\<forall>s x q. s \<in> gm x \<longrightarrow> eval_holds q (mc_qry c x q) s)"

text \<open>
  A component leaves a concretization alone when none of its operations
  changes what that concretization says. For components that each own one
  field of a record this is the lens law that updating one field leaves the
  others.
\<close>

definition mcp_frame :: "'s mcp_component \<Rightarrow> ('s \<Rightarrow> store set) \<Rightarrow> bool" where
  "mcp_frame c gm \<longleftrightarrow>
     (\<forall>A a x. gm (mc_step c A a x) = gm x)
     \<and> (\<forall>ci p q. q \<in> set (mc_en c ci p) \<longrightarrow>
          gm (fst q) = gm (fst p) \<and> gm (snd q) = gm (snd p))
     \<and> (\<forall>ci x de. gm (mc_comb c ci x de) = gm x)"

text \<open>
  Cooperating analyses come as pairs of a concretization and a component.
  They are independent when each leaves the others' concretizations alone.
\<close>

type_synonym 's certified_component = "('s \<Rightarrow> store set) \<times> 's mcp_component"

fun mcp_independent :: "'s certified_component list \<Rightarrow> bool" where
  "mcp_independent [] \<longleftrightarrow> True"
| "mcp_independent ((g, c) # gcs) \<longleftrightarrow>
     (\<forall>(g', c') \<in> set gcs. mcp_frame c g' \<and> mcp_frame c' g) \<and> mcp_independent gcs"

section \<open>The combined operations\<close>

text \<open>
  The combined operations run the active components in turn. Each reads only
  its own field, which no other component writes, so the order does not
  matter; the fold is merely one way to write ``all of them''. The answers are
  fixed once per edge, from the predecessor state, and every component gets
  the same answers, as every Goblint component gets the same \<open>man.ask\<close>.
\<close>

definition mcp_step :: "'s mcp_component list \<Rightarrow> answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_step cs A a x = fold (\<lambda>c y. mc_step c A a y) cs x"

definition mcp_en_from ::
  "'s mcp_component list \<Rightarrow> call_info \<Rightarrow> 's \<times> 's \<Rightarrow> 's enter_result list" where
  "mcp_en_from cs ci p = fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) cs [p]"

definition mcp_comb :: "'s mcp_component list \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_comb cs ci x de = fold (\<lambda>c y. mc_comb c ci y de) cs x"

definition mcp_qry :: "'s mcp_component list \<Rightarrow> 's \<Rightarrow> answers" where
  "mcp_qry cs x q = fold (\<lambda>c r. r \<sqinter> mc_qry c x q) cs \<top>"

definition mcp_qs :: "'s mcp_component list \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> query list" where
  "mcp_qs cs a x = concat (map (\<lambda>c. mc_qs c a x) cs)"

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
  "(\<forall>c \<in> set cs. mcp_frame c g) \<Longrightarrow> g (fold (\<lambda>c y. mc_comb c ci y de) cs x) = g x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma mcp_gamma_frame:
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (mc_step c A a x) = mcp_gamma gs x"
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (mc_comb c ci x de) = mcp_gamma gs x"
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
    and "s \<in> mcp_gamma (map fst gcs) x" and "t \<in> mcp_gamma (map fst gcs) de"
  shows "combine_collect \<G> (ci_dst ci) s t
           \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) ci x de)"
  using assms
proof (induction gcs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  let ?x1 = "mc_comb c ci x de"
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  have own: "combine_collect \<G> (ci_dst ci) s t \<in> g ?x1"
    using Cons.prems(1,3,4) unfolding gc by (simp add: mcp_component_sound_def)
  have own_kept: "g (mcp_comb (map snd gcs) ci ?x1 de) = g ?x1"
    unfolding mcp_comb_def by (rule gamma_fold_comb) (use frames in auto)
  have rest_eq: "mcp_gamma (map fst gcs) ?x1 = mcp_gamma (map fst gcs) x"
    by (rule mcp_gamma_frame(2)) (use frames in auto)
  have rest: "combine_collect \<G> (ci_dst ci) s t
      \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) ci ?x1 de)"
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
    and E: "E = call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s"
  shows "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) (map snd gcs) ps).
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
  then obtain q where q: "q \<in> set (mc_en c ci p)" "s \<in> g (fst q)" "E \<in> g (snd q)"
    using p(2) unfolding E mcp_component_sound_def by meson
  have keep: "d (fst q) = d (fst p) \<and> d (snd q) = d (snd p)"
    if "d \<in> fst ` set gcs \<union> set ds" for d
  proof -
    have "mcp_frame c d" using that frames(1) Cons.prems(3) unfolding gc by auto
    then show ?thesis using q(1) unfolding mcp_frame_def by blast
  qed
  have q_in: "q \<in> set (concat (map (mc_en c ci) ps))"
    using p(1) q(1) by auto
  have "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) (map snd gcs)
                 (concat (map (mc_en c ci) ps))).
          s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma (g # ds) (fst p)
          \<and> E \<in> mcp_gamma (map fst gcs) (snd p) \<and> E \<in> mcp_gamma (g # ds) (snd p)"
  proof (rule Cons.IH)
    show "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c" using Cons.prems(1) by simp
    show "mcp_independent gcs" by (fact frames(3))
    show "\<forall>c' \<in> snd ` set gcs. \<forall>d \<in> set (g # ds). mcp_frame c' d"
      using frames(2) Cons.prems(3) unfolding gc by auto
    show "\<exists>p \<in> set (concat (map (mc_en c ci) ps)).
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
  "s \<in> mcp_gamma (map fst gcs) x \<Longrightarrow> \<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c
   \<Longrightarrow> eval_holds q r s
   \<Longrightarrow> eval_holds q (fold (\<lambda>c r. r \<sqinter> mc_qry c x q) (map snd gcs) r) s"
proof (induction gcs arbitrary: r)
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  have "eval_holds q (mc_qry c x q) s"
    using Cons.prems unfolding gc by (simp add: mcp_component_sound_def)
  with Cons.prems(3) have "eval_holds q (r \<sqinter> mc_qry c x q) s"
    by (rule eval_query.inf_sound)
  then show ?case
    using Cons.IH[of "r \<sqinter> mc_qry c x q"] Cons.prems(1,2) unfolding gc by simp
qed simp

section \<open>A component as a specification\<close>

text \<open>
  A component runs as the local specification whose fields are its own
  operations. Entry starts both halves at the caller's record.
\<close>

definition component_spec :: "'s mcp_component \<Rightarrow> ('x,'k,'v,'s::bot,'G) dg_spec" where
  "component_spec c = local_dg_spec (mc_qs c) (mc_qry c)
     (\<lambda>A. mc_step c A EA_Nop)
     (\<lambda>A x e. mc_step c A (EA_Assign x e))
     (\<lambda>A sc x. mc_step c A (EA_Special sc x))
     (\<lambda>A b pol. mc_step c A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>A p. mc_step c A (EA_Body p))
     (\<lambda>A e p. mc_step c A (EA_Ret e p))
     (\<lambda>ci d. mc_en c ci (d, d))
     (\<lambda>A ev. mc_step c A (event_action ev))
     (mc_comb_env c)
     (mc_comb_assign c)"

lemma local_spec_step_component:
  "local_spec_step (mc_step c A EA_Nop) (\<lambda>x e. mc_step c A (EA_Assign x e))
     (\<lambda>sc x. mc_step c A (EA_Special sc x))
     (\<lambda>b pol. mc_step c A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>p. mc_step c A (EA_Body p)) (\<lambda>e p. mc_step c A (EA_Ret e p))
     (\<lambda>ev. mc_step c A (event_action ev)) a
   = mc_step c A a"
  by (cases a) simp_all

theorem component_local_spec:
  assumes sound: "mcp_component_sound \<G> gm c"
  shows "sound_local_dg_spec (mc_qry c)
     (\<lambda>A. mc_step c A EA_Nop)
     (\<lambda>A x e. mc_step c A (EA_Assign x e))
     (\<lambda>A sc x. mc_step c A (EA_Special sc x))
     (\<lambda>A b pol. mc_step c A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>A p. mc_step c A (EA_Body p))
     (\<lambda>A e p. mc_step c A (EA_Ret e p))
     (\<lambda>ci d. mc_en c ci (d, d))
     (\<lambda>A ev. mc_step c A (event_action ev))
     (mc_comb_env c)
     (mc_comb_assign c)
     gm \<G>"
proof (unfold_locales, goal_cases)
  case (1 d d')
  then show ?case using sound unfolding mcp_component_sound_def by blast
next
  case (2 a d A)
  show ?case
    unfolding local_spec_step_component using sound unfolding mcp_component_sound_def by blast
next
  case (3 s d ci)
  then obtain q where "q \<in> set (mc_en c ci (d, d))" "s \<in> gm (fst q)"
      "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gm (snd q)"
    using sound unfolding mcp_component_sound_def by (metis fst_conv)
  then show ?case
    by (intro entry_pairs_coverI[of "fst q" "snd q"]) simp_all
next
  case (4 s dc t de ci)
  then show ?case using sound unfolding mcp_component_sound_def by blast
next
  case (5 s d q)
  then show ?case using sound unfolding mcp_component_sound_def by blast
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
  stage keeps the caller's record, and its assign stage runs every component's
  composite. Running every env stage before every assign stage would need the
  stages of different components to commute, which independence of their
  concretizations does not give.
\<close>

fun mcp_combine :: "'s mcp_component list \<Rightarrow> 's mcp_component" where
  "mcp_combine [c] = c"
| "mcp_combine cs = \<lparr>
     mc_qry = mcp_qry cs,
     mc_qs = mcp_qs cs,
     mc_step = mcp_step cs,
     mc_en = mcp_en_from cs,
     mc_comb_env = (\<lambda>ci dc de. dc),
     mc_comb_assign = mcp_comb cs \<rparr>"

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
  have comb: "mcp_combine (map snd gcs) = \<lparr>
     mc_qry = mcp_qry (map snd gcs), mc_qs = mcp_qs (map snd gcs),
     mc_step = mcp_step (map snd gcs), mc_en = mcp_en_from (map snd gcs),
     mc_comb_env = (\<lambda>ci dc de. dc), mc_comb_assign = mcp_comb (map snd gcs) \<rparr>"
    using False ne by (cases "map snd gcs" rule: mcp_combine.cases) (auto simp: Cons_eq_map_conv)
  have enter: "\<exists>q \<in> set (mcp_en_from (map snd gcs) ci p).
                 s \<in> mcp_gamma (map fst gcs) (fst q)
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> mcp_gamma (map fst gcs) (snd q)"
    if "s \<in> mcp_gamma (map fst gcs) (fst p)" for s ci p
    using mcp_en_fold_sound[OF sound indep, of "[]" "[p]" s _ ci] that
    by (auto simp: mcp_en_from_def)
  have mono: "\<forall>x y. x \<le> y \<longrightarrow> mcp_gamma (map fst gcs) x \<subseteq> mcp_gamma (map fst gcs) y"
    using sound by (fastforce simp: mcp_gamma_def mcp_component_sound_def)
  have qry: "\<forall>s x q. s \<in> mcp_gamma (map fst gcs) x
               \<longrightarrow> eval_holds q (mcp_qry (map snd gcs) x q) s"
    unfolding mcp_qry_def using mcp_qry_fold_sound[OF _ sound] by simp
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
  concretization reads that field.
\<close>

definition lens_component ::
  "('s \<Rightarrow> 'c) \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> 's)
   \<Rightarrow> (edge_action \<Rightarrow> 'c \<Rightarrow> query list) \<Rightarrow> ('c \<Rightarrow> answers)
   \<Rightarrow> (answers \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (answers \<Rightarrow> pname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (answers \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c enter_result list)
   \<Rightarrow> (answers \<Rightarrow> analysis_event \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (call_info \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> 's mcp_component"
where
  "lens_component get put qs qry sk asn sp br bd rt en ev ce ca = \<lparr>
     mc_qry = (\<lambda>x. qry (get x)),
     mc_qs = (\<lambda>a x. qs a (get x)),
     mc_step = (\<lambda>A a x. put x (local_spec_step (sk A) (asn A) (sp A) (br A) (bd A) (rt A) (ev A)
                                 a (get x))),
     mc_en = (\<lambda>ci p. map (\<lambda>(c, e). (put (fst p) c, put (snd p) e)) (en ci (get (fst p)))),
     mc_comb_env = (\<lambda>ci x de. put x (ce ci (get x) (get de))),
     mc_comb_assign = (\<lambda>ci x de. put x (ca ci (get x) (get de))) \<rparr>"

theorem lens_component_sound:
  assumes spec: "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "mcp_component_sound \<G> (\<lambda>x. gammaD (get x))
           (lens_component get put qs qry sk asn sp br bd rt en ev ce ca)"
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
  shows "mcp_frame (lens_component get1 put1 qs1 qry1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1)
                   (\<lambda>x. g2 (get2 x))"
  unfolding mcp_frame_def lens_component_def by (auto simp: assms)

subsection \<open>A local specification over the whole state\<close>

text \<open>
  Through the identity lens a local specification is a component over its own
  carrier, and that component runs as exactly the specification it came from:
  a single analysis passes through \<^const>\<open>component_spec\<close> unchanged.
\<close>

abbreviation local_component where
  "local_component \<equiv> lens_component id (\<lambda>_ v. v)"

lemma local_spec_step_event_action [simp]:
  "local_spec_step sk asn sp br bd rt ev (event_action e) = ev e"
  by (cases e) simp

theorem component_spec_local_component:
  "component_spec (local_component qs qry sk asn sp br bd rt en ev ce ca)
   = local_dg_spec qs qry sk asn sp br bd rt en ev ce ca"
proof -
  have en: "(\<lambda>ci d. map (\<lambda>(c, e). (c, e)) (en ci d)) = en"
    by (simp add: fun_eq_iff case_prod_beta)
  have br: "(\<lambda>A b pol. local_spec_step (sk A) (asn A) (sp A) (br A) (bd A) (rt A) (ev A)
               (if pol then EA_Assume b else EA_AssumeNot b)) = br"
    by (simp add: fun_eq_iff)
  show ?thesis
    unfolding component_spec_def lens_component_def
    by (simp add: en br)
qed

theorem local_component_sound:
  assumes "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
  shows "mcp_component_sound \<G> gammaD (local_component qs qry sk asn sp br bd rt en ev ce ca)"
proof -
  have "mcp_component_sound \<G> (\<lambda>x. gammaD (id x))
          (local_component qs qry sk asn sp br bd rt en ev ce ca)"
    by (rule lens_component_sound[OF assms]) simp_all
  then show ?thesis by simp
qed

section \<open>A component on one field of a larger state\<close>

text \<open>
  A component over its own carrier \<open>'c\<close> runs on one field of the combined
  state through a lens: every operation reads the field, and writes back only
  the field. This is \<^const>\<open>lens_component\<close> for a component that already
  exists rather than for the operations of a local specification.
\<close>

definition lens_of :: "('s \<Rightarrow> 'c) \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> 's) \<Rightarrow> 'c mcp_component \<Rightarrow> 's mcp_component"
where
  "lens_of get put c = \<lparr>
     mc_qry = (\<lambda>x. mc_qry c (get x)),
     mc_qs = (\<lambda>a x. mc_qs c a (get x)),
     mc_step = (\<lambda>A a x. put x (mc_step c A a (get x))),
     mc_en = (\<lambda>ci p. map (\<lambda>(q, e). (put (fst p) q, put (snd p) e))
                        (mc_en c ci (get (fst p), get (snd p)))),
     mc_comb_env = (\<lambda>ci x de. put x (mc_comb_env c ci (get x) (get de))),
     mc_comb_assign = (\<lambda>ci x de. put x (mc_comb_assign c ci (get x) (get de))) \<rparr>"

lemma get_mc_comb_lens_of:
  assumes "\<And>x v. get (put x v) = v"
  shows "get (mc_comb (lens_of get put c) ci x de) = mc_comb c ci (get x) (get de)"
  by (simp add: lens_of_def assms)

theorem lens_of_sound:
  assumes sound: "mcp_component_sound \<G> g c"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "mcp_component_sound \<G> (\<lambda>x. g (get x)) (lens_of get put c)"
proof -
  have enter: "\<exists>q \<in> set (mc_en (lens_of get put c) ci p).
                 s \<in> g (get (fst q))
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> g (get (snd q))"
    if s_in: "s \<in> g (get (fst p))" for s ci p
  proof -
    have "s \<in> g (fst (get (fst p), get (snd p)))" using s_in by simp
    then obtain q where "q \<in> set (mc_en c ci (get (fst p), get (snd p)))" "s \<in> g (fst q)"
        "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound unfolding mcp_component_sound_def by metis  
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

section \<open>Normalizing what a component produces\<close>

text \<open>
  A normalization \<open>k\<close> that keeps a state's concretization may be applied to
  everything a component produces: each step, both halves of each entry, and
  the return after its second stage. The first stage of a return is left
  alone, because the component's soundness speaks only about the composite.
  The combined state of several analyses uses this to become unreachable as
  soon as one active analysis is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close>.
\<close>

definition map_component :: "('s \<Rightarrow> 's) \<Rightarrow> 's mcp_component \<Rightarrow> 's mcp_component" where
  "map_component k c = c\<lparr>
     mc_step := (\<lambda>A a x. k (mc_step c A a x)),
     mc_en := (\<lambda>ci p. map (\<lambda>(q, e). (k q, k e)) (mc_en c ci p)),
     mc_comb_assign := (\<lambda>ci x de. k (mc_comb_assign c ci x de)) \<rparr>"

theorem map_component_sound:
  assumes sound: "mcp_component_sound \<G> g c"
    and keep: "\<And>x. g (k x) = g x"
  shows "mcp_component_sound \<G> g (map_component k c)"
proof -
  have enter: "\<exists>q \<in> set (mc_en (map_component k c) ci p).
                 s \<in> g (fst q)
                 \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
    if s_in: "s \<in> g (fst p)" for s ci p
  proof -
    obtain q where "q \<in> set (mc_en c ci p)" "s \<in> g (fst q)"
        "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound s_in unfolding mcp_component_sound_def by metis
    then show ?thesis
      by (intro bexI[of _ "(k (fst q), k (snd q))"]) (auto simp: map_component_def keep)
  qed
  show ?thesis
    using sound enter unfolding mcp_component_sound_def
    by (simp add: map_component_def keep)
qed

section \<open>One field of a reachability-lifted record\<close>

text \<open>
  The combined state is a record of reachability-lifted fields under one more
  reachability lift, whose \<^const>\<open>Bot\<close> is the state no analysis can reach. A
  field's lens reads \<^const>\<open>Bot\<close> there, and writing a reachable value into it
  starts from the record whose fields are all \<^const>\<open>Bot\<close>. Writing \<^const>\<open>Bot\<close>
  into the unreachable state leaves it unreachable, so writing back what was
  read changes nothing.
\<close>

definition lift_get :: "('r \<Rightarrow> 'c lifted) \<Rightarrow> 'r lifted \<Rightarrow> 'c lifted" where
  "lift_get f x = (case x of Bot \<Rightarrow> Bot | Lifted r \<Rightarrow> f r)"

definition lift_put :: "('r \<Rightarrow> 'c lifted \<Rightarrow> 'r) \<Rightarrow> 'r::bot lifted \<Rightarrow> 'c lifted \<Rightarrow> 'r lifted" where
  "lift_put u x v =
     (case x of
        Bot \<Rightarrow> (case v of Bot \<Rightarrow> Bot | Lifted _ \<Rightarrow> Lifted (u \<bottom> v))
      | Lifted r \<Rightarrow> Lifted (u r v))"

lemma lift_get_simps [simp]:
  "lift_get f Bot = Bot" "lift_get f (Lifted r) = f r"
  by (simp_all add: lift_get_def)

lemma lift_get_put:
  assumes "\<And>r v. f (u r v) = v" and "f \<bottom> = Bot"
  shows "lift_get f (lift_put u x v) = v"
  using assms by (cases x; cases v) (simp_all add: lift_put_def)

lemma lift_put_get:
  assumes "\<And>r. u r (f r) = r"
  shows "lift_put u x (lift_get f x) = x"
  using assms by (cases x) (simp_all add: lift_put_def)

lemma lift_get_mono:
  fixes f :: "'r::semilattice_sup \<Rightarrow> 'c::semilattice_sup lifted"
  assumes "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "x \<le> y \<Longrightarrow> lift_get f x \<le> lift_get f y"
  using assms by (cases x; cases y) simp_all

lemma lift_get_put_other:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = Bot"
  shows "lift_get f2 (lift_put u1 x v) = lift_get f2 x"
  using assms by (cases x; cases v) (simp_all add: lift_put_def)
end
