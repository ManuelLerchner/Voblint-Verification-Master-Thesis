theory MCP_Spec
  imports "Voblint_Framework.DG_Spec_Sound"
begin

section \<open>Many cooperating analyses over one state\<close>

text \<open>
  Goblint's \<open>MCP\<close> runs every activated analysis on its own part of one
  combined state (\<open>mCP.ml\<close> at \<open>0dc12d355\<close>). Voblint keeps the combined state
  as one type \<open>'s\<close>, a record with a field per registered analysis, and a
  component as operations on the whole record that touch only its own field.
  The activation list chooses which components run; the fields of inactive
  analyses are never read.

  A component's operations are those of a local specification, with two
  changes that let components be chained over one record. Its entry transfer
  takes the pair of records built so far and sets its own field in both
  halves. Its return is one function, the composite of the two combine stages.
\<close>

record 's mcp_component =
  mc_gamma :: "'s \<Rightarrow> store set"
  mc_qry :: "'s \<Rightarrow> answers"
  mc_qs :: "edge_action \<Rightarrow> 's \<Rightarrow> query list"
  mc_step :: "answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's"
  mc_en :: "call_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  mc_comb :: "call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"

text \<open>
  A component is sound when each operation covers the concrete behaviour for
  its own concretization, whatever the other fields of the record hold. The
  step is proved against every answer function that holds at the start store,
  as in \<^locale>\<open>sound_local_dg_spec\<close>.
\<close>

definition mcp_component_sound :: "(vname \<Rightarrow> bool) \<Rightarrow> 's::order mcp_component \<Rightarrow> bool" where
  "mcp_component_sound \<G> c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> mc_gamma c x \<subseteq> mc_gamma c y)
     \<and> (\<forall>A a x. edge_collect a (mc_gamma c x \<inter> Collect (eval_query.oracle_holds A))
                  \<subseteq> mc_gamma c (mc_step c A a x))
     \<and> (\<forall>s ci p. s \<in> mc_gamma c (fst p) \<longrightarrow>
          (\<exists>q \<in> set (mc_en c ci p). s \<in> mc_gamma c (fst q)
             \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> mc_gamma c (snd q)))
     \<and> (\<forall>s t ci x de. s \<in> mc_gamma c x \<longrightarrow> t \<in> mc_gamma c de \<longrightarrow>
          combine_collect \<G> (ci_dst ci) s t \<in> mc_gamma c (mc_comb c ci x de))
     \<and> (\<forall>s x q. s \<in> mc_gamma c x \<longrightarrow> eval_holds q (mc_qry c x q) s)"

text \<open>
  Two components are independent when neither operation of one changes what
  the other's concretization says. For components that each own one field of
  a record this is the lens law that updating one field leaves the others.
\<close>

definition mcp_frame :: "'s mcp_component \<Rightarrow> 's mcp_component \<Rightarrow> bool" where
  "mcp_frame c d \<longleftrightarrow>
     (\<forall>A a x. mc_gamma d (mc_step c A a x) = mc_gamma d x)
     \<and> (\<forall>ci p q. q \<in> set (mc_en c ci p) \<longrightarrow>
          mc_gamma d (fst q) = mc_gamma d (fst p) \<and> mc_gamma d (snd q) = mc_gamma d (snd p))
     \<and> (\<forall>ci x de. mc_gamma d (mc_comb c ci x de) = mc_gamma d x)"

fun mcp_independent :: "'s mcp_component list \<Rightarrow> bool" where
  "mcp_independent [] \<longleftrightarrow> True"
| "mcp_independent (c # cs) \<longleftrightarrow>
     (\<forall>d \<in> set cs. mcp_frame c d \<and> mcp_frame d c) \<and> mcp_independent cs"

section \<open>The combined specification\<close>

text \<open>
  The combined operations run the active components in turn. Each reads only
  its own field, which no other component writes, so the order does not
  matter; the fold is merely one way to write ``all of them''. The answers are
  fixed once per edge, from the predecessor state, and every component gets
  the same answers, as every Goblint component gets the same \<open>man.ask\<close>.
\<close>

definition mcp_step :: "'s mcp_component list \<Rightarrow> answers \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_step cs A a x = fold (\<lambda>c y. mc_step c A a y) cs x"

definition mcp_en ::
  "'s mcp_component list \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's enter_result list" where
  "mcp_en cs ci x = fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) cs [(x, x)]"

definition mcp_comb :: "'s mcp_component list \<Rightarrow> call_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_comb cs ci x de = fold (\<lambda>c y. mc_comb c ci y de) cs x"

definition mcp_qry :: "'s mcp_component list \<Rightarrow> 's \<Rightarrow> answers" where
  "mcp_qry cs x q = fold (\<lambda>c r. r \<sqinter> mc_qry c x q) cs \<top>"

definition mcp_qs :: "'s mcp_component list \<Rightarrow> edge_action \<Rightarrow> 's \<Rightarrow> query list" where
  "mcp_qs cs a x = concat (map (\<lambda>c. mc_qs c a x) cs)"

definition mcp_gamma :: "'s mcp_component list \<Rightarrow> 's \<Rightarrow> store set" where
  "mcp_gamma cs x = (\<Inter>c \<in> set cs. mc_gamma c x)"

definition mcp_spec :: "'s mcp_component list \<Rightarrow> ('x,'k,'v,'s::bot,'G) dg_spec" where
  "mcp_spec cs = local_dg_spec (mcp_qs cs) (mcp_qry cs)
     (\<lambda>A. mcp_step cs A EA_Nop)
     (\<lambda>A x e. mcp_step cs A (EA_Assign x e))
     (\<lambda>A sc x. mcp_step cs A (EA_Special sc x))
     (\<lambda>A b pol. mcp_step cs A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>A p. mcp_step cs A (EA_Body p))
     (\<lambda>A e p. mcp_step cs A (EA_Ret e p))
     (mcp_en cs)
     (\<lambda>A ev. mcp_step cs A (event_action ev))
     (\<lambda>ci dc de. dc)
     (mcp_comb cs)"

lemma local_spec_step_mcp:
  "local_spec_step (mcp_step cs A EA_Nop) (\<lambda>x e. mcp_step cs A (EA_Assign x e))
     (\<lambda>sc x. mcp_step cs A (EA_Special sc x))
     (\<lambda>b pol. mcp_step cs A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>p. mcp_step cs A (EA_Body p)) (\<lambda>e p. mcp_step cs A (EA_Ret e p))
     (\<lambda>ev. mcp_step cs A (event_action ev)) a
   = mcp_step cs A a"
  by (cases a) simp_all

section \<open>Soundness of the combination\<close>

lemma mcp_gamma_Cons [simp]: "mcp_gamma (c # cs) x = mc_gamma c x \<inter> mcp_gamma cs x"
  by (simp add: mcp_gamma_def)

lemma mcp_gamma_Nil [simp]: "mcp_gamma [] x = UNIV"
  by (simp add: mcp_gamma_def)

text \<open>Components a fold runs leave the concretization of an independent one as
  it was.\<close>

lemma mc_gamma_fold_step:
  "(\<forall>c \<in> set cs. mcp_frame c d)
   \<Longrightarrow> mc_gamma d (fold (\<lambda>c y. mc_step c A a y) cs x) = mc_gamma d x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma mc_gamma_fold_comb:
  "(\<forall>c \<in> set cs. mcp_frame c d)
   \<Longrightarrow> mc_gamma d (fold (\<lambda>c y. mc_comb c ci y de) cs x) = mc_gamma d x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma mcp_gamma_frame:
  "(\<forall>d \<in> set cs. mcp_frame c d) \<Longrightarrow> mcp_gamma cs (mc_step c A a x) = mcp_gamma cs x"
  "(\<forall>d \<in> set cs. mcp_frame c d) \<Longrightarrow> mcp_gamma cs (mc_comb c ci x de) = mcp_gamma cs x"
  by (auto simp: mcp_gamma_def mcp_frame_def)

lemma mcp_step_sound:
  assumes "\<forall>c \<in> set cs. mcp_component_sound \<G> c" and "mcp_independent cs"
  shows "edge_collect a (mcp_gamma cs x \<inter> Collect (eval_query.oracle_holds A))
           \<subseteq> mcp_gamma cs (mcp_step cs A a x)"
  using assms
proof (induction cs arbitrary: x)
  case Nil
  then show ?case by (simp add: mcp_step_def)
next
  case (Cons c cs)
  let ?O = "Collect (eval_query.oracle_holds A)"
  let ?x1 = "mc_step c A a x"
  have frames: "\<forall>d \<in> set cs. mcp_frame c d \<and> mcp_frame d c" "mcp_independent cs"
    using Cons.prems(2) by simp_all
  have own: "edge_collect a (mc_gamma c x \<inter> ?O) \<subseteq> mc_gamma c ?x1"
    using Cons.prems(1) by (simp add: mcp_component_sound_def)
  have own_kept: "mc_gamma c (mcp_step cs A a ?x1) = mc_gamma c ?x1"
    unfolding mcp_step_def by (rule mc_gamma_fold_step) (use frames in blast)
  have rest: "edge_collect a (mcp_gamma cs ?x1 \<inter> ?O) \<subseteq> mcp_gamma cs (mcp_step cs A a ?x1)"
    by (rule Cons.IH) (use Cons.prems(1) frames in simp_all)
  have rest_eq: "mcp_gamma cs ?x1 = mcp_gamma cs x"
    by (rule mcp_gamma_frame(1)) (use frames in blast)
  have "edge_collect a (mcp_gamma (c # cs) x \<inter> ?O)
          \<subseteq> edge_collect a (mc_gamma c x \<inter> ?O) \<inter> edge_collect a (mcp_gamma cs ?x1 \<inter> ?O)"
    by (intro Int_greatest edge_collect_mono) (auto simp: rest_eq)
  also have "\<dots> \<subseteq> mcp_gamma (c # cs) (mcp_step (c # cs) A a x)"
    using own own_kept rest by (auto simp: mcp_step_def)
  finally show ?case .
qed

lemma mcp_comb_sound:
  assumes "\<forall>c \<in> set cs. mcp_component_sound \<G> c" and "mcp_independent cs"
    and "s \<in> mcp_gamma cs x" and "t \<in> mcp_gamma cs de"
  shows "combine_collect \<G> (ci_dst ci) s t \<in> mcp_gamma cs (mcp_comb cs ci x de)"
  using assms
proof (induction cs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  let ?x1 = "mc_comb c ci x de"
  have frames: "\<forall>d \<in> set cs. mcp_frame c d \<and> mcp_frame d c" "mcp_independent cs"
    using Cons.prems(2) by simp_all
  have own: "combine_collect \<G> (ci_dst ci) s t \<in> mc_gamma c ?x1"
    using Cons.prems(1,3,4) by (simp add: mcp_component_sound_def)
  have own_kept: "mc_gamma c (mcp_comb cs ci ?x1 de) = mc_gamma c ?x1"
    unfolding mcp_comb_def by (rule mc_gamma_fold_comb) (use frames in blast)
  have rest_eq: "mcp_gamma cs ?x1 = mcp_gamma cs x"
    by (rule mcp_gamma_frame(2)) (use frames in blast)
  have rest: "combine_collect \<G> (ci_dst ci) s t \<in> mcp_gamma cs (mcp_comb cs ci ?x1 de)"
    by (rule Cons.IH) (use Cons.prems frames rest_eq in simp_all)
  show ?case
    using own own_kept rest by (simp add: mcp_comb_def)
qed

text \<open>
  Entry threads a list of pairs through the components. The invariant carries
  the components already run (\<open>ds\<close>), whose fields are set in both halves, and
  those still to run (\<open>cs\<close>), whose fields are still the caller's.
\<close>

lemma mcp_en_fold_sound:
  assumes "\<forall>c \<in> set cs. mcp_component_sound \<G> c" and "mcp_independent cs"
    and "\<forall>c \<in> set cs. \<forall>d \<in> set ds. mcp_frame c d"
    and "\<exists>p \<in> set ps. s \<in> mcp_gamma cs (fst p) \<and> s \<in> mcp_gamma ds (fst p)
                       \<and> E \<in> mcp_gamma ds (snd p)"
    and E: "E = call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s"
  shows "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) cs ps).
           s \<in> mcp_gamma cs (fst p) \<and> s \<in> mcp_gamma ds (fst p)
           \<and> E \<in> mcp_gamma cs (snd p) \<and> E \<in> mcp_gamma ds (snd p)"
  using assms(1-4)
proof (induction cs arbitrary: ps ds)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  have frames: "\<forall>d \<in> set cs. mcp_frame c d \<and> mcp_frame d c" "mcp_independent cs"
    using Cons.prems(2) by simp_all
  obtain p where p: "p \<in> set ps" "s \<in> mc_gamma c (fst p)" "s \<in> mcp_gamma cs (fst p)"
      "s \<in> mcp_gamma ds (fst p)" "E \<in> mcp_gamma ds (snd p)"
    using Cons.prems(4) by auto
  have "mcp_component_sound \<G> c" using Cons.prems(1) by simp
  then obtain q where q: "q \<in> set (mc_en c ci p)" "s \<in> mc_gamma c (fst q)" "E \<in> mc_gamma c (snd q)"
    using p(2) unfolding E mcp_component_sound_def by meson
  have keep: "mc_gamma d (fst q) = mc_gamma d (fst p) \<and> mc_gamma d (snd q) = mc_gamma d (snd p)"
    if "d \<in> set cs \<union> set ds" for d
  proof -
    have "mcp_frame c d" using that frames(1) Cons.prems(3) by auto
    then show ?thesis using q(1) unfolding mcp_frame_def by blast
  qed
  have q_in: "q \<in> set (concat (map (mc_en c ci) ps))"
    using p(1) q(1) by auto
  have "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (mc_en c ci) ps)) cs (concat (map (mc_en c ci) ps))).
          s \<in> mcp_gamma cs (fst p) \<and> s \<in> mcp_gamma (c # ds) (fst p)
          \<and> E \<in> mcp_gamma cs (snd p) \<and> E \<in> mcp_gamma (c # ds) (snd p)"
  proof (rule Cons.IH)
    show "\<forall>c \<in> set cs. mcp_component_sound \<G> c" using Cons.prems(1) by simp
    show "mcp_independent cs" by (fact frames(2))
    show "\<forall>c' \<in> set cs. \<forall>d \<in> set (c # ds). mcp_frame c' d"
      using frames(1) Cons.prems(3) by auto
    show "\<exists>p \<in> set (concat (map (mc_en c ci) ps)).
            s \<in> mcp_gamma cs (fst p) \<and> s \<in> mcp_gamma (c # ds) (fst p)
            \<and> E \<in> mcp_gamma (c # ds) (snd p)"
    proof (rule bexI[OF _ q_in])
      show "s \<in> mcp_gamma cs (fst q) \<and> s \<in> mcp_gamma (c # ds) (fst q)
              \<and> E \<in> mcp_gamma (c # ds) (snd q)"
        using p(3-5) q(2,3) keep by (auto simp: mcp_gamma_def)
    qed
  qed
  then show ?case by (auto simp: mcp_gamma_def)
qed

lemma mcp_qry_fold_sound:
  "s \<in> mcp_gamma cs x \<Longrightarrow> \<forall>c \<in> set cs. mcp_component_sound \<G> c \<Longrightarrow> eval_holds q r s
   \<Longrightarrow> eval_holds q (fold (\<lambda>c r. r \<sqinter> mc_qry c x q) cs r) s"
proof (induction cs arbitrary: r)
  case (Cons c cs)
  have "eval_holds q (mc_qry c x q) s"
    using Cons.prems by (simp add: mcp_component_sound_def)
  with Cons.prems(3) have "eval_holds q (r \<sqinter> mc_qry c x q) s"
    by (rule eval_query.inf_sound)
  then show ?case
    using Cons.IH[of "r \<sqinter> mc_qry c x q"] Cons.prems(1,2) by (simp del: inf_ivl_def)
qed simp

theorem mcp_local_spec:
  assumes sound: "\<forall>c \<in> set cs. mcp_component_sound \<G> c" and indep: "mcp_independent cs"
  shows "sound_local_dg_spec (mcp_qry cs)
     (\<lambda>A. mcp_step cs A EA_Nop)
     (\<lambda>A x e. mcp_step cs A (EA_Assign x e))
     (\<lambda>A sc x. mcp_step cs A (EA_Special sc x))
     (\<lambda>A b pol. mcp_step cs A (if pol then EA_Assume b else EA_AssumeNot b))
     (\<lambda>A p. mcp_step cs A (EA_Body p))
     (\<lambda>A e p. mcp_step cs A (EA_Ret e p))
     (mcp_en cs)
     (\<lambda>A ev. mcp_step cs A (event_action ev))
     (\<lambda>ci dc de. dc)
     (mcp_comb cs)
     (mcp_gamma cs) \<G>"
proof (unfold_locales, goal_cases)
  case (1 d d')
  then show ?case
    using sound unfolding mcp_gamma_def mcp_component_sound_def by fastforce
next
  case (2 a d A)
  show ?case
    unfolding local_spec_step_mcp by (rule mcp_step_sound[OF sound indep])
next
  case (3 s d ci)
  have "\<exists>p \<in> set (mcp_en cs ci d).
          s \<in> mcp_gamma cs (fst p) \<and> s \<in> mcp_gamma [] (fst p)
          \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
              \<in> mcp_gamma cs (snd p)
          \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
              \<in> mcp_gamma [] (snd p)"
    unfolding mcp_en_def
    by (rule mcp_en_fold_sound[OF sound indep]) (use 3 in simp_all)
  then obtain p where "p \<in> set (mcp_en cs ci d)" "s \<in> mcp_gamma cs (fst p)"
      "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> mcp_gamma cs (snd p)"
    by blast
  then show ?case
    by (intro entry_pairs_coverI[of "fst p" "snd p"]) simp_all
next
  case (4 s dc t de ci)
  then show ?case by (rule mcp_comb_sound[OF sound indep])
next
  case (5 s d q)
  then show ?case
    unfolding mcp_qry_def by (rule mcp_qry_fold_sound[OF _ sound]) simp
qed

theorem mcp_contract:
  assumes "\<forall>c \<in> set cs. mcp_component_sound \<G> c" and "mcp_independent cs"
  shows "analysis_contract (mcp_spec cs) (\<lambda>d g. mcp_gamma cs d) \<G>"
  unfolding mcp_spec_def
  by (rule sound_local_dg_spec.local_spec_contract[OF mcp_local_spec[OF assms]])

section \<open>A local specification as a component\<close>

text \<open>
  A registered analysis is a local specification over its own carrier \<open>'c\<close>.
  A lens \<open>get\<close>/\<open>put\<close> places that carrier in one field of the combined record,
  and \<open>lens_component\<close> runs the specification on that field, as Goblint's
  \<open>inner_man\<close> hands a component its own part of the \<open>MCP\<close> state.
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
   \<Rightarrow> ('c \<Rightarrow> store set) \<Rightarrow> 's mcp_component"
where
  "lens_component get put qs qry sk asn sp br bd rt en ev ce ca gammaD = \<lparr>
     mc_gamma = (\<lambda>x. gammaD (get x)),
     mc_qry = (\<lambda>x. qry (get x)),
     mc_qs = (\<lambda>a x. qs a (get x)),
     mc_step = (\<lambda>A a x. put x (local_spec_step (sk A) (asn A) (sp A) (br A) (bd A) (rt A) (ev A)
                                 a (get x))),
     mc_en = (\<lambda>ci p. map (\<lambda>(c, e). (put (fst p) c, put (snd p) e)) (en ci (get (fst p)))),
     mc_comb = (\<lambda>ci x de. put x (ca ci (ce ci (get x) (get de)) (get de))) \<rparr>"

theorem lens_component_sound:
  assumes spec: "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "mcp_component_sound \<G>
           (lens_component get put qs qry sk asn sp br bd rt en ev ce ca gammaD)"
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
  shows "mcp_frame (lens_component get1 put1 qs1 qry1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1 g1)
                   (lens_component get2 put2 qs2 qry2 sk2 asn2 sp2 br2 bd2 rt2 en2 ev2 ce2 ca2 g2)"
  unfolding mcp_frame_def lens_component_def by (auto simp: assms)

end
