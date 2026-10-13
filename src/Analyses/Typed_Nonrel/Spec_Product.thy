theory Spec_Product
  imports "Voblint_Framework.MCP_Spec" "Voblint_Framework.Local_Spec_Product"
begin

section \<open>Two analyses in one solve\<close>

text \<open>
  Goblint's \<^verbatim>\<open>MCP2\<close> (\<^verbatim>\<open>src/analyses/mCP.ml\<close> at \<^verbatim>\<open>0dc12d355\<close>) runs every activated
  analysis on its own part of one state and applies each operation componentwise; an
  entry takes the cartesian product of the components' alternatives. \<open>spec_product\<close> is
  that construction for two specifications over any variables and expressions, on the
  componentwise pair carrier \<^typ>\<open>('a, 'b) analysis_product\<close>. Each component keeps its
  own reachability flag, so a component's intermediate return state, which has no
  meaning of its own, is never collapsed by the other. The product describes the stores
  both components admit. Components do not query each other: the product answers every
  query with top, and each component receives the incoming channel.
\<close>

type_synonym ('a, 'b) pstate = "('a lifted, 'b lifted) analysis_product lifted"

fun pmap :: "('a lifted \<Rightarrow> 'a lifted) \<Rightarrow> ('b lifted \<Rightarrow> 'b lifted) \<Rightarrow> ('a, 'b) pstate \<Rightarrow> ('a, 'b) pstate" where
  "pmap f g Bot = Bot"
| "pmap f g (Lifted (Product a b)) = Lifted (Product (f a) (g b))"

fun pmap2 :: "('a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted) \<Rightarrow> ('b lifted \<Rightarrow> 'b lifted \<Rightarrow> 'b lifted)
    \<Rightarrow> ('a, 'b) pstate \<Rightarrow> ('a, 'b) pstate \<Rightarrow> ('a, 'b) pstate" where
  "pmap2 f g (Lifted (Product a b)) (Lifted (Product a' b')) = Lifted (Product (f a a') (g b b'))"
| "pmap2 f g (Lifted (Product a b)) Bot = Lifted (Product (f a Bot) (g b Bot))"
| "pmap2 f g Bot _ = Bot"

fun pleft_of :: "('a, 'b) pstate \<Rightarrow> 'a lifted" where
  "pleft_of Bot = Bot" | "pleft_of (Lifted (Product a b)) = a"

fun pright_of :: "('a, 'b) pstate \<Rightarrow> 'b lifted" where
  "pright_of Bot = Bot" | "pright_of (Lifted (Product a b)) = b"

definition penter ::
    "(('a lifted \<times> 'a lifted) list) \<Rightarrow> (('b lifted \<times> 'b lifted) list)
       \<Rightarrow> ((('a, 'b) pstate \<times> ('a, 'b) pstate) list)" where
  "penter xs ys =
     [(Lifted (Product x1 x2), Lifted (Product y1 y2)). (x1, y1) \<leftarrow> xs, (x2, y2) \<leftarrow> ys]"

lemma penter_mem:
  "(x1, y1) \<in> set xs \<Longrightarrow> (x2, y2) \<in> set ys
     \<Longrightarrow> (Lifted (Product x1 x2), Lifted (Product y1 y2)) \<in> set (penter xs ys)"
  unfolding penter_def by force

definition spec_product ::
    "('vr, 'e, 'a lifted) glocal_spec \<Rightarrow> ('vr, 'e, 'b lifted) glocal_spec
       \<Rightarrow> ('vr, 'e, ('a, 'b) pstate) glocal_spec" where
  "spec_product c1 c2 =
     \<lparr> ls_query = query_unknown,
       ls_skip = (\<lambda>ch. pmap (ls_skip c1 ch) (ls_skip c2 ch)),
       ls_assign = (\<lambda>ch x e. pmap (ls_assign c1 ch x e) (ls_assign c2 ch x e)),
       ls_special = (\<lambda>ch sc x. pmap (ls_special c1 ch sc x) (ls_special c2 ch sc x)),
       ls_branch = (\<lambda>ch b pol. pmap (ls_branch c1 ch b pol) (ls_branch c2 ch b pol)),
       ls_body = (\<lambda>ch q. pmap (ls_body c1 ch q) (ls_body c2 ch q)),
       ls_return = (\<lambda>ch r q. pmap (ls_return c1 ch r q) (ls_return c2 ch r q)),
       ls_event = (\<lambda>ch ev. pmap (ls_event c1 ch ev) (ls_event c2 ch ev)),
       ls_enter = (\<lambda>ch ci p. case fst p of
           Lifted (Product a1 a2) \<Rightarrow>
             penter (ls_enter c1 ch ci (a1, pleft_of (snd p))) (ls_enter c2 ch ci (a2, pright_of (snd p)))
         | Bot \<Rightarrow> [p]),
       ls_combine_env = (\<lambda>ch ch' ci.
           pmap2 (ls_combine_env c1 ch ch' ci) (ls_combine_env c2 ch ch' ci)),
       ls_combine_assign = (\<lambda>ch' ci.
           pmap2 (ls_combine_assign c1 ch' ci) (ls_combine_assign c2 ch' ci)) \<rparr>"

definition pgamma :: "('a lifted \<Rightarrow> 'x set) \<Rightarrow> ('b lifted \<Rightarrow> 'x set) \<Rightarrow> ('a, 'b) pstate \<Rightarrow> 'x set" where
  "pgamma g1 g2 d = (case d of Bot \<Rightarrow> {} | Lifted (Product a b) \<Rightarrow> g1 a \<inter> g2 b)"

lemma pgamma_simps [simp]:
  "pgamma g1 g2 Bot = {}"
  "pgamma g1 g2 (Lifted (Product a b)) = g1 a \<inter> g2 b"
  by (simp_all add: pgamma_def)

context mcp_sem
begin

theorem spec_product_sound:
  assumes s1: "gsound_local_spec gm1 c1" and s2: "gsound_local_spec gm2 c2"
  shows "gsound_local_spec (pgamma gm1 gm2) (spec_product c1 c2)"
proof (rule sound_local_specI)
  note m1 = sound_local_spec_monoD[OF s1] and m2 = sound_local_spec_monoD[OF s2]
  have L: "\<exists>a b. x = Lifted (Product a b) \<and> s \<in> gm1 a \<and> s \<in> gm2 b"
    if "s \<in> pgamma gm1 gm2 x" for s x
    using that by (auto simp: pgamma_def split: lifted.splits analysis_product.splits)
  show "\<And>x y. x \<le> y \<Longrightarrow> pgamma gm1 gm2 x \<subseteq> pgamma gm1 gm2 y"
  proof -
    fix x y :: "('a, 'b) pstate" assume "x \<le> y"
    then show "pgamma gm1 gm2 x \<subseteq> pgamma gm1 gm2 y"
      using m1 m2 by (fastforce simp: pgamma_def split: lifted.splits analysis_product.splits)
  qed
  show "gsound_query (pgamma gm1 gm2) (ls_query (spec_product c1 c2))"
    by (simp add: spec_product_def sound_query_unknown)
  show "gsound_skip (pgamma gm1 gm2) (ls_skip (spec_product c1 c2))"
    using sound_local_spec_skipD[OF s1] sound_local_spec_skipD[OF s2]
    by (fastforce simp: gsound_skip_def spec_product_def dest!: L)
  show "gsound_assign (pgamma gm1 gm2) (ls_assign (spec_product c1 c2))"
    using sound_local_spec_assignD[OF s1] sound_local_spec_assignD[OF s2]
    by (fastforce simp: gsound_assign_def spec_product_def dest!: L)
  show "gsound_special (pgamma gm1 gm2) (ls_special (spec_product c1 c2))"
    using sound_local_spec_specialD[OF s1] sound_local_spec_specialD[OF s2]
    by (fastforce simp: gsound_special_def spec_product_def dest!: L)
  show "gsound_branch (pgamma gm1 gm2) (ls_branch (spec_product c1 c2))"
    using sound_local_spec_branchD[OF s1] sound_local_spec_branchD[OF s2]
    by (fastforce simp: gsound_branch_def spec_product_def dest!: L)
  show "gsound_body (pgamma gm1 gm2) (ls_body (spec_product c1 c2))"
    using sound_local_spec_bodyD[OF s1] sound_local_spec_bodyD[OF s2]
    by (fastforce simp: gsound_body_def spec_product_def dest!: L)
  show "gsound_return (pgamma gm1 gm2) (ls_return (spec_product c1 c2))"
    using sound_local_spec_returnD[OF s1] sound_local_spec_returnD[OF s2]
    by (fastforce simp: gsound_return_def spec_product_def dest!: L)
  show "gsound_event (pgamma gm1 gm2) (ls_event (spec_product c1 c2))"
    using sound_local_spec_eventD[OF s1] sound_local_spec_eventD[OF s2]
    by (fastforce simp: gsound_event_def spec_product_def dest!: L)
  show "gsound_enter (pgamma gm1 gm2) (ls_enter (spec_product c1 c2))"
    unfolding gsound_enter_def
  proof (intro allI impI)
    fix ch s ci and p :: "('a, 'b) pstate \<times> ('a, 'b) pstate"
    assume sp: "s \<in> pgamma gm1 gm2 (fst p)" and h: "geval_query.channel_holds ev ch s"
    obtain a1 a2 where fp: "fst p = Lifted (Product a1 a2)" and s1a: "s \<in> gm1 a1" and s2a: "s \<in> gm2 a2"
      using L[OF sp] by blast
    obtain q1 where q1: "q1 \<in> set (ls_enter c1 ch ci (a1, pleft_of (snd p)))"
      and q1s: "s \<in> gm1 (fst q1)"
      and q1e: "gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gm1 (snd q1)"
      using sound_local_spec_enterD[OF s1, unfolded gsound_enter_def, rule_format,
          of s "(a1, pleft_of (snd p))" ch ci] s1a h by auto
    obtain q2 where q2: "q2 \<in> set (ls_enter c2 ch ci (a2, pright_of (snd p)))"
      and q2s: "s \<in> gm2 (fst q2)"
      and q2e: "gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gm2 (snd q2)"
      using sound_local_spec_enterD[OF s2, unfolded gsound_enter_def, rule_format,
          of s "(a2, pright_of (snd p))" ch ci] s2a h by auto
    show "\<exists>q \<in> set (ls_enter (spec_product c1 c2) ch ci p). s \<in> pgamma gm1 gm2 (fst q)
            \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> pgamma gm1 gm2 (snd q)"
    proof (rule bexI[of _ "(Lifted (Product (fst q1) (fst q2)), Lifted (Product (snd q1) (snd q2)))"])
      show "(Lifted (Product (fst q1) (fst q2)), Lifted (Product (snd q1) (snd q2)))
              \<in> set (ls_enter (spec_product c1 c2) ch ci p)"
        using penter_mem[of "fst q1" "snd q1" _ "fst q2" "snd q2"] q1 q2
        by (simp add: spec_product_def fp)
    qed (use q1s q2s q1e q2e in simp)
  qed
  show "gsound_combine (pgamma gm1 gm2) (ls_combine_env (spec_product c1 c2))
          (ls_combine_assign (spec_product c1 c2))"
    unfolding gsound_combine_def
  proof (intro allI impI)
    fix ch ch' s t ci x de
    assume sx: "s \<in> pgamma gm1 gm2 x" and h: "geval_query.channel_holds ev ch s"
      and tde: "t \<in> pgamma gm1 gm2 de" and h': "geval_query.channel_holds ev ch' t"
    obtain a1 a2 where x: "x = Lifted (Product a1 a2)" and "s \<in> gm1 a1" "s \<in> gm2 a2"
      using L[OF sx] by blast
    moreover obtain d1 d2 where de: "de = Lifted (Product d1 d2)" and "t \<in> gm1 d1" "t \<in> gm2 d2"
      using L[OF tde] by blast
    ultimately show "gcombine_collect (ci_dst ci) s t \<in> pgamma gm1 gm2
        (ls_combine_assign (spec_product c1 c2) ch' ci (ls_combine_env (spec_product c1 c2) ch ch' ci x de) de)"
      using sound_local_spec_combineD[OF s1, unfolded gsound_combine_def, rule_format, of s a1 ch t d1 ch' ci]
        sound_local_spec_combineD[OF s2, unfolded gsound_combine_def, rule_format, of s a2 ch t d2 ch' ci]
        h h' by (simp add: spec_product_def)
  qed
qed

end

end
