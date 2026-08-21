theory Call_String_Solver_Projection
  imports Call_String_Context Context_Refinement
begin

section \<open>Generic k1 <= k2 CallString projection\<close>

text \<open>
  Everything here is generic in the bound \<open>k1\<close>, the fine variable list \<open>vars2_lst\<close>, the
  fine solution \<open>sigma2\<close>, and the coarse equation system \<open>T1\<close>/its start unknown \<open>root1\<close>.
  Nothing below names a concrete program, a concrete \<open>k2\<close>, or a concrete pair of
  equation systems: the same construction applies to any \<open>k1\<close>-bounded CallString
  equation system seeded from any finite fragment of any finer solution. The carrier
  \<open>'d\<close> stays an arbitrary \<^class>\<open>bounded_semilattice_sup_bot\<close>, so no domain, no solver
  instance, and no CFG appears here either --- only the call-string key type of
  \<^theory>\<open>Voblint_Core.Call_String_Context\<close> and the generic seeding infrastructure of
  \<^theory>\<open>Voblint_Core.Context_Refinement\<close>.
\<close>

subsection \<open>The projection\<close>

text \<open>The finite join, over every fine variable at the same procedure point whose context
  truncates to \<open>c1\<close>, of the fine solution there. A singleton match is plain passthrough; a
  genuine context merge picks up every matching branch. No case distinction between the
  two is needed or possible from outside: the fold finds whichever fine variables actually
  match.\<close>
definition proj_local ::
  "nat \<Rightarrow> (pp \<times> call_string) list
   \<Rightarrow> (pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot)
   \<Rightarrow> pp \<times> call_string \<Rightarrow> 'd" where
  "proj_local k1 vars2_lst sigma2 vc1 =
     foldr (\<lambda>vc2 acc. if fst vc2 = fst vc1 \<and> take k1 (snd vc2) = snd vc1
                       then sigma2 (Inl vc2) \<squnion> acc else acc)
       vars2_lst bot"

text \<open>The same, for a coarse global/seed key: \<open>Global\<close> passes through (there is exactly
  one), and \<open>Seed p c1\<close> joins the fine seed values at every fine activation of \<open>p\<close> (every
  covered \<open>(FunctionEntry p, c2)\<close>) whose context truncates to \<open>c1\<close>. Reusing \<open>vars2_lst\<close>
  here, rather than a separately enumerated seed-key list, keeps this in agreement with
  \<^const>\<open>proj_local\<close>: a seed is relevant exactly when its own entry node is a covered
  fine variable -- true of any \<open>routed_cmb_g\<close>-based equation system, since a seed is only
  ever published as \<open>Seed (FunctionEntry (result_proc ex)) ctx'\<close>.\<close>
definition proj_global ::
  "nat \<Rightarrow> (pp \<times> call_string) list
   \<Rightarrow> (pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot)
   \<Rightarrow> call_string_gk \<Rightarrow> 'd" where
  "proj_global k1 vars2_lst sigma2 gk1 =
     (case gk1 of
        Global \<Rightarrow> sigma2 (Inr Global)
      | Seed p c1 \<Rightarrow>
          foldr (\<lambda>vc2 acc. if fst vc2 = p \<and> take k1 (snd vc2) = c1
                            then sigma2 (Inr (Seed p (snd vc2))) \<squnion> acc else acc)
            vars2_lst bot)"

definition proj_P ::
  "nat \<Rightarrow> (pp \<times> call_string) list
   \<Rightarrow> (pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot)
   \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> 'd" where
  "proj_P k1 vars2_lst sigma2 x =
     (case x of Inl vc1 \<Rightarrow> proj_local k1 vars2_lst sigma2 vc1
              | Inr gk1 \<Rightarrow> proj_global k1 vars2_lst sigma2 gk1)"

text \<open>The coarse global/seed keys worth strengthening: \<open>Global\<close> together with the \<open>k1\<close>
  projection of every fine seed key headed by a covered fine entry node. Derived from
  \<open>vars2_lst\<close> itself, not enumerated separately, so it is exactly the image of
  \<^const>\<open>proj_global\<close>'s own domain restricted to entry nodes -- never a hand-picked guess
  at which keys happen to matter.\<close>
definition proj_global_keys ::
  "nat \<Rightarrow> (pp \<times> call_string) list \<Rightarrow> call_string_gk list" where
  "proj_global_keys k1 vars2_lst =
     Global # remdups (map (\<lambda>vc2. Seed (fst vc2) (take k1 (snd vc2)))
                          (filter (\<lambda>vc2. is_FunctionEntry (fst vc2)) vars2_lst))"

subsection \<open>What the projection actually captures\<close>

text \<open>Every covered fine local unknown is dominated by the coarse projection at its
  truncated context: this is the precise sense in which \<^const>\<open>proj_local\<close> quotients
  the fine solution rather than discarding it.\<close>
lemma proj_local_ge:
  fixes sigma2 :: "pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot"
  assumes "(p, c2) \<in> set vars2_lst"
  shows "sigma2 (Inl (p, c2)) \<le> proj_local k1 vars2_lst sigma2 (p, take k1 c2)"
  unfolding proj_local_def fst_conv snd_conv using assms
proof (induction vars2_lst)
  case Nil
  then show ?case by simp
next
  case (Cons vc2 vars2_lst)
  show ?case
  proof (cases "vc2 = (p, c2)")
    case True
    then show ?thesis by simp
  next
    case False
    with Cons.prems have mem: "(p, c2) \<in> set vars2_lst" by simp
    have le: "foldr (\<lambda>vc2' acc. if fst vc2' = p \<and> take k1 (snd vc2') = take k1 c2
                                 then sigma2 (Inl vc2') \<squnion> acc else acc) vars2_lst bot
                \<le> foldr (\<lambda>vc2' acc. if fst vc2' = p \<and> take k1 (snd vc2') = take k1 c2
                                     then sigma2 (Inl vc2') \<squnion> acc else acc)
                    (vc2 # vars2_lst) bot"
      by simp
    from order_trans[OF Cons.IH[OF mem] le] show ?thesis .
  qed
qed

text \<open>The same, for a fine seed value at a covered fine entry activation.\<close>
lemma proj_global_ge:
  fixes sigma2 :: "pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot"
  assumes "(p, c2) \<in> set vars2_lst"
  shows "sigma2 (Inr (Seed p c2)) \<le> proj_global k1 vars2_lst sigma2 (Seed p (take k1 c2))"
  unfolding proj_global_def call_string_gk.case using assms
proof (induction vars2_lst)
  case Nil
  then show ?case by simp
next
  case (Cons vc2 vars2_lst)
  show ?case
  proof (cases "vc2 = (p, c2)")
    case True
    then show ?thesis by simp
  next
    case False
    with Cons.prems have mem: "(p, c2) \<in> set vars2_lst" by simp
    have le: "foldr (\<lambda>vc2' acc. if fst vc2' = p \<and> take k1 (snd vc2') = take k1 c2
                                 then sigma2 (Inr (Seed p (snd vc2'))) \<squnion> acc else acc) vars2_lst bot
                \<le> foldr (\<lambda>vc2' acc. if fst vc2' = p \<and> take k1 (snd vc2') = take k1 c2
                                     then sigma2 (Inr (Seed p (snd vc2'))) \<squnion> acc else acc)
                    (vc2 # vars2_lst) bot"
      by simp
    from order_trans[OF Cons.IH[OF mem] le] show ?thesis .
  qed
qed

text \<open>At equal precision, projection never discards information: every covered fine value
  is dominated by the (trivially re-truncated) projection at its own context. This is
  @{thm [source] proj_local_ge}/@{thm [source] proj_global_ge} specialised at \<open>k1 = k2\<close>;
  it does not by
  itself say the projection introduces no merging at all, since that additionally needs
  every fine context already bounded by \<open>k1\<close> (true of any actual \<open>k1\<close>-CallString solve,
  but not assumed here).\<close>
lemma proj_local_ge_refl:
  fixes sigma2 :: "pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot"
  assumes "(p, c2) \<in> set vars2_lst"  shows "sigma2 (Inl (p, c2)) \<le> proj_local (length c2) vars2_lst sigma2 (p, c2)"
proof -
  have "sigma2 (Inl (p, c2)) \<le> proj_local (length c2) vars2_lst sigma2 (p, take (length c2) c2)"
    by (rule proj_local_ge[OF assms])
  then show ?thesis by simp
qed

subsection \<open>Agreement with routed contexts\<close>

text \<open>The central fact that lets \<^const>\<open>proj_global\<close>'s key shape agree with what a
  \<open>routed_cmb_g\<close>-based equation actually computes: if the coarse caller context is already
  the \<open>k1\<close>-truncation of the fine caller context, routing a call at \<open>k1\<close> from the coarse
  context agrees with truncating the \<open>k2\<close>-routed callee context down to \<open>k1\<close>. This is
  \<^const>\<open>Call_String_Context.cs_route\<close>'s own truncation behaviour
  (\<^theory>\<open>Voblint_Core.Call_String_Context\<close> stays solver-agnostic and does not state it in
  this two-context form itself); the closure argument in \<open>Call_String_Solver_Refinement_Seeded\<close>
  does not need it, since it never re-evaluates a fine equation's own routing -- it is
  recorded here as the fact that would justify a \<open>comb\<close>-hook simulation argument, should
  one ever be wanted.\<close>
lemma cs_route_project_ctx:
  assumes "k1 \<le> k2"
  shows "cs_route k1 u (take k1 ctx2) d ca = take k1 (cs_route k2 u ctx2 d ca)"  using assms
  unfolding cs_route_def by (cases k1) simp_all

subsection \<open>The packaged refinement theorem\<close>

text \<open>Seeding a \<open>k1\<close>-bounded equation system \<open>T1\<close> with the finite fine-to-coarse
  projection  and running the ordinary, unmodified solver already gives a post-solution of
  \<open>T1\<close> itself, together with domination of the projected information on both the local
  and the global/seed side -- via @{thm [source] post_solution_of_seeded} alone. No hook-specific
  reasoning, and no relation between \<open>T1\<close> and whatever equation system \<open>sigma2\<close> actually
  solves, is needed: \<open>sigma2\<close> and \<open>vars2_lst\<close> are consumed purely as data. \<open>k1 \<le> k2\<close> is
  not a hypothesis of this theorem -- it only matters for choosing \<open>vars2_lst\<close>/\<open>sigma2\<close>
  meaningfully (a genuinely \<open>k2\<close>-bounded fine solution) and for @{thm [source] cs_route_project_ctx}
  above, not for this closure step.\<close>
definition project_seeded_eqs ::
  "nat \<Rightarrow> (pp \<times> call_string) list
   \<Rightarrow> (pp \<times> call_string + call_string_gk \<Rightarrow> 'd::bounded_semilattice_sup_bot)
   \<Rightarrow> (pp \<times> call_string, call_string_gk, 'd) eqsT
   \<Rightarrow> pp \<times> call_string
   \<Rightarrow> (pp \<times> call_string, call_string_gk, 'd) eqsT" where
  "project_seeded_eqs k1 vars2_lst sigma2 T1 root1 =
     seed_rhs T1 (proj_P k1 vars2_lst sigma2) (proj_global_keys k1 vars2_lst) root1"

theorem call_string_projection_refinement:
  fixes T1 :: "(pp \<times> call_string, call_string_gk, 'd::bounded_semilattice_sup_bot) eqsT"
  assumes pp: "part_post_solution
                 (project_seeded_eqs k1 vars2_lst sigma2 T1 root1) root1 sigma1 vars1"
  shows "part_post_solution T1 root1 sigma1 vars1"
    and "\<forall>u \<in> vars1. proj_P k1 vars2_lst sigma2 (Inl u) \<le> sigma1 (Inl u)"
    and "\<forall>g \<in> set (proj_global_keys k1 vars2_lst). proj_P k1 vars2_lst sigma2 (Inr g) \<le> sigma1 (Inr g)"
  using post_solution_of_seeded[OF pp[unfolded project_seeded_eqs_def]]
  unfolding project_seeded_eqs_def by auto

end
