theory Context_Refinement
  imports Strategy_Tree_Post_Solution Strategy_Tree_Combinators
begin

section \<open>Seeded equation systems\<close>

text \<open>
  A right-hand side that always joins a fixed local seed into its answer, and
  additionally publishes a fixed side contribution at one designated unknown
  for each key in a finite seed list. Built from @{const seqcomp_tree}, so it
  inherits @{const seqcomp_tree}'s characterization lemmas rather than adding
  a second strategy-tree combinator.
\<close>

primrec seed_sides ::
  "'g list \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "seed_sides [] s t = t"
| "seed_sides (g # gs) s t = Side g (s (Inr g)) (seed_sides gs s t)"

lemma traverse_seed_sides:
  "traverse_rhs (seed_sides gs s t) sigma = traverse_rhs t sigma"
  by (induction gs) simp_all

lemma dep_aux_seed_sides:
  "dep_aux sigma (seed_sides gs s t) = dep_aux sigma t"
  by (induction gs) simp_all

lemma sides_of_rhs_seed_sides:
  "sides_of_rhs (seed_sides gs s t) sigma
     = foldr (\<lambda>g m. m(Inr g := m (Inr g) \<squnion> s (Inr g))) gs (sides_of_rhs t sigma)"
  by (induction gs) (simp_all add: Let_def)

text \<open>Every key on the seed list is dominated by the published side map, regardless of
  which other keys precede or follow it in the list.\<close>
lemma sides_of_rhs_seed_sides_mem:
  fixes t :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree"
  assumes "g \<in> set gs"
  shows "s (Inr g) \<le> sides_of_rhs (seed_sides gs s t) sigma (Inr g)"
  using assms
proof (induction gs)
  case Nil
  then show ?case by simp
next
  case (Cons g' gs)
  show ?case
  proof (cases "g' = g")
    case True
    then show ?thesis by (simp add: Let_def)
  next
    case False
    with Cons.prems have mem: "g \<in> set gs" by simp
    have le: "sides_of_rhs (seed_sides gs s t) sigma (Inr g)
                \<le> sides_of_rhs (seed_sides (g' # gs) s t) sigma (Inr g)"
      by (simp add: Let_def fun_upd_def)
    from order_trans[OF Cons.IH[OF mem] le] show ?thesis .
  qed
qed

definition seed_eqs ::
  "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'g list \<Rightarrow> 'x
   \<Rightarrow> ('x, 'g, 'd) eqsT"
where
  "seed_eqs T s gseeds x0 x = do {
     d \<leftarrow> T x;
     seed_sides (if x = x0 then gseeds else []) s (answer (d \<squnion> s (Inl x)))
   }"

text \<open>
  @{const seed_eqs} joins the seed's local value into every unknown's answer,
  and at the designated unknown @{term x0} additionally publishes the seed's
  global values along the given key list. It is built from @{const
  seqcomp_tree} and @{const seed_sides}, so @{const eq}, @{const dep}, and
  @{const sides_of_rhs} at @{const seed_eqs} reduce to the underlying system's
  values by the characterization lemmas above, never by re-deriving
  \<^typ>\<open>('x,'g,'d) strategy_tree\<close> induction.
\<close>

lemma eq_seed_eqs [simp]:
  "eq (seed_eqs T s gseeds x0) x sigma = eq T x sigma \<squnion> s (Inl x)"
  unfolding seed_eqs_def
  by (simp add: traverse_seqcomp traverse_seed_sides)

lemma dep_seed_eqs [simp]:
  "dep (seed_eqs T s gseeds x0) sigma x = dep T sigma x"
  unfolding seed_eqs_def dep_def
  by (simp add: dep_aux_seqcomp dep_aux_seed_sides)

lemma sides_of_rhs_seed_eqs_ge:
  "sides_of_rhs (T x) sigma \<le> sides_of_rhs (seed_eqs T s gseeds x0 x) sigma"
  unfolding seed_eqs_def
  by (simp add: sides_of_rhs_seqcomp)

text \<open>
  A post-solution of the seeded system at its own seed unknown is a
  post-solution of the underlying system on the same set, and the seed is
  dominated everywhere that set reaches --- not, in general, everywhere the
  seed itself is defined. A projection witness built from @{const seed_eqs}
  must show separately that its seed's support lands inside the seeded
  solve's own stable set for domination to hold beyond \<open>vars\<close>.
\<close>

text \<open>The third conclusion needs only @{term x0}'s own membership (always true of
  @{const part_post_solution}'s start unknown) and @{thm [source] sides_of_rhs_seed_sides_mem}:
  the seed list is published exactly once, at @{term x0}'s own equation, so every key on it is
  dominated there regardless of whether @{term x0} is itself a genuine merge point for any
  particular key.\<close>
theorem post_solution_of_seeded:
  fixes T :: "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT"
    and vars :: "'x set"
  assumes pp: "part_post_solution (seed_eqs T s gseeds x0) x0 sigma vars"
  shows "part_post_solution T x0 sigma vars"
    and "\<forall>u \<in> vars. s (Inl u) \<le> sigma (Inl u)"
    and "\<forall>g \<in> set gseeds. s (Inr g) \<le> sigma (Inr g)"
proof -
  have x0_vars: "x0 \<in> vars"
    using pp unfolding part_post_solution_iff_se_constraint_holds by blast
  have closed: "\<forall>u \<in> vars. dep\<^sub>L T sigma u \<subseteq> vars"
    using pp unfolding dep\<^sub>L_def by simp
  have seed_and_rhs: "\<forall>u \<in> vars. eq T u sigma \<le> sigma (Inl u) \<and> s (Inl u) \<le> sigma (Inl u)"
    using pp by (simp add: le_sup_iff)
  have side_le: "\<forall>u \<in> vars. sides_of_rhs (T u) sigma \<le> sigma"
  proof
    fix u assume "u \<in> vars"
    then have "sides_of_rhs (seed_eqs T s gseeds x0 u) sigma \<le> sigma"
      using pp by simp
    with sides_of_rhs_seed_eqs_ge[of T u sigma s gseeds x0] show
      "sides_of_rhs (T u) sigma \<le> sigma" by (rule order_trans)
  qed
  have x0_side_le: "sides_of_rhs (seed_eqs T s gseeds x0 x0) sigma \<le> sigma"
    using pp x0_vars by simp
  have global_le: "\<forall>g \<in> set gseeds. s (Inr g) \<le> sigma (Inr g)"
  proof
    fix g assume mem: "g \<in> set gseeds"
    have eq_form: "sides_of_rhs (seed_eqs T s gseeds x0 x0) sigma (Inr g)
          = sides_of_rhs (T x0) sigma (Inr g)
            \<squnion> sides_of_rhs (seed_sides gseeds s (Answer (traverse_rhs (T x0) sigma \<squnion> s (Inl x0))))
                sigma (Inr g)"
      unfolding seed_eqs_def by simp
    have mem_le: "s (Inr g)
          \<le> sides_of_rhs (seed_sides gseeds s (Answer (traverse_rhs (T x0) sigma \<squnion> s (Inl x0))))
              sigma (Inr g)"
      by (rule sides_of_rhs_seed_sides_mem[OF mem])
    have "s (Inr g) \<le> sides_of_rhs (seed_eqs T s gseeds x0 x0) sigma (Inr g)"
      unfolding eq_form by (rule order_trans[OF mem_le sup_ge2])
    also have "\<dots> \<le> sigma (Inr g)"
      using x0_side_le by (simp add: le_fun_def)
    finally show "s (Inr g) \<le> sigma (Inr g)" .
  qed
  show "part_post_solution T x0 sigma vars"
    using pp closed seed_and_rhs side_le by auto
  show "\<forall>u \<in> vars. s (Inl u) \<le> sigma (Inl u)"
    using seed_and_rhs by auto
  show "\<forall>g \<in> set gseeds. s (Inr g) \<le> sigma (Inr g)"
    using global_le by auto
qed

end
