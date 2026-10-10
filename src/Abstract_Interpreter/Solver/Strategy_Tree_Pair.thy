theory Strategy_Tree_Pair
  imports Strategy_Tree_Side_Buffering
begin

section \<open>A right-hand side as a pair\<close>

text \<open>
  A side-effecting right-hand side is often presented as a function from a valuation to a
  pair: the contributions it publishes, a partial map from unknowns to values, and its own
  value. A strategy tree evaluates to the same pair. The second component is
  \<^const>\<open>traverse_rhs\<close>; the first is \<^const>\<open>sides_of_rhs\<close> restricted to the keys
  \<^const>\<open>side_path\<close> visits, so a key that receives only \<open>\<bottom>\<close> stays in the domain and
  a key that receives nothing does not. Both components come from the existing evaluators.
\<close>

definition rhs_sides ::
  "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x + 'g \<rightharpoonup> 'd"
where
  "rhs_sides t \<sigma> = (Some \<circ> sides_of_rhs t \<sigma>) |` (Inr ` set (side_path \<sigma> t))"

definition rhs_pair ::
  "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x + 'g \<Rightarrow> 'd)
     \<Rightarrow> ('x + 'g \<rightharpoonup> 'd) \<times> 'd"
where
  "rhs_pair t \<sigma> = (rhs_sides t \<sigma>, traverse_rhs t \<sigma>)"

subsection \<open>The partial map loses nothing\<close>

text \<open>Off the visited keys \<^const>\<open>sides_of_rhs\<close> is \<open>\<bottom>\<close>, so reading the map back with \<^const>\<open>mlup\<close> recovers it.\<close>

lemma sides_of_rhs_Inl [simp]: "sides_of_rhs t \<sigma> (Inl u) = \<bottom>"
  by (induction t) (simp_all add: Let_def)

lemma sides_of_rhs_off_path:
  "g \<notin> set (side_path \<sigma> t) \<Longrightarrow> sides_of_rhs t \<sigma> (Inr g) = \<bottom>"
  by (induction t) (auto simp: Let_def)

lemma rhs_sides_apply:
  "rhs_sides t \<sigma> z =
     (if z \<in> Inr ` set (side_path \<sigma> t) then Some (sides_of_rhs t \<sigma> z) else None)"
  by (simp add: rhs_sides_def restrict_map_def)

lemma dom_rhs_sides: "dom (rhs_sides t \<sigma>) = Inr ` set (side_path \<sigma> t)"
  by (auto simp: dom_def rhs_sides_apply)

text \<open>Side effects only reach global unknowns; a local unknown is never in the domain.\<close>

lemma rhs_sides_Inl [simp]: "rhs_sides t \<sigma> (Inl u) = None"
  by (auto simp: rhs_sides_apply)

lemma mlup_rhs_sides: "mlup (rhs_sides t \<sigma>) = sides_of_rhs t \<sigma>"
proof
  fix z
  show "mlup (rhs_sides t \<sigma>) z = sides_of_rhs t \<sigma> z"
    by (cases z) (auto simp: mlup_def rhs_sides_apply sides_of_rhs_off_path image_iff)
qed

text \<open>
  Several side effects to one unknown appear once in the domain, with the join of their values,
  in the order of the traversal.
\<close>

lemma rhs_sides_Side:
  "rhs_sides (Side g d t) \<sigma> = (rhs_sides t \<sigma>)(Inr g \<mapsto> mlup (rhs_sides t \<sigma>) (Inr g) \<squnion> d)"
  by (rule ext) (auto simp: mlup_rhs_sides rhs_sides_apply Let_def)

lemma rhs_pair_two_sides:
  "rhs_pair (Side g a (Side g b (Answer d))) \<sigma> = ([Inr g \<mapsto> b \<squnion> a], d)"
  unfolding rhs_pair_def by (auto simp: rhs_sides_apply Let_def intro!: ext)

subsection \<open>The certificate in pair form\<close>

text \<open>A side map is below a valuation exactly when every contribution it publishes is below its target.\<close>

lemma sides_of_rhs_le_iff_rhs_sides:
  "sides_of_rhs t \<sigma> \<le> \<sigma> \<longleftrightarrow> (\<forall>z d. rhs_sides t \<sigma> z = Some d \<longrightarrow> d \<le> \<sigma> z)"
proof
  assume "sides_of_rhs t \<sigma> \<le> \<sigma>"
  then show "\<forall>z d. rhs_sides t \<sigma> z = Some d \<longrightarrow> d \<le> \<sigma> z"
    by (auto simp: rhs_sides_apply le_fun_def)
next
  assume bound: "\<forall>z d. rhs_sides t \<sigma> z = Some d \<longrightarrow> d \<le> \<sigma> z"
  show "sides_of_rhs t \<sigma> \<le> \<sigma>"
  proof (rule le_funI)
    fix z
    show "sides_of_rhs t \<sigma> z \<le> \<sigma> z"
    proof (cases "z \<in> Inr ` set (side_path \<sigma> t)")
      case True
      then show ?thesis
        using bound by (simp add: rhs_sides_apply)
    next
      case False
      then have "sides_of_rhs t \<sigma> z = \<bottom>"
        by (cases z) (auto simp: sides_of_rhs_off_path image_iff)
      then show ?thesis
        by simp
    qed
  qed
qed

text \<open>
  \<^const>\<open>part_post_solution\<close> with its local and side bounds stated on the pair: the
  value is below the unknown, and every published contribution is below its target. The
  bounds constrain the side-effect targets although they are global unknowns outside
  \<open>vars\<close>, and say nothing about unknowns outside \<open>vars\<close> that the solve never reached.
\<close>

theorem part_post_solution_iff_rhs_pair:
  "part_post_solution T x \<sigma> vars \<longleftrightarrow>
     x \<in> vars \<and> (\<forall>u \<in> vars. dep\<^sub>L T \<sigma> u \<subseteq> vars \<and>
       (case rhs_pair (T u) \<sigma> of (\<rho>, d) \<Rightarrow>
          d \<le> \<sigma> (Inl u) \<and> (\<forall>z d'. \<rho> z = Some d' \<longrightarrow> d' \<le> \<sigma> z)))"
  unfolding rhs_pair_def by (simp add: sides_of_rhs_le_iff_rhs_sides)

end
