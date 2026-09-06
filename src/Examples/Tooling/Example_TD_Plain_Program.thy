theory Example_TD_Plain_Program
  imports
    "Voblint_Solver.Strategy_Tree_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Must-be-initialized analysis compiled from a side-effect-free strategy program\<close>

text \<open>
  A must-be-initialized analysis: at each program point, which variables are guaranteed to
  already hold a value. Each unknown's right-hand side is the set of variables definitely
  initialized at that point, computed from its predecessors' sets. Unlike the lock-set
  example (\<open>Example_TD_Side_Program\<close>), no unknown ever publishes to a global, so the
  \<open>strategy_program\<close> below never calls \<^const>\<open>sp_read_global\<close> or \<^const>\<open>sp_publish\<close> --
  it is Tilscher's TD (not TDside) running example, rewritten through the same typed
  frontend.

  \<^verbatim>\<open>
  a = 17
  while true:
    b = a * a
    if b < 10: break
    a = a - 1
  \<close>
\<close>

subsection \<open>Definition of the domain\<close>

text \<open>
  The domain is structurally identical to the lock-set example's: an inverse power-set
  lattice over \<open>{a, b}\<close>, empty set as \<open>\<top>\<close>, \<open>{a, b}\<close> as \<open>\<bottom>\<close>, join as intersection, plain
  join as widening, no-op narrowing. It needs the full \<open>order_bot\<close> /
  \<open>bounded_semilattice_sup_bot\<close> / \<open>bounded_lattice\<close> / \<open>warrowing\<close> instantiation -- unlike
  the original TD-only example, which only needed \<open>bot\<close> and \<open>equal\<close> -- because running it
  under all four TDside update-rule disciplines exercises every one.
\<close>

datatype pv = a | b

typedef D = "Pow {a, b}"
  by auto

setup_lifting D.type_definition_D

instantiation D :: equal
begin
  definition equal_D :: "D \<Rightarrow> D \<Rightarrow> bool"
    where "equal_D d1 d2 = (Rep_D d1 = Rep_D d2)"

  instance by standard (simp add: equal_D_def Rep_D_inject)
end

instantiation D :: order_bot
begin
  lift_definition less_eq_D :: "D \<Rightarrow> D \<Rightarrow> bool" is "\<lambda>d1 d2. d2 \<subseteq> d1" .

  definition less_D :: "D \<Rightarrow> D \<Rightarrow> bool"
    where "less_D d1 d2 = (d1 \<le> d2 \<and> \<not> d2 \<le> d1)"

  lift_definition bot_D :: D is "{a, b}" by simp

  instance
    apply standard
    unfolding less_D_def
    by (transfer, simp)+
end

instantiation D :: bounded_semilattice_sup_bot
begin
  lift_definition sup_D :: "D \<Rightarrow> D \<Rightarrow> D" is "(\<inter>)"
    by auto

  instance
    apply standard
    unfolding less_eq_D_def
    by (transfer, simp)+
end

instantiation D :: bounded_lattice
begin
  lift_definition top_D :: D is "{}"
    by simp

  lift_definition inf_D :: "D \<Rightarrow> D \<Rightarrow> D" is "(\<union>)"
    by simp

  instance
    by standard (transfer, simp)+
end

lemma D_cases [consumes 0]:
  fixes d :: D
  obtains "d = Abs_D {}" | "d = Abs_D {a}" | "d = Abs_D {b}" | "d = Abs_D {a, b}"
proof -
  consider "Rep_D d = {}" | "Rep_D d = {a}" | "Rep_D d = {b}" | "Rep_D d = {a, b}"
    using Rep_D by auto
  then have "d = Abs_D {} \<or> d = Abs_D {a} \<or> d = Abs_D {b} \<or> d = Abs_D {a, b}"
    using Rep_D_inverse [of d, symmetric] by cases auto
  then show ?thesis using that by fastforce
qed

instantiation D :: warrowing
begin
  definition widen_D :: "D \<Rightarrow> D \<Rightarrow> D"
    where "widen_D = (\<squnion>)"

  definition narrow_D :: "D \<Rightarrow> D \<Rightarrow> D"
    where "narrow_D d1 d2 = d1"

  lift_definition max_D :: "D set \<Rightarrow> D" is
    "\<lambda>Q. if {} \<in> Q then {} else if {a} \<in> Q then {a} else if {b} \<in> Q then {b} else {a, b}"
    by simp

  lemma pow_ab: "Pow {a, b} = {{}, {a}, {b}, {a, b}}"
    using Pow_insert [of b "{}"] Pow_insert [of a "{b}"] by auto

  lemma subset_Pow: "(\<forall>x \<in> Q. x \<subseteq> {a, b}) = (Q \<subseteq> Pow {a, b})"
    using pv.exhaust by blast

  lemma widen_wf: "wf {(x :: D, y :: D). x \<noteq> y \<and> (\<exists>z. x = y \<squnion> z)}"
    apply (intro wfI_min)
    subgoal for x Q
      apply (intro bexI [of _ "max_D Q"])
      subgoal
        apply transfer
        subgoal for x Q
          apply (simp only: mem_Collect_eq prod.case)
          apply (simp split: if_splits)
          using Int_insert_left [of a "{b}"] subset_singletonD [OF Int_lower1 [of "{_}"]]
          by metis+
        done
      subgoal
        apply transfer
        subgoal for x Q
          by (cases "x = {}"; cases "x = {a}"; cases "x = {b}"; cases "x = {a, b}") auto
        done
      done
    done

  instance
    apply standard
    unfolding widen_D_def narrow_D_def
    using widen_wf
    by simp_all
end

text \<open>\<open>insert_D\<close> and \<open>set_to_D\<close> build a \<open>D\<close> value from a concrete set of variables.\<close>

lift_definition insert_D :: "pv \<Rightarrow> D \<Rightarrow> D"
  is "\<lambda>e d. if e \<in> {a, b} then Set.insert e d else d"
  by auto

definition set_to_D :: "pv set \<Rightarrow> D" where
  "set_to_D s = fold (\<lambda>e acc. if e \<in> s then insert_D e acc else acc) [a, b] \<top>"

subsection \<open>Definition of the equation system\<close>

text \<open>
  No right-hand side below queries a global or publishes: each is a side-effect-free
  \<open>strategy_program\<close> over \<open>(Unknown, unit, D, D)\<close>, and \<open>Z\<close>'s later query of \<open>W\<close> is only
  reached when its earlier read of \<open>Y\<close> was uninformative -- the compiled query set is
  value-dependent, not fixed (contrast \<open>Example_TD_Side_Program\<close>, whose queries never
  branch on a value).
\<close>

datatype Unknown = X | Y | Z | W

fun initialized_program :: "Unknown \<Rightarrow> (Unknown, unit, D, D) strategy_program" where
  "initialized_program X =
     do {
       d1 \<leftarrow> sp_read_local Y;
       if d1 = \<top> then
         sp_return \<top>
       else
         do {
           d2 \<leftarrow> sp_read_local Z;
           sp_return (d1 \<squnion> d2)
         }
     }"
| "initialized_program Y =
     do {
       d \<leftarrow> sp_read_local Z;
       if d \<in> {\<top>, set_to_D {b}}
       then sp_return (set_to_D {b})
       else sp_return \<bottom>
     }"
| "initialized_program Z =
     do {
       d1 \<leftarrow> sp_read_local Y;
       if d1 \<in> {\<top>, set_to_D {a}} then
         sp_return (set_to_D {a})
       else
         do {
           d2 \<leftarrow> sp_read_local W;
           if d2 \<in> {\<top>, set_to_D {a}}
           then sp_return (set_to_D {a})
           else sp_return \<bottom>
         }
     }"
| "initialized_program W = sp_return \<top>"

definition initialized_eqs :: "(Unknown, unit, D) eqsT"
  where "initialized_eqs u = sp_compile (initialized_program u)"

subsection \<open>Representative compiled trees\<close>

text \<open>
  \<open>X\<close> shows a query whose second dependency is conditional on the first query's result;
  \<open>Z\<close> shows the same value-dependent pattern one level deeper.
\<close>

lemma initialized_eqs_X:
  "initialized_eqs X =
     QueryL Y (\<lambda>d1.
       if d1 = \<top> then
         Answer \<top>
       else
         QueryL Z (\<lambda>d2. Answer (d1 \<squnion> d2)))"
  unfolding initialized_eqs_def sp_compile_def
  by (auto split: if_splits intro!: ext)

lemma initialized_eqs_Z:
  "initialized_eqs Z =
     QueryL Y (\<lambda>d1.
       if d1 \<in> {\<top>, set_to_D {a}} then
         Answer (set_to_D {a})
       else
         QueryL W (\<lambda>d2.
           if d2 \<in> {\<top>, set_to_D {a}}
           then Answer (set_to_D {a})
           else Answer \<bottom>))"
  unfolding initialized_eqs_def sp_compile_def
  by (auto split: if_splits intro!: ext)

subsection \<open>Solving under every update rule\<close>

text \<open>
  The system has no side effects, so the four TDside disciplines differ only in local
  fixpoint iteration, not in how a global slot combines contributions; they agree
  everywhere here.
\<close>

lemma initialized_X_join:
  "Rep_D (snd (TD_side_always_join_Interp_solve initialized_eqs X) (Inl X)) = {a}"
  by eval

lemma initialized_X_per_origin:
  "Rep_D (snd (TD_side_per_origin_Interp_solve initialized_eqs X) (Inl X)) = {a}"
  by eval

lemma initialized_X_warrow:
  "Rep_D (snd (TD_side_warrowing_apinis_Interp_solve initialized_eqs X) (Inl X)) = {a}"
  by eval

lemma initialized_X_warrow_per_origin:
  "Rep_D (snd (TD_side_warrowing_per_origin_Interp_solve initialized_eqs X) (Inl X)) = {a}"
  by eval

text \<open>The value at every unknown, read from the \<open>join\<close> discipline (the other three agree,
  per the four lemmas above).\<close>

definition initialized_full_valuation where
  "initialized_full_valuation =
     map (\<lambda>u. (u, Rep_D (snd (TD_side_always_join_Interp_solve initialized_eqs X) (Inl u))))
       [X, Y, Z, W]"

lemma initialized_full_valuation_expected:
  "initialized_full_valuation = [(X, {a}), (Y, {a, b}), (Z, {a}), (W, {})]"
  by eval

end
