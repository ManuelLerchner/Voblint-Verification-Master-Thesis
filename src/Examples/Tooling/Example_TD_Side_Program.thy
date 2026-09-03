theory Example_TD_Side_Program
  imports
    "Voblint_Solver.Strategy_Tree_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Lock-set analysis compiled from a typed strategy program\<close>

text \<open>
  A lock-set analysis for a program where \<open>main\<close> loops forever, spawning a thread running
  \<open>f\<close> on each iteration, then accesses the shared variable \<open>g\<close> while holding lock \<open>a\<close>;
  \<open>f\<close> accesses \<open>g\<close> while holding both \<open>a\<close> and \<open>b\<close>. A local unknown's right-hand side is
  the set of locks definitely held at that program point; the global unknown \<open>lock\<^sub>g\<close>
  collects, through side contributions, the lock set held at every access to \<open>g\<close>. This is
  Tilscher's TDside running example, rewritten through the typed \<open>strategy_program\<close>
  frontend rather than the raw \<open>strategy_tree\<close> constructors the original example builds
  by hand.

  \<^verbatim>\<open>
  1  int g;

  2  main () {
  3    while(1) {
  4      create(f);
  5      lock(a);
  6      g++;
  7      unlock(a);
  8    }
  9  }

  10  f () {
  11    lock(a);
  12    lock(b);
  13    g--;
  14    unlock(a);
  15    unlock(b);
  16  }
  \<close>
\<close>

subsection \<open>Definition of the domain\<close>

text \<open>
  The lock-set domain is an inverse power-set lattice over \<open>{a, b}\<close>: the empty set
  (\<open>\<top>\<close>) is the least informative over-approximation of the locks definitely held, and
  \<open>{a, b}\<close> (\<open>\<bottom>\<close>) is the fixpoint start value. Join is set intersection -- combining two
  paths keeps only the locks both agree on holding. The lattice has height 3, so widening
  is plain join and narrowing is a no-op.
\<close>

datatype lock = a | b

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
    using lock.exhaust by blast

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

subsection \<open>Definition of the equation system\<close>

text \<open>
  \<open>lock_D\<close> and \<open>unlock_D\<close> are the transfer functions for the two program statements.
  Each right-hand side below is written as a typed \<open>strategy_program\<close> and compiled once
  with \<^const>\<open>sp_compile\<close> into \<open>lock_eqs\<close>, the \<open>eqsT\<close> the solver runs -- identical to the
  tree the reference example builds by hand, checked below for a representative sample.
\<close>

lift_definition lock_D :: "lock \<Rightarrow> D \<Rightarrow> D"
  is "\<lambda>e d. if e \<in> {a, b} then Set.insert e d else d"
  by auto

lift_definition unlock_D :: "lock \<Rightarrow> D \<Rightarrow> D" is Set.remove
  by auto

datatype Unknown_L = u2 | u3 | u4 | u5 | u6 | u7 | u8 | u11 | u12 | u13 | u14 | u15 | u16
datatype Unknown_G = lock\<^sub>g

fun lock_program :: "Unknown_L \<Rightarrow> (Unknown_L, Unknown_G, D, D) strategy_program" where
  "lock_program u2 = sp_return \<top>"
| "lock_program u3 =
     do {
       d1 \<leftarrow> sp_read_local u2;
       d2 \<leftarrow> sp_read_local u7;
       sp_return (d1 \<squnion> unlock_D a d2)
     }"
| "lock_program u4 = sp_read_local u3"
| "lock_program u5 =
     do {
       d \<leftarrow> sp_read_local u4;
       _ \<leftarrow> sp_read_local u16;
       sp_return d
     }"
| "lock_program u6 =
     do {
       d \<leftarrow> sp_read_local u5;
       sp_return (lock_D a d)
     }"
| "lock_program u7 =
     do {
       d \<leftarrow> sp_read_local u6;
       _ \<leftarrow> sp_publish lock\<^sub>g d;
       sp_return d
     }"
| "lock_program u8 =
     do {
       d \<leftarrow> sp_read_local u7;
       sp_return (unlock_D a d)
     }"
| "lock_program u11 = sp_return \<top>"
| "lock_program u12 =
     do {
       d \<leftarrow> sp_read_local u11;
       sp_return (lock_D a d)
     }"
| "lock_program u13 =
     do {
       d \<leftarrow> sp_read_local u12;
       sp_return (lock_D b d)
     }"
| "lock_program u14 =
     do {
       d \<leftarrow> sp_read_local u13;
       _ \<leftarrow> sp_publish lock\<^sub>g d;
       sp_return d
     }"
| "lock_program u15 =
     do {
       d \<leftarrow> sp_read_local u14;
       sp_return (unlock_D a d)
     }"
| "lock_program u16 =
     do {
       d \<leftarrow> sp_read_local u15;
       sp_return (unlock_D b d)
     }"

definition lock_eqs :: "(Unknown_L, Unknown_G, D) eqsT"
  where "lock_eqs u = sp_compile (lock_program u)"

subsection \<open>Representative compiled trees\<close>

text \<open>
  \<open>u3\<close> shows two independent local queries combined by \<open>\<squnion>\<close>; \<open>u5\<close> shows a read whose
  result is threaded past a synchronizing read of a thread's own exit; \<open>u7\<close> and \<open>u14\<close>
  show the two side contributions to \<open>lock\<^sub>g\<close>.
\<close>

lemma lock_eqs_u3:
  "lock_eqs u3 =
     QueryL u2 (\<lambda>d1.
       QueryL u7 (\<lambda>d2.
         Answer (d1 \<squnion> unlock_D a d2)))"
  by (simp add: lock_eqs_def sp_compile_def)

lemma lock_eqs_u5:
  "lock_eqs u5 =
     QueryL u4 (\<lambda>d.
       QueryL u16 (\<lambda>_.
         Answer d))"
  by (simp add: lock_eqs_def sp_compile_def)

lemma lock_eqs_u7:
  "lock_eqs u7 =
     QueryL u6 (\<lambda>d.
       Side lock\<^sub>g d
         (Answer d))"
  by (simp add: lock_eqs_def sp_compile_def)

lemma lock_eqs_u14:
  "lock_eqs u14 =
     QueryL u13 (\<lambda>d.
       Side lock\<^sub>g d
         (Answer d))"
  by (simp add: lock_eqs_def sp_compile_def)

subsection \<open>Solving under every update rule\<close>

text \<open>
  \<open>main\<close> accesses \<open>g\<close> while holding only \<open>a\<close>; \<open>f\<close> accesses \<open>g\<close> while holding \<open>a\<close> and
  \<open>b\<close>; the global slot is their intersection, \<open>{a}\<close>. The system is loss-free -- join
  already terminates on a height-3 lattice -- so all four update rules agree everywhere.
\<close>

lemma lock_global_join:
  "Rep_D (snd (TD_side_always_join_Interp_solve lock_eqs u8) (Inr lock\<^sub>g)) = {a}"
  by eval

lemma lock_global_per_origin:
  "Rep_D (snd (TD_side_per_origin_Interp_solve lock_eqs u8) (Inr lock\<^sub>g)) = {a}"
  by eval

lemma lock_global_warrow:
  "Rep_D (snd (TD_side_warrowing_apinis_Interp_solve lock_eqs u8) (Inr lock\<^sub>g)) = {a}"
  by eval

lemma lock_global_warrow_per_origin:
  "Rep_D (snd (TD_side_warrowing_per_origin_Interp_solve lock_eqs u8) (Inr lock\<^sub>g)) = {a}"
  by eval

lemma main_exit_join:
  "Rep_D (snd (TD_side_always_join_Interp_solve lock_eqs u8) (Inl u8)) = {}"
  by eval

lemma main_exit_per_origin:
  "Rep_D (snd (TD_side_per_origin_Interp_solve lock_eqs u8) (Inl u8)) = {}"
  by eval

lemma main_exit_warrow:
  "Rep_D (snd (TD_side_warrowing_apinis_Interp_solve lock_eqs u8) (Inl u8)) = {}"
  by eval

lemma main_exit_warrow_per_origin:
  "Rep_D (snd (TD_side_warrowing_per_origin_Interp_solve lock_eqs u8) (Inl u8)) = {}"
  by eval

text \<open>
  The value at every local unknown, read from the \<open>join\<close> discipline (the other three
  agree, per the eight lemmas above): \<open>main\<close>'s body (\<open>u3\<close>--\<open>u8\<close>) never itself
  holds a lock outside \<open>u6\<close>--\<open>u7\<close>, and \<open>f\<close>'s body (\<open>u11\<close>--\<open>u16\<close>) accumulates \<open>a\<close> then
  \<open>b\<close> before releasing both.
\<close>

definition lock_full_valuation where
  "lock_full_valuation =
     map (\<lambda>u. (u, Rep_D (snd (TD_side_always_join_Interp_solve lock_eqs u8) (Inl u))))
       [u2, u3, u4, u5, u6, u7, u8, u11, u12, u13, u14, u15, u16]"

lemma lock_full_valuation_expected:
  "lock_full_valuation =
     [(u2, {}), (u3, {}), (u4, {}), (u5, {}), (u6, {a}), (u7, {a}), (u8, {}),
      (u11, {}), (u12, {a}), (u13, {a, b}), (u14, {a, b}), (u15, {b}), (u16, {})]"
  by eval

end
