theory Bool_Refine
  imports Main
begin

section \<open>Refining a state by a Boolean condition\<close>

text \<open>
  A guard narrows the state by the truth value its condition must have. The Boolean
  structure of the condition is the same for every language: a negation flips the
  required truth value; a conjunction that must hold and a disjunction that must fail
  narrow by both operands in turn; a disjunction that must hold, or a conjunction that
  must fail, holds through one of its operands, so each operand that can still have the
  required value narrows the state on its own and the results are joined, as Goblint's
  \<^verbatim>\<open>BaseInvariant\<close> joins the alternatives of a disjunction (\<^verbatim>\<open>baseInvariant.ml\<close>,
  lines 724-731 at \<^verbatim>\<open>0dc12d355\<close>). An operand is dropped when its forward value rules the
  required truth value out. When neither operand can have it, no store satisfies the
  condition, and the language decides the result: bottom, as Goblint's \<^verbatim>\<open>Deadcode\<close>,
  or the state unchanged when its caller discards the branch by other means.

  A language supplies a view of its conditions as negation, conjunction, disjunction or
  atom, a size that decreases on operands, how an atom narrows a state, the
  feasibility test, the join and the infeasible result.
\<close>

datatype 'e bool_view = BV_Not 'e | BV_And 'e 'e | BV_Or 'e 'e | BV_Atom

locale bool_refine =
  fixes view :: "'e \<Rightarrow> 'e bool_view" and sz :: "'e \<Rightarrow> nat"
    and atom :: "'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's" and feas :: "'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> bool"
    and join :: "'s \<Rightarrow> 's \<Rightarrow> 's" and dead :: "'s \<Rightarrow> 's"
  assumes sz_not: "view e = BV_Not a \<Longrightarrow> sz a < sz e"
    and sz_and: "view e = BV_And a b \<Longrightarrow> sz a < sz e \<and> sz b < sz e"
    and sz_or: "view e = BV_Or a b \<Longrightarrow> sz a < sz e \<and> sz b < sz e"
begin

function brefine :: "'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's" where
  "brefine e pol \<sigma> =
     (case view e of
        BV_Not a \<Rightarrow> brefine a (\<not> pol) \<sigma>
      | BV_And a b \<Rightarrow>
          if pol then brefine b True (brefine a True \<sigma>)
          else (case (feas a False \<sigma>, feas b False \<sigma>) of
                  (True, True) \<Rightarrow> join (brefine a False \<sigma>) (brefine b False \<sigma>)
                | (True, False) \<Rightarrow> brefine a False \<sigma>
                | (False, True) \<Rightarrow> brefine b False \<sigma>
                | (False, False) \<Rightarrow> dead \<sigma>)
      | BV_Or a b \<Rightarrow>
          if pol then (case (feas a True \<sigma>, feas b True \<sigma>) of
                  (True, True) \<Rightarrow> join (brefine a True \<sigma>) (brefine b True \<sigma>)
                | (True, False) \<Rightarrow> brefine a True \<sigma>
                | (False, True) \<Rightarrow> brefine b True \<sigma>
                | (False, False) \<Rightarrow> dead \<sigma>)
          else brefine b False (brefine a False \<sigma>)
      | BV_Atom \<Rightarrow> atom e pol \<sigma>)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(e, pol, \<sigma>). sz e)")
     (auto dest: sz_not sz_and sz_or)

declare brefine.simps [simp del]

text \<open>
  A store that satisfies the condition with the required truth value stays described:
  the atom's narrowing, the feasibility test and the join are sound, and the view
  reflects how the language evaluates negation, conjunction and disjunction.
\<close>

lemma brefine_sound:
  fixes ev :: "'e \<Rightarrow> 't \<Rightarrow> int" and \<gamma> :: "'s \<Rightarrow> 't set"
  assumes atom_sound: "\<And>e pol \<sigma> t. view e = BV_Atom \<Longrightarrow> t \<in> \<gamma> \<sigma> \<Longrightarrow> (ev e t \<noteq> 0) = pol
        \<Longrightarrow> t \<in> \<gamma> (atom e pol \<sigma>)"
    and ev_not: "\<And>e a t. view e = BV_Not a \<Longrightarrow> (ev e t \<noteq> 0) = (ev a t = 0)"
    and ev_and: "\<And>e a b t. view e = BV_And a b \<Longrightarrow> (ev e t \<noteq> 0) = (ev a t \<noteq> 0 \<and> ev b t \<noteq> 0)"
    and ev_or: "\<And>e a b t. view e = BV_Or a b \<Longrightarrow> (ev e t \<noteq> 0) = (ev a t \<noteq> 0 \<or> ev b t \<noteq> 0)"
    and feas_sound: "\<And>e pol \<sigma> t. t \<in> \<gamma> \<sigma> \<Longrightarrow> (ev e t \<noteq> 0) = pol \<Longrightarrow> feas e pol \<sigma>"
    and join1: "\<And>x y t. t \<in> \<gamma> x \<Longrightarrow> t \<in> \<gamma> (join x y)"
    and join2: "\<And>x y t. t \<in> \<gamma> y \<Longrightarrow> t \<in> \<gamma> (join x y)"
  shows "t \<in> \<gamma> \<sigma> \<Longrightarrow> (ev e t \<noteq> 0) = pol \<Longrightarrow> t \<in> \<gamma> (brefine e pol \<sigma>)"
proof (induction e pol \<sigma> rule: brefine.induct)
  case (1 e pol \<sigma>)
  show ?case
  proof (cases "view e")
    case (BV_Not a)
    with 1 ev_not[OF BV_Not, of t] show ?thesis by (subst brefine.simps) simp
  next
    case (BV_And a b)
    show ?thesis
    proof (cases pol)
      case True
      with 1 ev_and[OF BV_And, of t] BV_And show ?thesis by (subst brefine.simps) simp
    next
      case False
      with 1 ev_and[OF BV_And, of t] BV_And feas_sound[of t \<sigma> a False] feas_sound[of t \<sigma> b False]
      show ?thesis
        by (subst brefine.simps) (auto split: bool.splits intro: join1 join2)
    qed
  next
    case (BV_Or a b)
    show ?thesis
    proof (cases pol)
      case True
      with 1 ev_or[OF BV_Or, of t] BV_Or feas_sound[of t \<sigma> a True] feas_sound[of t \<sigma> b True]
      show ?thesis
        by (subst brefine.simps) (auto split: bool.splits intro: join1 join2)
    next
      case False
      with 1 ev_or[OF BV_Or, of t] BV_Or show ?thesis by (subst brefine.simps) simp
    qed
  next
    case BV_Atom
    with 1 atom_sound show ?thesis by (subst brefine.simps) simp
  qed
qed

text \<open>A property every step keeps is kept. The atom need keep it only for conditions
  in a class \<open>P\<close> that contains the operands of its members, such as the conditions that
  do not read a given variable.\<close>

lemma brefine_inv:
  assumes sub_not: "\<And>e a. view e = BV_Not a \<Longrightarrow> P e \<Longrightarrow> P a"
    and sub_and: "\<And>e a b. view e = BV_And a b \<Longrightarrow> P e \<Longrightarrow> P a \<and> P b"
    and sub_or: "\<And>e a b. view e = BV_Or a b \<Longrightarrow> P e \<Longrightarrow> P a \<and> P b"
    and atom_inv: "\<And>e pol \<sigma>. view e = BV_Atom \<Longrightarrow> P e \<Longrightarrow> Q \<sigma> \<Longrightarrow> Q (atom e pol \<sigma>)"
    and join_inv: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> Q (join x y)"
    and dead_inv: "\<And>x. Q x \<Longrightarrow> Q (dead x)"
  shows "P e \<Longrightarrow> Q \<sigma> \<Longrightarrow> Q (brefine e pol \<sigma>)"
proof (induction e pol \<sigma> rule: brefine.induct)
  case (1 e pol \<sigma>)
  show ?case
  proof (cases "view e")
    case (BV_Not a)
    with 1 sub_not[OF BV_Not] show ?thesis by (subst brefine.simps) simp
  next
    case (BV_And a b)
    with 1 sub_and[OF BV_And] show ?thesis
      by (subst brefine.simps) (auto split: bool.splits intro: join_inv dead_inv)
  next
    case (BV_Or a b)
    with 1 sub_or[OF BV_Or] show ?thesis
      by (subst brefine.simps) (auto split: bool.splits intro: join_inv dead_inv)
  next
    case BV_Atom
    with 1 atom_inv show ?thesis by (subst brefine.simps) simp
  qed
qed

end

end
