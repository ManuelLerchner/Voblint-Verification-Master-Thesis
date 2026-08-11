theory TD_Side_CFG
  imports Constraint_System_Sound Split_State "Voblint_VIMP.VIMP_Globals" "TD.TD_side"
begin

(* TD_side defines a record field \<sigma> for its internal state; hide the short
   name so our \<sigma> variables (abstract state maps) are unambiguous. *)
hide_const (open) \<sigma>

section \<open>Side IP solver: generic base\<close>

text \<open>
  Generic base for the side-effecting interprocedural solver.

  A locals/globals split on abstract states: restrict_local / restrict_global
  keep one component (the other set to bot), so their join recovers the
  original state.  side_env combines the local unknown at a program point with
  the single global unknown.

  The interprocedural strategy tree and transfer functions live in TD_Side_Tree;
  monotonicity and solver preconditions live in TD_Side_Eff_Bounds and TD_Side_Eff_Cone_Lemmas.
\<close>

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local_for gs \<sigma> = (%x. if gs x then bot else \<sigma> x)"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for gs \<sigma> = (%x. if gs x then \<sigma> x else bot)"

lemma restrict_local_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_local_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_local_for gs sigma2"
  unfolding restrict_local_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_global_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_global_for gs sigma2"
  unfolding restrict_global_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_local_for_join [simp]:
  "restrict_local_for gs (A \<squnion> B) = restrict_local_for gs A \<squnion> restrict_local_for gs B"
  unfolding restrict_local_for_def sup_fun_def by (rule ext) simp

lemma restrict_global_for_join [simp]:
  "restrict_global_for gs (A \<squnion> B) = restrict_global_for gs A \<squnion> restrict_global_for gs B"
  unfolding restrict_global_for_def sup_fun_def by (rule ext) simp

lemma restrict_local_for_idem [simp]:
  "restrict_local_for gs (restrict_local_for gs A) = restrict_local_for gs A"
  unfolding restrict_local_for_def by (rule ext) simp

lemma restrict_global_for_idem [simp]:
  "restrict_global_for gs (restrict_global_for gs A) = restrict_global_for gs A"
  unfolding restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_restrict_global_for_bot [simp]:
  "restrict_local_for gs (restrict_global_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_global_for_restrict_local_for_bot [simp]:
  "restrict_global_for gs (restrict_local_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_global_join:
  "restrict_local_for gs \<sigma> \<squnion> restrict_global_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_global_for_local_join:
  "restrict_global_for gs \<sigma> \<squnion> restrict_local_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp
lemma restrict_global_for_sup [simp]:
  "restrict_global_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_global_for gs B"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_local_for_sup [simp]:
  "restrict_local_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_local_for gs A"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp



(* Monotonicity in the queried assignment (join = \<squnion>). *)

lemma join_abs_state_left_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and acc1 acc2 s :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join acc1 s \<le> join acc2 s"
  by (rule join_mono[OF acc_le order_refl])

lemma join_abs_state_right_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and s acc1 acc2 :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join s acc1 \<le> join s acc2"
  by (rule join_mono[OF order_refl acc_le])


(* restrict_local / restrict_global are join-homomorphisms, idempotent, and
   annihilate each other; together these make the algebra confluent, so a
   split-state combine such as restrict_local (restrict_local A \<squnion> restrict_global B)
   = restrict_local A closes by plain simp without a dedicated lemma. *)
(* combine_env\<^sup>#'s primitive definition is a single if-then-else lambda; this
   reduces it to the confluent restrict_local_for/restrict_global_for algebra so
   proofs never need to unfold combine_env_abs_def and re-derive the split by
   hand. *)
lemma combine_env_abs_for_eq_restrict:
  "combine_env\<^sup># gs sc se =
     restrict_local_for gs sc \<squnion> restrict_global_for gs se"
  unfolding combine_env_abs_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp


subsection \<open>Split-state bridge\<close>

text \<open>
  The split representation of \<open>Split_State\<close> packages exactly this
  \<^const>\<open>restrict_local_for\<close> / \<^const>\<open>restrict_global_for\<close> decomposition:
  \<^const>\<open>split_state\<close> is the pair of the two restrictions, restriction pairs
  are well-formed split states, and \<^const>\<open>merge_state\<close> of two restrictions
  is their join.
\<close>

lemma split_state_eq_restrict:
  "split_state gs \<sigma> = (restrict_local_for gs \<sigma>, restrict_global_for gs \<sigma>)"
  unfolding split_state_def restrict_local_for_def restrict_global_for_def by simp

lemma wf_split_restrict:
  "wf_split gs (restrict_local_for gs A, restrict_global_for gs B)"
  unfolding wf_split_def restrict_local_for_def restrict_global_for_def by simp

lemma merge_state_restrict:
  "merge_state gs (restrict_local_for gs A, restrict_global_for gs B)
   = restrict_local_for gs A \<squnion> restrict_global_for gs B"
  unfolding merge_state_def restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp


(* The abstract state combined from the local unknown at v and the join of all
   named-global unknowns (glob_env).  At 'g = unit this is the single global
   unknown \<sigma> (Inr ()) (glob_env_unit). *)
definition side_env ::
  "(pp + 'g::finite => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> glob_env \<sigma>"

(* The base unfold: 23 call sites across the solver core reach past this
   definition via unfolding side_env_def. Left untagged: a locale
   abbreviation (ltr_gamma.gamma_ltr) is itself stated in terms of side_env,
   and eagerly expanding side_env elsewhere breaks the term-shape matching
   that abbreviation's own unfold relies on -- cite explicitly instead. *)
lemma side_env_apply:
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> glob_env \<sigma>"
  unfolding side_env_def by (rule refl)

(* Reading a single named global g combined with the locals at v. *)
definition side_env_g ::
  "(pp + 'g => 'a::bounded_semilattice_sup_bot abs_state) => 'g => pp => 'a abs_state"
where
  "side_env_g \<sigma> g v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr g)"

lemma side_env_eq_side_env_g:
  "side_env \<sigma> v = side_env_g \<sigma> () v"
  unfolding side_env_def side_env_g_def by (simp add: glob_env_unit)

(* Reading a single named global is a tighter view than the joined global
   environment: side_env_g picks one slot, side_env joins all of them. *)
lemma side_env_g_le_side_env:
  fixes \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "side_env_g \<sigma> g v \<le> side_env \<sigma> v"
  unfolding side_env_g_def side_env_def
  by (rule sup_mono[OF order_refl glob_env_upper])


subsection \<open>Unit-global effectful trees\<close>

text \<open>
  Unit-global effectful trees query the local program point and the unit global
  slot, compute one abstract post-state, then split that result between the local
  Answer and the global Side contribution consumed by TD_side.
\<close>

definition unit_edge_tree ::
  "(vname => bool)
   => ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state)
   => (unit, 'a) edge_tf_tree"
where
  "unit_edge_tree gs f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global_for gs res)
         (Answer (restrict_local_for gs res))))"

(* Procedure-return combine: query the caller local cc, the callee-exit local
   ex, and the global; reassemble locals-from-caller + globals-from-callee
   (= combine_env\<^sup>#) and split into a local Answer and a global Side. *)
definition unit_combine_tree ::
  "(vname => bool) => vname option => pp => pp
   => (pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "unit_combine_tree gs dst cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = combine_collect_abs gs dst (sc \<squnion> g) (se \<squnion> g) in
       Side () (restrict_global_for gs res)
         (Answer (restrict_local_for gs res)))))"

lemma traverse_unit_edge_tree:
  "traverse_rhs (unit_edge_tree gs f u) \<sigma> = restrict_local_for gs (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_edge_tree_def by (simp add: Let_def)

(* The tree's single Side contribution to the global slot is the global
   restriction of the result. *)
lemma sides_unit_edge_tree_Inr:
  "sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inr ()) =
   restrict_global_for gs (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_edge_tree_def by (simp add: Let_def)

(* Reassembling the tree's local Answer and global Side recovers the full result. *)
lemma etf_full_unit_edge_tree:
  "etf_full (unit_edge_tree gs f u) \<sigma> = f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def
  by (simp add: all_sides_eq_sides_Inr_unit traverse_unit_edge_tree sides_unit_edge_tree_Inr
        restrict_local_for_global_join)



(* The unit-global combine tree returns the combined locals as its Answer; unlike
   a plain combine_env these include the destination when the call assigns one. *)
lemma traverse_unit_combine_tree:
  "traverse_rhs (unit_combine_tree gs dst cc ex) \<sigma>
     = restrict_local_for gs (combine_collect_abs gs dst (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))
                                              (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_combine_tree_def by (simp add: Let_def)

(* The unit-global combine tree contributes the combined globals to the global slot. *)
lemma sides_unit_combine_tree_Inr:
  "sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inr ()) =
   restrict_global_for gs (combine_collect_abs gs dst (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))
                                            (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_combine_tree_def by (simp add: Let_def)

(* The unit-global combine tree reassembles to the fixed abstract combine. *)
lemma etf_full_unit_combine_tree:
  "etf_full (unit_combine_tree gs dst cc ex) \<sigma>
   = combine_collect_abs gs dst (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))
       (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
proof -
  let ?res = "combine_collect_abs gs dst (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))
                (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
  have "etf_full (unit_combine_tree gs dst cc ex) \<sigma>
          = restrict_local_for gs ?res \<squnion> restrict_global_for gs ?res"
    unfolding etf_full_def unit_combine_tree_def
    by (simp add: Let_def)
  also have "\<dots> = ?res"
    by (rule restrict_local_for_global_join)
  finally show ?thesis .
qed


subsection \<open>Local-only effectful edge trees\<close>

text \<open>
  When an edge transfer preserves globals and only reads locals, the tree can
  query the source local unknown without @{term QueryG}.  Soundness and
  post-fixpoint bounds use @{const etf_full} joined with @{const glob_env}.
\<close>

definition local_bot_on_locals ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> bool"
where
  "local_bot_on_locals gs g \<longleftrightarrow> (\<forall>x. \<not> gs x \<longrightarrow> g x = bot)"

lemma local_bot_join:
  assumes "local_bot_on_locals gs (a :: 'a::bounded_semilattice_sup_bot abs_state)"
    and "local_bot_on_locals gs b"
  shows "local_bot_on_locals gs (a \<squnion> b)"
  using assms unfolding local_bot_on_locals_def by (auto simp: sup_fun_def)

lemma glob_env_local_bot:
  fixes \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes inr: "\<And>g. local_bot_on_locals gs (\<sigma> (Inr g))"
  shows "local_bot_on_locals gs (glob_env \<sigma>)"
  unfolding local_bot_on_locals_def glob_env_def abs_join_set_def
proof (clarify)
  fix x
  assume ng: "\<not> gs x"
  have elem_bot: "\<And>a. a \<in> range (\<lambda>g. \<sigma> (Inr g)) \<Longrightarrow> a x = bot"
    using inr ng unfolding local_bot_on_locals_def by auto
  have fold_bot:
    "\<And>A. finite A \<Longrightarrow> A \<subseteq> range (\<lambda>g. \<sigma> (Inr g)) \<Longrightarrow>
      Finite_Set.fold (\<squnion>) bot A x = bot"
  proof -
    fix A
    assume finA: "finite A"
      and subA: "A \<subseteq> range (\<lambda>g. \<sigma> (Inr g))"
    from finA subA show "Finite_Set.fold (\<squnion>) bot A x = bot"
    proof (induction A rule: finite_induct)
      case empty
      then show ?case by simp
    next
      case (insert a A)
      have subA: "A \<subseteq> range (\<lambda>g. \<sigma> (Inr g))"
        using insert.prems by auto
      have ax: "a x = bot"
        using insert.prems elem_bot by auto
      have ih: "Finite_Set.fold (\<squnion>) bot A x = bot"
        using insert.IH[OF subA] .
      have fold_insert:
        "Finite_Set.fold (\<squnion>) bot (insert a A) =
         a \<squnion> Finite_Set.fold (\<squnion>) bot A"
        using insert.hyps by (simp)
      have "Finite_Set.fold (\<squnion>) bot (insert a A) x =
            (a \<squnion> Finite_Set.fold (\<squnion>) bot A) x"
        using fold_insert by simp
      also have "... = bot"
        using ax ih by (simp add: sup_fun_def)
      finally show ?case .
    qed
  qed
  show "Finite_Set.fold (\<squnion>) bot (range (\<lambda>g. \<sigma> (Inr g))) x = bot"
    using fold_bot by simp
qed

(* Every named-global slot of an inr_slot_locals_bot state is itself
   local-bot; hoisted here (ahead of its first use below) so downstream
   proofs can cite it instead of re-deriving it from both definitions. *)
lemma inr_slot_locals_bot_imp [dest]:
  "inr_slot_locals_bot gs \<sigma> \<Longrightarrow> local_bot_on_locals gs (\<sigma> (Inr g))"
  unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto

definition local_edge_invariant ::
  "(vname => bool) => ('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> bool"
where
  "local_edge_invariant gs f \<longleftrightarrow>
     (\<forall>su g. local_bot_on_locals gs g \<longrightarrow>
        f (restrict_local_for gs su \<squnion> g) =
        restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g)"

(* The direct instantiation of local_edge_invariant's definition, cited by
   domain instances instead of re-unfolding the quantified definition at
   every call site. *)
lemma local_edge_invariantD:
  "local_edge_invariant gs f \<Longrightarrow> local_bot_on_locals gs g \<Longrightarrow>
   f (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g"
  unfolding local_edge_invariant_def by blast

lemma local_edge_invariant_local_result:
  assumes inv: "local_edge_invariant gs f"
  shows "restrict_local_for gs (f (restrict_local_for gs su)) = f (restrict_local_for gs su)"
proof -
  have "f (restrict_local_for gs su \<squnion> bot) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> bot"
    using inv unfolding local_edge_invariant_def local_bot_on_locals_def
    by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
  then show ?thesis by simp
qed

lemma local_edge_invariant_comp:
  assumes f: "local_edge_invariant gs f"
    and h: "local_edge_invariant gs h"
  shows "local_edge_invariant gs (\<lambda>su. f (h su))"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals gs g"
  have h_step: "h (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (h (restrict_local_for gs su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  have h_local: "restrict_local_for gs (h (restrict_local_for gs su)) = h (restrict_local_for gs su)"
    using local_edge_invariant_local_result[OF h, of su] .
  show "f (h (restrict_local_for gs su \<squnion> g)) = restrict_local_for gs (f (h (restrict_local_for gs su))) \<squnion> g"
    using f lb h_step h_local unfolding local_edge_invariant_def by metis
qed

lemma local_edge_invariant_sup:
  assumes f: "local_edge_invariant gs f"
    and h: "local_edge_invariant gs h"
  shows "local_edge_invariant gs (\<lambda>su. f su \<squnion> h su)"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals gs g"
  have f_step: "f (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g"
    using f lb unfolding local_edge_invariant_def by blast
  have h_step: "h (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (h (restrict_local_for gs su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  show "f (restrict_local_for gs su \<squnion> g) \<squnion> h (restrict_local_for gs su \<squnion> g) =
        restrict_local_for gs (f (restrict_local_for gs su) \<squnion> h (restrict_local_for gs su)) \<squnion> g"
    using f_step h_step
    by (simp add: restrict_local_for_sup sup_assoc sup_left_commute sup_commute)
qed

definition local_edge_tree ::
  "(vname => bool) => ('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "local_edge_tree gs f u =
     QueryL u (\<lambda>su. Answer
       (restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> restrict_global_for gs su))"

lemma traverse_local_edge_tree:
  "traverse_rhs (local_edge_tree gs f u) \<sigma> =
   restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion> restrict_global_for gs (\<sigma> (Inl u))"
  unfolding local_edge_tree_def by simp

lemma sides_local_edge_tree_Inr:
  "sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inr ()) = bot"
  unfolding local_edge_tree_def by simp

lemma local_bot_on_locals_restrict_global [intro]:
  "local_bot_on_locals gs (restrict_global_for gs \<sigma>)"
  unfolding restrict_global_for_def local_bot_on_locals_def by simp

lemma le_restrict_global_for_when_local_bot:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes lb: "local_bot_on_locals gs a"
  assumes le: "a \<le> b"
  shows "a \<le> restrict_global_for gs b"
  unfolding restrict_global_for_def le_fun_def
proof (intro allI impI)
  fix x
  have ax: "a x \<le> b x"
    using le by (simp add: le_funD)
  show "a x \<le> (if gs x then b x else bot)"
    using ax lb unfolding local_bot_on_locals_def by (cases "gs x") auto

qed


lemma sides_inr_local_bot_unit_edge_tree:
  "local_bot_on_locals gs (sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_edge_tree_Inr
    by (rule local_bot_on_locals_restrict_global)
next
  case False
  have bot: "sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inr g) = bot"
    unfolding unit_edge_tree_def using False by simp
  show ?thesis unfolding local_bot_on_locals_def bot by simp
qed

lemma sides_inr_local_bot_local_edge_tree:
  "local_bot_on_locals gs (sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inr g))"
  unfolding local_edge_tree_def local_bot_on_locals_def by simp

lemma sides_inr_local_bot_unit_combine_tree:
  "local_bot_on_locals gs (sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_combine_tree_Inr
    by (rule local_bot_on_locals_restrict_global)
next
  case False
  have bot: "sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inr g) = bot"
    unfolding unit_combine_tree_def using False by simp
  show ?thesis unfolding local_bot_on_locals_def bot by simp
qed

lemma all_sides_local_edge_tree:
  "all_sides (local_edge_tree gs f u) \<sigma> = bot"
  unfolding local_edge_tree_def by simp

lemma sides_local_edge_tree_Inl:
  "sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inl u') = bot"
  unfolding local_edge_tree_def by simp

lemma etf_full_local_edge_tree:
  "etf_full (local_edge_tree gs f u) \<sigma> =
   restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion> restrict_global_for gs (\<sigma> (Inl u))"
  unfolding etf_full_def traverse_local_edge_tree all_sides_local_edge_tree by simp

lemma etf_collecting_full_local_edge_tree:
  "etf_collecting_full (local_edge_tree gs f u) \<sigma> =
   restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion>
   restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
  by (simp add: all_sides_local_edge_tree etf_collecting_full_def etf_full_def
      traverse_local_edge_tree)

lemma dep_aux_local_edge_tree:
  "dep_aux \<sigma>1 (local_edge_tree gs f u) = dep_aux \<sigma>2 (local_edge_tree gs f u)"
  unfolding local_edge_tree_def by simp

lemma etf_collecting_full_le_side_env:
  fixes t :: "(pp, 'g::finite, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
    and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and w :: pp
  assumes le: "etf_full t \<sigma> \<le> side_env \<sigma> w"
  shows "etf_collecting_full t \<sigma> \<le> side_env \<sigma> w"
proof -
  have "etf_collecting_full t \<sigma> = etf_full t \<sigma> \<squnion> glob_env \<sigma>"
    unfolding etf_collecting_full_def ..
  also have "\<dots> \<le> side_env \<sigma> w \<squnion> glob_env \<sigma>"
    using le by (rule sup_mono[OF _ order_refl])
  also have "\<dots> = side_env \<sigma> w"
    unfolding side_env_def by (simp add: sup_assoc sup_commute sup_left_commute)
  finally show ?thesis .
qed

lemma id_local_edge_invariant: "local_edge_invariant gs (\<lambda>env. env)"
  unfolding local_edge_invariant_def by (simp add: restrict_local_for_idem)


lemma local_edge_invariant_side_env_eq:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes inv: "local_edge_invariant gs f"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  shows "f (side_env \<sigma> u) =
    restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion>
    restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
proof -
  have lb: "local_bot_on_locals gs (\<sigma> (Inr ()))"
    using inr_slot_locals_bot_imp[OF inr] .
  have gb: "local_bot_on_locals gs (glob_env \<sigma>)"
    unfolding glob_env_unit by (rule lb)
  have rg: "local_bot_on_locals gs (restrict_global_for gs (\<sigma> (Inl u)))"
    by (rule local_bot_on_locals_restrict_global)
  have g: "local_bot_on_locals gs (restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
    by (rule local_bot_join[OF rg gb])
  have env: "side_env \<sigma> u = restrict_local_for gs (\<sigma> (Inl u)) \<squnion>
              (restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
  proof -
    have "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
      unfolding side_env_def ..
    also have "\<dots> = (restrict_local_for gs (\<sigma> (Inl u)) \<squnion> restrict_global_for gs (\<sigma> (Inl u)))
                    \<squnion> glob_env \<sigma>"
      by (simp add: restrict_local_for_global_join)
    also have "\<dots> = restrict_local_for gs (\<sigma> (Inl u)) \<squnion>
                    (restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
      by (simp add: sup_assoc)
    finally show ?thesis .
  qed
  have step: "f (restrict_local_for gs (\<sigma> (Inl u)) \<squnion>
                  (restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)) =
              restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion>
              (restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
    using local_edge_invariantD[OF inv g] .
  show ?thesis
    by (simp only: env step sup_assoc)
qed

lemma local_edge_invariant_le_etf_collecting_full:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and u :: pp
  assumes inv: "local_edge_invariant gs f"
    and lb: "local_bot_on_locals gs (\<sigma> (Inr ()))"
  shows "f (restrict_local_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) \<le>
         etf_collecting_full (local_edge_tree gs f u) \<sigma>"
proof -
  have gb: "local_bot_on_locals gs (glob_env \<sigma>)"
    using lb glob_env_unit
    by (auto intro!: glob_env_local_bot)
  have eq: "f (restrict_local_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) =
            restrict_local_for gs (f (restrict_local_for gs (\<sigma> (Inl u)))) \<squnion> glob_env \<sigma>"
    using inv gb unfolding local_edge_invariant_def by blast
  show ?thesis unfolding etf_collecting_full_local_edge_tree eq
    by (simp add: boolean_algebra_cancel.sup1 s.fun_left_comm)
qed

lemma Inl_dep_aux_local_edge_tree:
  "Inl u \<in> dep_aux \<sigma> (local_edge_tree gs f u)"
  unfolding local_edge_tree_def by simp

subsection \<open>Effectful transfer record factories\<close>

definition unit_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "unit_etf_of_transfer gs tf = \<lparr>
    etf_nop        = (\<lambda>u. unit_edge_tree gs (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. unit_edge_tree gs (apply_tf tf (EA_Assign x e)) u),
    etf_random     = (\<lambda>x u. unit_edge_tree gs (apply_tf tf (EA_Random x)) u),
    etf_assume     = (\<lambda>b u. unit_edge_tree gs (apply_tf tf (EA_Assume b)) u),
    etf_assume_not = (\<lambda>b u. unit_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (tf_enter tf xs es) u),
    etf_combine    = unit_combine_tree gs
  \<rparr>"

definition mixed_etf_edge_tree ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> edge_action \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "mixed_etf_edge_tree gs tf a u =
    (if local_edge_action gs a then local_edge_tree gs (apply_tf tf a) u
     else unit_edge_tree gs (apply_tf tf a) u)"

definition mixed_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "mixed_etf_of_transfer gs tf = \<lparr>
    etf_nop        = mixed_etf_edge_tree gs tf EA_Nop,
    etf_assign     = (\<lambda>x e. mixed_etf_edge_tree gs tf (EA_Assign x e)),
    etf_random     = (\<lambda>x. mixed_etf_edge_tree gs tf (EA_Random x)),
    etf_assume     = (\<lambda>b. mixed_etf_edge_tree gs tf (EA_Assume b)),
    etf_assume_not = (\<lambda>b. mixed_etf_edge_tree gs tf (EA_AssumeNot b)),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (tf_enter tf xs es) u),
    etf_combine    = unit_combine_tree gs
  \<rparr>"


lemma apply_etf_unit_of_transfer:
  "apply_etf (unit_etf_of_transfer gs tf) a u = unit_edge_tree gs (apply_tf tf a) u"
  unfolding unit_etf_of_transfer_def
  by (cases a)
     (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some apply_tf_EA_Check
       split: option.splits)

lemma etf_combine_unit_of_transfer:
  "etf_combine (unit_etf_of_transfer gs tf) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding unit_etf_of_transfer_def by simp

lemma apply_etf_mixed_of_transfer:
  "apply_etf (mixed_etf_of_transfer gs tf) a u = mixed_etf_edge_tree gs tf a u"
  unfolding mixed_etf_of_transfer_def mixed_etf_edge_tree_def
  by (cases a)
     (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some apply_tf_EA_Check
       split: option.splits)

lemma etf_combine_mixed_of_transfer:
  "etf_combine (mixed_etf_of_transfer gs tf) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding mixed_etf_of_transfer_def by simp

lemma mixed_etf_edge_tree_local:
  assumes "local_edge_action gs a"
  shows "mixed_etf_edge_tree gs tf a u = local_edge_tree gs (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

lemma mixed_etf_edge_tree_unit:
  assumes "\<not> local_edge_action gs a"
  shows "mixed_etf_edge_tree gs tf a u = unit_edge_tree gs (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

subsection \<open>Generic collecting soundness for tree shapes\<close>

context sound_transfer_for
begin

lemma in_gamma_unit_edge_tree_nop:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full (unit_edge_tree gs (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
proof -
  have eq: "etf_full (unit_edge_tree gs (apply_tf tf EA_Nop) u) \<sigma> =
           \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    unfolding apply_tf.simps etf_full_unit_edge_tree glob_env_unit by simp
  have st: "s \<in> \<lbrakk>etf_full (unit_edge_tree gs (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
    using s unfolding eq by simp
  show ?thesis using in_gamma_etf_collecting_full[OF st] by simp
qed

lemma in_gamma_unit_edge_tree_assign:
  fixes x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree gs (apply_tf tf (EA_Assign x e)) u) \<sigma>\<rbrakk>"
  using tf_sound_assign_forD[OF s]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_random:
  fixes x u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := v) \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree gs (apply_tf tf (EA_Random x)) u) \<sigma>\<rbrakk>"
  using tf_sound_random_forD[OF s]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_assume:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree gs (apply_tf tf (EA_Assume b)) u) \<sigma>\<rbrakk>"
  using tf_sound_assume_forD[OF s hb]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_assume_not:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "\<not> bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u) \<sigma>\<rbrakk>"
  using tf_sound_assume_not_forD[OF s hb]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_enter:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
           \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree gs (tf_enter tf xs es) u) \<sigma>\<rbrakk>"
  using tf_sound_enter_forD[OF s]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_local_edge_tree_nop:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree gs (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
proof -
  have eq: "etf_collecting_full (local_edge_tree gs (apply_tf tf EA_Nop) u) \<sigma> =
           \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    unfolding apply_tf.simps
    by (simp add: etf_collecting_full_local_edge_tree restrict_local_for_global_join
         local_edge_invariant_local_result[OF id_local_edge_invariant])
  show ?thesis using s unfolding eq glob_env_unit by simp
qed

lemma in_gamma_local_edge_tree_assign:
  fixes x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant gs (apply_tf tf (EA_Assign x e))"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree gs (apply_tf tf (EA_Assign x e)) u) \<sigma>\<rbrakk>"
proof -
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s(x := aval e s) \<in> \<lbrakk>apply_tf tf (EA_Assign x e) (side_env \<sigma> u) \<rbrakk>"
    using tf_sound_assign_forD[OF s] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_Assign x e) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assign x e)) u) \<sigma>"
  proof -
    have "apply_tf tf (EA_Assign x e) (side_env \<sigma> u) =
          restrict_local_for gs (apply_tf tf (EA_Assign x e) (restrict_local_for gs (\<sigma> (Inl u))))
          \<squnion> restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
      by (rule local_edge_invariant_side_env_eq[OF inv inr])
    also have "\<dots> = etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assign x e)) u) \<sigma>"
      by (rule etf_collecting_full_local_edge_tree[symmetric])
    finally have "apply_tf tf (EA_Assign x e) (side_env \<sigma> u) =
          etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assign x e)) u) \<sigma>" .
    then show ?thesis by simp
  qed
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_random:
  fixes x u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant gs (apply_tf tf (EA_Random x))"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := v) \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree gs (apply_tf tf (EA_Random x)) u) \<sigma>\<rbrakk>"
proof -
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s(x := v) \<in> \<lbrakk>apply_tf tf (EA_Random x) (side_env \<sigma> u) \<rbrakk>"
    using tf_sound_random_forD[OF s] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_Random x) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Random x)) u) \<sigma>"
  proof -
    have "apply_tf tf (EA_Random x) (side_env \<sigma> u) =
          restrict_local_for gs (apply_tf tf (EA_Random x) (restrict_local_for gs (\<sigma> (Inl u))))
          \<squnion> restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
      by (rule local_edge_invariant_side_env_eq[OF inv inr])
    also have "\<dots> = etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Random x)) u) \<sigma>"
      by (rule etf_collecting_full_local_edge_tree[symmetric])
    finally have "apply_tf tf (EA_Random x) (side_env \<sigma> u) =
          etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Random x)) u) \<sigma>" .
    then show ?thesis by simp
  qed
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_assume:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant gs (apply_tf tf (EA_Assume b))"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree gs (apply_tf tf (EA_Assume b)) u) \<sigma>\<rbrakk>"
proof -
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s \<in> \<lbrakk>apply_tf tf (EA_Assume b) (side_env \<sigma> u)\<rbrakk>"
    using tf_sound_assume_forD[OF s hb] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_Assume b) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assume b)) u) \<sigma>"
  proof -
    have "apply_tf tf (EA_Assume b) (side_env \<sigma> u) =
          restrict_local_for gs (apply_tf tf (EA_Assume b) (restrict_local_for gs (\<sigma> (Inl u))))
          \<squnion> restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
      by (rule local_edge_invariant_side_env_eq[OF inv inr])
    also have "\<dots> = etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assume b)) u) \<sigma>"
      by (rule etf_collecting_full_local_edge_tree[symmetric])
    finally have "apply_tf tf (EA_Assume b) (side_env \<sigma> u) =
          etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_Assume b)) u) \<sigma>" .
    then show ?thesis by simp
  qed
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_assume_not:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant gs (apply_tf tf (EA_AssumeNot b))"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "\<not> bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u) \<sigma>\<rbrakk>"
proof -
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s \<in> \<lbrakk>apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u)\<rbrakk>"
    using tf_sound_assume_not_forD[OF s hb] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u) \<sigma>"
  proof -
    have "apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u) =
          restrict_local_for gs (apply_tf tf (EA_AssumeNot b) (restrict_local_for gs (\<sigma> (Inl u))))
          \<squnion> restrict_global_for gs (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
      by (rule local_edge_invariant_side_env_eq[OF inv inr])
    also have "\<dots> = etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u) \<sigma>"
      by (rule etf_collecting_full_local_edge_tree[symmetric])
    finally have "apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u) =
          etf_collecting_full (local_edge_tree gs (apply_tf tf (EA_AssumeNot b)) u) \<sigma>" .
    then show ?thesis by simp
  qed
  show ?thesis using st le gamma_state_mono by blast
qed

end

subsection \<open>Generic effectful soundness from domain transfer\<close>

lemma sound_effectful_transfer_unit_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer_for gs tf"
  shows "sound_effectful_transfer gs (unit_etf_of_transfer gs tf)"
proof -
  interpret sound_transfer_for gs tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s \<in> \<lbrakk>etf_collecting_full (etf_nop (unit_etf_of_transfer gs tf) u) \<sigma>\<rbrakk>)"
    proof (intro allI impI ballI)
      fix u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>" and s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      show "s \<in> \<lbrakk>etf_collecting_full (etf_nop (unit_etf_of_transfer gs tf) u) \<sigma>\<rbrakk>"
        using s inr in_gamma_unit_edge_tree_nop
        by (simp add: unit_etf_of_transfer_def glob_env_unit)
    qed
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
                (etf_assign (unit_etf_of_transfer gs tf) x e u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assign)
  next
    show "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<forall>v.
              s(x := v) \<in> \<lbrakk>etf_collecting_full
                (etf_random (unit_etf_of_transfer gs tf) x u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_random)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume (unit_etf_of_transfer gs tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assume)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<not> bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume_not (unit_etf_of_transfer gs tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assume_not)

  next
    show "\<forall>xs (es::aexp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
                \<in> \<lbrakk>etf_collecting_full
                (etf_enter (unit_etf_of_transfer gs tf) xs es u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_enter)

  next
    show "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              combine_collect gs dst s t
                \<in> \<lbrakk>etf_full (etf_combine (unit_etf_of_transfer gs tf) dst cc ex) \<sigma>\<rbrakk>)"
      by (auto simp add: etf_combine_unit_of_transfer etf_full_unit_combine_tree
           intro: combine_collect_sound)
  qed
qed


lemma sound_effectful_transfer_mixed_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer_for gs tf"
  assumes loc_inv: "\<And>a. local_edge_action gs a \<Longrightarrow>
      local_edge_invariant gs (apply_tf tf a)"
  shows "sound_effectful_transfer gs (mixed_etf_of_transfer gs tf)"
proof -
  interpret sound_transfer_for gs tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s \<in> \<lbrakk>etf_collecting_full (etf_nop (mixed_etf_of_transfer gs tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: mixed_etf_of_transfer_def local_edge_action.simps
           mixed_etf_edge_tree_local glob_env_unit
           intro: in_gamma_local_edge_tree_nop)
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
                (etf_assign (mixed_etf_of_transfer gs tf) x e u) \<sigma>\<rbrakk>)"
    proof (intro allI impI ballI)
      fix x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      show "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
              (etf_assign (mixed_etf_of_transfer gs tf) x e u) \<sigma>\<rbrakk>"
        by (simp add: glob_env_unit in_gamma_local_edge_tree_assign in_gamma_unit_edge_tree_assign inr
            loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def s)
    qed
  next
    show "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<forall>v.
              s(x := v) \<in> \<lbrakk>etf_collecting_full
                (etf_random (mixed_etf_of_transfer gs tf) x u) \<sigma>\<rbrakk>)"
    proof (intro allI impI ballI)
      fix x u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store and v
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      show "s(x := v) \<in> \<lbrakk>etf_collecting_full
              (etf_random (mixed_etf_of_transfer gs tf) x u) \<sigma>\<rbrakk>"
        by (simp add: glob_env_unit in_gamma_local_edge_tree_random in_gamma_unit_edge_tree_random inr
            loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def s)
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume (mixed_etf_of_transfer gs tf) b u) \<sigma>\<rbrakk>)"
      by (simp add: glob_env_unit in_gamma_local_edge_tree_assume in_gamma_unit_edge_tree_assume
          loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<not> bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume_not (mixed_etf_of_transfer gs tf) b u) \<sigma>\<rbrakk>)"
      by (simp add: glob_env_unit in_gamma_local_edge_tree_assume_not in_gamma_unit_edge_tree_assume_not
          loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def)

  next
    show "\<forall>xs (es::aexp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
                \<in> \<lbrakk>etf_collecting_full
                (etf_enter (mixed_etf_of_transfer gs tf) xs es u) \<sigma>\<rbrakk>)"
      by (auto simp add: mixed_etf_of_transfer_def local_edge_action.simps
           mixed_etf_edge_tree_unit glob_env_unit
           intro: in_gamma_unit_edge_tree_enter)
  next
    show "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              combine_collect gs dst s t
                \<in> \<lbrakk>etf_full (etf_combine (mixed_etf_of_transfer gs tf) dst cc ex) \<sigma>\<rbrakk>)"
      by (auto simp add: etf_combine_mixed_of_transfer etf_full_unit_combine_tree
           intro: combine_collect_sound)
  qed
qed

(* Generic reachability over the solver's local dependency relation: a single
   dependency step lands in the transitive closure, which is itself transitive. *)
lemma trans_dep\<^sub>L_step_in:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> dep\<^sub>L T \<sigma> x"
  shows "y \<in> trans_dep\<^sub>L T \<sigma> x"
  using assms by blast

lemma trans_dep\<^sub>L_trans:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> trans_dep\<^sub>L T \<sigma> x"
    and "z \<in> dep\<^sub>L T \<sigma> y"
  shows "z \<in> trans_dep\<^sub>L T \<sigma> x"
  by (metis Nitpick.tranclp_unfold assms(1,2) mem_Collect_eq tranclp.trancl_into_trancl)


end
