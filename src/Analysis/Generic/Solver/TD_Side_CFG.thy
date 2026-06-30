theory TD_Side_CFG
  imports Constraint_System_Sound "Voblint_IMP2.IMP2_Globals" "TD.TD_side"
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
  monotonicity and solver preconditions live in TD_Side_Eff_Bounds and TD_Side_Eff_Soundness.
\<close>

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local \<sigma> = (\<lambda>x. if is_global x then bot else \<sigma> x)"

definition restrict_global ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global \<sigma> = (\<lambda>x. if is_global x then \<sigma> x else bot)"

lemma restrict_local_global_join:
  "restrict_local \<sigma> \<squnion> restrict_global \<sigma> = \<sigma>"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

lemma restrict_local_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_local (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_local sigma2"
  unfolding restrict_local_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_global (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_global sigma2"
  unfolding restrict_global_def le_fun_def
  by (auto dest: le_funD)


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


(* Joining the local restriction of A with the global restriction of B is the
   abstract combine: locals from A, globals from B. *)
lemma restrict_combine:
  "restrict_local A \<squnion> restrict_global B = (\<lambda>x. if is_global x then B x else A x)"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

(* The combine keeps locals from A and globals from B; its local restriction is
   restrict_local A, its global restriction restrict_global B. *)
lemma restrict_local_combine_eq:
  "restrict_local (restrict_local A \<squnion> restrict_global B) = restrict_local A"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

lemma restrict_global_combine_eq:
  "restrict_global (restrict_local A \<squnion> restrict_global B) = restrict_global B"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp


(* The abstract state combined from the local unknown at v and the join of all
   named-global unknowns (glob_env).  At 'g = unit this is the single global
   unknown \<sigma> (Inr ()) (glob_env_unit). *)
definition side_env ::
  "(pp + 'g::finite => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> glob_env \<sigma>"

(* Reading a single named global g combined with the locals at v. *)
definition side_env_g ::
  "(pp + 'g => 'a::bounded_semilattice_sup_bot abs_state) => 'g => pp => 'a abs_state"
where
  "side_env_g \<sigma> g v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr g)"

lemma side_env_eq_side_env_g:
  "side_env \<sigma> v = side_env_g \<sigma> () v"
  unfolding side_env_def side_env_g_def by (simp add: glob_env_unit)


subsection \<open>Unit-global effectful trees\<close>

text \<open>
  Unit-global effectful trees query the local program point and the unit global
  slot, compute one abstract post-state, then split that result between the local
  Answer and the global Side contribution consumed by TD_side.
\<close>

definition unit_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state => 'a abs_state)
   => (unit, 'a) edge_tf_tree"
where
  "unit_edge_tree f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res))))"

(* Procedure-return combine: query the caller local cc, the callee-exit local
   ex, and the global; reassemble locals-from-caller + globals-from-callee
   (= combine_abs) and split into a local Answer and a global Side. *)
definition unit_combine_tree ::
  "pp => pp => (pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "unit_combine_tree cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res)))))"

lemma traverse_unit_edge_tree:
  "traverse_rhs (unit_edge_tree f u) \<sigma> = restrict_local (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_edge_tree_def by (simp add: Let_def)

(* The tree's single Side contribution to the global slot is the global
   restriction of the result. *)
lemma sides_unit_edge_tree_Inr:
  "sides_of_rhs (unit_edge_tree f u) \<sigma> (Inr ()) =
   restrict_global (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding unit_edge_tree_def by (simp add: Let_def)

(* Reassembling the tree's local Answer and global Side recovers the full result. *)
lemma etf_full_unit_edge_tree:
  "etf_full (unit_edge_tree f u) \<sigma> = f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def
  by (simp add: all_sides_eq_sides_Inr_unit traverse_unit_edge_tree sides_unit_edge_tree_Inr
        restrict_local_global_join)

(* The unit-global combine tree returns the caller's locals as its Answer. *)
lemma traverse_unit_combine_tree:
  "traverse_rhs (unit_combine_tree cc ex) \<sigma> = restrict_local (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))"
  unfolding unit_combine_tree_def by (simp add: Let_def restrict_local_combine_eq)

(* The unit-global combine tree contributes the callee-exit globals to the global slot. *)
lemma sides_unit_combine_tree_Inr:
  "sides_of_rhs (unit_combine_tree cc ex) \<sigma> (Inr ()) =
   restrict_global (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
  unfolding unit_combine_tree_def by (simp add: Let_def restrict_global_combine_eq)

(* The unit-global combine tree reassembles to the fixed abstract combine. *)
lemma etf_full_unit_combine_tree:
  "etf_full (unit_combine_tree cc ex) \<sigma>
   = \<langle>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())|\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rangle>"
  unfolding etf_full_def unit_combine_tree_def
  by (simp add: all_sides_eq_sides_Inr_unit[unfolded unit_combine_tree_def] Let_def
        restrict_local_combine_eq restrict_global_combine_eq restrict_combine combine_abs_def)


subsection \<open>Local-only effectful edge trees\<close>

text \<open>
  When an edge transfer preserves globals and only reads locals, the tree can
  query the source local unknown without @{term QueryG}.  Soundness and
  post-fixpoint bounds use @{const etf_full} joined with @{const glob_env}.
\<close>

definition local_bot_on_locals ::
  "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> bool"
where
  "local_bot_on_locals g \<longleftrightarrow> (\<forall>x. \<not> is_global x \<longrightarrow> g x = bot)"

lemma local_bot_join:
  assumes "local_bot_on_locals (a :: 'a::bounded_semilattice_sup_bot abs_state)"
    and "local_bot_on_locals b"
  shows "local_bot_on_locals (a \<squnion> b)"
  using assms unfolding local_bot_on_locals_def by (auto simp: sup_fun_def)

lemma glob_env_local_bot:
  fixes \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes inr: "\<And>g. local_bot_on_locals (\<sigma> (Inr g))"
  shows "local_bot_on_locals (glob_env \<sigma>)"
  unfolding local_bot_on_locals_def glob_env_def abs_join_set_def
proof (clarify)
  fix x
  assume ng: "\<not> is_global x"
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

definition local_edge_invariant ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> bool"
where
  "local_edge_invariant f \<longleftrightarrow>
     (\<forall>su g. local_bot_on_locals g \<longrightarrow>
        f (restrict_local su \<squnion> g) =
        restrict_local (f (restrict_local su)) \<squnion> g)"

lemma local_edge_invariant_local_result:
  assumes inv: "local_edge_invariant f"
  shows "restrict_local (f (restrict_local su)) = f (restrict_local su)"
proof -
  have "f (restrict_local su \<squnion> bot) = restrict_local (f (restrict_local su)) \<squnion> bot"
    using inv unfolding local_edge_invariant_def local_bot_on_locals_def
    by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
  then show ?thesis by simp
qed

lemma local_edge_invariant_comp:
  assumes f: "local_edge_invariant f"
    and h: "local_edge_invariant h"
  shows "local_edge_invariant (\<lambda>su. f (h su))"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals g"
  have h_step: "h (restrict_local su \<squnion> g) = restrict_local (h (restrict_local su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  have h_local: "restrict_local (h (restrict_local su)) = h (restrict_local su)"
    using local_edge_invariant_local_result[OF h, of su] .
  show "f (h (restrict_local su \<squnion> g)) = restrict_local (f (h (restrict_local su))) \<squnion> g"
    using f lb h_step h_local unfolding local_edge_invariant_def by metis
qed

lemma local_edge_invariant_sup:
  assumes f: "local_edge_invariant f"
    and h: "local_edge_invariant h"
  shows "local_edge_invariant (\<lambda>su. f su \<squnion> h su)"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals g"
  have f_step: "f (restrict_local su \<squnion> g) = restrict_local (f (restrict_local su)) \<squnion> g"
    using f lb unfolding local_edge_invariant_def by blast
  have h_step: "h (restrict_local su \<squnion> g) = restrict_local (h (restrict_local su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  show "f (restrict_local su \<squnion> g) \<squnion> h (restrict_local su \<squnion> g) =
        restrict_local (f (restrict_local su) \<squnion> h (restrict_local su)) \<squnion> g"
    using f_step h_step lb
    unfolding restrict_local_def local_bot_on_locals_def sup_fun_def
    by (auto simp: fun_eq_iff sup_assoc sup_left_commute sup_commute)
qed

definition local_env_independent ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> bool"
where
  "local_env_independent f \<longleftrightarrow>
     (\<forall>su g. local_bot_on_locals g \<longrightarrow>
        f (su \<squnion> g) = f (restrict_local su \<squnion> g))"

definition local_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "local_edge_tree f u =
     QueryL u (\<lambda>su. Answer
       (restrict_local (f (restrict_local su)) \<squnion> restrict_global su))"

lemma traverse_local_edge_tree:
  "traverse_rhs (local_edge_tree f u) \<sigma> =
   restrict_local (f (restrict_local (\<sigma> (Inl u)))) \<squnion> restrict_global (\<sigma> (Inl u))"
  unfolding local_edge_tree_def by simp

lemma sides_local_edge_tree_Inr:
  "sides_of_rhs (local_edge_tree f u) \<sigma> (Inr ()) = bot"
  unfolding local_edge_tree_def by simp

lemma local_bot_on_locals_restrict_global:
  "local_bot_on_locals (restrict_global \<sigma>)"
  unfolding restrict_global_def local_bot_on_locals_def by simp

lemma le_restrict_global_when_local_bot:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes lb: "local_bot_on_locals a"
  assumes le: "a \<le> b"
  shows "a \<le> restrict_global b"
  unfolding restrict_global_def le_fun_def
proof (intro allI impI)
  fix x
  have ax: "a x \<le> b x"
    using le by (simp add: le_funD)
  show "a x \<le> (if is_global x then b x else bot)"
    using ax lb unfolding local_bot_on_locals_def by (cases "is_global x") auto

qed


lemma sides_inr_local_bot_unit_edge_tree:
  "local_bot_on_locals (sides_of_rhs (unit_edge_tree f u) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_edge_tree_Inr
    by (rule local_bot_on_locals_restrict_global)
next
  case False
  have bot: "sides_of_rhs (unit_edge_tree f u) \<sigma> (Inr g) = bot"
    unfolding unit_edge_tree_def using False by simp
  show ?thesis unfolding local_bot_on_locals_def bot by simp
qed

lemma sides_inr_local_bot_local_edge_tree:
  "local_bot_on_locals (sides_of_rhs (local_edge_tree f u) \<sigma> (Inr g))"
  unfolding local_edge_tree_def local_bot_on_locals_def by simp

lemma sides_inr_local_bot_unit_combine_tree:
  "local_bot_on_locals (sides_of_rhs (unit_combine_tree cc ex) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_combine_tree_Inr
    by (rule local_bot_on_locals_restrict_global)
next
  case False
  have bot: "sides_of_rhs (unit_combine_tree cc ex) \<sigma> (Inr g) = bot"
    unfolding unit_combine_tree_def using False by simp
  show ?thesis unfolding local_bot_on_locals_def bot by simp
qed

lemma all_sides_local_edge_tree:
  "all_sides (local_edge_tree f u) \<sigma> = bot"
  unfolding local_edge_tree_def by simp

lemma sides_local_edge_tree_Inl:
  "sides_of_rhs (local_edge_tree f u) \<sigma> (Inl u') = bot"
  unfolding local_edge_tree_def by simp

lemma etf_full_local_edge_tree:
  "etf_full (local_edge_tree f u) \<sigma> =
   restrict_local (f (restrict_local (\<sigma> (Inl u)))) \<squnion> restrict_global (\<sigma> (Inl u))"
  unfolding etf_full_def traverse_local_edge_tree all_sides_local_edge_tree by simp

lemma etf_collecting_full_local_edge_tree:
  "etf_collecting_full (local_edge_tree f u) \<sigma> =
   restrict_local (f (restrict_local (\<sigma> (Inl u)))) \<squnion>
   restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
  by (simp add: all_sides_local_edge_tree etf_collecting_full_def etf_full_def
      traverse_local_edge_tree)

lemma dep_aux_local_edge_tree:
  "dep_aux \<sigma>1 (local_edge_tree f u) = dep_aux \<sigma>2 (local_edge_tree f u)"
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

lemma id_local_edge_invariant: "local_edge_invariant (\<lambda>env. env)"
  unfolding local_edge_invariant_def by (auto simp: restrict_local_def sup_fun_def)


lemma local_edge_invariant_side_env_eq:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes inv: "local_edge_invariant f"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "f (side_env \<sigma> u) =
    restrict_local (f (restrict_local (\<sigma> (Inl u)))) \<squnion>
    restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
proof -
  have lb: "local_bot_on_locals (\<sigma> (Inr ()))"
    using inr unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto
  have gb: "local_bot_on_locals (glob_env \<sigma>)"
    unfolding glob_env_unit
    using inr
    by (auto intro!: glob_env_local_bot simp: inr_slot_locals_bot_def local_bot_on_locals_def)
  have rg: "local_bot_on_locals (restrict_global (\<sigma> (Inl u)))"
    by (simp add: local_bot_on_locals_def restrict_global_def)
  have g: "local_bot_on_locals (restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
    by (rule local_bot_join[OF rg gb])
  have env: "side_env \<sigma> u = restrict_local (\<sigma> (Inl u)) \<squnion>
              restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
    unfolding side_env_def by (simp add: restrict_local_global_join glob_env_unit)
  show ?thesis
    using inv g env
    unfolding local_edge_invariant_def
    by (metis sup_assoc)
qed

lemma local_edge_invariant_le_etf_collecting_full:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and u :: pp
  assumes inv: "local_edge_invariant f"
    and lb: "local_bot_on_locals (\<sigma> (Inr ()))"
  shows "f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) \<le>
         etf_collecting_full (local_edge_tree f u) \<sigma>"
proof -
  have gb: "local_bot_on_locals (glob_env \<sigma>)"
    using lb glob_env_unit
    by (auto intro!: glob_env_local_bot)
  have eq: "f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) =
            restrict_local (f (restrict_local (\<sigma> (Inl u)))) \<squnion> glob_env \<sigma>"
    using inv gb unfolding local_edge_invariant_def by blast
  show ?thesis unfolding etf_collecting_full_local_edge_tree eq
    by (simp add: boolean_algebra_cancel.sup1 s.fun_left_comm)
qed

lemma Inl_dep_aux_local_edge_tree:
  "Inl u \<in> dep_aux \<sigma> (local_edge_tree f u)"
  unfolding local_edge_tree_def by simp

lemma inr_slot_locals_bot_imp:
  "inr_slot_locals_bot \<sigma> \<Longrightarrow> local_bot_on_locals (\<sigma> (Inr g))"
  unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto

lemma local_env_independent_side_env:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and u :: pp
  assumes ind: "local_env_independent f"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "f (side_env \<sigma> u) = f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
proof -
  have gb: "local_bot_on_locals (glob_env \<sigma>)"
    using inr glob_env_local_bot inr_slot_locals_bot_imp by blast
  show ?thesis
    using ind[unfolded local_env_independent_def, rule_format, OF gb]
    unfolding side_env_def by simp
qed

subsection \<open>Effectful transfer record factories\<close>

definition unit_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "unit_etf_of_transfer tf = \<lparr>
    etf_nop        = (\<lambda>u. unit_edge_tree (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. unit_edge_tree (apply_tf tf (EA_Assign x e)) u),
    etf_assume     = (\<lambda>b u. unit_edge_tree (apply_tf tf (EA_Assume b)) u),
    etf_assume_not = (\<lambda>b u. unit_edge_tree (apply_tf tf (EA_AssumeNot b)) u),
    etf_enter      = (\<lambda>u. unit_edge_tree (apply_tf tf EA_Enter) u),
    etf_combine    = unit_combine_tree
  \<rparr>"

definition mixed_etf_edge_tree ::
  "'a::sound_domain domain_transfer \<Rightarrow> edge_action \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "mixed_etf_edge_tree tf a u =
    (if local_edge_action a then local_edge_tree (apply_tf tf a) u
     else unit_edge_tree (apply_tf tf a) u)"

definition mixed_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "mixed_etf_of_transfer tf = \<lparr>
    etf_nop        = mixed_etf_edge_tree tf EA_Nop,
    etf_assign     = (\<lambda>x e. mixed_etf_edge_tree tf (EA_Assign x e)),
    etf_assume     = (\<lambda>b. mixed_etf_edge_tree tf (EA_Assume b)),
    etf_assume_not = (\<lambda>b. mixed_etf_edge_tree tf (EA_AssumeNot b)),
    etf_enter      = mixed_etf_edge_tree tf EA_Enter,
    etf_combine    = unit_combine_tree
  \<rparr>"

lemma apply_etf_unit_of_transfer:
  "apply_etf (unit_etf_of_transfer tf) a u = unit_edge_tree (apply_tf tf a) u"
  unfolding unit_etf_of_transfer_def by (cases a) simp_all

lemma etf_combine_unit_of_transfer:
  "etf_combine (unit_etf_of_transfer tf) cc ex = unit_combine_tree cc ex"
  unfolding unit_etf_of_transfer_def by simp

lemma apply_etf_mixed_of_transfer:
  "apply_etf (mixed_etf_of_transfer tf) a u = mixed_etf_edge_tree tf a u"
  unfolding mixed_etf_of_transfer_def by (cases a) simp_all

lemma etf_combine_mixed_of_transfer:
  "etf_combine (mixed_etf_of_transfer tf) cc ex = unit_combine_tree cc ex"
  unfolding mixed_etf_of_transfer_def by simp

lemma mixed_etf_edge_tree_local:
  assumes "local_edge_action a"
  shows "mixed_etf_edge_tree tf a u = local_edge_tree (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

lemma mixed_etf_edge_tree_unit:
  assumes "\<not> local_edge_action a"
  shows "mixed_etf_edge_tree tf a u = unit_edge_tree (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

subsection \<open>Generic collecting soundness for tree shapes\<close>

context sound_transfer
begin

lemma in_gamma_unit_edge_tree_nop:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full (unit_edge_tree (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
proof -
  have eq: "etf_full (unit_edge_tree (apply_tf tf EA_Nop) u) \<sigma> =
           \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    unfolding apply_tf.simps etf_full_unit_edge_tree glob_env_unit by simp
  have st: "s \<in> \<lbrakk>etf_full (unit_edge_tree (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
    using s unfolding eq by simp
  show ?thesis using in_gamma_etf_collecting_full[OF st] by simp
qed

lemma in_gamma_unit_edge_tree_assign:
  fixes x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree (apply_tf tf (EA_Assign x e)) u) \<sigma>\<rbrakk>"
  using tf_sound_assign[rule_format, OF s]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_assume:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree (apply_tf tf (EA_Assume b)) u) \<sigma>\<rbrakk>"
  using tf_sound_assume[rule_format, OF s hb]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_assume_not:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "\<not> bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree (apply_tf tf (EA_AssumeNot b)) u) \<sigma>\<rbrakk>"
  using tf_sound_assume_not[rule_format, OF s hb]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_unit_edge_tree_enter:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>etf_collecting_full
           (unit_edge_tree (apply_tf tf EA_Enter) u) \<sigma>\<rbrakk>"
  using tf_sound_enter[rule_format, OF s]
  by (auto simp add: etf_full_unit_edge_tree glob_env_unit intro: in_gamma_etf_collecting_full)

lemma in_gamma_local_edge_tree:
  fixes f :: "'a abs_state \<Rightarrow> 'a abs_state"
    and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant f"
  assumes ind: "local_env_independent f"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes gamma: "s \<in> \<lbrakk>f (side_env \<sigma> u)\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full (local_edge_tree f u) \<sigma>\<rbrakk>"
proof -
  have lb: "local_bot_on_locals (\<sigma> (Inr ()))"
    using inr_slot_locals_bot_imp[OF inr] .
  have env: "f (side_env \<sigma> u) =
              f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)"
    using local_env_independent_side_env[OF ind inr] .
  have st: "s \<in> \<lbrakk>f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>)\<rbrakk>"
    using gamma env by simp
  have le: "f (restrict_local (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) \<le>
            etf_collecting_full (local_edge_tree f u) \<sigma>"
    by (rule local_edge_invariant_le_etf_collecting_full[of f \<sigma> u, OF inv lb])
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_nop:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree (apply_tf tf EA_Nop) u) \<sigma>\<rbrakk>"
proof -
  have eq: "etf_collecting_full (local_edge_tree (apply_tf tf EA_Nop) u) \<sigma> =
           \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    unfolding apply_tf.simps
    by (simp add: etf_collecting_full_local_edge_tree restrict_local_global_join
         local_edge_invariant_local_result[OF id_local_edge_invariant])
  show ?thesis using s unfolding eq glob_env_unit by simp
qed

lemma in_gamma_local_edge_tree_assign:
  fixes x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant (apply_tf tf (EA_Assign x e))"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>"
  shows "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree (apply_tf tf (EA_Assign x e)) u) \<sigma>\<rbrakk>"
proof -
  have lb: "local_bot_on_locals (\<sigma> (Inr ()))"
    using inr unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s(x := aval e s) \<in> \<lbrakk>apply_tf tf (EA_Assign x e) (side_env \<sigma> u) \<rbrakk>"
    using tf_sound_assign[rule_format, OF s] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_Assign x e) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree (apply_tf tf (EA_Assign x e)) u) \<sigma>"
    using local_edge_invariant_side_env_eq[OF inv inr]
      local_edge_invariant_le_etf_collecting_full[of "apply_tf tf (EA_Assign x e)" \<sigma> u, OF inv lb]
    unfolding apply_tf.simps etf_collecting_full_local_edge_tree by simp
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_assume:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant (apply_tf tf (EA_Assume b))"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree (apply_tf tf (EA_Assume b)) u) \<sigma>\<rbrakk>"
proof -
  have lb: "local_bot_on_locals (\<sigma> (Inr ()))"
    using inr unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s \<in> \<lbrakk>apply_tf tf (EA_Assume b) (side_env \<sigma> u)\<rbrakk>"
    using tf_sound_assume[rule_format, OF s hb] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_Assume b) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree (apply_tf tf (EA_Assume b)) u) \<sigma>"
    using local_edge_invariant_side_env_eq[OF inv inr]
      local_edge_invariant_le_etf_collecting_full[of "apply_tf tf (EA_Assume b)" \<sigma> u, OF inv lb]
    unfolding apply_tf.simps etf_collecting_full_local_edge_tree by simp
  show ?thesis using st le gamma_state_mono by blast
qed

lemma in_gamma_local_edge_tree_assume_not:
  fixes b u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
  assumes inv: "local_edge_invariant (apply_tf tf (EA_AssumeNot b))"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>" and hb: "\<not> bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full
           (local_edge_tree (apply_tf tf (EA_AssumeNot b)) u) \<sigma>\<rbrakk>"
proof -
  have lb: "local_bot_on_locals (\<sigma> (Inr ()))"
    using inr unfolding inr_slot_locals_bot_def local_bot_on_locals_def by auto
  have env: "side_env \<sigma> u = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
    by (simp add: side_env_def glob_env_unit)
  have st: "s \<in> \<lbrakk>apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u)\<rbrakk>"
    using tf_sound_assume_not[rule_format, OF s hb] unfolding env apply_tf.simps by simp
  have le: "apply_tf tf (EA_AssumeNot b) (side_env \<sigma> u) \<le>
            etf_collecting_full (local_edge_tree (apply_tf tf (EA_AssumeNot b)) u) \<sigma>"
    using local_edge_invariant_side_env_eq[OF inv inr]
      local_edge_invariant_le_etf_collecting_full[of "apply_tf tf (EA_AssumeNot b)" \<sigma> u, OF inv lb]
    unfolding apply_tf.simps etf_collecting_full_local_edge_tree by simp
  show ?thesis using st le gamma_state_mono by blast
qed

end

subsection \<open>Generic effectful soundness from domain transfer\<close>

lemma sound_effectful_transfer_unit_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer tf"
  shows "sound_effectful_transfer (unit_etf_of_transfer tf)"
proof -
  interpret sound_transfer tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s \<in> \<lbrakk>etf_collecting_full (etf_nop (unit_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
    proof (intro allI impI ballI)
      fix u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume inr: "inr_slot_locals_bot \<sigma>" and s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      show "s \<in> \<lbrakk>etf_collecting_full (etf_nop (unit_etf_of_transfer tf) u) \<sigma>\<rbrakk>"
        using s inr in_gamma_unit_edge_tree_nop
        by (simp add: unit_etf_of_transfer_def glob_env_unit)
    qed
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
                (etf_assign (unit_etf_of_transfer tf) x e u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assign)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume (unit_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assume)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<not> bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume_not (unit_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_assume_not)

  next
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              enter_state s \<in> \<lbrakk>etf_collecting_full
                (etf_enter (unit_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: unit_etf_of_transfer_def glob_env_unit
           intro: in_gamma_unit_edge_tree_enter)

  next
    show "\<forall>cc ex \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              <s|t> \<in> \<lbrakk>etf_full (etf_combine (unit_etf_of_transfer tf) cc ex) \<sigma>\<rbrakk>)"
      by (auto simp add: etf_combine_unit_of_transfer etf_full_unit_combine_tree
           intro: combine_states_sound)
  qed
qed

lemma sound_effectful_transfer_mixed_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer tf"
  assumes loc_inv: "\<And>a. local_edge_action a \<Longrightarrow>
      local_edge_invariant (apply_tf tf a)"
  shows "sound_effectful_transfer (mixed_etf_of_transfer tf)"
proof -
  interpret sound_transfer tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s \<in> \<lbrakk>etf_collecting_full (etf_nop (mixed_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: mixed_etf_of_transfer_def local_edge_action.simps
           mixed_etf_edge_tree_local glob_env_unit
           intro: in_gamma_local_edge_tree_nop)
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
                (etf_assign (mixed_etf_of_transfer tf) x e u) \<sigma>\<rbrakk>)"
    proof (intro allI impI ballI)
      fix x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume inr: "inr_slot_locals_bot \<sigma>"
        and s: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      show "s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
              (etf_assign (mixed_etf_of_transfer tf) x e u) \<sigma>\<rbrakk>"
        by (simp add: glob_env_unit in_gamma_local_edge_tree_assign in_gamma_unit_edge_tree_assign inr
            loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def s)
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume (mixed_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (simp add: glob_env_unit in_gamma_local_edge_tree_assume in_gamma_unit_edge_tree_assume
          loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<not> bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume_not (mixed_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (simp add: glob_env_unit in_gamma_local_edge_tree_assume_not in_gamma_unit_edge_tree_assume_not
          loc_inv mixed_etf_edge_tree_def mixed_etf_of_transfer_def)

  next
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              enter_state s \<in> \<lbrakk>etf_collecting_full
                (etf_enter (mixed_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: mixed_etf_of_transfer_def local_edge_action.simps
           mixed_etf_edge_tree_unit glob_env_unit
           intro: in_gamma_unit_edge_tree_enter)
  next
    show "\<forall>cc ex \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              <s|t> \<in> \<lbrakk>etf_full (etf_combine (mixed_etf_of_transfer tf) cc ex) \<sigma>\<rbrakk>)"
      by (auto simp add: etf_combine_mixed_of_transfer etf_full_unit_combine_tree
           intro: combine_states_sound)
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
