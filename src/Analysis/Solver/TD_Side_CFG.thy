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


subsection \<open>Unit-global pure-transfer trees\<close>

text \<open>
  pure_edge_tree builds the unit-global effectful tree used by domains whose
  concrete transfer is still described by a domain_transfer: query the local
  state at u, query the unit global slot, apply the transfer to their join, then
  split the result into a local Answer and a global Side.
\<close>

definition pure_edge_tree ::
  "'a::bounded_semilattice_sup_bot domain_transfer => edge_action => (unit, 'a) edge_tf_tree"
where
  "pure_edge_tree tf a u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = apply_tf tf a (su \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res))))"

(* Procedure-return combine: query the caller local cc, the callee-exit local
   ex, and the global; reassemble locals-from-caller + globals-from-callee
   (= combine_abs) and split into a local Answer and a global Side. *)
definition pure_combine_tree ::
  "pp => pp => (pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "pure_combine_tree cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res)))))"

definition pure_effectful_transfer ::
  "'a::bounded_semilattice_sup_bot domain_transfer =>
   (unit, 'a) effectful_domain_transfer => bool"
where
  "pure_effectful_transfer tf etf \<longleftrightarrow>
     etf_nop etf = pure_edge_tree tf EA_Nop \<and>
     etf_assign etf = (\<lambda>x e. pure_edge_tree tf (EA_Assign x e)) \<and>
     etf_assume etf = (\<lambda>b. pure_edge_tree tf (EA_Assume b)) \<and>
     etf_assume_not etf = (\<lambda>b. pure_edge_tree tf (EA_AssumeNot b)) \<and>
     etf_enter etf = pure_edge_tree tf EA_Enter \<and>
     etf_combine etf = pure_combine_tree"

lemma pure_effectful_transfer_apply:
  assumes "pure_effectful_transfer tf etf"
  shows "apply_etf etf a u = pure_edge_tree tf a u"
  using assms unfolding pure_effectful_transfer_def
  by (cases a) simp_all

lemma pure_effectful_transfer_combine:
  assumes "pure_effectful_transfer tf etf"
  shows "etf_combine etf = pure_combine_tree"
  using assms unfolding pure_effectful_transfer_def by simp



lemma traverse_pure_edge_tree:
  "traverse_rhs (pure_edge_tree tf a u) \<sigma> =
   restrict_local (apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding pure_edge_tree_def by (simp add: Let_def)

(* The tree's single Side contribution to the global slot is the global
   restriction of the pure result. *)
lemma sides_pure_edge_tree_Inr:
  "sides_of_rhs (pure_edge_tree tf a u) \<sigma> (Inr ()) =
   restrict_global (apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding pure_edge_tree_def by (simp add: Let_def)

(* Reassembling the tree's local Answer and global Side recovers the full pure
   result -- restrict_local and restrict_global join back to the original. *)
lemma etf_full_pure_edge_tree:
  "etf_full (pure_edge_tree tf a u) \<sigma> = apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def
  by (simp add: all_sides_eq_sides_Inr_unit traverse_pure_edge_tree sides_pure_edge_tree_Inr
        restrict_local_global_join)




(* The unit-global combine tree returns the caller's locals as its Answer. *)
lemma traverse_pure_combine_tree:
  "traverse_rhs (pure_combine_tree cc ex) \<sigma> = restrict_local (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))"
  unfolding pure_combine_tree_def by (simp add: Let_def restrict_local_combine_eq)

(* The unit-global combine tree contributes the callee-exit globals to the global slot. *)
lemma sides_pure_combine_tree_Inr:
  "sides_of_rhs (pure_combine_tree cc ex) \<sigma> (Inr ()) =
   restrict_global (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
  unfolding pure_combine_tree_def by (simp add: Let_def restrict_global_combine_eq)

(* The unit-global combine tree reassembles to the fixed abstract combine. *)
lemma etf_full_pure_combine_tree:
  "etf_full (pure_combine_tree cc ex) \<sigma>
   = \<langle>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())|\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rangle>"
  unfolding etf_full_def pure_combine_tree_def
  by (simp add: all_sides_eq_sides_Inr_unit[unfolded pure_combine_tree_def] Let_def
        restrict_local_combine_eq restrict_global_combine_eq restrict_combine combine_abs_def)

text \<open>
  A pure-transfer-shaped effectful record satisfies the effectful soundness
  contract whenever the underlying domain_transfer satisfies the pure soundness
  contract.
\<close>

lemma sound_transfer_imp_sound_effectful_pure_etf:
  assumes st_axioms: "sound_transfer tf"
  assumes shape: "pure_effectful_transfer tf etf"
  shows "sound_effectful_transfer etf"
proof -
  interpret st: sound_transfer tf by (rule st_axioms)
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            s \<in> \<lbrakk>etf_full (etf_nop etf u) \<sigma>\<rbrakk>"
      using shape by (simp add: pure_effectful_transfer_def etf_full_pure_edge_tree)
  next
    show "\<forall>x e u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            s(x := aval e s) \<in> \<lbrakk>etf_full (etf_assign etf x e u) \<sigma>\<rbrakk>"
    proof (intro allI ballI)
      fix x e and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume m: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      have eq: "etf_full (etf_assign etf x e u) \<sigma>
                  = tf_assign tf x e (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        using shape by (simp add: pure_effectful_transfer_def etf_full_pure_edge_tree)
      show "s(x := aval e s) \<in> \<lbrakk>etf_full (etf_assign etf x e u) \<sigma>\<rbrakk>"
        unfolding eq using st.tf_sound_assign m by blast
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            bval b s \<longrightarrow> s \<in> \<lbrakk>etf_full (etf_assume etf b u) \<sigma>\<rbrakk>"
    proof (intro allI ballI impI)
      fix b :: bexp and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume m: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>" and bv: "bval b s"
      have eq: "etf_full (etf_assume etf b u) \<sigma>
                  = tf_assume tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        using shape by (simp add: pure_effectful_transfer_def etf_full_pure_edge_tree)
      show "s \<in> \<lbrakk>etf_full (etf_assume etf b u) \<sigma>\<rbrakk>"
        unfolding eq using st.tf_sound_assume m bv by blast
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<not> bval b s \<longrightarrow> s \<in> \<lbrakk>etf_full (etf_assume_not etf b u) \<sigma>\<rbrakk>"
    proof (intro allI ballI impI)
      fix b :: bexp and u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume m: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>" and bv: "\<not> bval b s"
      have eq: "etf_full (etf_assume_not etf b u) \<sigma>
                  = tf_assume_not tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        using shape by (simp add: pure_effectful_transfer_def etf_full_pure_edge_tree)
      show "s \<in> \<lbrakk>etf_full (etf_assume_not etf b u) \<sigma>\<rbrakk>"
        unfolding eq using st.tf_sound_assume_not m bv by blast
    qed
  next
    show "\<forall>u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            enter_state s \<in> \<lbrakk>etf_full (etf_enter etf u) \<sigma>\<rbrakk>"
    proof (intro allI ballI)
      fix u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s :: store
      assume m: "s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      have eq: "etf_full (etf_enter etf u) \<sigma>
                  = tf_enter tf (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        using shape by (simp add: pure_effectful_transfer_def etf_full_pure_edge_tree)
      show "enter_state s \<in> \<lbrakk>etf_full (etf_enter etf u) \<sigma>\<rbrakk>"
        unfolding eq using st.tf_sound_enter m by blast
    qed
  next
    show "\<forall>cc ex \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              <s|t> \<in> \<lbrakk>etf_full (etf_combine etf cc ex) \<sigma>\<rbrakk>"
    proof (intro allI ballI)
      fix cc ex :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state" and s t :: store
      assume sc: "s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>"
         and te: "t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      have eq: "etf_full (etf_combine etf cc ex) \<sigma>
                  = \<langle>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())|\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rangle>"
        using shape by (simp add: pure_effectful_transfer_def etf_full_pure_combine_tree)
      show "<s|t> \<in> \<lbrakk>etf_full (etf_combine etf cc ex) \<sigma>\<rbrakk>"
        unfolding eq using combine_states_sound[OF sc te] .
    qed
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
