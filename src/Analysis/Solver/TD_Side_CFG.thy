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

  The interprocedural strategy tree and transfer functions live in TD_Side_IP_Tree;
  monotonicity and solver preconditions live in TD_Side_IP_Eff_Bounds and TD_Side_IP_Eff_Soundness.
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
  by (auto dest: le_funD simp: bot_least)

lemma restrict_global_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_global (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_global sigma2"
  unfolding restrict_global_def le_fun_def
  by (auto dest: le_funD simp: bot_least)


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


(* The abstract state combined from the local unknown at v and the single
   global unknown. *)
definition side_env ::
  "(pp + unit => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr ())"

(* Generalisation of side_env to named globals: side_env_g \<sigma> g v = \<sigma>(Inl v) \<squnion> \<sigma>(Inr g). *)
definition side_env_g ::
  "(pp + 'g => 'a::bounded_semilattice_sup_bot abs_state) => 'g => pp => 'a abs_state"
where
  "side_env_g \<sigma> g v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr g)"

lemma side_env_eq_side_env_g:
  "side_env \<sigma> v = side_env_g \<sigma> () v"
  unfolding side_env_def side_env_g_def by simp


subsection \<open>Pure-domain effectful transfer shim\<close>

text \<open>
  pure_edge_tree wraps a domain_transfer into an effectful tree: query the
  local state at u, query the single global unknown (), apply the pure TF to
  their join, split the result into a local Answer and a global Side.

  etf_from_tf lifts a domain_transfer to an effectful_domain_transfer using
  this shim for every action.  apply_etf (etf_from_tf tf) a u = pure_edge_tree tf a u.
\<close>

definition pure_edge_tree ::
  "'a::bounded_semilattice_sup_bot domain_transfer => edge_action => (unit, 'a) edge_tf_tree"
where
  "pure_edge_tree tf a u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = apply_tf tf a (su \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res))))"

(* Shim for the procedure-return combine: query the caller local cc, the
   callee-exit local ex, and the global; reassemble locals-from-caller +
   globals-from-callee (= combine_abs) and split into a local Answer and a
   global Side -- the fixed combine_abs default, lifted into the effectful form. *)
definition pure_combine_tree ::
  "pp => pp => (pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "pure_combine_tree cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
       Side () (restrict_global res)
         (Answer (restrict_local res)))))"

definition etf_from_tf ::
  "'a::bounded_semilattice_sup_bot domain_transfer => (unit, 'a) effectful_domain_transfer"
where
  "etf_from_tf tf = \<lparr>
    etf_nop        = pure_edge_tree tf EA_Nop,
    etf_assign     = \<lambda>x e. pure_edge_tree tf (EA_Assign x e),
    etf_assume     = \<lambda>b. pure_edge_tree tf (EA_Assume b),
    etf_assume_not = \<lambda>b. pure_edge_tree tf (EA_AssumeNot b),
    etf_enter      = pure_edge_tree tf EA_Enter,
    etf_combine    = pure_combine_tree
  \<rparr>"

lemma etf_combine_from_tf [simp]:
  "etf_combine (etf_from_tf tf) = pure_combine_tree"
  by (simp add: etf_from_tf_def)

lemma apply_etf_from_tf [simp]:
  "apply_etf (etf_from_tf tf) a u = pure_edge_tree tf a u"
  by (cases a) (simp_all add: etf_from_tf_def)

lemma traverse_pure_edge_tree:
  "traverse_rhs (pure_edge_tree tf a u) \<sigma> =
   restrict_local (apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding pure_edge_tree_def by (simp add: Let_def)

(* The shim's single Side contribution to the global slot is the global
   restriction of the pure result. *)
lemma sides_pure_edge_tree_Inr:
  "sides_of_rhs (pure_edge_tree tf a u) \<sigma> (Inr ()) =
   restrict_global (apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  unfolding pure_edge_tree_def by (simp add: Let_def)

(* Reassembling the shim's local Answer and global Side recovers the full pure
   result -- restrict_local and restrict_global join back to the original. *)
lemma etf_full_pure_edge_tree:
  "etf_full (pure_edge_tree tf a u) \<sigma> = apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def
  by (simp add: all_sides_eq_sides_Inr_unit traverse_pure_edge_tree sides_pure_edge_tree_Inr
        restrict_local_global_join)

lemma etf_full_etf_from_tf:
  "etf_full (apply_etf (etf_from_tf tf) a u) \<sigma> = apply_tf tf a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  by (simp add: apply_etf_from_tf etf_full_pure_edge_tree)

(* The shim's combine tree returns the caller's locals as its Answer. *)
lemma traverse_pure_combine_tree:
  "traverse_rhs (pure_combine_tree cc ex) \<sigma> = restrict_local (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))"
  unfolding pure_combine_tree_def by (simp add: Let_def restrict_local_combine_eq)

(* The shim's combine tree contributes the callee-exit globals to the global slot. *)
lemma sides_pure_combine_tree_Inr:
  "sides_of_rhs (pure_combine_tree cc ex) \<sigma> (Inr ()) =
   restrict_global (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
  unfolding pure_combine_tree_def by (simp add: Let_def restrict_global_combine_eq)

(* The shim's combine tree reassembles to the fixed abstract combine. *)
lemma etf_full_pure_combine_tree:
  "etf_full (pure_combine_tree cc ex) \<sigma>
   = combine_abs (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())) (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def pure_combine_tree_def
  by (simp add: all_sides_eq_sides_Inr_unit[unfolded pure_combine_tree_def] Let_def
        restrict_local_combine_eq restrict_global_combine_eq restrict_combine combine_abs_def)

text \<open>
  Every sound pure transfer record satisfies the effectful soundness contract via
  the shim.  The four obligations reduce, through etf_full_etf_from_tf, to the
  four sound_transfer obligations on the combined source state -- so no concrete
  domain needs a fresh soundness proof to enter the effectful interface.
\<close>

lemma sound_transfer_imp_sound_effectful:
  assumes "sound_transfer \<gamma> tf"
  shows "sound_effectful_transfer \<gamma> (etf_from_tf tf)"
proof -
  interpret st: sound_transfer \<gamma> tf by (rule assms)
  show ?thesis
  proof (unfold_locales)
    show "\<forall>u \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
            s \<in> st.gamma_state (etf_full (etf_nop (etf_from_tf tf) u) \<sigma>)"
    proof (intro allI ballI)
      fix u :: pp and \<sigma> and s :: store
      assume m: "s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      have eq: "etf_full (etf_nop (etf_from_tf tf) u) \<sigma>
                  = \<sigma> (Inl u) \<squnion> \<sigma> (Inr ())"
        by (simp add: etf_from_tf_def etf_full_pure_edge_tree)
      show "s \<in> st.gamma_state (etf_full (etf_nop (etf_from_tf tf) u) \<sigma>)"
        using m by (simp add: eq)
    qed
  next
    show "\<forall>x e u \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
            s(x := aval e s)
              \<in> st.gamma_state (etf_full (etf_assign (etf_from_tf tf) x e u) \<sigma>)"
    proof (intro allI ballI)
      fix x e and u :: pp and \<sigma> and s :: store
      assume m: "s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      have eq: "etf_full (etf_assign (etf_from_tf tf) x e u) \<sigma>
                  = tf_assign tf x e (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        by (simp add: etf_from_tf_def etf_full_pure_edge_tree)
      have "s(x := aval e s)
              \<in> st.gamma_state (tf_assign tf x e (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
        using st.tf_sound_assign m by blast
      thus "s(x := aval e s)
              \<in> st.gamma_state (etf_full (etf_assign (etf_from_tf tf) x e u) \<sigma>)"
        by (simp add: eq)
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())). bval b s
            \<longrightarrow> s \<in> st.gamma_state (etf_full (etf_assume (etf_from_tf tf) b u) \<sigma>)"
    proof (intro allI ballI impI)
      fix b :: bexp and u :: pp and \<sigma> and s :: store
      assume m: "s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))" and bv: "bval b s"
      have eq: "etf_full (etf_assume (etf_from_tf tf) b u) \<sigma>
                  = tf_assume tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        by (simp add: etf_from_tf_def etf_full_pure_edge_tree)
      have "s \<in> st.gamma_state (tf_assume tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
        using st.tf_sound_assume m bv by blast
      thus "s \<in> st.gamma_state (etf_full (etf_assume (etf_from_tf tf) b u) \<sigma>)"
        by (simp add: eq)
    qed
  next
    show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())). \<not> bval b s
            \<longrightarrow> s \<in> st.gamma_state (etf_full (etf_assume_not (etf_from_tf tf) b u) \<sigma>)"
    proof (intro allI ballI impI)
      fix b :: bexp and u :: pp and \<sigma> and s :: store
      assume m: "s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))" and bv: "\<not> bval b s"
      have eq: "etf_full (etf_assume_not (etf_from_tf tf) b u) \<sigma>
                  = tf_assume_not tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        by (simp add: etf_from_tf_def etf_full_pure_edge_tree)
      have "s \<in> st.gamma_state (tf_assume_not tf b (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
        using st.tf_sound_assume_not m bv by blast
      thus "s \<in> st.gamma_state (etf_full (etf_assume_not (etf_from_tf tf) b u) \<sigma>)"
        by (simp add: eq)
    qed
  next
    show "\<forall>u \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
            enter_state s \<in> st.gamma_state (etf_full (etf_enter (etf_from_tf tf) u) \<sigma>)"
    proof (intro allI ballI)
      fix u :: pp and \<sigma> and s :: store
      assume m: "s \<in> st.gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      have eq: "etf_full (etf_enter (etf_from_tf tf) u) \<sigma>
                  = tf_enter tf (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
        by (simp add: etf_from_tf_def etf_full_pure_edge_tree)
      have "enter_state s \<in> st.gamma_state (tf_enter tf (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
        using st.tf_sound_enter m by blast
      thus "enter_state s \<in> st.gamma_state (etf_full (etf_enter (etf_from_tf tf) u) \<sigma>)"
        by (simp add: eq)
    qed
  next
    show "\<forall>cc ex \<sigma>. \<forall>s \<in> st.gamma_state (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())).
            \<forall>t \<in> st.gamma_state (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())).
              combine_states s t
                \<in> st.gamma_state (etf_full (etf_combine (etf_from_tf tf) cc ex) \<sigma>)"
    proof (intro allI ballI)
      fix cc ex :: pp and \<sigma> and s t :: store
      assume sc: "s \<in> st.gamma_state (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))"
         and te: "t \<in> st.gamma_state (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
      have eq: "etf_full (etf_combine (etf_from_tf tf) cc ex) \<sigma>
                  = combine_abs (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())) (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"
        by (simp add: etf_full_pure_combine_tree)
      show "combine_states s t
              \<in> st.gamma_state (etf_full (etf_combine (etf_from_tf tf) cc ex) \<sigma>)"
        unfolding eq using st.combine_states_sound[OF sc te] .
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
