theory Sign_Named_Global_Eff
  imports Sign_Side_Soundness
begin

section \<open>A genuinely effectful, named-global Sign transfer\<close>

text \<open>
  This theory exhibits a NON-unit, genuinely effectful witness of the
  sound_effectful_transfer contract -- closing the instantiation gap for the
  'g::finite generalisation of the effectful interface.  It demonstrates both
  capabilities the single-pot unit interface lacks:

  - Gap 1 (named globals): contributions are routed to one of two distinct global
    unknowns (Gpos / Gneg) rather than a single pot.
  - Gap 2 (effectful transfer): the assign tree READS the abstract value of the
    flag variable ''Gflag'' (via the queried global environment) and routes the
    contribution conditionally on its sign.

  Soundness is clean: etf_full joins ALL Side contributions (all_sides), so the
  routing target does not change the reassembled full result -- it is always the
  pure sign_tf result on the queried source state.  The precision benefit is in
  the per-slot fixed-point values, which stay distinct (Sign_Named_Global_precise
  below): a query of one named unknown is not polluted by the other.
\<close>

subsection \<open>A two-element global-name type\<close>

datatype gname = Gpos | Gneg

lemma UNIV_gname: "(UNIV :: gname set) = {Gpos, Gneg}"
  using gname.exhaust by blast

instance gname :: finite
  by intro_classes (simp add: UNIV_gname)

text \<open>
  The named-global environment for gname is the join of the two slots.  This is
  the concrete shape of glob_env at 'g = gname.
\<close>
lemma glob_env_gname:
  "glob_env \<sigma> = \<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)"
proof -
  have "glob_env \<sigma> = abs_join_set (\<squnion>) \<bottom> ((\<lambda>g. \<sigma> (Inr g)) ` {Gpos, Gneg})"
    unfolding glob_env_def by (simp add: UNIV_gname)
  also have "\<dots> = abs_join_set (\<squnion>) \<bottom> {\<sigma> (Inr Gpos), \<sigma> (Inr Gneg)}" by simp
  also have "\<dots> = \<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)"
  proof (rule order_antisym)
    show "abs_join_set (\<squnion>) \<bottom> {\<sigma> (Inr Gpos), \<sigma> (Inr Gneg)}
            \<le> \<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)"
      by (rule abs_join_set_le) auto
    show "\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)
            \<le> abs_join_set (\<squnion>) \<bottom> {\<sigma> (Inr Gpos), \<sigma> (Inr Gneg)}"
    proof (rule sup_least)
      show "\<sigma> (Inr Gpos) \<le> abs_join_set (\<squnion>) \<bottom> {\<sigma> (Inr Gpos), \<sigma> (Inr Gneg)}"
        using glob_env_upper[of \<sigma> Gpos] unfolding glob_env_def
        by (simp add: UNIV_gname)
      show "\<sigma> (Inr Gneg) \<le> abs_join_set (\<squnion>) \<bottom> {\<sigma> (Inr Gpos), \<sigma> (Inr Gneg)}"
        using glob_env_upper[of \<sigma> Gneg] unfolding glob_env_def
        by (simp add: UNIV_gname)
    qed
  qed
  finally show ?thesis .
qed

subsection \<open>The routed tree builder\<close>

text \<open>
  route_tree queries the local unknown at u and both global slots, reassembles the
  source state, applies a pure abstract step f, and emits the global part to a
  routed slot.  Because etf_full joins all Side contributions, etf_full collapses
  to f on the source state regardless of the routing (route_tree_etf_full).
\<close>

definition route_tree ::
  "(sign abs_state \<Rightarrow> gname) \<Rightarrow> (sign abs_state \<Rightarrow> sign abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp, gname, sign abs_state) strategy_tree"
where
  "route_tree route f u =
     QueryL u (\<lambda>su. QueryG Gpos (\<lambda>gp. QueryG Gneg (\<lambda>gn.
       let env = su \<squnion> gp \<squnion> gn; res = f env
       in Side (route env) (restrict_global res) (Answer (restrict_local res)))))"

lemma route_tree_etf_full:
  "etf_full (route_tree route f u) \<sigma> = f (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding etf_full_def route_tree_def
  by (simp add: Let_def restrict_local_global_join glob_env_gname sup_assoc)

subsection \<open>The flag-routed combine builder\<close>

definition route_combine ::
  "(sign abs_state \<Rightarrow> gname) \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, gname, sign abs_state) strategy_tree"
where
  "route_combine route cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG Gpos (\<lambda>gp. QueryG Gneg (\<lambda>gn.
       let envc = sc \<squnion> gp \<squnion> gn; enve = se \<squnion> gp \<squnion> gn;
           res = combine_abs envc enve
       in Side (route envc) (restrict_global res) (Answer (restrict_local res))))))"

lemma route_combine_etf_full:
  "etf_full (route_combine route cc ex) \<sigma>
   = combine_abs (\<sigma> (Inl cc) \<squnion> glob_env \<sigma>) (\<sigma> (Inl ex) \<squnion> glob_env \<sigma>)"
  unfolding etf_full_def route_combine_def
  by (simp add: Let_def restrict_local_global_join glob_env_gname sup_assoc)

subsection \<open>The flag-routed effectful transfer record\<close>

text \<open>
  The routing function: route to Gpos when the abstract value of ''Gflag'' in the
  reassembled state is definitely positive, else to Gneg.  Only the assign tree
  routes by the flag; the other actions route to a fixed slot (the choice is
  irrelevant to soundness).
\<close>

definition flag_route :: "sign abs_state \<Rightarrow> gname" where
  "flag_route env = (if env ''Gflag'' = SPos then Gpos else Gneg)"

definition flag_etf :: "(gname, sign) effectful_domain_transfer" where
  "flag_etf =
     \<lparr> etf_nop        = route_tree (\<lambda>_. Gpos) (apply_tf sign_tf EA_Nop),
       etf_assign     = \<lambda>x a. route_tree flag_route (apply_tf sign_tf (EA_Assign x a)),
       etf_assume     = \<lambda>b. route_tree (\<lambda>_. Gpos) (apply_tf sign_tf (EA_Assume b)),
       etf_assume_not = \<lambda>b. route_tree (\<lambda>_. Gpos) (apply_tf sign_tf (EA_AssumeNot b)),
       etf_enter      = route_tree (\<lambda>_. Gpos) (apply_tf sign_tf EA_Enter),
       etf_combine    = route_combine (\<lambda>_. Gpos) \<rparr>"

lemma flag_etf_full_nop:
  "etf_full (etf_nop flag_etf u) \<sigma> = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
  unfolding flag_etf_def by (simp add: route_tree_etf_full sup_fun_def)

lemma flag_etf_full_assign:
  "etf_full (etf_assign flag_etf x a u) \<sigma>
   = tf_assign sign_tf x a (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding flag_etf_def by (simp add: route_tree_etf_full)

lemma flag_etf_full_assume:
  "etf_full (etf_assume flag_etf b u) \<sigma>
   = tf_assume sign_tf b (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding flag_etf_def by (simp add: route_tree_etf_full)

lemma flag_etf_full_assume_not:
  "etf_full (etf_assume_not flag_etf b u) \<sigma>
   = tf_assume_not sign_tf b (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding flag_etf_def by (simp add: route_tree_etf_full)

lemma flag_etf_full_enter:
  "etf_full (etf_enter flag_etf u) \<sigma>
   = tf_enter sign_tf (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding flag_etf_def by (simp add: route_tree_etf_full)

lemma flag_etf_full_combine:
  "etf_full (etf_combine flag_etf cc ex) \<sigma>
   = combine_abs (\<sigma> (Inl cc) \<squnion> glob_env \<sigma>) (\<sigma> (Inl ex) \<squnion> glob_env \<sigma>)"
  unfolding flag_etf_def by (simp add: route_combine_etf_full)

subsection \<open>Soundness: a non-unit witness of sound_effectful_transfer\<close>

theorem flag_etf_sound:
  "sound_effectful_transfer gamma_sign flag_etf"
proof (unfold_locales)
  show "\<forall>u \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl u) \<squnion> glob_env \<sigma>).
          s \<in> sign_domain.gamma_state (etf_full (etf_nop flag_etf u) \<sigma>)"
    by (simp add: flag_etf_full_nop)
next
  show "\<forall>x a u \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl u) \<squnion> glob_env \<sigma>).
          s(x := aval a s)
            \<in> sign_domain.gamma_state (etf_full (etf_assign flag_etf x a u) \<sigma>)"
    using sign_tf_sound_assign by (simp add: flag_etf_full_assign)
next
  show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl u) \<squnion> glob_env \<sigma>). bval b s
          \<longrightarrow> s \<in> sign_domain.gamma_state (etf_full (etf_assume flag_etf b u) \<sigma>)"
    using sign_tf_sound_assume by (simp add: flag_etf_full_assume)
next
  show "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl u) \<squnion> glob_env \<sigma>). \<not> bval b s
          \<longrightarrow> s \<in> sign_domain.gamma_state (etf_full (etf_assume_not flag_etf b u) \<sigma>)"
    using sign_tf_sound_assume_not by (simp add: flag_etf_full_assume_not)
next
  show "\<forall>u \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl u) \<squnion> glob_env \<sigma>).
          enter_state s \<in> sign_domain.gamma_state (etf_full (etf_enter flag_etf u) \<sigma>)"
    using sign_tf_sound_enter by (simp add: flag_etf_full_enter)
next
  show "\<forall>cc ex \<sigma>. \<forall>s \<in> sign_domain.gamma_state (\<sigma> (Inl cc) \<squnion> glob_env \<sigma>).
          \<forall>t \<in> sign_domain.gamma_state (\<sigma> (Inl ex) \<squnion> glob_env \<sigma>).
            combine_states s t
              \<in> sign_domain.gamma_state (etf_full (etf_combine flag_etf cc ex) \<sigma>)"
    by (auto simp: flag_etf_full_combine intro: sign_domain.combine_states_sound)
qed

subsection \<open>Precision: the two named slots stay distinct\<close>

text \<open>
  The routing the unit interface cannot express: when the flag is definitely
  positive, the assign's contribution lands ONLY in the Gpos slot; the Gneg slot
  receives nothing from this tree.  With a single pot (unit) both contributions
  would merge and a conflicting later write would force STop; here the slots are
  kept apart.
\<close>

lemma flag_assign_routes_pos:
  assumes "(\<sigma> (Inl u) \<squnion> glob_env \<sigma>) ''Gflag'' = SPos"
  shows "sides_of_rhs (etf_assign flag_etf x a u) \<sigma> (Inr Gneg) = \<bottom>"
proof -
  let ?env = "\<sigma> (Inl u) \<squnion> \<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)"
  have env: "?env = \<sigma> (Inl u) \<squnion> glob_env \<sigma>" by (simp add: glob_env_gname sup_assoc)
  have "flag_route ?env = Gpos"
    using assms unfolding flag_route_def env by simp
  thus ?thesis
    unfolding flag_etf_def route_tree_def by (simp add: Let_def)
qed

lemma flag_assign_routes_neg:
  assumes "(\<sigma> (Inl u) \<squnion> glob_env \<sigma>) ''Gflag'' \<noteq> SPos"
  shows "sides_of_rhs (etf_assign flag_etf x a u) \<sigma> (Inr Gpos) = \<bottom>"
proof -
  let ?env = "\<sigma> (Inl u) \<squnion> \<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)"
  have env: "?env = \<sigma> (Inl u) \<squnion> glob_env \<sigma>" by (simp add: glob_env_gname sup_assoc)
  have "flag_route ?env = Gneg"
    using assms unfolding flag_route_def env by simp
  thus ?thesis
    unfolding flag_etf_def route_tree_def by (simp add: Let_def)
qed

end
