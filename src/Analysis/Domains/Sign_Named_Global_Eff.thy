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
           res = \<langle>envc|enve\<rangle>
       in Side (route envc) (restrict_global res) (Answer (restrict_local res))))))"

lemma route_combine_etf_full:
  "etf_full (route_combine route cc ex) \<sigma>
   = \<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>"
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
   = \<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>"
  unfolding flag_etf_def by (simp add: route_combine_etf_full)

subsection \<open>Soundness: a non-unit witness of sound_effectful_transfer\<close>

theorem flag_etf_sound:
  "sound_effectful_transfer flag_etf"
proof (unfold_locales)
  show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            s \<in> \<lbrakk>etf_collecting_full (etf_nop flag_etf u) \<sigma>\<rbrakk>)"
    by (auto simp add: flag_etf_full_nop intro: in_gamma_etf_collecting_full)
next
  show "\<forall>x a u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            s(x := aval a s)
              \<in> \<lbrakk>etf_collecting_full (etf_assign flag_etf x a u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assign
    by (auto simp add: flag_etf_full_assign intro: in_gamma_etf_collecting_full)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. bval b s
          \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full (etf_assume flag_etf b u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assume
    by (auto simp add: flag_etf_full_assume intro: in_gamma_etf_collecting_full)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. \<not> bval b s
          \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full (etf_assume_not flag_etf b u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assume_not
    by (auto simp add: flag_etf_full_assume_not intro: in_gamma_etf_collecting_full)
next
  show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            enter_state s \<in> \<lbrakk>etf_collecting_full (etf_enter flag_etf u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_enter
    by (auto simp add: flag_etf_full_enter intro: in_gamma_etf_collecting_full)
next
  show "\<forall>cc ex \<sigma>.
       inr_slot_locals_bot \<sigma> \<longrightarrow>
       (\<forall>s\<in>\<lbrakk>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>\<rbrakk>.
           \<forall>t\<in>\<lbrakk>\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rbrakk>. <s|t> \<in> \<lbrakk>etf_full (etf_combine flag_etf cc ex) \<sigma>\<rbrakk>) "
    by (auto simp: flag_etf_full_combine intro: combine_states_sound)
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

subsection \<open>Computational shape of the routed trees\<close>

text \<open>
  traverse_rhs collapses the QueryL / QueryG skeleton and ignores the Side slot,
  so it is the pure abstract step on the reassembled source state -- independent
  of the routing.  sides_of_rhs, for a CONSTANT route, lands the global part in
  exactly that one named slot.
\<close>

lemma traverse_route_tree:
  "traverse_rhs (route_tree route f u) \<sigma>
   = restrict_local (f (\<sigma> (Inl u) \<squnion> glob_env \<sigma>))"
  unfolding route_tree_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma sides_route_tree_const:
  "sides_of_rhs (route_tree (\<lambda>_. gg) f u) \<sigma>
   = (\<lambda>_. \<bottom>)(Inr gg := restrict_global (f (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)))"
  unfolding route_tree_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma dep_aux_route_tree:
  "dep_aux \<sigma> (route_tree route f u) = {Inl u, Inr Gpos, Inr Gneg}"
  unfolding route_tree_def by (simp add: Let_def)

lemma traverse_route_combine:
  "traverse_rhs (route_combine route cc ex) \<sigma>
   = restrict_local \<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>"
  unfolding route_combine_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma sides_route_combine_const:
  "sides_of_rhs (route_combine (\<lambda>_. gg) cc ex) \<sigma>
   = (\<lambda>_. \<bottom>)(Inr gg
       := restrict_global \<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>)"
  unfolding route_combine_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma dep_aux_route_combine:
  "dep_aux \<sigma> (route_combine route cc ex) = {Inl cc, Inl ex, Inr Gpos, Inr Gneg}"
  unfolding route_combine_def by (simp add: Let_def)

lemma sides_inr_local_bot_route_tree_const:
  fixes gg :: gname
  shows "local_bot_on_locals (sides_of_rhs (route_tree (\<lambda>_. gg) f u) \<sigma> (Inr g))"
proof (cases "g = gg")
  case True
  show ?thesis
    using local_bot_on_locals_restrict_global[where \<sigma>="f (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"]
    by (simp add: True sides_route_tree_const)
next
  case False
  show ?thesis by (simp add: False sides_route_tree_const local_bot_on_locals_def)
qed

lemma sides_inr_local_bot_route_combine_const:
  fixes gg :: gname
  shows "local_bot_on_locals (sides_of_rhs (route_combine (\<lambda>_. gg) cc ex) \<sigma> (Inr g))"
proof (cases "g = gg")
  case True
  show ?thesis
    using local_bot_on_locals_restrict_global[where \<sigma>="\<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>"]
    by (simp add: True sides_route_combine_const)
next
  case False
  show ?thesis by (simp add: False sides_route_combine_const local_bot_on_locals_def)
qed

lemma combine_abs_mono:
  "sc1 \<le> sc2 \<Longrightarrow> se1 \<le> se2 \<Longrightarrow> \<langle>sc1|se1\<rangle> \<le> \<langle>sc2|se2\<rangle>"
  by (auto simp: combine_abs_def le_fun_def)

subsection \<open>A monotone named-global witness for the TD_side solver\<close>

text \<open>
  flag_etf's assign tree routes CONDITIONALLY on the flag's sign, which is not
  monotone in the solver environment: as \<sigma> grows, ''Gflag'' can move from SPos to
  STop, flipping the contribution Gpos -> Gneg, so sides_of_rhs is not
  \<sigma>-monotone and flag_etf fails the TD_side mono_sides precondition.  (The
  conditional routing stays a sound, precise PER-TREE witness -- flag_etf_sound,
  flag_assign_routes_pos / _neg above -- it just cannot drive the fixpoint
  solver.)

  To carry a genuinely named-global analysis THROUGH the real solver, route with
  CONSTANT slots: edge contributions to Gpos, combine (procedure-return)
  contributions to Gneg.  Both named slots are populated and the routing is
  monotone, so the three TD_side preconditions discharge from the generic
  per-tree lemmas in TD_Side_Eff_Bounds.
\<close>

definition named_etf :: "(gname, sign) effectful_domain_transfer" where
  "named_etf =
     \<lparr> etf_nop        = route_tree (\<lambda>_. Gpos) (apply_tf sign_tf EA_Nop),
       etf_assign     = \<lambda>x a. route_tree (\<lambda>_. Gpos) (apply_tf sign_tf (EA_Assign x a)),
       etf_assume     = \<lambda>b. route_tree (\<lambda>_. Gpos) (apply_tf sign_tf (EA_Assume b)),
       etf_assume_not = \<lambda>b. route_tree (\<lambda>_. Gpos) (apply_tf sign_tf (EA_AssumeNot b)),
       etf_enter      = route_tree (\<lambda>_. Gpos) (apply_tf sign_tf EA_Enter),
       etf_combine    = route_combine (\<lambda>_. Gneg) \<rparr>"

lemma apply_etf_named:
  "apply_etf named_etf a u = route_tree (\<lambda>_. Gpos) (apply_tf sign_tf a) u"
  by (cases a) (simp_all add: named_etf_def)

lemma etf_combine_named:
  "etf_combine named_etf cc ex = route_combine (\<lambda>_. Gneg) cc ex"
  by (simp add: named_etf_def)

lemma named_edge_inr_local_bot:
  "\<And>a u \<sigma>' g. local_bot_on_locals (sides_of_rhs (apply_etf named_etf a u) \<sigma>' (Inr g))"
  unfolding apply_etf_named by (rule sides_inr_local_bot_route_tree_const)

lemma named_comb_inr_local_bot:
  "\<And>cc ex \<sigma>' g. local_bot_on_locals (sides_of_rhs (etf_combine named_etf cc ex) \<sigma>' (Inr g))"
  unfolding etf_combine_named by (rule sides_inr_local_bot_route_combine_const)

lemma named_etf_full_nop:
  "etf_full (etf_nop named_etf u) \<sigma> = \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
  unfolding named_etf_def by (simp add: route_tree_etf_full sup_fun_def)

lemma named_etf_full_assign:
  "etf_full (etf_assign named_etf x a u) \<sigma>
   = tf_assign sign_tf x a (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_assume:
  "etf_full (etf_assume named_etf b u) \<sigma>
   = tf_assume sign_tf b (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_assume_not:
  "etf_full (etf_assume_not named_etf b u) \<sigma>
   = tf_assume_not sign_tf b (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_enter:
  "etf_full (etf_enter named_etf u) \<sigma>
   = tf_enter sign_tf (\<sigma> (Inl u) \<squnion> glob_env \<sigma>)"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_combine:
  "etf_full (etf_combine named_etf cc ex) \<sigma>
   = \<langle>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>|\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rangle>"
  unfolding named_etf_def by (simp add: route_combine_etf_full)

theorem named_etf_sound:
  "sound_effectful_transfer named_etf"
proof (unfold_locales)
  show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            s \<in> \<lbrakk>etf_collecting_full (etf_nop named_etf u) \<sigma>\<rbrakk>)"
    by (auto simp add: named_etf_full_nop intro: in_gamma_etf_collecting_full)
next
  show "\<forall>x a u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            s(x := aval a s)
              \<in> \<lbrakk>etf_collecting_full (etf_assign named_etf x a u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assign
    by (auto simp add: named_etf_full_assign intro: in_gamma_etf_collecting_full)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. bval b s
          \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full (etf_assume named_etf b u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assume
    by (auto simp add: named_etf_full_assume intro: in_gamma_etf_collecting_full)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. \<not> bval b s
          \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full (etf_assume_not named_etf b u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_assume_not
    by (auto simp add: named_etf_full_assume_not intro: in_gamma_etf_collecting_full)
next
  show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
            enter_state s \<in> \<lbrakk>etf_collecting_full (etf_enter named_etf u) \<sigma>\<rbrakk>)"
    using sign_tf_sound_enter
    by (auto simp add: named_etf_full_enter intro: in_gamma_etf_collecting_full)
next
  show "\<forall>cc ex \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
          (\<forall>s\<in>\<lbrakk>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>\<rbrakk>.
           \<forall>t\<in>\<lbrakk>\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rbrakk>. <s|t> \<in> \<lbrakk>etf_full (etf_combine named_etf cc ex) \<sigma>\<rbrakk>)"
    by (auto simp: named_etf_full_combine intro: combine_states_sound)
qed

subsection \<open>TD_side preconditions for named_etf (constant routing is monotone)\<close>

lemma named_traverse_mono:
  assumes "s1 \<le> s2"
  shows "traverse_rhs (apply_etf named_etf a u) s1
         \<le> traverse_rhs (apply_etf named_etf a u) s2"
  unfolding apply_etf_named traverse_route_tree
  by (rule restrict_local_mono[OF sign_tf_mono[OF
        sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])

lemma named_comb_traverse_mono:
  assumes "s1 \<le> s2"
  shows "traverse_rhs (etf_combine named_etf cc ex) s1
         \<le> traverse_rhs (etf_combine named_etf cc ex) s2"
  unfolding etf_combine_named traverse_route_combine
  by (rule restrict_local_mono[OF combine_abs_mono[OF
        sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]
        sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])

lemma named_sides_mono:
  assumes "s1 \<le> s2"
  shows "sides_of_rhs (apply_etf named_etf a u) s1
         \<le> sides_of_rhs (apply_etf named_etf a u) s2"
proof -
  have d: "restrict_global (apply_tf sign_tf a (s1 (Inl u) \<squnion> glob_env s1))
           \<le> restrict_global (apply_tf sign_tf a (s2 (Inl u) \<squnion> glob_env s2))"
    by (rule restrict_global_mono[OF sign_tf_mono[OF
          sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])
  show ?thesis
    unfolding apply_etf_named sides_route_tree_const
    using d by (auto simp: le_fun_def)
qed

lemma named_comb_sides_mono:
  assumes "s1 \<le> s2"
  shows "sides_of_rhs (etf_combine named_etf cc ex) s1
         \<le> sides_of_rhs (etf_combine named_etf cc ex) s2"
proof -
  have d: "restrict_global \<langle>s1 (Inl cc) \<squnion> glob_env s1|s1 (Inl ex) \<squnion> glob_env s1\<rangle>
           \<le> restrict_global \<langle>s2 (Inl cc) \<squnion> glob_env s2|s2 (Inl ex) \<squnion> glob_env s2\<rangle>"
    by (rule restrict_global_mono[OF combine_abs_mono[OF
          sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]
          sup_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])
  show ?thesis
    unfolding etf_combine_named sides_route_combine_const
    using d by (auto simp: le_fun_def)
qed

lemma named_edge_static: "static_deps (apply_etf named_etf a u)"
  unfolding apply_etf_named static_deps_def by (simp add: dep_aux_route_tree)

lemma named_comb_static: "static_deps (etf_combine named_etf cc ex)"
  unfolding etf_combine_named static_deps_def by (simp add: dep_aux_route_combine)

lemma named_edge_dep: "Inl z \<in> dep_aux \<sigma> (apply_etf named_etf b z)"
  unfolding apply_etf_named by (simp add: dep_aux_route_tree)

lemma named_comb_dep1: "Inl cc \<in> dep_aux \<sigma> (etf_combine named_etf cc ex)"
  unfolding etf_combine_named by (simp add: dep_aux_route_combine)

lemma named_comb_dep2: "Inl ex \<in> dep_aux \<sigma> (etf_combine named_etf cc ex)"
  unfolding etf_combine_named by (simp add: dep_aux_route_combine)

lemma named_etf_is_mono_eq:
  "is_mono_eq (side_cfg_T_eff g named_etf bot0 s0 gseed)"
  by (rule side_cfg_T_eff_is_mono_eq_gen[OF named_traverse_mono named_comb_traverse_mono])

lemma named_etf_mono_sides:
  "mono_sides (side_cfg_T_eff g named_etf bot0 s0 gseed)"
  by (rule side_cfg_T_eff_mono_sides_gen[OF named_sides_mono named_comb_sides_mono])

lemma named_etf_mono_deps:
  "mono_deps (side_cfg_T_eff g named_etf bot0 s0 gseed)"
  by (rule side_cfg_T_eff_mono_deps_gen[OF named_edge_static named_comb_static])

subsection \<open>Headline: a named-global analysis sound through the real side solver\<close>

text \<open>
  The named-global Sign analysis uses two slots Gpos / Gneg ('g = gname) and
  over-approximates the interprocedural CFG collecting semantics at the program
  exit through the effectful side TD solver (side_analyse_eff at 'g = gname).
  The three TD_side preconditions are discharged for named_etf directly from the
  generic per-tree lemmas; the cone contracts hold by the routed trees' query
  skeleton. The initial globals are seeded into the Gpos slot.
\<close>

theorem named_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) named_etf bot s0 Gpos
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main named_etf bot s0 Gpos
         (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  have gs: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using s_sound by simp
  have collect:
    "cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> \<lbrakk>side_analyse_eff \<Pi> ps main named_etf bot s0 Gpos
         (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_pruned_gen
          [OF named_etf_sound named_etf_is_mono_eq named_etf_mono_sides named_etf_mono_deps
              side_solve_dom gs named_edge_dep named_comb_dep1 named_comb_dep2
              named_edge_static named_comb_static
              named_edge_inr_local_bot named_comb_inr_local_bot])
  show ?thesis
    using collect collect_exit by blast
qed

subsection \<open>Why the conditional flag routing cannot drive the solver\<close>

text \<open>
  For the record: the conditional flag_etf is NOT mono_sides, so the goal below
  is deliberately abandoned with oops -- it is not a provable obligation, by
  design.  As sigma grows the reassembled flag value can move SPos -> STop, so
  flag_route flips the assign contribution Gpos -> Gneg; the side map then drops
  its Gpos entry, breaking sigma-monotonicity of sides_of_rhs.  This is precisely
  why the through-solver headline above uses the constant-routed named_etf.
  flag_etf's value is the per-tree precision it expresses
  (flag_assign_routes_pos / _neg), not fixpoint-solver compatibility.
\<close>
lemma flag_etf_mono_sides_unprovable:
  "mono_sides (side_cfg_T_eff g flag_etf bot0 s0 gseed)"
  oops

end
