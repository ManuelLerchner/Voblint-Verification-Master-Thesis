theory Sign_Named_Global_Eff
  imports Sign_Side_Soundness Voblint_Core.Strategy_Tree_Combinators
begin

section \<open>A genuinely effectful, named-global Sign transfer\<close>

text \<open>The effectful transfer routes contributions to two distinct global
  unknowns. Its assignment tree reads the abstract value of @{text "''Gflag''"} and
  selects a target from its sign. Reassembling the state joins every side contribution,
  so routing preserves soundness while keeping unrelated fixed-point slots separate.\<close>

text \<open>\<open>route_tree\<close> queries the local unknown and selected global slots;
  \<open>apply_etf\<close> evaluates the transfer; and \<open>etf_full\<close> rejoins its answer and side effects.
  \<open>se_constraint_holds\<close> states the corresponding post-solution bound used by the solver
  soundness theorem.\<close>

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
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign abs_state lifted \<Rightarrow> gname) \<Rightarrow> (sign abs_state \<Rightarrow> sign abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp, gname, sign abs_state lifted) strategy_tree"
where
  "route_tree gs route f u =
     read_local_cont u (\<lambda>su. read_global_cont Gpos (\<lambda>gp. read_global_cont Gneg (\<lambda>gn.
       let g = gp \<squnion> gn;
           env = assemble_local_global su g;
           res = transfer_lift is_bot_state f env
       in depend_on (route env) (map_lift (restrict_global_for gs) res)
            (answer (map_lift (restrict_local_for gs) res)))))"

lemma route_tree_etf_full:
  "etf_full (route_tree gs route f u) \<sigma>
   = transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding etf_full_def route_tree_def
  apply (simp add: Let_def glob_env_gname sup_assoc)
  apply (cases "transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)))")
   apply simp
  apply (simp add: restrict_local_for_global_join)
  done

subsection \<open>The flag-routed combine builder\<close>

definition route_combine ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign abs_state lifted \<Rightarrow> gname) \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, gname, sign abs_state lifted) strategy_tree"
where
  "route_combine gs route dst cc ex =
     read_local_cont cc (\<lambda>sc. read_local_cont ex (\<lambda>se. read_global_cont Gpos (\<lambda>gp. read_global_cont Gneg (\<lambda>gn.
       let g = gp \<squnion> gn;
           envc = assemble_local_global sc g; enve = assemble_local_global se g;
           res = transfer_lift2 is_bot_state (combine\<^sup># gs dst) envc enve
       in depend_on (route envc) (map_lift (restrict_global_for gs) res)
            (answer (map_lift (restrict_local_for gs) res))))))"

lemma route_combine_etf_full:
  "etf_full (route_combine gs route dst cc ex) \<sigma>
   = transfer_lift2 is_bot_state (combine\<^sup># gs dst)
       (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
       (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>))"
  unfolding etf_full_def route_combine_def
  apply (simp add: Let_def glob_env_gname sup_assoc)
  apply (cases "transfer_lift2 is_bot_state (combine\<^sup># gs dst)
                  (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)))
                  (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)))")
   apply simp
  apply (simp add: restrict_local_for_global_join)
  done


subsection \<open>Shared soundness skeleton for the routed families\<close>

text \<open>Both routed families reassemble the source state and apply the same pure
  sign step, so \<open>etf_full\<close> collapses to that step regardless of the routing.
  Given the six collapse facts, the \<open>sound_effectful_transfer\<close> obligations are
  discharged uniformly -- the routed families below differ only in their
  routing, not their soundness.\<close>
lemma in_gamma_transfer_lift:
  fixes x :: "sign abs_state lifted" and s s' :: store and f :: "sign abs_state \<Rightarrow> sign abs_state"
  assumes s: "s \<in> gamma_state_lift x"
  assumes sound: "\<And>env. s \<in> \<lbrakk>env\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>f env\<rbrakk>"
  shows "s' \<in> gamma_state_lift (transfer_lift is_bot_state f x)"
proof (cases x)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted env)
  have hs: "s \<in> \<lbrakk>env\<rbrakk>" using s Lifted by simp
  have hf: "s' \<in> \<lbrakk>f env\<rbrakk>" using sound[OF hs] .
  have not_bot: "\<not> is_bot_state (f env)" using hf is_bot_state_witnessI by blast
  show ?thesis unfolding Lifted transfer_lift_Lifted using hf not_bot by simp
qed

lemma in_gamma_transfer_lift2:
  fixes x y :: "sign abs_state lifted" and s t s' :: store
    and f :: "sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state"
  assumes s: "s \<in> gamma_state_lift x" and t: "t \<in> gamma_state_lift y"
  assumes sound: "\<And>envc enve. s \<in> \<lbrakk>envc\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>enve\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>f envc enve\<rbrakk>"
  shows "s' \<in> gamma_state_lift (transfer_lift2 is_bot_state f x y)"
proof (cases x)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted envc)
  note hx = this
  show ?thesis
  proof (cases y)
    case Bot
    then show ?thesis using t by simp
  next
    case (Lifted enve)
    have hs: "s \<in> \<lbrakk>envc\<rbrakk>" using s hx by simp
    have ht: "t \<in> \<lbrakk>enve\<rbrakk>" using t Lifted by simp
    have hf: "s' \<in> \<lbrakk>f envc enve\<rbrakk>" using sound[OF hs ht] .
    have not_bot: "\<not> is_bot_state (f envc enve)" using hf is_bot_state_witnessI by blast
    show ?thesis unfolding hx Lifted transfer_lift2_Lifted using hf not_bot by simp
  qed
qed

lemma in_gamma_etf_collecting_lift_of_transfer:
  fixes t :: "(pp, gname, sign abs_state lifted) strategy_tree"
    and \<sigma> :: "pp + gname \<Rightarrow> sign abs_state lifted" and s s' :: store
    and f :: "sign abs_state \<Rightarrow> sign abs_state" and x :: "sign abs_state lifted"
  assumes eq: "etf_full t \<sigma> = transfer_lift is_bot_state f x"
  assumes s: "s \<in> gamma_state_lift x"
  assumes sound: "\<And>env. s \<in> \<lbrakk>env\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>f env\<rbrakk>"
  shows "s' \<in> gamma_state_lift (etf_collecting_full_lift t \<sigma>)"
proof (rule in_gamma_etf_collecting_full_lift)
  show "s' \<in> gamma_state_lift (etf_full t \<sigma>)"
    unfolding eq by (rule in_gamma_transfer_lift[OF s sound])
qed

lemma route_family_etf_sound:
  fixes E :: "(gname, sign) effectful_domain_transfer"
  assumes nop: "\<And>u \<sigma>. etf_full (etf_nop E u) \<sigma>
                   = transfer_lift is_bot_state (\<lambda>x. x) (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and assign: "\<And>x a u \<sigma>. etf_full (etf_assign E x a u) \<sigma>
                   = transfer_lift is_bot_state (assign\<^sup># (sign_tf_for gs) x a)
                       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and random: "\<And>x u \<sigma>. etf_full (etf_random E x u) \<sigma>
                   = transfer_lift is_bot_state (tf_random (sign_tf_for gs) x)
                       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and assm: "\<And>b u \<sigma>. etf_full (etf_assume E b u) \<sigma>
                   = transfer_lift is_bot_state (tf_assume (sign_tf_for gs) b)
                       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and assm_not: "\<And>b u \<sigma>. etf_full (etf_assume_not E b u) \<sigma>
                   = transfer_lift is_bot_state (tf_assume_not (sign_tf_for gs) b)
                       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and enter: "\<And>xs es u \<sigma>. etf_full (etf_enter E xs es u) \<sigma>
                   = transfer_lift is_bot_state (enter\<^sup># (sign_tf_for gs) xs es)
                       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
    and combine: "\<And>dst cc ex \<sigma>. etf_full (etf_combine E dst cc ex) \<sigma>
                   = transfer_lift2 is_bot_state (combine\<^sup># gs dst)
                       (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
                       (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>))"
  shows "sound_effectful_transfer gs E"
proof (unfold_locales)
  show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
            s \<in> gamma_state_lift (etf_collecting_full_lift (etf_nop E u) \<sigma>))"
    by (auto simp add: nop intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>x a u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
            s(x := aval a s)
              \<in> gamma_state_lift (etf_collecting_full_lift (etf_assign E x a u) \<sigma>))"
    using assign_sign_sound
    by (auto simp add: assign sign_tf_for_def intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)). \<forall>v.
            s(x := v)
              \<in> gamma_state_lift (etf_collecting_full_lift (etf_random E x u) \<sigma>))"
    using random_sign_sound
    by (auto simp add: random sign_tf_for_def intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)). bval b s
          \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift (etf_assume E b u) \<sigma>))"
    using assume_sign_sound
    by (auto simp add: assm sign_tf_for_def intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)). \<not> bval b s
          \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift (etf_assume_not E b u) \<sigma>))"
    using assume_not_sign_sound
    by (auto simp add: assm_not sign_tf_for_def intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>xs es u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
          (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
            bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
              \<in> gamma_state_lift (etf_collecting_full_lift (etf_enter E xs es u) \<sigma>))"
    using enter_sign_for_sound
    by (auto simp add: enter sign_tf_for_def intro: in_gamma_etf_collecting_lift_of_transfer)
next
  show "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s\<in>gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>)).
           \<forall>t\<in>gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>)).
             combine_collect gs dst s t \<in> gamma_state_lift (etf_full (etf_combine E dst cc ex) \<sigma>))"
    by (auto simp: combine intro: in_gamma_transfer_lift2 combine_collect_sound)
qed

subsection \<open>Computational shape of the routed trees\<close>

text \<open>
  traverse_rhs collapses the QueryL / QueryG skeleton and ignores the Side slot,
  so it is the pure abstract step on the reassembled source state -- independent
  of the routing.  sides_of_rhs, for a CONSTANT route, lands the global part in
  exactly that one named slot.
\<close>

lemma traverse_route_tree:
  "traverse_rhs (route_tree gs route f u) \<sigma>
   = map_lift (restrict_local_for gs)
       (transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)))"
  unfolding route_tree_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma sides_route_tree_const:
  "sides_of_rhs (route_tree gs (\<lambda>_. gg) f u) \<sigma>
   = (\<lambda>_. Bot)(Inr gg :=
       map_lift (restrict_global_for gs)
         (transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))))"
  unfolding route_tree_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma dep_aux_route_tree:
  "dep_aux \<sigma> (route_tree gs route f u) = {Inl u, Inr Gpos, Inr Gneg}"
  unfolding route_tree_def by (simp add: Let_def)

lemma traverse_route_combine:
  "traverse_rhs (route_combine gs route dst cc ex) \<sigma>
   = map_lift (restrict_local_for gs)
       (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
         (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
         (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>)))"
  unfolding route_combine_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma sides_route_combine_const:
  "sides_of_rhs (route_combine gs (\<lambda>_. gg) dst cc ex) \<sigma>
   = (\<lambda>_. Bot)(Inr gg
       := map_lift (restrict_global_for gs)
            (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
              (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
              (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>))))"
  unfolding route_combine_def
  by (simp add: Let_def glob_env_gname sup_assoc)

lemma dep_aux_route_combine:
  "dep_aux \<sigma> (route_combine gs route dst cc ex) = {Inl cc, Inl ex, Inr Gpos, Inr Gneg}"
  unfolding route_combine_def by (simp add: Let_def)

lemma sides_inr_local_bot_route_tree_const:
  fixes gg :: gname
  shows "local_bot_on_locals_lift gs (sides_of_rhs (route_tree gs (\<lambda>_. gg) f u) \<sigma> (Inr g))"
proof (cases "g = gg")
  case True
  show ?thesis
    unfolding True sides_route_tree_const
    by (simp add: local_bot_on_locals_lift_map_restrict_global)
next
  case False
  show ?thesis by (simp add: False sides_route_tree_const)
qed

lemma sides_inr_local_bot_route_combine_const:
  fixes gg :: gname
  shows "local_bot_on_locals_lift gs (sides_of_rhs (route_combine gs (\<lambda>_. gg) dst cc ex) \<sigma> (Inr g))"
proof (cases "g = gg")
  case True
  show ?thesis
    unfolding True sides_route_combine_const
    by (simp add: local_bot_on_locals_lift_map_restrict_global)
next
  case False
  show ?thesis by (simp add: False sides_route_combine_const)
qed

lemma combine_env_abs_mono:
  "sc1 \<le> sc2 \<Longrightarrow> se1 \<le> se2 \<Longrightarrow> combine_env\<^sup># gs sc1 se1 \<le> combine_env\<^sup># gs sc2 se2"
  by (auto simp: combine_env_abs_def le_fun_def)

subsection \<open>A monotone named-global witness for the TD_side solver\<close>

text \<open>
  To carry a genuinely named-global analysis through the real solver, route with
  CONSTANT slots: edge contributions to Gpos, combine (procedure-return)
  contributions to Gneg.  Both named slots are populated and the routing is
  monotone (unlike a routing that depends on the reassembled state, which is not
  \<sigma>-monotone and fails the TD_side mono_sides precondition), so the three
  TD_side preconditions discharge from the generic per-tree lemmas in
  TD_Side_Eff_Bounds.
\<close>

definition named_etf :: "(vname \<Rightarrow> bool) \<Rightarrow> (gname, sign) effectful_domain_transfer" where
  "named_etf gs =
     \<lparr> etf_nop        = route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) EA_Nop),
       etf_assign     = \<lambda>x a. route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) (EA_Assign x a)),
       etf_random     = \<lambda>x. route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) (EA_Random x)),
       etf_assume     = \<lambda>b. route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) (EA_Assume b)),
       etf_assume_not = \<lambda>b. route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) (EA_AssumeNot b)),
       etf_enter      = (\<lambda>xs es. route_tree gs (\<lambda>_. Gpos) (enter\<^sup># (sign_tf_for gs) xs es)),
       etf_combine    = route_combine gs (\<lambda>_. Gneg) \<rparr>"

lemma apply_etf_named:
  "apply_etf (named_etf gs) a u = route_tree gs (\<lambda>_. Gpos) (apply_tf (sign_tf_for gs) a) u"
  by (cases a)
     (simp_all add: named_etf_def apply_tf_EA_Ret_None apply_tf_EA_Ret_Some apply_tf_EA_Check
        split: option.splits)

lemma etf_combine_named:
  "etf_combine (named_etf gs) dst cc ex = route_combine gs (\<lambda>_. Gneg) dst cc ex"
  by (simp add: named_etf_def)

lemma etf_enter_named:
  "etf_enter (named_etf gs) fs as cl = route_tree gs (\<lambda>_. Gpos) (enter\<^sup># (sign_tf_for gs) fs as) cl"
  by (simp add: named_etf_def)

lemma named_enter_mono:
  "s1 \<le> s2 \<Longrightarrow> enter\<^sup># (sign_tf_for gs) fs as s1 \<le> enter\<^sup># (sign_tf_for gs) fs as s2"
  by (simp add: sign_tf_for_def enter_sign_for_mono)

lemma named_edge_inr_local_bot:
  "\<And>a u \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (apply_etf (named_etf gs) a u) \<sigma>' (Inr g))"
  unfolding apply_etf_named by (rule sides_inr_local_bot_route_tree_const)

lemma named_comb_inr_local_bot:
  "\<And>dst cc ex \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine (named_etf gs) dst cc ex) \<sigma>' (Inr g))"
  unfolding etf_combine_named by (rule sides_inr_local_bot_route_combine_const)

lemma named_etf_full_nop:
  "etf_full (etf_nop (named_etf gs) u) \<sigma>
   = transfer_lift is_bot_state (\<lambda>x. x) (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
proof -
  have "apply_tf (sign_tf_for gs) EA_Nop = (\<lambda>x. x)" by (rule ext) simp
  then show ?thesis unfolding named_etf_def by (simp add: route_tree_etf_full)
qed

lemma named_etf_full_assign:
  "etf_full (etf_assign (named_etf gs) x a u) \<sigma>
   = transfer_lift is_bot_state (assign\<^sup># (sign_tf_for gs) x a)
       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_random:
  "etf_full (etf_random (named_etf gs) x u) \<sigma>
   = transfer_lift is_bot_state (tf_random (sign_tf_for gs) x)
       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_assume:
  "etf_full (etf_assume (named_etf gs) b u) \<sigma>
   = transfer_lift is_bot_state (tf_assume (sign_tf_for gs) b)
       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_assume_not:
  "etf_full (etf_assume_not (named_etf gs) b u) \<sigma>
   = transfer_lift is_bot_state (tf_assume_not (sign_tf_for gs) b)
       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_enter:
  "etf_full (etf_enter (named_etf gs) xs es u) \<sigma>
   = transfer_lift is_bot_state (enter\<^sup># (sign_tf_for gs) xs es)
       (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_tree_etf_full)

lemma named_etf_full_combine:
  "etf_full (etf_combine (named_etf gs) dst cc ex) \<sigma>
   = transfer_lift2 is_bot_state (combine\<^sup># gs dst)
       (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
       (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>))"
  unfolding named_etf_def by (simp add: route_combine_etf_full)

theorem named_etf_sound:
  "sound_effectful_transfer gs (named_etf gs)"
  by (rule route_family_etf_sound[OF named_etf_full_nop named_etf_full_assign
        named_etf_full_random named_etf_full_assume named_etf_full_assume_not
        named_etf_full_enter named_etf_full_combine])

subsection \<open>TD_side preconditions for named_etf (constant routing is monotone)\<close>

lemma named_traverse_mono:
  assumes "s1 \<le> s2"
  shows "traverse_rhs (apply_etf (named_etf gs) a u) s1
         \<le> traverse_rhs (apply_etf (named_etf gs) a u) s2"
  unfolding apply_etf_named traverse_route_tree
  by (rule map_lift_mono[OF restrict_local_for_mono
        transfer_lift_mono[OF sign_tf_for_mono is_bot_state_mono
          assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])

lemma named_comb_traverse_mono:
  assumes "s1 \<le> s2"
  shows "traverse_rhs (etf_combine (named_etf gs) dst cc ex) s1
         \<le> traverse_rhs (etf_combine (named_etf gs) dst cc ex) s2"
  unfolding etf_combine_named traverse_route_combine
  by (rule map_lift_mono[OF restrict_local_for_mono
        transfer_lift2_mono[OF combine_collect_abs_mono is_bot_state_mono
          assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]
          assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])

lemma named_sides_mono:
  assumes "s1 \<le> s2"
  shows "sides_of_rhs (apply_etf (named_etf gs) a u) s1
         \<le> sides_of_rhs (apply_etf (named_etf gs) a u) s2"
proof -
  have d: "map_lift (restrict_global_for gs)
             (transfer_lift is_bot_state (apply_tf (sign_tf_for gs) a)
               (assemble_local_global (s1 (Inl u)) (glob_env s1)))
           \<le> map_lift (restrict_global_for gs)
             (transfer_lift is_bot_state (apply_tf (sign_tf_for gs) a)
               (assemble_local_global (s2 (Inl u)) (glob_env s2)))"
    by (rule map_lift_mono[OF restrict_global_for_mono
          transfer_lift_mono[OF sign_tf_for_mono is_bot_state_mono
            assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])
  show ?thesis
    unfolding apply_etf_named sides_route_tree_const
    using d by (auto simp: le_fun_def)
qed

lemma named_comb_sides_mono:
  assumes "s1 \<le> s2"
  shows "sides_of_rhs (etf_combine (named_etf gs) dst cc ex) s1
         \<le> sides_of_rhs (etf_combine (named_etf gs) dst cc ex) s2"
proof -
  have d: "map_lift (restrict_global_for gs)
             (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
               (assemble_local_global (s1 (Inl cc)) (glob_env s1))
               (assemble_local_global (s1 (Inl ex)) (glob_env s1)))
           \<le> map_lift (restrict_global_for gs)
             (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
               (assemble_local_global (s2 (Inl cc)) (glob_env s2))
               (assemble_local_global (s2 (Inl ex)) (glob_env s2)))"
    by (rule map_lift_mono[OF restrict_global_for_mono
          transfer_lift2_mono[OF combine_collect_abs_mono is_bot_state_mono
            assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]
            assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])
  show ?thesis
    unfolding etf_combine_named sides_route_combine_const
    using d by (auto simp: le_fun_def)
qed

lemma named_edge_static: "static_deps (apply_etf (named_etf gs) a u)"
  unfolding apply_etf_named static_deps_def by (simp add: dep_aux_route_tree)

lemma named_comb_static: "static_deps (etf_combine (named_etf gs) dst cc ex)"
  unfolding etf_combine_named static_deps_def by (simp add: dep_aux_route_combine)

lemma named_edge_dep: "Inl z \<in> dep_aux \<sigma> (apply_etf (named_etf gs) b z)"
  unfolding apply_etf_named by (simp add: dep_aux_route_tree)

lemma named_comb_dep1: "Inl cc \<in> dep_aux \<sigma> (etf_combine (named_etf gs) dst cc ex)"
  unfolding etf_combine_named by (simp add: dep_aux_route_combine)

lemma named_comb_dep2: "Inl ex \<in> dep_aux \<sigma> (etf_combine (named_etf gs) dst cc ex)"
  unfolding etf_combine_named by (simp add: dep_aux_route_combine)

lemma named_enter_traverse_mono:
  assumes "s1 \<le> s2"
  shows "traverse_rhs (etf_enter (named_etf gs) fs as cl) s1
         \<le> traverse_rhs (etf_enter (named_etf gs) fs as cl) s2"
  unfolding etf_enter_named traverse_route_tree
  by (rule map_lift_mono[OF restrict_local_for_mono
        transfer_lift_mono[OF named_enter_mono is_bot_state_mono
          assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])

lemma named_enter_sides_mono:
  assumes "s1 \<le> s2"
  shows "sides_of_rhs (etf_enter (named_etf gs) fs as cl) s1
         \<le> sides_of_rhs (etf_enter (named_etf gs) fs as cl) s2"
proof -
  have d: "map_lift (restrict_global_for gs)
             (transfer_lift is_bot_state (enter\<^sup># (sign_tf_for gs) fs as)
               (assemble_local_global (s1 (Inl cl)) (glob_env s1)))
           \<le> map_lift (restrict_global_for gs)
             (transfer_lift is_bot_state (enter\<^sup># (sign_tf_for gs) fs as)
               (assemble_local_global (s2 (Inl cl)) (glob_env s2)))"
    by (rule map_lift_mono[OF restrict_global_for_mono
          transfer_lift_mono[OF named_enter_mono is_bot_state_mono
            assemble_local_global_mono[OF le_funD[OF assms] glob_env_mono[OF assms]]]])
  show ?thesis
    unfolding etf_enter_named sides_route_tree_const
    using d by (auto simp: le_fun_def)
qed

lemma named_enter_static: "static_deps (etf_enter (named_etf gs) fs as cl)"
  unfolding etf_enter_named static_deps_def by (simp add: dep_aux_route_tree)

lemma named_enter_dep: "Inl cl \<in> dep_aux \<sigma> (etf_enter (named_etf gs) fs as cl)"
  unfolding etf_enter_named by (simp add: dep_aux_route_tree)

lemma named_enter_inr_local_bot:
  "\<And>fs as cl \<sigma>' g. local_bot_on_locals_lift gs (sides_of_rhs (etf_enter (named_etf gs) fs as cl) \<sigma>' (Inr g))"
  unfolding etf_enter_named by (rule sides_inr_local_bot_route_tree_const)

text \<open>
  A route_tree/route_combine tree writes exactly one Side, so all_sides collapses to
  that single written value regardless of which key route selected -- the tree's
  local Answer and its Side agree on reachability whenever they agree on the
  underlying transfer_lift/transfer_lift2 result, which is exactly what
  traverse_route_tree/traverse_route_combine already state.
\<close>

lemma all_sides_route_tree:
  "all_sides (route_tree gs route f u) \<sigma>
   = map_lift (restrict_global_for gs)
       (transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)))"
  unfolding route_tree_def
  apply (simp add: Let_def glob_env_gname sup_assoc)
  apply (cases "map_lift (restrict_global_for gs)
                  (transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg))))")
   apply (simp_all add: sup_lifted.simps)
  done

lemma all_sides_route_combine:
  "all_sides (route_combine gs route dst cc ex) \<sigma>
   = map_lift (restrict_global_for gs)
       (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
         (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
         (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>)))"
  unfolding route_combine_def
  apply (simp add: Let_def glob_env_gname sup_assoc)
  apply (cases "map_lift (restrict_global_for gs)
                  (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
                    (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg)))
                    (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr Gpos) \<squnion> \<sigma> (Inr Gneg))))")
   apply (simp_all add: sup_lifted.simps)
  done

lemma reachability_coherent_route_tree:
  "reachability_coherent_tree (route_tree gs route f u) \<sigma>"
  unfolding reachability_coherent_tree_def
  by (cases "transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>))")
     (simp_all add: traverse_route_tree all_sides_route_tree)

lemma reachability_coherent_route_combine:
  "reachability_coherent_tree (route_combine gs route dst cc ex) \<sigma>"
  unfolding reachability_coherent_tree_def
  by (cases "transfer_lift2 is_bot_state (combine\<^sup># gs dst)
               (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>))
               (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>))")
     (simp_all add: traverse_route_combine all_sides_route_combine)

lemma named_edge_coherent:
  "\<And>a u \<sigma>'. reachability_coherent_tree (apply_etf (named_etf gs) a u) \<sigma>'"
  unfolding apply_etf_named by (rule reachability_coherent_route_tree)

lemma named_enter_coherent:
  "\<And>cl fs as \<sigma>'. reachability_coherent_tree (etf_enter (named_etf gs) fs as cl) \<sigma>'"
  unfolding etf_enter_named by (rule reachability_coherent_route_tree)

lemma named_comb_coherent:
  "\<And>cc ex dst \<sigma>'. reachability_coherent_tree (etf_combine (named_etf gs) dst cc ex) \<sigma>'"
  unfolding etf_combine_named by (rule reachability_coherent_route_combine)

lemma named_etf_is_mono_eq:
  "is_mono_eq (side_cfg_T_eff gs g (named_etf gs) bot0 s0 gseed)"
  by (rule side_cfg_T_eff_is_mono_eq_gen[OF named_traverse_mono named_enter_traverse_mono named_comb_traverse_mono])

lemma named_etf_mono_sides:
  "mono_sides (side_cfg_T_eff gs g (named_etf gs) bot0 s0 gseed)"
  by (rule side_cfg_T_eff_mono_sides_gen[OF named_sides_mono named_enter_sides_mono named_comb_sides_mono])

lemma named_etf_mono_deps:
  "mono_deps (side_cfg_T_eff gs g (named_etf gs) bot0 s0 gseed)"
  by (rule side_cfg_T_eff_mono_deps_gen[OF named_edge_static named_enter_static named_comb_static])

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
  fixes \<Pi> ps mnm main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) (named_etf gs) bot s0 Gpos
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "t \<in> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (named_etf gs) bot s0 Gpos
         (cfg_exit (compile_prog \<Pi> ps mnm main)))"
proof -
  have sub: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using s_sound by simp
  have collect:
    "ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))
     \<le> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (named_etf gs) bot s0 Gpos
         (cfg_exit (compile_prog \<Pi> ps mnm main)))"
    by (rule side_analyse_eff_collect_sound_exit_ltr
          [OF named_etf_sound named_etf_is_mono_eq named_etf_mono_sides named_etf_mono_deps
              side_solve_dom sub
              named_edge_dep named_enter_dep named_comb_dep1 named_comb_dep2
              named_edge_static named_enter_static named_comb_static
              named_edge_inr_local_bot named_enter_inr_local_bot named_comb_inr_local_bot
              named_edge_coherent named_enter_coherent named_comb_coherent])
  show ?thesis
    using collect collect_exit by blast
qed

section \<open>Reading and writing one named global\<close>

text \<open>\<open>sideg_tree\<close> queries the local unknown and exactly one named global, then
  routes the global result to one selected slot. Its soundness statement therefore uses
  \<open>side_env_g\<close> rather than the join of every global slot.\<close>

definition sideg_tree ::
  "(vname \<Rightarrow> bool) \<Rightarrow> gname \<Rightarrow> gname \<Rightarrow> (sign abs_state \<Rightarrow> sign abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp, gname, sign abs_state) strategy_tree"
where
  "sideg_tree gs gread gwrite f u = do {
     su \<leftarrow> read_local u;
     g \<leftarrow> read_global gread;
     let res = f (su \<squnion> g);
     depend_on gwrite (restrict_global_for gs res) (answer (restrict_local_for gs res))
   }"

text \<open>
  The tree reads exactly the local unknown u and the one named global gread --
  the man.global g contract: a single selected global, not the joined view.
\<close>
lemma dep_aux_sideg_tree:
  "dep_aux \<sigma> (sideg_tree gs gread gwrite f u) = {Inl u, Inr gread}"
  unfolding sideg_tree_def by (simp add: Let_def)

lemma traverse_sideg_tree:
  "traverse_rhs (sideg_tree gs gread gwrite f u) \<sigma>
   = restrict_local_for gs (f (side_env_g \<sigma> gread u))"
  unfolding sideg_tree_def side_env_g_def by (simp add: Let_def)

text \<open>
  The man.sideg g' contract: the whole global contribution lands in the single
  selected slot gwrite; every other named slot receives bot.
\<close>
lemma sides_sideg_tree:
  "sides_of_rhs (sideg_tree gs gread gwrite f u) \<sigma>
   = (\<lambda>_. \<bottom>)(Inr gwrite := restrict_global_for gs (f (side_env_g \<sigma> gread u)))"
  unfolding sideg_tree_def side_env_g_def by (simp add: Let_def)

lemma etf_full_sideg_tree:
  "etf_full (sideg_tree gs gread gwrite f u) \<sigma> = f (side_env_g \<sigma> gread u)"
  unfolding etf_full_def sideg_tree_def side_env_g_def
  by (simp add: Let_def restrict_local_for_global_join)

text \<open>
  Soundness of a man.sideg assignment stated through the single-global read: if a
  concrete store concretises the selected-global source view side_env_g, its
  post-store concretises the reassembled full result.  This is the manager-style
  contract -- read one named global, write one named global -- for the sign
  assignment transfer.
\<close>
theorem sideg_assign_sound:
  assumes "s \<in> \<lbrakk>side_env_g \<sigma> gread u\<rbrakk>"
  shows "s(x := aval a s)
         \<in> \<lbrakk>etf_full (sideg_tree gs gread gwrite
                       (apply_tf (sign_tf_for gs) (EA_Assign x a)) u) \<sigma>\<rbrakk>"
proof -
  have "s(x := aval a s) \<in> \<lbrakk>assign\<^sup># (sign_tf_for gs) x a (side_env_g \<sigma> gread u)\<rbrakk>"
    using assign_sign_sound[OF assms] by (simp add: sign_tf_for_def)
  thus ?thesis by (simp add: etf_full_sideg_tree)
qed

subsection \<open>Two named keys: read one, write the other\<close>

text \<open>
  Instantiating gread = Gpos, gwrite = Gneg exhibits the two-key routing the
  single-pot unit interface cannot express: the contribution lands only in Gneg,
  and the Gpos slot the transfer read is left untouched by this tree.
\<close>
lemma sideg_pos_neg_writes_only_neg:
  "sides_of_rhs (sideg_tree gs Gpos Gneg f u) \<sigma> (Inr Gpos) = \<bottom>"
  by (simp add: sides_sideg_tree)

lemma sideg_pos_neg_reads_only_pos:
  "dep_aux \<sigma> (sideg_tree gs Gpos Gneg f u) = {Inl u, Inr Gpos}"
  by (simp add: dep_aux_sideg_tree)

text \<open>
  The joined-view bridge: because a single-global read is tighter than the joined
  side_env (side_env_g_le_side_env), every concrete store of the selected-global
  view is also a concrete store of the joined view.  A theorem phrased against
  the joined global environment therefore subsumes the man.global read.
\<close>
lemma gamma_side_env_g_subset_side_env:
  "\<lbrakk>side_env_g \<sigma> g v\<rbrakk> \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
  by (rule gamma_state_mono[OF side_env_g_le_side_env])

end

