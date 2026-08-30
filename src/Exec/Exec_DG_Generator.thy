section \<open>The executable equation generator and its transport\<close>

text \<open>
  The generator that turns a compiled CFG into an executable D/G equation system, and the
  transport of one node's equation --- value, side effects and dependencies --- through the
  readback. \<open>dg_reader_commute_gen\<close> states that transport once for an arbitrary pair
  of readers preserving \<open>bot\<close> and \<open>(\<squnion>)\<close>; every concrete readback in the pipeline is one of
  its instances.
\<close>

theory Exec_DG_Generator
  imports
    Exec_DG_Trees
begin
subsection \<open>The executable D/G equation generator\<close>

text \<open>
  The executable generator is the same polymorphic seeded keyed generator
  (\<open>side_cfg_T_eff_keyed_seed_dg\<close>) the abstract \<open>sound_dg_spec.dg_gen\<close> uses,
  instantiated at an \<open>'a exec_dg_st\<close>-valued analysis spec.  Unit context (\<open>gkey = (\<lambda>_. ())\<close>),
  no procedure-entry seed (\<open>frame_seed = (\<lambda>_. bot)\<close>).
\<close>

definition dg_cmb_at_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec
     \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pname
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_at_of S ctx ca cc p =
     map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx))
       (dg_spec_combine_tree S (call_info_of ca p) cc (FunctionResult p)))"

definition dg_cmb_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_of S g route ctx ca cc v =
     side_rhs_fold_dg bot (map (dg_cmb_at_of S ctx ca cc) (static_targets g v cc ca))"

definition dg_extra_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree list"
where
  "dg_extra_of S g route ctx v =
     map (\<lambda>(cl, ca).
       map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx))
         (dg_edge_tree (dgs_enter S (call_info_of ca (case v of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined)))
            cl))) (entry_call_list g v)"

definition dg_gen_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) eqsT"
where
  "dg_gen_of S g bot0 s0d s0g =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. ())
       (\<lambda>_ _ _ _. ()) (dg_cmb_of S g) (dg_extra_of S g) g S bot0 s0d s0g"

subsection \<open>Side-effect commutation for the generator\<close>

lemma sides_of_rhs_Inl_bot: "sides_of_rhs t \<sigma> (Inl a) = bot"
  by (induction t arbitrary: \<sigma>) (auto simp: Let_def)

subsection \<open>Generic \<open>se_constraint_holds\<close> builders\<close>

text \<open>
  The most important missing abstraction is assembling a node's
  \<open>se_constraint_holds\<close> obligation for the abstract, hook-generated equation
  system from a scoped \<^const>\<open>dg_refines_on\<close> fact -- itself already produced
  by composing the item-1 hook-wrapper equations, the item-2
  singleton-generator reductions, and a domain transfer-agreement lemma.
  \<open>outside\<close> is deliberately an arbitrary bound (as in
  \<open>le_lift_if_dg_refines_on_and_le\<close>) rather than a fixed top element, so no
  domain has to supply one it does not have; an instance's own completed
  sigma (\<^const>\<open>completed_sigma_abs\<close>) unfolds \<open>complete_abs_on\<close>/
  \<open>fun_of_exec_dg_st_for\<close> back to whatever concrete bound it fixed.
\<close>

lemma complete_abs_on_bot_le_fun_of_exec_dg_st_for:
  fixes exec_bound :: "'a::order_bot exec_dg_st" and universe :: "location set"
  shows "complete_abs_on gs universe (\<lambda>_. bot) exec_bound \<le> fun_of_exec_dg_st_for gs exec_bound"
  by (rule le_funI) (simp add: complete_abs_on_def fun_of_exec_dg_st_for_def)

lemma local_bound_of_dg_refines:
  fixes v :: pp
    and exec_local :: "'a::bounded_semilattice_sup_bot exec_dg_st"
    and abs_local :: "'a abs_state"
  assumes exec_le: "exec_local \<le> exec_bound"
    and dg_ref: "dg_refines_on (set (locations_of v))
        (DG exec_local exec_side) (DG abs_local abs_side)"
    and outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
        abs_local x \<le> outside x"
  shows "abs_local \<le> complete_abs_on gs (set (locations_of v)) outside exec_bound"
proof -
  have refines: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q exec_local location = abs_local (location_vname location)"
    using dg_refines_onD_local[OF dg_ref] by simp
  show ?thesis
    by (rule le_lift_if_dg_refines_on_and_le[OF refines outside_le exec_le])
qed

lemma side_bound_of_dg_refines:
  fixes v :: pp
    and exec_side :: "'a::bounded_semilattice_sup_bot exec_dg_st"
    and abs_side :: "'a abs_state"
  assumes dg_ref_side: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q exec_side location = abs_side (location_vname location)"
    and outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
        abs_side x \<le> bot"
    and le: "exec_side \<le> exec_bound"
  shows "abs_side \<le> fun_of_exec_dg_st_for gs exec_bound"
proof -
  have lifted: "abs_side \<le> complete_abs_on gs (set (locations_of v)) (\<lambda>_. bot) exec_bound"
    by (rule le_lift_if_dg_refines_on_and_le[OF dg_ref_side outside_le le])
  show ?thesis
    using order_trans[OF lifted complete_abs_on_bot_le_fun_of_exec_dg_st_for] .
qed

text \<open>Bundling the two halves of \<open>se_constraint_holds\<close> at a node: the local
  bound and the side bound above, plus the structural fact just proved
  (\<open>sides_of_rhs_Inl_bot\<close>) that side effects at a node never touch \<open>Inl\<close>
  keys.\<close>

lemma se_constraint_holds_of_dg_refines:
  fixes v_key :: 'k
    and abs_local_val :: "'a::bounded_semilattice_sup_bot abs_state"
    and abs_side_val :: "'a abs_state"
  assumes local_le: "abs_local_val \<le> locals (sigma (Inl v_key))"
    and side_le: "abs_side_val \<le> globs (sigma (Inr ()))"
    and traverse_locals: "locals traverse_val = abs_local_val"
    and traverse_globs_bot: "globs traverse_val = bot"
    and sides_val_Inl_bot: "\<And>x. sides_val (Inl x) = bot"
    and sides_locals_bot: "locals (sides_val (Inr ())) = bot"
    and sides_globs: "globs (sides_val (Inr ())) = abs_side_val"
  shows "traverse_val \<le> sigma (Inl v_key) \<and> sides_val \<le> sigma"
proof (intro conjI le_funI)
  show "traverse_val \<le> sigma (Inl v_key)"
    unfolding less_eq_dg_state_def
    using local_le traverse_locals traverse_globs_bot by simp
next
  fix k show "sides_val k \<le> sigma k"
  proof (cases k)
    case (Inl x)    then show ?thesis
      by (simp add: sides_val_Inl_bot less_eq_dg_state_def bot_dg_state_def)
  next
    case (Inr y)
    then show ?thesis
      using side_le sides_locals_bot sides_globs by (simp add: less_eq_dg_state_def)
  qed
qed

subsection \<open>Generic per-node post-solution transport\<close>

text \<open>
  \<open>placed_hook_se_edge\<close> fuses what an instance would otherwise prove in two
  steps -- a \<^const>\<open>dg_refines_on\<close> bridge from a raw transfer-agreement
  hypothesis, then \<open>se_constraint_holds_of_dg_refines\<close> -- into one
  call, generic over the CFG, the placement policy, and the domain.
  \<^const>\<open>placed_dg_gen_of_strict\<close> and \<^const>\<open>placed_abs_dg_gen_of\<close> are
  unfolded internally at the single-incoming-edge/no-calls node shape, so no
  instance needs its own single-edge reduction lemma.
  \<^const>\<open>completed_sigma_abs\<close> is fixed as the abstract valuation, so the
  outside-scope bound at every node comes from \<^const>\<open>complete_abs_on\<close>
  instead of being re-derived per instance.
\<close>

lemma placed_hook_se_edge:
  fixes gs :: "vname => bool"
    and owner_of :: "pp => pname"
    and locations_of :: "pp => location list"
    and keep_local publish_side :: "scoped_location => bool"
    and transfer_st :: "edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and transfer_abs :: "edge_action => 'a abs_state => 'a abs_state"
    and enter_st :: "call_info => 'a exec_dg_st => 'a exec_dg_st"
    and enter_abs :: "call_info => 'a abs_state => 'a abs_state \<times> 'a abs_state"
    and g :: cfg and bot0 :: "'a exec_dg_st" and s0d s0g :: "'a exec_dg_st"
    and bot0_abs :: "'a abs_state" and s0d_abs s0g_abs :: "'a abs_state" and top_val :: 'a
    and sigma_exec :: "pp \<times> unit + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and v u :: pp and a :: edge_action
  defines "sigma_abs \<equiv> completed_sigma_abs gs locations_of top_val sigma_exec"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "intra_predecessor_list g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0_eq: "bot0 = bot" and bot0_abs_eq: "bot0_abs = bot"
    and top_ge: "\<And>y. y \<le> top_val"
    and se: "se_constraint_holds
      (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (v, ())"
    and canonical: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      location = location_of gs (location_vname location)"
    and raw: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)) location =
      transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs) (location_vname location)"
    and side_outside_raw: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      publish_side (owner_of v, location_of gs x) \<longrightarrow>
      transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs) x \<le> bot"
  shows "se_constraint_holds
    (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
      bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (v, ())"
proof -
  have exec_eq: "eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec =
      DG (project_resolved_on_strict (owner_of v) (locations_of v) keep_local
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec))) bot"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: not_entry pred no_combine no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      traverse_rhs_placed_dg_edge_of_strict dg_hook_D_def dg_hook_G_def)
  have exec_sides: "sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()) =
      DG bot (project_resolved_on_strict (owner_of v) (locations_of v) publish_side
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)))"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: not_entry pred no_combine no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      sides_of_rhs_placed_dg_edge_of_strict dg_hook_D_def dg_hook_G_def)
  have abs_eq: "eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs =
      DG (project_abs_on (owner_of v) gs keep_local
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs))) bot"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: not_entry pred no_combine no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      traverse_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def)
  have abs_sides: "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()) =
      DG bot (project_abs_on (owner_of v) gs publish_side
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)))"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: not_entry pred no_combine no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      sides_of_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def)
  have bridge: "dg_refines_on (set (locations_of v))
      (DG (project_resolved_on_strict (owner_of v) (locations_of v) keep_local
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)))
        (project_resolved_on_strict (owner_of v) (locations_of v) publish_side
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec))))
      (DG (project_abs_on (owner_of v) gs keep_local
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)))
        (project_abs_on (owner_of v) gs publish_side
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs))))"
    by (rule dg_refines_on_project_strict[OF raw canonical])
  have dg_ref: "dg_refines_on (set (locations_of v))
      (DG (locals (eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
              transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec))
        (globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
              transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()))))
      (DG (locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
              bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs))
        (globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
              bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()))))"
    using bridge by (simp add: exec_eq exec_sides abs_eq abs_sides)
  have exec_le: "locals (eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec) \<le>
      locals (sigma_exec (Inl (v, ())))"
    using se_constraint_holds_local[OF se] by (simp add: less_eq_dg_state_def)
  have exec_side_le: "globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ())) \<le>
      globs (sigma_exec (Inr ()))"
    using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  have outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) x \<le> top_val"
    by (simp add: abs_eq project_abs_on_def project_component_def top_ge)
  have local_le: "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) \<le> locals (sigma_abs (Inl (v, ())))"
    using local_bound_of_dg_refines[
        where locations_of = locations_of and outside = "\<lambda>_. top_val",
        OF exec_le dg_ref outside_le]
    by (simp add: sigma_abs_def completed_sigma_abs_Inl)
  have side_outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) x \<le> bot"
    by (simp add: abs_sides project_abs_on_def project_component_def side_outside_raw)
  have dg_ref_side: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q (globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
          transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()))) location =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
          bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) (location_vname location)"
    using dg_refines_onD_side[OF dg_ref] by simp
  have side_le: "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
    using side_bound_of_dg_refines[OF dg_ref_side side_outside_le exec_side_le]
    by (simp add: sigma_abs_def completed_sigma_abs_Inr)
  show ?thesis
    unfolding se_constraint_holds_def
  proof (rule se_constraint_holds_of_dg_refines)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) \<le> locals (sigma_abs (Inl (v, ())))"
      by (rule local_le)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
      by (rule side_le)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) =
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs)"
      by (rule refl)
    show "globs (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) = bot"
      by (simp add: abs_eq)
    fix x show "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inl x) = bot"
      by (simp add: sides_of_rhs_Inl_bot)
  next
    show "locals (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) = bot"
      by (simp add: abs_sides)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()))"
      by (rule refl)
  qed
qed

text \<open>
  \<open>placed_hook_se_entry\<close> is the entry-node counterpart of \<open>placed_hook_se_edge\<close>:
  the seed values \<open>s0d\<close>/\<open>s0g\<close> take the place of a predecessor's traversal
  value, so the obligation is a direct agreement between the two seeds
  instead of a per-edge transfer-agreement hypothesis.
\<close>

lemma placed_hook_se_entry:
  fixes gs :: "vname => bool"
    and owner_of :: "pp => pname"
    and locations_of :: "pp => location list"
    and keep_local publish_side :: "scoped_location => bool"
    and transfer_st :: "edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and transfer_abs :: "edge_action => 'a abs_state => 'a abs_state"
    and enter_st :: "call_info => 'a exec_dg_st => 'a exec_dg_st"
    and enter_abs :: "call_info => 'a abs_state => 'a abs_state \<times> 'a abs_state"
    and g :: cfg and bot0 :: "'a exec_dg_st" and s0d s0g :: "'a exec_dg_st"
    and bot0_abs :: "'a abs_state" and s0d_abs s0g_abs :: "'a abs_state" and top_val :: 'a
    and sigma_exec :: "pp \<times> unit + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  defines "sigma_abs \<equiv> completed_sigma_abs gs locations_of top_val sigma_exec"
  assumes entry_no_edge: "intra_predecessor_list g (cfg_entry g) = []"
    and entry_no_combine: "return_call_action_list g (cfg_entry g) = []"
    and entry_no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0_eq: "bot0 = bot" and bot0_abs_eq: "bot0_abs = bot"
    and top_ge: "\<And>y. y \<le> top_val"
    and se: "se_constraint_holds
      (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (cfg_entry g, ())) sigma_exec (cfg_entry g, ())"
    and local_raw: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
      lookup_resolved_st_q s0d location = s0d_abs (location_vname location)"
    and side_raw: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
      lookup_resolved_st_q s0g location = s0g_abs (location_vname location)"
    and side_outside_raw: "\<And>x. location_of gs x \<notin> set (locations_of (cfg_entry g)) \<Longrightarrow>
      s0g_abs x \<le> bot"
  shows "se_constraint_holds
    (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
      bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (cfg_entry g, ())"
proof -
  have exec_eq: "eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (cfg_entry g, ()) sigma_exec = DG s0d bot"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have exec_sides: "sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (cfg_entry g, ())) sigma_exec (Inr ()) = DG bot s0g"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have abs_eq: "eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs = DG s0d_abs bot"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have abs_sides: "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ()) = DG bot s0g_abs"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have local_le: "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) \<le> locals (sigma_abs (Inl (cfg_entry g, ())))"
  proof -
    have exec_le: "s0d \<le> locals (sigma_exec (Inl (cfg_entry g, ())))"
      using se_constraint_holds_local[OF se] by (simp add: exec_eq less_eq_dg_state_def)
    have refines: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
        lookup_resolved_st_q s0d location = s0d_abs (location_vname location)"
      by (rule local_raw)
    have outside: "\<And>x. location_of gs x \<notin> set (locations_of (cfg_entry g)) \<Longrightarrow> s0d_abs x \<le> top_val"
      by (simp add: top_ge)
    have lifted: "s0d_abs \<le> complete_abs_on gs (set (locations_of (cfg_entry g))) (\<lambda>_. top_val)
        (locals (sigma_exec (Inl (cfg_entry g, ()))))"
      by (rule le_lift_if_dg_refines_on_and_le[
          where gs = gs and universe = "set (locations_of (cfg_entry g))" and outside = "\<lambda>_. top_val",
          OF refines outside exec_le])
    show ?thesis
      unfolding abs_eq
      by (simp add: sigma_abs_def completed_sigma_abs_Inl lifted)
  qed
  have side_le: "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
  proof -
    have exec_le: "s0g \<le> globs (sigma_exec (Inr ()))"
      using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
      by (simp add: exec_sides less_eq_dg_state_def)
    have lifted: "s0g_abs \<le> fun_of_exec_dg_st_for gs (globs (sigma_exec (Inr ())))"
      by (rule side_bound_of_dg_refines[
          where locations_of = locations_of and v = "cfg_entry g" and gs = gs,
          OF side_raw side_outside_raw exec_le])
    show ?thesis
      unfolding abs_sides
      by (simp add: sigma_abs_def completed_sigma_abs_Inr lifted)
  qed
  show ?thesis
    unfolding se_constraint_holds_def
  proof (rule se_constraint_holds_of_dg_refines)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) \<le> locals (sigma_abs (Inl (cfg_entry g, ())))"
      by (rule local_le)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
      by (rule side_le)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) =
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs)"
      by (rule refl)
    show "globs (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) = bot"
      by (simp add: abs_eq)
    fix x show "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inl x) = bot"
      by (simp add: sides_of_rhs_Inl_bot)
  next
    show "locals (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) = bot"
      by (simp add: abs_sides)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ()))"
      by (rule refl)
  qed
qed



lemma sides_dg_edge_tree_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (dg_edge_tree step_st u) \<tau>_st k)
       = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (step_abs (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl u)))) (fun_of_exec_dg_st_for gs (globs (\<tau>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (fst (step_st (locals (\<tau>_st (Inl u))) (globs (\<tau>_st (Inr ())))))"
    using H[of "locals (\<tau>_st (Inl u))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_edge_tree_Inr fun_of_dg_st_for_def fun_of_resolved_st_q_for_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: sides_dg_edge_tree_Inl fun_of_dg_st_for_bot)
qed


lemma sides_dg_combine_tree_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (dg_combine_tree comb_st dst cc ex) \<tau>_st k)
       = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (comb_abs dst (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl cc)))) (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl ex)))) (fun_of_exec_dg_st_for gs (globs (\<tau>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (fst (comb_st dst (locals (\<tau>_st (Inl cc))) (locals (\<tau>_st (Inl ex))) (globs (\<tau>_st (Inr ())))))"
    using H[of dst "locals (\<tau>_st (Inl cc))" "locals (\<tau>_st (Inl ex))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_combine_tree_Inr fun_of_dg_st_for_def fun_of_resolved_st_q_for_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: dg_combine_tree_def fun_of_dg_st_for_bot)
qed

lemma sides_wrap_reduce:
  "sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk t)) \<sigma> (Inr gk)
     = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum lk (\<lambda>_. gk) z)) (Inr ())"
  apply (subst sides_map_gtree_unit[where r="\<lambda>_. gk", simplified])
  apply (subst sides_map_ltree_Inr)
  apply (simp add: sum.map_comp o_def)
  done


lemma sides_wrapped_edge_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_for_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_for gs (sides_of_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_edge_tree_commute_for)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_for_bot)
  qed
qed


lemma sides_wrapped_combine_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_for_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_for gs (sides_of_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_combine_tree_commute_for)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_for_bot)
  qed
qed


subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

lemma dep_aux_dg_edge_tree: "dep_aux \<sigma> (dg_edge_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_tree_def dep_aux_def)

lemma dep_aux_dg_combine_tree: "dep_aux \<sigma> (dg_combine_tree comb dst cc ex) = {Inl cc, Inl ex, Inr ()}"
  by (auto simp: dg_combine_tree_def dep_aux_def)

lemma dep_aux_Side: "dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t"
  by (simp add: dep_aux_def)

lemma dep_aux_map_gtree:
  "dep_aux \<sigma> (map_gtree r t) = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) (auto simp: dep_aux_def)

lemma dep_aux_wrapped_edge_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_edge_tree)

lemma dep_aux_wrapped_combine_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_combine_tree)

lemma dep_aux_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs) ts_st ts_abs"
  shows "dep_aux \<sigma>_st (side_rhs_fold_dg acc_st ts_st) = dep_aux \<sigma>_abs (side_rhs_fold_dg acc_abs ts_abs)"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: dep_aux_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hd: "dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs" using Cons.hyps(1) by simp
  have ih: "dep_aux \<sigma>_st (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st)
          = dep_aux \<sigma>_abs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) ts_abs)"
    by (rule Cons.IH)
  show ?case by (simp add: dep_aux_seqcomp hd ih)
qed

subsection \<open>Classifier-parametric fold transport\<close>

text \<open>
  Fold-commute lemmas reading through the generic \<open>fun_of_exec_dg_st_for gs\<close>/
  \<open>fun_of_dg_st_for gs\<close> readback.  \<open>dep_aux_side_rhs_fold_dg_commute\<close> already
  never mentions a readback, so it transports unchanged.
\<close>

lemma side_acc_dg_commute_for:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))
           ts_st ts_abs"
  shows "fun_of_exec_dg_st_for gs (side_acc_dg acc_st \<sigma>_st ts_st)
           = side_acc_dg (fun_of_exec_dg_st_for gs acc_st) (fun_of_dg_st_for gs \<circ> \<sigma>_st) ts_abs"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hl: "fun_of_exec_dg_st_for gs (locals (traverse_rhs t_st \<sigma>_st))
              = locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_for_simps(1))
  have h: "fun_of_exec_dg_st_for gs (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st))
           = fun_of_exec_dg_st_for gs acc_st \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))"
    unfolding fun_of_exec_dg_st_for_def
    by (simp add: fun_of_resolved_st_q_for_sup hl[unfolded fun_of_exec_dg_st_for_def])
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg.simps(2))
qed

lemma sides_side_rhs_fold_dg_commute_for:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k))
           ts_st ts_abs"
  shows "fun_of_dg_st_for gs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st k)
           = sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: fun_of_dg_st_for_bot bot_fun_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have sd: "fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih: "fun_of_dg_st_for gs (sides_of_rhs (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st k)
          = sides_of_rhs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))) ts_abs) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp fun_of_dg_st_for_sup sd ih comp_def)
qed

subsection \<open>Scoped fold transport\<close>

text \<open>
  Scoped counterparts of \<open>side_acc_dg_commute_for\<close> and
  \<open>sides_side_rhs_fold_dg_commute_for\<close>: instead of full \<open>fun_of_dg_st_for\<close>
  equality per tree, each tree's output need only \<^const>\<open>dg_refines_on\<close> a finite
  scope.  \<^const>\<open>dg_refines_on\<close> is closed under \<open>\<squnion>\<close> (\<open>dg_refines_on_sup\<close>) and holds
  trivially at \<open>bot\<close> (\<open>dg_refines_on_bot\<close>), so the fold argument is the same
  induction as the classifier-parametric version, just carried through
  \<open>dg_refines_on\<close> instead of equality.  Locals and sides are wrapped as
  \<open>DG _ bot\<close> / \<open>DG bot _\<close> so \<^const>\<open>dg_refines_on\<close>'s own locals/globs pairing
  can be reused unchanged.
\<close>

lemma bot_abs_state_apply [simp]:
  "(bot :: ('a::bot) abs_state) x = bot"
  by (simp add: bot_fun_def)

text \<open>
  Proved pointwise: \<open>lookup_resolved_st_q ... loc :: 'a\<close> and \<open>abs_val x :: 'a\<close> are
  both scalar, so the induction never touches a function-typed \<open>bot\<close> as a whole
  value --- the earlier attempt through \<^const>\<open>dg_refines_on\<close>'s \<open>DG _ bot\<close>
  wrapping kept producing syntactically different (though equal) eta-forms of
  \<open>bot :: 'a abs_state\<close> that \<open>simp\<close> would not always bridge.  The DG-wrapped
  \<^const>\<open>dg_refines_on\<close> statements below are recovered as thin corollaries of
  the pointwise facts.
\<close>

lemma side_acc_dg_lookup_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc))
           ts_st ts_abs"
    and acc_refines: "\<forall>loc\<in>universe. lookup_resolved_st_q acc_st loc = acc_abs (location_vname loc)"
  shows "\<forall>loc\<in>universe. lookup_resolved_st_q (side_acc_dg acc_st \<sigma>_st ts_st) loc =
      side_acc_dg acc_abs \<sigma>_abs ts_abs (location_vname loc)"
proof -
  have general: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc))
           ts_st ts_abs \<Longrightarrow>
      (\<forall>loc\<in>universe. lookup_resolved_st_q p loc = q (location_vname loc)) \<Longrightarrow>
      (\<forall>loc\<in>universe. lookup_resolved_st_q (side_acc_dg p \<sigma>_st ts_st) loc =
        side_acc_dg q \<sigma>_abs ts_abs (location_vname loc))"
    for p q ts_st ts_abs
  proof (induction ts_st ts_abs arbitrary: p q rule: list_all2_induct)
    case Nil
    thus ?case by simp
  next
    case (Cons t_st ts_st t_abs ts_abs)
    have hd: "\<forall>loc\<in>universe. lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
        locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc)"
      using Cons.hyps(1) by simp
    have step: "\<forall>loc\<in>universe. lookup_resolved_st_q (p \<squnion> locals (traverse_rhs t_st \<sigma>_st)) loc =
        (q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) (location_vname loc)"
      using Cons.prems hd by (simp add: sup_fun_def)
    show ?case
      using Cons.IH[where p = "p \<squnion> locals (traverse_rhs t_st \<sigma>_st)"
        and q = "q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)", OF step]
      by (metis side_acc_dg.simps(2))
  qed
  show ?thesis using list_refines acc_refines by (rule general)
qed

lemma side_acc_dg_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. dg_refines_on universe
             (DG (locals (traverse_rhs t_st \<sigma>_st)) bot)
             (DG (locals (traverse_rhs t_abs \<sigma>_abs)) bot))
           ts_st ts_abs"
    and acc_refines: "dg_refines_on universe (DG acc_st bot) (DG acc_abs bot)"
  shows "dg_refines_on universe
    (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)
    (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot)"
proof (rule dg_refines_onI)
  fix location assume loc: "location \<in> universe"
  have lr: "list_all2 (\<lambda>t_st t_abs. \<forall>l\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) l =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname l)) ts_st ts_abs"
    using list_refines by (rule list_all2_mono) (fastforce dest: dg_refines_onD_local)
  have ar: "\<forall>l\<in>universe. lookup_resolved_st_q acc_st l = acc_abs (location_vname l)"
    using acc_refines by (fastforce dest: dg_refines_onD_local)
  have combined: "\<forall>l\<in>universe. lookup_resolved_st_q (side_acc_dg acc_st \<sigma>_st ts_st) l =
      side_acc_dg acc_abs \<sigma>_abs ts_abs (location_vname l)"
    using ar lr side_acc_dg_lookup_refines_on by blast
  show "lookup_resolved_st_q (locals (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)) location =
      locals (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot) (location_vname location)"
    using combined loc by simp
next
  fix location assume "location \<in> universe"
  show "lookup_resolved_st_q (globs (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)) location =
      globs (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot) (location_vname location)"
    by simp
qed

lemma sides_side_rhs_fold_dg_lookup_refines_on:
  assumes sides_refines: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc))
           ts_st ts_abs"
  shows "\<forall>loc\<in>universe.
      lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))) loc =
      globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())) (location_vname loc)"
proof -
  have general: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc))
           ts_st ts_abs \<Longrightarrow>
      (\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg p ts_st) \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs (side_rhs_fold_dg q ts_abs) \<sigma>_abs (Inr ())) (location_vname loc))"
    for p q ts_st ts_abs
  proof (induction ts_st ts_abs arbitrary: p q rule: list_all2_induct)
    case Nil
    thus ?case by (simp add: bot_dg_state_def) 
  next
    case (Cons t_st ts_st t_abs ts_abs)
    have sd: "\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc)"
      using Cons.hyps(1) by simp
    have ih: "\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs
          (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs
          (side_rhs_fold_dg (q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) ts_abs) \<sigma>_abs (Inr ()))
          (location_vname loc)"
      by (rule Cons.IH)
    show ?case
      using sd ih
      by (simp add: sides_of_rhs_seqcomp sup_dg_state_def sup_fun_def)
  qed
  show ?thesis using sides_refines by (rule general)
qed

lemma sides_side_rhs_fold_dg_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. dg_refines_on universe
             (DG (locals (traverse_rhs t_st \<sigma>_st)) bot)
             (DG (locals (traverse_rhs t_abs \<sigma>_abs)) bot)
           \<and> dg_refines_on universe
             (DG bot (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))))
             (DG bot (globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())))))
           ts_st ts_abs"
  shows "dg_refines_on universe
    (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))
    (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ()))))"
proof (rule dg_refines_onI)
  fix location assume "location \<in> universe"
  show "lookup_resolved_st_q
      (locals (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))) location =
      locals (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())))) (location_vname location)"
    by simp
next
  fix location assume loc: "location \<in> universe"
  have sr: "list_all2 (\<lambda>t_st t_abs. \<forall>l\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) l =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname l)) ts_st ts_abs"
    using list_refines by (rule list_all2_mono) (fastforce dest: dg_refines_onD_side)
  have combined: "\<forall>l\<in>universe.
      lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))) l =
      globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())) (location_vname l)"
    by (rule sides_side_rhs_fold_dg_lookup_refines_on[OF sr])
  show "lookup_resolved_st_q
      (globs (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))) location =
      globs (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ()))))
        (location_vname location)"
    using combined loc by simp
qed

text \<open>
  Support and default transport through the same two folds, needed
  alongside the \<open>_refines_on\<close> facts above to invoke the inequality-lifting
  lemma at the generator level: the fold's own accumulator and each folded
  tree's local output are both scope-bounded and bot-defaulted (by the
  strict projection), so the whole fold is too.
\<close>

lemma side_acc_dg_support_bounded:
  fixes acc :: "('a::bounded_semilattice_sup_bot) exec_dg_st"
  assumes acc_bounded: "set (effective_support (rep_resolved_st acc)) \<subseteq> scope"
    and trees_bounded: "\<forall>t \<in> set ts.
      set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma)))) \<subseteq> scope"
  shows "set (effective_support (rep_resolved_st (side_acc_dg acc sigma ts))) \<subseteq> scope"
proof -
  have general: "set (effective_support (rep_resolved_st p)) \<subseteq> scope \<Longrightarrow>
      (\<forall>t \<in> set ts. set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma)))) \<subseteq> scope) \<Longrightarrow>
      set (effective_support (rep_resolved_st (side_acc_dg p sigma ts))) \<subseteq> scope"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by simp
  next
    case (Cons t ts)
    have step: "set (effective_support (rep_resolved_st
        (p \<squnion> locals (traverse_rhs t sigma)))) \<subseteq> scope"
    proof -
      have "set (effective_support (rep_resolved_st (p \<squnion> locals (traverse_rhs t sigma)))) \<subseteq>
          set (effective_support (rep_resolved_st p)) \<union>
          set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma))))"
        by (rule effective_support_rep_sup_resolved_st_q)
      also have "\<dots> \<subseteq> scope"
        using Cons.prems by auto
      finally show ?thesis .
    qed
    show ?case
      using Cons.IH[OF step] Cons.prems by simp
  qed
  show ?thesis using acc_bounded trees_bounded by (rule general)
qed

lemma side_acc_dg_default_bot:
  fixes acc :: "('a::bounded_semilattice_sup_bot) exec_dg_st"
  assumes acc_default: "resolved_default (rep_resolved_st acc) = (\<lambda>_. bot)"
    and trees_default: "\<forall>t \<in> set ts.
      resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) = (\<lambda>_. bot)"
  shows "resolved_default (rep_resolved_st (side_acc_dg acc sigma ts)) = (\<lambda>_. bot)"
proof -
  have general: "resolved_default (rep_resolved_st p) = (\<lambda>_. bot) \<Longrightarrow>
      (\<forall>t \<in> set ts. resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) = (\<lambda>_. bot)) \<Longrightarrow>
      resolved_default (rep_resolved_st (side_acc_dg p sigma ts)) = (\<lambda>_. bot)"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by simp
  next
    case (Cons t ts)
    have step: "resolved_default (rep_resolved_st
        (p \<squnion> locals (traverse_rhs t sigma))) = (\<lambda>_. bot)"
    proof -
      have "resolved_default (rep_resolved_st (p \<squnion> locals (traverse_rhs t sigma))) loc =
          resolved_default (rep_resolved_st p) loc \<squnion>
          resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) loc" for loc
        by (rule resolved_default_rep_sup_resolved_st_q)
      then show ?thesis
        using Cons.prems by (simp add: fun_eq_iff)
    qed
    show ?case
      using Cons.IH[OF step] Cons.prems by simp
  qed
  show ?thesis using acc_default trees_default by (rule general)
qed

lemma sides_side_rhs_fold_dg_support_bounded:
  assumes trees_bounded: "\<forall>t \<in> set ts.
    set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope"
  shows "set (effective_support (rep_resolved_st
    (globs (sides_of_rhs (side_rhs_fold_dg acc ts) sigma (Inr ()))))) \<subseteq> scope"
proof -
  have general: "(\<forall>t \<in> set ts.
      set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope) \<Longrightarrow>
      set (effective_support (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg p ts) sigma (Inr ()))))) \<subseteq> scope"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by (simp add: bot_dg_state_def)
  next
    case (Cons t ts)
    have hd: "set (effective_support (rep_resolved_st
        (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope"
      using Cons.prems by simp
    have ih: "set (effective_support (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg
          (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ()))))) \<subseteq> scope"
      by (rule Cons.IH) (use Cons.prems in simp)
    show ?case
    proof -
      have "set (effective_support (rep_resolved_st
          (globs (sides_of_rhs (side_rhs_fold_dg p (t # ts)) sigma (Inr ()))))) =
        set (effective_support (rep_resolved_st
          (globs (sides_of_rhs t sigma (Inr ())) \<squnion>
           globs (sides_of_rhs
             (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))))"
        by (simp add: sides_of_rhs_seqcomp sup_dg_state_def)
      also have "\<dots> \<subseteq>
          set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<union>
          set (effective_support (rep_resolved_st
            (globs (sides_of_rhs
              (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))))"
        by (rule effective_support_rep_sup_resolved_st_q)
      also have "\<dots> \<subseteq> scope" using hd ih by auto
      finally show ?thesis .
    qed
  qed
  show ?thesis using trees_bounded by (rule general)
qed

lemma sides_side_rhs_fold_dg_default_bot:
  assumes trees_default: "\<forall>t \<in> set ts.
    resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)"
  shows "resolved_default (rep_resolved_st
    (globs (sides_of_rhs (side_rhs_fold_dg acc ts) sigma (Inr ())))) = (\<lambda>_. bot)"
proof -
  have general: "(\<forall>t \<in> set ts.
      resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)) \<Longrightarrow>
      resolved_default (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg p ts) sigma (Inr ())))) = (\<lambda>_. bot)"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case 
      by (auto simp add: bot_dg_state_def resolved_default_rep_bot_resolved_st_q)
  next
    case (Cons t ts)
    have hd: "resolved_default (rep_resolved_st
        (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)"
      using Cons.prems by simp
    have ih: "resolved_default (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg
          (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))) = (\<lambda>_. bot)"
      by (rule Cons.IH) (use Cons.prems in simp)
    show ?case
    proof -
      have "resolved_default (rep_resolved_st
          (globs (sides_of_rhs (side_rhs_fold_dg p (t # ts)) sigma (Inr ())))) =
        resolved_default (rep_resolved_st
          (globs (sides_of_rhs t sigma (Inr ())) \<squnion>
           globs (sides_of_rhs
             (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ()))))"
        by (simp add: sides_of_rhs_seqcomp sup_dg_state_def)
      also have "\<dots> = (\<lambda>loc.
          resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) loc \<squnion>
          resolved_default (rep_resolved_st
            (globs (sides_of_rhs
              (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))) loc)"
        by (rule ext) (rule resolved_default_rep_sup_resolved_st_q)
      also have "\<dots> = (\<lambda>_. bot)"
        using hd ih by (simp add: fun_eq_iff)
      finally show ?thesis .
    qed
  qed
  show ?thesis using trees_default by (rule general)
qed

subsection \<open>Carrier-generic whole-CFG commute\<close>

text \<open>
  \<open>dg_tree_st_commute_for\<close> / \<open>part_post_solution_seed_dg_st_to_abs_for\<close> below (and their
  five supporting theorems) only ever use that the readback preserves \<open>bot\<close> and \<open>(\<squnion>)\<close>; no
  proof in the chain inspects \<open>fun_of_resolved_st_q_for\<close> or \<open>abs_state\<close> itself.
  \<open>dg_reader_commute_gen\<close> factors that out: a pair of local/global readers \<open>Floc\<close>/\<open>Fglob\<close>
  satisfying those two laws, from which every whole-tree and whole-equation-system commute
  fact in this chain is proved once.  The raw readback \<open>fun_of_dg_st_for\<close> and the
  reachability-lifted readback are both thin instances of the same engine.
\<close>

definition fun_of_dg_st_gen ::
  "('a \<Rightarrow> 'a2) \<Rightarrow> ('b \<Rightarrow> 'b2) \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a2, 'b2) dg_state"
where
  "fun_of_dg_st_gen Floc Fglob d = DG (Floc (locals d)) (Fglob (globs d))"

lemma fun_of_dg_st_gen_simps [simp]:
  "locals (fun_of_dg_st_gen Floc Fglob d) = Floc (locals d)"
  "globs (fun_of_dg_st_gen Floc Fglob d) = Fglob (globs d)"
  "fun_of_dg_st_gen Floc Fglob (DG a b) = DG (Floc a) (Fglob b)"
  by (simp_all add: fun_of_dg_st_gen_def)

locale dg_reader_commute_gen =
  fixes Floc :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'a2::bounded_semilattice_sup_bot"
    and Fglob :: "'b::bounded_semilattice_sup_bot \<Rightarrow> 'b2::bounded_semilattice_sup_bot"
  assumes Floc_bot: "Floc bot = bot"
      and Floc_sup: "\<And>x y. Floc (x \<squnion> y) = Floc x \<squnion> Floc y"
      and Fglob_bot: "Fglob bot = bot"
      and Fglob_sup: "\<And>x y. Fglob (x \<squnion> y) = Fglob x \<squnion> Fglob y"
begin

lemma Floc_mono: "x \<le> y \<Longrightarrow> Floc x \<le> Floc y"
  by (metis Floc_sup le_iff_sup)

lemma Fglob_mono: "x \<le> y \<Longrightarrow> Fglob x \<le> Fglob y"
  by (metis Fglob_sup le_iff_sup)

lemma fun_of_dg_st_gen_bot [simp]:
  "fun_of_dg_st_gen Floc Fglob (bot :: ('a,'b) dg_state) = bot"
  by (simp add: bot_dg_state_def Floc_bot Fglob_bot)

lemma fun_of_dg_st_gen_sup:
  "fun_of_dg_st_gen Floc Fglob (a \<squnion> b :: ('a,'b) dg_state)
     = fun_of_dg_st_gen Floc Fglob a \<squnion> fun_of_dg_st_gen Floc Fglob b"
  by (simp add: sup_dg_state_def Floc_sup Fglob_sup)

lemma fun_of_dg_st_gen_mono:
  "(a :: ('a,'b) dg_state) \<le> b \<Longrightarrow> fun_of_dg_st_gen Floc Fglob a \<le> fun_of_dg_st_gen Floc Fglob b"
  by (auto simp: less_eq_dg_state_def Floc_mono Fglob_mono)

subsubsection \<open>Per-tree traversal commutation\<close>

lemma traverse_dg_edge_tree_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (traverse_rhs (dg_edge_tree step_st u) \<sigma>_st)
           = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have "snd (step_abs (Floc (locals (\<sigma>_st (Inl u)))) (Fglob (globs (\<sigma>_st (Inr ())))))
        = Floc (snd (step_st (locals (\<sigma>_st (Inl u))) (globs (\<sigma>_st (Inr ())))))"
    using H[of "locals (\<sigma>_st (Inl u))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_edge_tree Fglob_bot)
qed

lemma traverse_wrapped_edge_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (traverse_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st)
       = traverse_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_gen Floc Fglob (traverse_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)))
        = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_gen Floc Fglob \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)))"
    using H by (rule traverse_dg_edge_tree_commute)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

lemma sides_dg_edge_tree_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (dg_edge_tree step_st u) \<tau>_st k)
       = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_gen Floc Fglob \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (step_abs (Floc (locals (\<tau>_st (Inl u)))) (Fglob (globs (\<tau>_st (Inr ())))))
        = Fglob (fst (step_st (locals (\<tau>_st (Inl u))) (globs (\<tau>_st (Inr ())))))"
    using H[of "locals (\<tau>_st (Inl u))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_edge_tree_Inr Floc_bot hg o_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: sides_dg_edge_tree_Inl)
qed

lemma sides_wrapped_edge_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_gen Floc Fglob \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_edge_tree_commute)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb])
  qed
qed

subsubsection \<open>Bundled per-tree transport relation\<close>

definition dg_tree_st_commute ::
  "('u + 'k \<Rightarrow> ('a,'b) dg_state) \<Rightarrow> ('u, 'k, ('a,'b) dg_state) strategy_tree
    \<Rightarrow> ('u, 'k, ('a2,'b2) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute \<sigma>_st t_st t_abs \<longleftrightarrow>
     fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
   \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k)
   \<and> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"

lemma dg_tree_st_commute_trav:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_sides:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_dep:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"
  by (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_trav:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st)
                    = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_travsides:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
              \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_dep:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_wrapped_edge:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "dg_tree_st_commute \<sigma>_st
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  unfolding dg_tree_st_commute_def
  by (intro conjI allI
        traverse_wrapped_edge_commute[where step_st=step_st and step_abs=step_abs, OF H]
        sides_wrapped_edge_commute[where step_st=step_st and step_abs=step_abs, OF H]
        dep_aux_wrapped_edge_eq)

text \<open>The same transport at an address-formed edge tree: the source is read through the
  valuation either way, so only the published key needs a case distinction.\<close>

lemma traverse_dg_edge_tree_at_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (traverse_rhs (dg_edge_tree_at step_st src gk) \<sigma>_st)
           = traverse_rhs (dg_edge_tree_at step_abs src gk) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have "snd (step_abs (Floc (locals (\<sigma>_st src))) (Fglob (globs (\<sigma>_st (Inr gk)))))
        = Floc (snd (step_st (locals (\<sigma>_st src)) (globs (\<sigma>_st (Inr gk)))))"
    using H[of "locals (\<sigma>_st src)" "globs (\<sigma>_st (Inr gk))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_edge_tree_at Fglob_bot)
qed

lemma sides_dg_edge_tree_at_commute:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (dg_edge_tree_at step_st src gk) \<sigma>_st k)
       = sides_of_rhs (dg_edge_tree_at step_abs src gk) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
proof (cases "k = Inr gk")
  case True
  have "fst (step_abs (Floc (locals (\<sigma>_st src))) (Fglob (globs (\<sigma>_st (Inr gk)))))
        = Fglob (fst (step_st (locals (\<sigma>_st src)) (globs (\<sigma>_st (Inr gk)))))"
    using H[of "locals (\<sigma>_st src)" "globs (\<sigma>_st (Inr gk))"]
    by (metis map_prod_simp fst_conv surj_pair)
  with True show ?thesis
    by (simp add: sides_dg_edge_tree_at Floc_bot)
next
  case False
  then show ?thesis
    by (simp add: sides_dg_edge_tree_at_other)
qed

lemma dg_tree_st_commute_at_edge:
  assumes H: "\<And>d g. map_prod Fglob Floc (step_st d g) = step_abs (Floc d) (Fglob g)"
  shows "dg_tree_st_commute \<sigma>_st
           (dg_edge_tree_at step_st src gk) (dg_edge_tree_at step_abs src gk)"
  unfolding dg_tree_st_commute_def
  by (intro conjI allI
        traverse_dg_edge_tree_at_commute[where step_st=step_st and step_abs=step_abs, OF H]
        sides_dg_edge_tree_at_commute[where step_st=step_st and step_abs=step_abs, OF H])
     (simp add: dep_aux_dg_edge_tree_at)

subsubsection \<open>Combine-tree transport, generic in the reader\<close>

text \<open>
  The combine-tree analogue of \<open>traverse_dg_edge_tree_commute\<close>/\<open>sides_dg_edge_tree_commute\<close>
  above, factored generically here rather than duplicated per reader: the diagonal
  (\<open>fun_of_exec_dg_st_for gs\<close>) and lifted (\<open>map_lift (fun_of_exec_dg_st_for gs)\<close>) instances
  both cite these directly, so only the \<open>dg_cmb_of\<close>-specific instantiation below is
  reader-specific, not the tree-structure reasoning itself.
\<close>

lemma traverse_dg_combine_tree_commute:
  assumes H: "\<And>dst dc de g. map_prod Fglob Floc (comb_st dst dc de g)
                        = comb_abs dst (Floc dc) (Floc de) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (traverse_rhs (dg_combine_tree comb_st dst cc ex) \<sigma>_st)
           = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have "snd (comb_abs dst (Floc (locals (\<sigma>_st (Inl cc)))) (Floc (locals (\<sigma>_st (Inl ex))))
              (Fglob (globs (\<sigma>_st (Inr ())))))
        = Floc (snd (comb_st dst (locals (\<sigma>_st (Inl cc))) (locals (\<sigma>_st (Inl ex)))
              (globs (\<sigma>_st (Inr ())))))"
    using H[of dst "locals (\<sigma>_st (Inl cc))" "locals (\<sigma>_st (Inl ex))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_combine_tree Fglob_bot)
qed

lemma traverse_wrapped_combine_commute:
  assumes H: "\<And>dst dc de g. map_prod Fglob Floc (comb_st dst dc de g)
                        = comb_abs dst (Floc dc) (Floc de) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_gen Floc Fglob (traverse_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_gen Floc Fglob \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_combine_tree_commute)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

lemma sides_dg_combine_tree_commute:
  assumes H: "\<And>dst dc de g. map_prod Fglob Floc (comb_st dst dc de g)
                        = comb_abs dst (Floc dc) (Floc de) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (dg_combine_tree comb_st dst cc ex) \<tau>_st k)
       = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_gen Floc Fglob \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (comb_abs dst (Floc (locals (\<tau>_st (Inl cc)))) (Floc (locals (\<tau>_st (Inl ex)))) (Fglob (globs (\<tau>_st (Inr ())))))
        = Fglob (fst (comb_st dst (locals (\<tau>_st (Inl cc))) (locals (\<tau>_st (Inl ex))) (globs (\<tau>_st (Inr ())))))"
    using H[of dst "locals (\<tau>_st (Inl cc))" "locals (\<tau>_st (Inl ex))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_combine_tree_Inr Floc_bot hg o_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: dg_combine_tree_def fun_of_dg_st_gen_bot)
qed

lemma sides_wrapped_combine_commute:
  assumes H: "\<And>dst dc de g. map_prod Fglob Floc (comb_st dst dc de g)
                        = comb_abs dst (Floc dc) (Floc de) (Fglob g)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_gen Floc Fglob \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_combine_tree_commute)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb])
  qed
qed

lemma dg_tree_st_commute_wrapped_combine:
  assumes H: "\<And>dst dc de g. map_prod Fglob Floc (comb_st dst dc de g)
                        = comb_abs dst (Floc dc) (Floc de) (Fglob g)"
  shows "dg_tree_st_commute \<sigma>_st
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex)))
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex)))"
  unfolding dg_tree_st_commute_def
proof (intro conjI)
  show "fun_of_dg_st_gen Floc Fglob (traverse_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st)
          = traverse_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
    by (rule traverse_wrapped_combine_commute[where comb_st=comb_st and comb_abs=comb_abs, OF H])
next
  show "\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
          = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  proof
    fix k
    show "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
            = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
      by (rule sides_wrapped_combine_commute[where comb_st=comb_st and comb_abs=comb_abs, OF H])
  qed
next
  show "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex)))
          = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex)))"
    by (rule dep_aux_wrapped_combine_eq)
qed

end

context dg_reader_commute_gen
begin

subsubsection \<open>Classifier-parametric fold transport\<close>

lemma side_acc_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))
           ts_st ts_abs"
  shows "Floc (side_acc_dg acc_st \<sigma>_st ts_st)
           = side_acc_dg (Floc acc_st) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) ts_abs"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hl: "Floc (locals (traverse_rhs t_st \<sigma>_st))
              = locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_gen_simps(1))
  have h: "Floc (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st))
           = Floc acc_st \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    by (simp add: Floc_sup hl)
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg.simps(2))
qed

lemma sides_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k))
           ts_st ts_abs"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st k)
           = sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: bot_fun_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have sd: "fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih: "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st k)
          = sides_of_rhs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))) ts_abs) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp fun_of_dg_st_gen_sup sd ih comp_def)
qed

subsubsection \<open>Per-node tree-list transport for the generator\<close>

lemma seed_dg_list_commute:
  assumes Hstep: "\<And>a d g'. map_prod Fglob Floc (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (Floc d) (Fglob g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "list_all2 (dg_tree_st_commute \<sigma>_st)
    (map (\<lambda>(src, a). apply_dg_spec_at S_st a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_st route_st ctx ca cc v) (call_site_list g v)
      @ extra_st route_st ctx v)
    (map (\<lambda>(src, a). apply_dg_spec_at S_abs a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_abs route_abs ctx ca cc v) (call_site_list g v)
      @ extra_abs route_abs ctx v)"
proof -
  have edge_elem: "\<And>src a. dg_tree_st_commute \<sigma>_st
        (apply_dg_spec_at S_st a src (gkey ctx))
        (apply_dg_spec_at S_abs a src (gkey ctx))"
    unfolding apply_dg_spec_at_def
    by (rule dg_tree_st_commute_at_edge[where step_st="dg_spec_step S_st a"
          and step_abs="dg_spec_step S_abs a" for a, OF Hstep])
  show ?thesis
    by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl
                   edge_elem Hcmb Hextra split_beta)
qed

subsubsection \<open>Equation-system transport for the generic generator\<close>

lemma eq_seed_dg_commute:
  assumes Hstep: "\<And>a d g'. map_prod Fglob Floc (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (Floc d) (Fglob g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "fun_of_dg_st_gen Floc Fglob (eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) (v, ctx) \<sigma>_st)
       = eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
               (Floc bot0) (Floc s0d) (Fglob s0g)) (v, ctx) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
proof -
  have la: "list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))
    (map (\<lambda>(src, a). apply_dg_spec_at S_st a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_st route_st ctx ca cc v) (call_site_list g v) @ extra_st route_st ctx v)
    (map (\<lambda>(src, a). apply_dg_spec_at S_abs a src (gkey ctx)) (pred_sel g v ctx)
      @ map (\<lambda>(cc, ca). cmb_abs route_abs ctx ca cc v) (call_site_list g v) @ extra_abs route_abs ctx v)"
    by (rule dg_list_commute_trav[OF seed_dg_list_commute
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  show ?thesis
    unfolding eq_side_cfg_T_eff_keyed_seed_dg
    by (simp add: Floc_bot Fglob_bot side_acc_dg_commute[OF la] Floc_sup)
qed

lemma sides_seed_dg_commute:
  assumes Hstep: "\<And>a d g'. map_prod Fglob Floc (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (Floc d) (Fglob g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs
             (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, ctx)) \<sigma>_st k)
       = sides_of_rhs
             (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
                (Floc bot0) (Floc s0d) (Fglob s0g) (v, ctx)) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k))
    (map (\<lambda>(src, a). apply_dg_spec_at S_st a src (gkey ctx)) (pred_sel g w ctx)
      @ map (\<lambda>(cc, ca). cmb_st route_st ctx ca cc w) (call_site_list g w) @ extra_st route_st ctx w)
    (map (\<lambda>(src, a). apply_dg_spec_at S_abs a src (gkey ctx)) (pred_sel g w ctx)
      @ map (\<lambda>(cc, ca). cmb_abs route_abs ctx ca cc w) (call_site_list g w) @ extra_abs route_abs ctx w)"
    by (rule dg_list_commute_travsides[OF seed_dg_list_commute
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  have fold: "\<And>w acc_st k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_rhs_fold_dg acc_st
        (map (\<lambda>(src, a). apply_dg_spec_at S_st a src (gkey ctx)) (pred_sel g w ctx)
          @ map (\<lambda>(cc, ca). cmb_st route_st ctx ca cc w) (call_site_list g w) @ extra_st route_st ctx w)) \<sigma>_st k)
     = sides_of_rhs (side_rhs_fold_dg (Floc acc_st)
        (map (\<lambda>(src, a). apply_dg_spec_at S_abs a src (gkey ctx)) (pred_sel g w ctx)
          @ map (\<lambda>(cc, ca). cmb_abs route_abs ctx ca cc w) (call_site_list g w) @ extra_abs route_abs ctx w))
          (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    by (rule sides_side_rhs_fold_dg_commute[OF la])
  have seed: "fun_of_dg_st_gen Floc Fglob (DG bot0 s0g) = DG (Floc bot0) (Fglob s0g)"
    by simp
  show ?thesis
    unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
    by (simp add: Let_def fun_upd_apply fun_of_dg_st_gen_sup seed fold Floc_bot Floc_sup)
qed

lemma dep_seed_dg_eq:
  assumes Hstep: "\<And>a d g'. map_prod Fglob Floc (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (Floc d) (Fglob g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "dep_aux \<sigma>_st (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, ctx))
       = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs bot0' s0d' s0g' (v, ctx))"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs)
    (map (\<lambda>(src, a). apply_dg_spec_at S_st a src (gkey ctx)) (pred_sel g w ctx)
      @ map (\<lambda>(cc, ca). cmb_st route_st ctx ca cc w) (call_site_list g w) @ extra_st route_st ctx w)
    (map (\<lambda>(src, a). apply_dg_spec_at S_abs a src (gkey ctx)) (pred_sel g w ctx)
      @ map (\<lambda>(cc, ca). cmb_abs route_abs ctx ca cc w) (call_site_list g w) @ extra_abs route_abs ctx w)"
    by (rule dg_list_commute_dep[OF seed_dg_list_commute
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  show ?thesis
    unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
    by (simp add: dep_aux_Side dep_aux_side_rhs_fold_dg_commute[OF la])
qed

subsubsection \<open>The post-solution transport theorem\<close>

theorem part_post_solution_seed_dg_st_to_abs:
  assumes Hstep: "\<And>a d g'. map_prod Fglob Floc (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (Floc d) (Fglob g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
      and pp: "part_post_solution
                 (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
              (Floc bot0) (Floc s0d) (Fglob s0g)) x (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) vars"
proof (intro conjI ballI)
  show "x \<in> vars" using pp by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have dl: "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u \<subseteq> vars"
    using pp u by simp
  have "dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
          (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g) (v, c))
      = dep_aux \<sigma>_st (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, c))"
    by (rule dep_seed_dg_eq
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra, symmetric])
  hence "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g)) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) u
      = dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u"
    unfolding dep\<^sub>L_def dep_def uv by simp
  thus "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g)) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) u \<subseteq> vars"
    using dl by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st
              \<le> \<sigma>_st (Inl u)" using pp u by simp
  have "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g)) u (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
      = fun_of_dg_st_gen Floc Fglob (eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st)"
      unfolding uv by (simp add: eq_seed_dg_commute
            [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
               and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
               and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra])
  also have "\<dots> \<le> fun_of_dg_st_gen Floc Fglob (\<sigma>_st (Inl u))" using le by (rule fun_of_dg_st_gen_mono)
  finally show "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g)) u (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
              \<le> (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) (Inl u)" by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st
              \<le> \<sigma>_st" using pp u by simp
  show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g) u) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) \<le> fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st"
  proof (rule le_funI)
    fix k
    have "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g) u) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k
        = fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st k)"
      unfolding uv by (simp add: sides_seed_dg_commute
            [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
               and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
               and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra])
    also have "\<dots> \<le> fun_of_dg_st_gen Floc Fglob (\<sigma>_st k)"
      using le[THEN le_funD] by (rule fun_of_dg_st_gen_mono)
    finally show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (Floc bot0) (Floc s0d) (Fglob s0g) u) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k
                \<le> (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k" by simp
  qed
qed

subsubsection \<open>Routed heterogeneous CALL/COMB transport\<close>

text \<open>
  \<open>routed_cmb_g\<close>/\<open>routed_extra_g\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>) are the
  canonical heterogeneous routing shape: parametric only in a routing function
  \<open>route\<close> and a seed-key injection \<open>seed_key\<close>, with the seed payload carried
  on the \<open>locals\<close> half so \<open>'D\<close>/\<open>'G\<close> stay independent.  The two lemmas below
  feed this generic engine's \<open>Hcmb\<close>/\<open>Hextra\<close> obligations directly, so any
  context-sensitive analysis instantiating \<open>cmb\<close>/\<open>extra\<close> at \<open>routed_cmb_g\<close>/
  \<open>routed_extra_g\<close> discharges CALL/COMB transport once here rather than
  re-deriving its own tree-commute reasoning.
\<close>

lemma dg_tree_st_commute_side_rhs_fold_dg:
  assumes la: "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs"
  shows "dg_tree_st_commute \<sigma>_st
           (side_rhs_fold_dg acc_st ts_st) (side_rhs_fold_dg (Floc acc_st) ts_abs)"
proof -
  have dep: "(\<Union>t\<in>set ts_st. dep_aux \<sigma>_st t)
      = (\<Union>t\<in>set ts_abs. dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t)"
    using dg_list_commute_dep[OF la]
    by (induction rule: list_all2_induct) (auto simp: comp_def)
  show ?thesis
    unfolding dg_tree_st_commute_def
    by (simp add: traverse_side_rhs_fold_dg Fglob_bot dep_aux_side_rhs_fold_dg_char dep
          side_acc_dg_commute[OF dg_list_commute_trav[OF la]]
          sides_side_rhs_fold_dg_commute[OF dg_list_commute_travsides[OF la]])
qed

lemma dg_tree_st_commute_routed_cmb_g_at:
  assumes seed_ne: "\<And>p c. seed_key p c \<noteq> gk0"
    and Henter: "\<And>ci d g'. map_prod Fglob Floc (dgs_enter S_st ci d g')
                      = dgs_enter S_abs ci (Floc d) (Fglob g')"
    and Hcomb:  "\<And>ci dc de g'. map_prod Fglob Floc (dgs_combine S_st ci dc de g')
                      = dgs_combine S_abs ci (Floc dc) (Floc de) (Fglob g')"
    and Hcont:  "\<And>ci d g'. Floc (caller_cont S_st ci d g')
                      = caller_cont S_abs ci (Floc d) (Fglob g')"
    and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
  shows "dg_tree_st_commute \<sigma>_st
           (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p)
           (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
              (Floc caller) (Fglob globals1) p)"
proof -
  obtain dst fs as where ca_eq: "ca = CallEdge dst fs as" by (cases ca) auto
  let ?ci = "call_info_of (CallEdge dst fs as) p"
  let ?entry = "enter_local S_st ?ci caller globals1"
  let ?ctx' = "route_st cc ctx ?entry (CallEdge dst fs as)"
  let ?eg = "enter_global S_st ?ci caller globals1"
  let ?callee = "locals (\<sigma>_st (Inl (FunctionResult p, ?ctx')))"
  let ?dcont = "caller_cont S_st ?ci caller globals1"
  let ?globals2 = "globs (\<sigma>_st (Inr gk0))"
  let ?cg = "combine_global S_st ?ci ?dcont ?callee ?globals2"
  have Henter_g: "\<And>ci d g'. Fglob (enter_global S_st ci d g')
                    = enter_global S_abs ci (Floc d) (Fglob g')"
    using Henter by (metis map_prod_simp fst_conv surj_pair)
  have Henter_l: "\<And>ci d g'. Floc (enter_local S_st ci d g')
                    = enter_local S_abs ci (Floc d) (Fglob g')"
    using Henter by (metis map_prod_simp snd_conv surj_pair)
  have Hcomb_g: "\<And>ci dc de g'. Fglob (combine_global S_st ci dc de g')
                    = combine_global S_abs ci (Floc dc) (Floc de) (Fglob g')"
    using Hcomb by (metis map_prod_simp fst_conv surj_pair)
  have Hcomb_l: "\<And>ci dc de g'. Floc (combine_local S_st ci dc de g')
                    = combine_local S_abs ci (Floc dc) (Floc de) (Fglob g')"
    using Hcomb by (metis map_prod_simp snd_conv surj_pair)
  have route_eq: "route_abs cc ctx (enter_local S_abs ?ci (Floc caller) (Fglob globals1))
        (CallEdge dst fs as) = ?ctx'"
    using Hroute[of cc ctx ?entry "CallEdge dst fs as"] by (simp add: Henter_l)
  have trav: "traverse_rhs
        (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p) \<sigma>_st
      = DG (combine_local S_st ?ci ?dcont ?callee ?globals2) bot"
    unfolding ca_eq routed_cmb_g_at_def Let_def by simp
  have trav_abs: "traverse_rhs
        (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
           (Floc caller) (Fglob globals1) p)
        (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
      = DG (combine_local S_abs ?ci
              (caller_cont S_abs ?ci (Floc caller) (Fglob globals1))
              (Floc ?callee) (Fglob ?globals2)) bot"
    unfolding ca_eq routed_cmb_g_at_def Let_def by (simp add: route_eq)
  have trav_commute: "fun_of_dg_st_gen Floc Fglob
        (traverse_rhs (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p)
           \<sigma>_st)
      = traverse_rhs (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
            (Floc caller) (Fglob globals1) p)
          (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
    by (simp add: trav trav_abs Hcont Hcomb_l Fglob_bot)
  have sides: "\<And>k. sides_of_rhs
        (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p) \<sigma>_st k
      = (if k = Inr gk0 then DG bot (?eg \<squnion> ?cg)
         else if k = Inr (seed_key (FunctionEntry p) ?ctx')
           then DG ?entry bot
         else bot)"
    unfolding ca_eq routed_cmb_g_at_def Let_def
    by (simp add: seed_ne fun_upd_apply)
  have sides_abs: "\<And>k. sides_of_rhs
        (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
           (Floc caller) (Fglob globals1) p)
        (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k
      = (if k = Inr gk0 then DG bot (Fglob ?eg \<squnion> Fglob ?cg)
         else if k = Inr (seed_key (FunctionEntry p) ?ctx')
           then DG (Floc ?entry) bot
         else bot)"
    unfolding ca_eq routed_cmb_g_at_def Let_def
    by (simp add: route_eq seed_ne fun_upd_apply Henter_g Henter_l Hcont Hcomb_g)
  have sides_commute: "\<And>k. fun_of_dg_st_gen Floc Fglob
        (sides_of_rhs (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p)
           \<sigma>_st k)
      = sides_of_rhs (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
            (Floc caller) (Fglob globals1) p)
          (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    by (simp add: sides sides_abs Floc_bot Fglob_bot Fglob_sup)
  have dep: "dep_aux \<sigma>_st
        (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller globals1 p)
      = {Inr gk0, Inl (FunctionResult p, ?ctx')}"
    unfolding ca_eq routed_cmb_g_at_def Let_def by (simp add: insert_commute)
  have dep_abs: "dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
        (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
           (Floc caller) (Fglob globals1) p)
      = {Inr gk0, Inl (FunctionResult p, ?ctx')}"
    unfolding ca_eq routed_cmb_g_at_def Let_def by (simp add: route_eq insert_commute)
  show ?thesis
    unfolding dg_tree_st_commute_def
    using trav_commute sides_commute dep dep_abs by auto
qed

text \<open>The call site itself: the resolver must answer the same targets on both
  carriers, which is the resolution-level twin of \<open>Hroute\<close>. At
  \<^const>\<open>static_resolve\<close> that premise is free, since the answer never reads the
  state.\<close>

lemma dg_tree_st_commute_routed_cmb_g:
  assumes seed_ne: "\<And>p c. seed_key p c \<noteq> gk0"
    and Henter: "\<And>ci d g'. map_prod Fglob Floc (dgs_enter S_st ci d g')
                      = dgs_enter S_abs ci (Floc d) (Fglob g')"
    and Hcomb:  "\<And>ci dc de g'. map_prod Fglob Floc (dgs_combine S_st ci dc de g')
                      = dgs_combine S_abs ci (Floc dc) (Floc de) (Fglob g')"
    and Hcont:  "\<And>ci d g'. Floc (caller_cont S_st ci d g')
                      = caller_cont S_abs ci (Floc d) (Fglob g')"
    and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (Floc d) ca"
    and Hresolve: "\<And>w cc' ca' d. resolve_st w cc' ca' d = resolve_abs w cc' ca' (Floc d)"
  shows "dg_tree_st_commute \<sigma>_st
           (routed_cmb_g S_st gk0 seed_key resolve_st route_st ctx ca cc v)
           (routed_cmb_g S_abs gk0 seed_key resolve_abs route_abs ctx ca cc v)"
proof -
  let ?caller = "locals (\<sigma>_st (Inl (cc, ctx)))"
  let ?globals1 = "globs (\<sigma>_st (Inr gk0))"
  have at: "\<And>p. dg_tree_st_commute \<sigma>_st
      (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller ?globals1 p)
      (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
         (Floc ?caller) (Fglob ?globals1) p)"
    using seed_ne Henter Hcomb Hcont Hroute
    by (rule dg_tree_st_commute_routed_cmb_g_at)
  have la: "list_all2 (dg_tree_st_commute \<sigma>_st)
      (map (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller ?globals1)
        (resolve_st v cc ca ?caller))
      (map (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
              (Floc ?caller) (Fglob ?globals1))
        (resolve_st v cc ca ?caller))"
    by (simp add: list_all2_conv_all_nth at)
  have body: "dg_tree_st_commute \<sigma>_st
      (side_rhs_fold_dg bot
        (map (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller ?globals1)
          (resolve_st v cc ca ?caller)))
      (side_rhs_fold_dg bot
        (map (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc
                (Floc ?caller) (Fglob ?globals1))
          (resolve_st v cc ca ?caller)))"
    using dg_tree_st_commute_side_rhs_fold_dg[OF la, where acc_st = bot]
    by (simp add: Floc_bot)
  show ?thesis
    unfolding routed_cmb_g_def
    using body by (simp add: dg_tree_st_commute_def Hresolve[symmetric] comp_def)
qed
lemma dg_tree_st_commute_routed_extra_g:
  shows "list_all2 (dg_tree_st_commute \<sigma>_st)
           (routed_extra_g seed_key gk0 route_st ctx v)
           (routed_extra_g seed_key gk0 route_abs ctx v)"
  by (cases v) (simp_all add: routed_extra_g_def dg_tree_st_commute_def Fglob_bot)
end

end
