theory Routed_Domain_Exec
  imports
    DG_Local_State_Exec
    "Voblint_Framework.Routed_Context_Unit"
begin

section \<open>Routed execution, once for every domain and context policy\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> already reduces a domain's obligation to the routed
  spine to three primitive commute facts. What it deliberately does not carry is the
  \<^emph>\<open>routing\<close> layer: the equation system a routed analysis actually solves, and the
  executable-to-abstract transport of its post-solution. Each domain, at each context
  policy, re-derived that layer, and because \<^const>\<open>routed_cmb_g\<close> mentions no domain
  constant, those derivations differ only in the domain carrier, the routing function
  and a name prefix.

  This locale is that layer, stated once. It adds the seed-key pair the routed
  generator needs --- kept as parameters rather than a fixed datatype, so a domain
  keeps its own key type and this locale stays independent of how that type is
  eventually shared --- together with the executable and abstract routing functions
  and their agreement, and derives the commute and transport facts every routed
  instance needs. A context-insensitive instance passes \<^const>\<open>route_unit\<close> on both
  sides, where agreement is free; a call-string instance passes its own routing
  function on each side and discharges the agreement from that function's own laws.

  Deliberately absent: the equation-system, solved-table and result \<^theory_text>\<open>definition\<close>s
  themselves. They must stay concrete per-domain constants because they carry \<open>[code]\<close>
  equations, and \<^locale>\<open>routed_dg_domain_exec\<close>'s own \<open>empty_pred_exact\<close> is not
  dischargeable without fixing a concrete global set, so no locale carrying it can be
  interpreted globally. The domain keeps its definitions; what it stops re-proving is
  everything below.

  Also deliberately absent: the solver. The generated equation system is
  solver-independent, and \<open>TD_side_upd_rule\<close> already supplies
  \<open>part_post_solution_of_solve_c\<close> for every update rule on the menu, so a solver choice
  is an argument at the use site, never a parameter of the domain capability.
\<close>


locale routed_domain_exec =
  routed_dg_domain_exec gs empty_pred tf_st enter_st sk asn sp br bd rt en ev
  for gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "'a::sound_domain exec_dg_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and sk :: "'a abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" +
  fixes gk0 :: 'k
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route_st :: "pp \<Rightarrow> 'c \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and route_abs :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and resolve_st :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> pname list"
    and resolve_abs :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'a abs_state lifted \<Rightarrow> pname list"
  assumes seed_key_ne_gk0 [simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
      and route_agree: "\<And>u c' d ca. route_st u c' d ca
                          = route_abs u c' (map_lift (fun_of_resolved_st_q_for gs) d) ca"
      and resolve_agree: "\<And>g w cc ca d. resolve_st g w cc ca d
                          = resolve_abs g w cc ca (map_lift (fun_of_resolved_st_q_for gs) d)"
begin

text \<open>The routed combine tree commutes with the executable-to-abstract reader. \<open>spec_st\<close>
  and \<open>spec_abs\<close> come from \<^locale>\<open>routed_dg_domain_exec\<close>; nothing here mentions a domain
  constant beyond them, so one proof serves every instance. The caller continuation needs
  no hypothesis: \<^const>\<open>dg_spec_combine_transfer\<close> already runs it inside the combine
  sub-tree.\<close>

lemma dg_tree_st_commute_routed_cmb_g:
  "dg_reader_commute_gen.dg_tree_st_commute
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env
     (routed_cmb_g spec_st gk0 seed_key (resolve_st g) (\<lambda>d. d = Bot) route_st ctx ca cc ex)
     (routed_cmb_g spec_abs gk0 seed_key (resolve_abs g) (\<lambda>d. d = Bot) route_abs ctx ca cc ex)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [where Floc = "map_lift (fun_of_resolved_st_q_for gs)"
           and Fglob = "map_lift (fun_of_resolved_st_q_for gs)"])
     (rule dg_reader_commute_gen_lifted_for seed_key_ne_gk0
           Henter_lifted_for Hcomb_lifted_for
           route_agree map_lift_eq_Bot_iff resolve_agree)+

text \<open>The routed extra-goal list commutes elementwise, for the same reason.\<close>

lemma hextra_commute_routed:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for gs))
                (map_lift (fun_of_resolved_st_q_for gs)) env)
     (routed_extra_g seed_key gk0 route_st ctx w)
     (routed_extra_g seed_key gk0 route_abs ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g
        [OF dg_reader_commute_gen_lifted_for])

text \<open>
  The buffered generator a domain actually solves, reconciled with the unbuffered one
  the framework is stated over --- at the executable spec, before any readback.

  Both reshaping hooks are the identity here. The buffered generator only ever asks a
  hook to hoist what it publishes at the buffered key \<open>gk0\<close>; this spec is local-only,
  so its intra tree and its routed combine publish nothing there, and each tree is
  already its own contribution analogue. That is a property of the trees --- read off
  \<open>routed_cmb_g_side_free_at_gk0\<close> and the local-only compile-down facts --- not of any
  analysis family: a spec whose transfers do publish at \<open>gk0\<close> would have to supply
  reshaped hooks instead, with the same generic bridge unchanged. The routed seed
  survives untouched, because a seed key is never \<open>gk0\<close> and the bridge requires
  off-key sides to be preserved, not removed.

  An instance that interprets the spine at \<open>spec_st\<close> hands this post-solution to
  \<^locale>\<open>dg_ctx_activation_base\<close> directly.
\<close>

abbreviation intra_st :: "'c \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> edge_action
   \<Rightarrow> (pp \<times> 'c, 'k, ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) strategy_tree"
where
  "intra_st ctx' src a \<equiv> dg_spec_edge_tree spec_st a src (\<lambda>_. gk0)"

abbreviation cmb_st :: "cfg \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> 'c, 'k, ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) strategy_tree"
where
  "cmb_st g \<equiv> routed_cmb_g spec_st gk0 seed_key (resolve_st g) (\<lambda>d. d = Bot)"

text \<open>The two tree properties that make the identity hooks legitimate: neither the
  compiled intra edge nor the routed combine publishes at \<open>gk0\<close>, and both answer with
  \<open>bot\<close> on the globals half.\<close>

lemma intra_st_side_free: "sides_of_rhs (intra_st ctx' src a) \<tau> z = bot"
  by (simp add: dg_spec_edge_tree_def dg_spec_step_local_state_st_for_lifted)

lemma cmb_st_side_free_at_gk0: "sides_of_rhs (cmb_st g route' ctx' ca cc ex) \<tau> (Inr gk0) = bot"
  by (rule routed_cmb_g_side_free_at_gk0)
     (auto simp: dgs_enter_local_state_st_for_lifted
        dg_spec_combine_transfer_local_state_st_for_lifted
        local_transfer_def local_combine_transfer_def seed_key_ne_gk0 bot_fun_def
        dest!: enter_runs_local_pub_bot)

theorem pp_st:
  assumes pp: "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. gk0) route_st
        intra_st (cmb_st g) (routed_extra_g seed_key gk0)
        g bot0 s0d s0g)
     x0 sigma_st vars"
  shows "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. gk0) route_st
        intra_st (cmb_st g) (routed_extra_g seed_key gk0)
        g bot0 s0d s0g)
     x0 sigma_st vars"
proof (rule part_post_solution_seed_dg_buffered_to_old
    [where cmb_c = "cmb_st g" and it_c = intra_st])
  show "\<And>c' src a \<tau>. locals (traverse_rhs (intra_st c' src a) \<tau>)
         = locals (traverse_rhs (intra_st c' src a) \<tau>)"
    by (rule refl)
  show "\<And>c' src a \<tau>. locals (sides_of_rhs (intra_st c' src a) \<tau> (Inr ((\<lambda>_. gk0) c'))) = bot"
    by (simp add: intra_st_side_free bot_dg_state_def)
  show "\<And>c' src a \<tau>. globs (traverse_rhs (intra_st c' src a) \<tau>)
         = globs (sides_of_rhs (intra_st c' src a) \<tau> (Inr ((\<lambda>_. gk0) c')))"
    by (simp add: dg_spec_edge_tree_def dg_spec_step_local_state_st_for_lifted bot_dg_state_def)
  show "\<And>c' src a \<tau>. sides_of_rhs (intra_st c' src a) \<tau> (Inr ((\<lambda>_. gk0) c')) = bot"
    by (rule intra_st_side_free)
  show "\<And>c' src a \<tau> z. z \<noteq> Inr ((\<lambda>_. gk0) c') \<Longrightarrow>
         sides_of_rhs (intra_st c' src a) \<tau> z = sides_of_rhs (intra_st c' src a) \<tau> z"
    by (rule refl)
  show "\<And>c' src a \<tau>. dep_aux \<tau> (intra_st c' src a) = dep_aux \<tau> (intra_st c' src a)"
    by (rule refl)
  show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs (cmb_st g route_st c' ca cc ex) \<tau>)
         = locals (traverse_rhs (cmb_st g route_st c' ca cc ex) \<tau>)"
    by (rule refl)
  show "\<And>c' ca cc ex \<tau>.
         locals (sides_of_rhs (cmb_st g route_st c' ca cc ex) \<tau> (Inr ((\<lambda>_. gk0) c'))) = bot"
    by (simp add: cmb_st_side_free_at_gk0 bot_dg_state_def)
  show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs (cmb_st g route_st c' ca cc ex) \<tau>)
         = globs (sides_of_rhs (cmb_st g route_st c' ca cc ex) \<tau> (Inr ((\<lambda>_. gk0) c')))"
    by (simp add: routed_cmb_g_global_free cmb_st_side_free_at_gk0 bot_dg_state_def)
  show "\<And>c' ca cc ex \<tau>.
         sides_of_rhs (cmb_st g route_st c' ca cc ex) \<tau> (Inr ((\<lambda>_. gk0) c')) = bot"
    by (rule cmb_st_side_free_at_gk0)
  show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. gk0) c') \<Longrightarrow>
         sides_of_rhs (cmb_st g route_st c' ca cc ex) \<tau> z
           = sides_of_rhs (cmb_st g route_st c' ca cc ex) \<tau> z"
    by (rule refl)
  show "\<And>c' ca cc ex \<tau>. dep_aux \<tau> (cmb_st g route_st c' ca cc ex)
         = dep_aux \<tau> (cmb_st g route_st c' ca cc ex)"
    by (rule refl)
  show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g seed_key gk0 route_st c' w)
         \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    by (rule routed_extra_g_free)
  show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g seed_key gk0 route_st c' w)
         \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
    by (rule routed_extra_g_local_only)
qed (rule pp)
end

end
