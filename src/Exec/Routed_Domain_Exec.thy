theory Routed_Domain_Exec
  imports
    DG_Base_Exec
    "Voblint_Core.Routed_Context_Unit"
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
  routed_dg_domain_exec gs empty_pred tf_st enter_st tf
  for gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "'a::sound_domain exec_dg_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and tf :: "'a domain_transfer" +
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

text \<open>The executable and abstract routed specs this domain solves at. Abbreviations, not
  definitions: a domain's own \<open>*_spec\<close>/\<open>*_abs_spec\<close> constant unfolds to exactly these, so
  its existing \<^theory_text>\<open>unfolding\<close> steps keep working unchanged.\<close>

abbreviation spec_st :: "('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_spec" where
  "spec_st \<equiv> base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"

abbreviation spec_abs :: "('a abs_state lifted, 'a abs_state lifted) dg_spec" where
  "spec_abs \<equiv> base_dg_spec_for_lifted gs is_empty_state tf"

text \<open>The routed combine tree commutes with the executable-to-abstract reader. Mentions no
  domain constant beyond the two specs, so one proof serves every instance.\<close>

lemma dg_tree_st_commute_routed_cmb_g:
  "dg_reader_commute_gen.dg_tree_st_commute
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env
     (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st ctx ca cc ex)
     (routed_cmb_g spec_abs gk0 seed_key (resolve_abs g) route_abs ctx ca cc ex)"
  apply (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [where Floc = "map_lift (fun_of_resolved_st_q_for gs)"
           and Fglob = "map_lift (fun_of_resolved_st_q_for gs)"])
       apply (rule dg_reader_commute_gen_lifted_for)
      apply (rule seed_key_ne_gk0)
     apply (rule Henter_lifted_for)
    apply (rule Hcomb_lifted_for)
   apply (rule Hcont_lifted_for)
  apply (rule route_agree)
  apply (rule resolve_agree)
  done

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
  the framework is stated over --- at the executable spec, before any readback. Every
  obligation is a \<^const>\<open>routed_cmb_g\<close> fact needing only \<open>seed_key_ne_gk0\<close>. An
  instance that interprets the spine at \<open>spec_st\<close> hands this post-solution to
  \<^locale>\<open>dg_ctx_activation_base\<close> directly.
\<close>
theorem pp_st:
  assumes pp: "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. gk0) route_st
        (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g))
        (routed_extra_g seed_key gk0)
        g spec_st bot0 s0d s0g)
     x0 sigma_st vars"
  shows "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. gk0) route_st
        (routed_cmb_g spec_st gk0 seed_key (resolve_st g)) (routed_extra_g seed_key gk0)
        g spec_st bot0 s0d s0g)
     x0 sigma_st vars"
proof (rule part_post_solution_seed_dg_buffered_to_old
    [where cmb_c = "routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)"])
  show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
           (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)
              route_st c' ca cc ex) \<tau>)
         = locals (traverse_rhs
           (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st c' ca cc ex) \<tau>)"
    by (rule routed_cmb_g_contribution_matches_local)
  show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
           (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st c' ca cc ex) \<tau>
           (Inr ((\<lambda>_. gk0) c'))) = bot"
    by (rule routed_cmb_g_side_pure[of seed_key gk0, OF seed_key_ne_gk0])
  show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
           (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)
              route_st c' ca cc ex) \<tau>)
         = globs (sides_of_rhs
           (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st c' ca cc ex) \<tau>
           (Inr ((\<lambda>_. gk0) c')))"
    by (rule routed_cmb_g_contribution_matches_global[of seed_key gk0, OF seed_key_ne_gk0])
  show "\<And>c' ca cc ex \<tau>. sides_of_rhs
           (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)
              route_st c' ca cc ex) \<tau>
           (Inr ((\<lambda>_. gk0) c')) = bot"
    by (rule routed_cmb_g_contribution_free_at_key[of seed_key gk0, OF seed_key_ne_gk0])
  show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. gk0) c') \<Longrightarrow> sides_of_rhs
           (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)
              route_st c' ca cc ex) \<tau> z
         = sides_of_rhs
           (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st c' ca cc ex) \<tau> z"
    by (rule routed_cmb_g_contribution_sides_off_key[of seed_key gk0, OF seed_key_ne_gk0])
  show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
           (routed_cmb_g_contribution spec_st gk0 seed_key (resolve_st g)
              route_st c' ca cc ex)
         = dep_aux \<tau>
           (routed_cmb_g spec_st gk0 seed_key (resolve_st g) route_st c' ca cc ex)"
    by (rule routed_cmb_g_contribution_dep)
  show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g seed_key gk0 route_st c' w)
         \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
    by (rule routed_extra_g_free)
  show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g seed_key gk0 route_st c' w)
         \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
    by (rule routed_extra_g_local_only)
qed (rule pp)

end

end
