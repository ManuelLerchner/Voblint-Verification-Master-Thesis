theory Routed_Exec_Refinement
  imports
    DG_Local_State_Exec_Refinement
begin

section \<open>Routed execution, once for every domain and context policy\<close>

text \<open>
  \<^locale>\<open>dg_domain_exec\<close> already reduces a domain's obligation to the routed
  spine to three primitive commute facts. What it deliberately does not carry is the
  \<^emph>\<open>routing\<close> layer: the equation system a routed analysis actually solves, and the
  executable-to-abstract transport of its post-solution. Each domain, at each context
  policy, re-derived that layer, and because \<^const>\<open>routed_call_program\<close> mentions no domain
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
  equations, and \<^locale>\<open>dg_domain_exec\<close>'s own \<open>empty_pred_exact\<close> is not
  dischargeable without fixing a concrete global set, so no locale carrying it can be
  interpreted globally. The domain keeps its definitions; what it stops re-proving is
  everything below.

  Also deliberately absent: the solver. The generated equation system is
  solver-independent, and \<open>TD_side_upd_rule\<close> already supplies
  \<open>partial_post_solution\<close> for every update rule on the menu, so a solver choice
  is an argument at the use site, never a parameter of the domain capability.
\<close>


subsection \<open>The buffered generator at any component\<close>

text \<open>
  The buffered generator a domain actually solves, reconciled with the unbuffered one
  the framework is stated over, for every component run as a specification. Both
  reshaping hooks are the identity: the buffered generator only asks a hook to hoist
  what it publishes at the buffered key \<open>analysis_global\<close>, and a component publishes nothing
  there, since its edge transfers, its entry and its return all read and write the
  local unknown only. Its queries do not change that: its channel is a pure function
  of the local value, so an asking transfer is still a local one.
\<close>

theorem pp_dg_spec_of:
  assumes S: "S = dg_spec_of c"
    and ne: "\<And>p ctx. seed p ctx \<noteq> analysis_global"
    and pp: "part_post_solution
     (routed_node_rhs_buffered intra_predecessor_addr_list call_site_list (\<lambda>_. analysis_global) route_st
        (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. analysis_global))
        (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        g bot0 s0d s0g)
     x0 sigma_st vars"
  shows "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. analysis_global) route_st
        (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. analysis_global))
        (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        g bot0 s0d s0g)
     x0 sigma_st vars"
proof -
  have wf: "dg_spec_wf S" by (simp add: S)
  have intra_free: "sides_of_program (dg_spec_edge_program S a src (\<lambda>_. analysis_global)) \<tau> z = bot"
    for a src \<tau> z
    by (simp add: S dg_spec_edge_program_def)
  have cmb_free: "sides_of_program
      (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route' ctx' ca cc ex)
      \<tau> (Inr analysis_global) = bot" for route' ctx' ca cc ex \<tau>
    by (rule routed_call_program_side_free_at_analysis_global[OF wf])
       (auto simp: S local_transfer_def local_combine_transfer_def ne
         dest!: enter_runs_local_pub_bot)
  show ?thesis
  proof (rule part_post_solution_routed_node_rhs_buffered
      [where cmb_c =
        "routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot)"
         and it_c = "\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. analysis_global)"])
    show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs intra_predecessor_addr_list
             call_site_list route_st (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. analysis_global))
             (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot))
             (routed_entry_seed_programs seed) g c' w). sp_wf p"
      by (rule routed_contribution_programs_wf)
         (auto intro: sp_wf_dg_spec_edge_program[OF wf] sp_wf_routed_call_program[OF wf])
    then show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs intra_predecessor_addr_list
             call_site_list route_st (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. analysis_global))
             (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot))
             (routed_entry_seed_programs seed) g c' w). sp_wf p" .
    show "\<And>c' src a \<tau>. dg_local (sides_of_program (dg_spec_edge_program S a src (\<lambda>_. analysis_global)) \<tau>
             (Inr ((\<lambda>_. analysis_global) c'))) = bot"
      by (simp add: intra_free bot_dg_state_def)
    show "\<And>c' src a \<tau>. dg_global (traverse_program (dg_spec_edge_program S a src (\<lambda>_. analysis_global)) \<tau>)
           = dg_global (sides_of_program (dg_spec_edge_program S a src (\<lambda>_. analysis_global)) \<tau>
               (Inr ((\<lambda>_. analysis_global) c')))"
      by (simp add: S dg_spec_edge_program_def bot_dg_state_def)
    show "\<And>c' src a \<tau>. sides_of_program (dg_spec_edge_program S a src (\<lambda>_. analysis_global)) \<tau>
             (Inr ((\<lambda>_. analysis_global) c')) = bot"
      by (rule intra_free)
    show "\<And>c' ca cc ex \<tau>. dg_local (sides_of_program
             (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
             \<tau> (Inr ((\<lambda>_. analysis_global) c'))) = bot"
      by (simp add: cmb_free bot_dg_state_def)
    show "\<And>c' ca cc ex \<tau>. dg_global (traverse_program
             (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex) \<tau>)
           = dg_global (sides_of_program
               (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
               \<tau> (Inr ((\<lambda>_. analysis_global) c')))"
      by (simp add: routed_call_program_global_free[OF wf] cmb_free bot_dg_state_def)
    show "\<And>c' ca cc ex \<tau>. sides_of_program
             (routed_call_program S analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
             \<tau> (Inr ((\<lambda>_. analysis_global) c')) = bot"
      by (rule cmb_free)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_entry_seed_programs seed route_st c' w)
           \<Longrightarrow> sides_of_program x \<tau> z = bot"
      by (rule routed_entry_seed_programs_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_entry_seed_programs seed route_st c' w)
           \<Longrightarrow> dg_global (traverse_program x \<tau>) = bot"
      by (rule routed_entry_seed_programs_local_only)
  qed (simp_all add: pp)
qed

text \<open>
  \<open>routed_domain_exec\<close> adds call routing to \<open>dg_domain_exec\<close>: seed keys
  never collide with the analysis global, and routing and callee resolution on
  the executable state agree with their abstract versions after readback.
\<close>

locale routed_domain_exec =
  dg_domain_exec \<G> empty_pred tf_st enter_st sk asn sp br bd rt en ev
  for \<G> :: "vname \<Rightarrow> bool"
    and empty_pred :: "'a::numeric_domain default_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st"
    and enter_st :: "call_info \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st"
    and sk :: "'a abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" +
  fixes analysis_global :: 'k
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route_st :: "pp \<Rightarrow> 'c \<Rightarrow> 'a default_st lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and route_abs :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and resolve_st :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'a default_st lifted \<Rightarrow> pname list"
    and resolve_abs :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> 'a abs_state lifted \<Rightarrow> pname list"
  assumes seed_ne_analysis_global [simp]: "\<And>p ctx. seed p ctx \<noteq> analysis_global"
      and route_agree: "\<And>u c' d ca. route_st u c' d ca
                          = route_abs u c' (map_lift (default_st_to_fun \<G>) d) ca"
      and resolve_agree: "\<And>g w cc ca d. resolve_st g w cc ca d
                          = resolve_abs g w cc ca (map_lift (default_st_to_fun \<G>) d)"
begin

text \<open>The routed combine tree commutes with the executable-to-abstract reader. \<open>spec_st\<close>
  and \<open>spec_abs\<close> come from \<^locale>\<open>dg_domain_exec\<close>; nothing here mentions a domain
  constant beyond them, so one proof serves every instance. The caller continuation needs
  no hypothesis: \<^const>\<open>dg_spec_combine_transfer\<close> already runs it inside the combine
  sub-tree.\<close>

lemma dg_prog_st_commute_routed_call_program:
  "dg_reader_commute_gen.dg_prog_st_commute
     (map_lift (default_st_to_fun \<G>)) (map_lift (default_st_to_fun \<G>)) env
     (routed_call_program spec_st analysis_global seed (resolve_st g) (\<lambda>d. d = Bot) route_st ctx ca cc ex)
     (routed_call_program spec_abs analysis_global seed (resolve_abs g) (\<lambda>d. d = Bot)
        route_abs ctx ca cc ex)"
  by (rule dg_reader_commute_gen.dg_prog_st_commute_routed_call_program
        [where Floc = "map_lift (default_st_to_fun \<G>)"
           and Fglob = "map_lift (default_st_to_fun \<G>)"])
     (rule dg_reader_commute_gen_lifted_for seed_ne_analysis_global
           dg_spec_wf_exec_dg_spec
           dg_spec_wf_lifted_state_dg_spec
           Henter_lifted_for Hcomb_lifted_for
           route_agree map_lift_eq_Bot_iff resolve_agree)+

text \<open>The routed extra-goal list commutes elementwise, for the same reason.\<close>

text \<open>
  The buffered generator a domain actually solves, reconciled with the unbuffered one
  the framework is stated over --- at the executable spec, before publication.

  Both reshaping hooks are the identity here. The buffered generator only ever asks a
  hook to hoist what it publishes at the buffered key \<open>analysis_global\<close>; this spec is local-only,
  so its intra tree and its routed combine publish nothing there, and each tree is
  already its own contribution analogue. That is a property of the trees --- read off
  \<open>routed_call_program_side_free_at_analysis_global\<close> and the local-only compile-down facts --- not of any
  analysis family: a spec whose transfers do publish at \<open>analysis_global\<close> would have to supply
  reshaped hooks instead, with the same generic bridge unchanged. The routed seed
  survives untouched, because a seed key is never \<open>analysis_global\<close> and the bridge requires
  off-key sides to be preserved, not removed.

  An instance that interprets the spine at \<open>spec_st\<close> hands this post-solution to
  \<^locale>\<open>dg_context_activation\<close> directly.
\<close>

abbreviation intra_st :: "'c \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> edge_action
   \<Rightarrow> (pp \<times> 'c, 'k, ('a default_st lifted, 'a default_st lifted) dg_state,
        ('a default_st lifted, 'a default_st lifted) dg_state) strategy_program"
where
  "intra_st ctx' src a \<equiv> dg_spec_edge_program spec_st a src (\<lambda>_. analysis_global)"

abbreviation cmb_st :: "cfg \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a default_st lifted \<Rightarrow> call_action \<Rightarrow> 'c)
   \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> 'c, 'k, ('a default_st lifted, 'a default_st lifted) dg_state,
        ('a default_st lifted, 'a default_st lifted) dg_state) strategy_program"
where
  "cmb_st g \<equiv> routed_call_program spec_st analysis_global seed (resolve_st g) (\<lambda>d. d = Bot)"

theorem pp_st:
  assumes pp: "part_post_solution
     (routed_node_rhs_buffered intra_predecessor_addr_list call_site_list (\<lambda>_. analysis_global) route_st
        intra_st (cmb_st g)
        (routed_entry_seed_programs seed)
        g bot0 s0d s0g)
     x0 sigma_st vars"
  shows "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. analysis_global) route_st
        intra_st (cmb_st g)
        (routed_entry_seed_programs seed)
        g bot0 s0d s0g)
     x0 sigma_st vars"
  by (rule pp_dg_spec_of[where S = spec_st])
     (rule exec_dg_spec_def, rule seed_ne_analysis_global, rule pp)

end

end
