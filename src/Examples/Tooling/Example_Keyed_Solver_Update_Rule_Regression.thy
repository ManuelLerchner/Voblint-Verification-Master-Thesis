theory Example_Keyed_Solver_Update_Rule_Regression
  imports
    "Voblint_Core.DG_Framework"
    "Voblint_Core.Routed_Context"
    "Voblint_Exec.Solver_Side_RG"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>Minimal keyed update-rule regression: multiple Side writes per RHS evaluation (issue #121, keyed)\<close>

text \<open>
  Isolates the keyed-generator instance of issue #121 at
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>'s own interface, independent of a real
  \<^typ>\<open>cfg\<close>, procedure calls, or Interval program construction: a dummy
  \<^typ>\<open>cfg\<close> with no edges of its own (\<open>intra = {}\<close>, \<open>calls = {}\<close>) paired with a
  hand-supplied \<open>pred_sel\<close> that reports two intra predecessors for one node --
  exactly the shape a real merge node with two incoming intra edges produces
  (\<^theory>\<open>Voblint_Core.DG_Framework\<close>'s own \<open>intra\<close> fold), collapsed to its
  essential two-write pattern.

  The two predecessor edges carry different \<open>edge_action\<close>s (\<open>EA_Nop\<close> vs.
  \<open>EA_Assign\<close>) against \<open>keyed_spec\<close> below, so their \<^const>\<open>dg_edge_tree\<close>
  contributions publish genuinely different global values -- reproducing the
  same per-origin-gate destabilization \<^const>\<open>update_global_warrowing_apinis\<close>
  exhibits, from two \<open>intra\<close> list entries of the same equation.
\<close>

definition keyed_spec :: "(ivl, ivl) dg_spec" where
  "keyed_spec =
     \<lparr> dgs_skip = \<lambda>d g. (g, d),
       dgs_assign = \<lambda>x e d g. (g \<squnion> Ivl (Fin 1) (Fin 1), d),
       dgs_special = \<lambda>sc x d g. (g, d),
       dgs_branch = \<lambda>b pol d g. (g, d),
       dgs_body = \<lambda>p d g. (g, d),
       dgs_return = \<lambda>e p d g. (g, d),
       dgs_enter = \<lambda>ci d g. (g, d),
       dgs_event = \<lambda>ev d g. (g, d),
       dgs_caller_cont = \<lambda>ci dc g. dc,
       dgs_combine_env = \<lambda>ci dc de g. (g, dc \<squnion> de),
       dgs_combine_assign = \<lambda>ci de g p. p \<rparr>"

definition keyed_dummy_cfg :: cfg where
  "keyed_dummy_cfg = \<lparr> intra = {}, calls = {}, cfg_entry = Statement 0, checks = {} \<rparr>"

text \<open>Two predecessors of \<open>Statement 1\<close>, both from \<open>Statement 0\<close>, with different
  \<open>edge_action\<close>s so their \<^const>\<open>dg_edge_tree\<close> contributions differ.\<close>
definition keyed_pred_sel ::
  "cfg \<Rightarrow> pp \<Rightarrow> unit \<Rightarrow> ((pp \<times> unit + unit) \<times> edge_action) list" where
  "keyed_pred_sel g v ctx =
     (if v = Statement 1 then
        [(Inl (Statement 0, ctx), EA_Nop),
         (Inl (Statement 0, ctx), EA_Assign (STR ''x'') (exp.N 0))]
      else [])"

text \<open>\<open>cmb\<close>/\<open>extra\<close> are never invoked: \<open>calls = {}\<close> makes
  \<open>return_call_action_list\<close>/\<open>entry_call_list\<close> empty for every node.\<close>
definition keyed_cmb :: "(pp \<Rightarrow> unit \<Rightarrow> ivl \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
    \<Rightarrow> (pp \<times> unit, unit, (ivl, ivl) dg_state) strategy_tree" where
  "keyed_cmb route ctx ca cc ex = answer (DG bot bot)"

definition keyed_cmb_c :: "(pp \<Rightarrow> unit \<Rightarrow> ivl \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
    \<Rightarrow> (pp \<times> unit, unit, (ivl, ivl) dg_state) strategy_tree" where
  "keyed_cmb_c route ctx ca cc ex = answer (DG bot bot)"

definition keyed_extra :: "(pp \<Rightarrow> unit \<Rightarrow> ivl \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
    \<Rightarrow> (pp \<times> unit, unit, (ivl, ivl) dg_state) strategy_tree list" where
  "keyed_extra route ctx v = []"

text \<open>The unbuffered generator: \<open>Statement 1\<close>'s equation issues two \<open>Side ()\<close>
  writes -- \<open>EA_Nop\<close>'s and \<open>EA_Assign\<close>'s -- in one RHS evaluation. Not run: a
  genuinely non-terminating \<open>by eval\<close> would hang the batch build (mirrors the
  flat file's documented convention).\<close>
definition keyed_multiwrite_eqs :: "(pp \<times> unit, unit, (ivl, ivl) dg_state) eqsT" where
  "keyed_multiwrite_eqs =
     side_cfg_T_eff_keyed_seed_dg keyed_pred_sel (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
       keyed_cmb keyed_extra keyed_dummy_cfg keyed_spec bot bot bot"

text \<open>The buffered generator: the same two predecessor contributions, folded
  Side-free via \<^const>\<open>apply_dg_spec_contribution\<close> and \<^const>\<open>fold_rhs_trees\<close>,
  published exactly once. Terminates under the completely unmodified vendored
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve_c\<close>.\<close>
definition keyed_multiwrite_buffered_eqs :: "(pp \<times> unit, unit, (ivl, ivl) dg_state) eqsT" where
  "keyed_multiwrite_buffered_eqs =
     side_cfg_T_eff_keyed_seed_dg_buffered keyed_pred_sel (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
       keyed_cmb_c keyed_extra keyed_dummy_cfg keyed_spec bot bot bot"

lemma keyed_multiwrite_buffered_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c keyed_multiwrite_buffered_eqs (Statement 1, ()) \<noteq> None"
  by eval

section \<open>Merge-node regression: a real two-predecessor CFG node\<close>

text \<open>
  Unlike \<open>keyed_multiwrite_buffered_eqs\<close> above, this uses a genuine \<^typ>\<open>cfg\<close>
  with two real \<open>intra\<close> edges into one merge node and the PRODUCTION
  \<^const>\<open>intra_predecessor_list\<close> selector (no hand-rolled \<open>pred_sel\<close>) --
  exactly the shape \<open>FunctionResult factorial\<close> has in the real factorial
  regression (two incoming intra edges, one per branch). \<open>merge_spec\<close>'s
  \<open>dgs_skip\<close>/\<open>dgs_assign\<close> answer fixed constants regardless of the incoming
  local/global state, so the solved global value at \<open>gkey ()\<close> is exactly
  the join of the two edges' own contributions, not a self-referential
  fixpoint -- letting the check below assert that join directly.
\<close>

definition merge_spec :: "(ivl, ivl) dg_spec" where
  "merge_spec =
     \<lparr> dgs_skip = \<lambda>d g. (Ivl (Fin 0) (Fin 0), d),
       dgs_assign = \<lambda>x e d g. (Ivl (Fin 1) (Fin 1), d),
       dgs_special = \<lambda>sc x d g. (g, d),
       dgs_branch = \<lambda>b pol d g. (g, d),
       dgs_body = \<lambda>p d g. (g, d),
       dgs_return = \<lambda>e p d g. (g, d),
       dgs_enter = \<lambda>ci d g. (g, d),
       dgs_event = \<lambda>ev d g. (g, d),
       dgs_caller_cont = \<lambda>ci dc g. dc,
       dgs_combine_env = \<lambda>ci dc de g. (g, dc \<squnion> de),
       dgs_combine_assign = \<lambda>ci de g p. p \<rparr>"

text \<open>Two real predecessors of \<open>Statement 2\<close>: \<open>Statement 0\<close> via \<open>EA_Nop\<close>,
  \<open>Statement 1\<close> via \<open>EA_Assign\<close>. \<open>calls = {}\<close> keeps \<open>cmb\<close>/\<open>extra\<close> unused, as
  in \<open>keyed_dummy_cfg\<close>.\<close>
definition merge_cfg :: cfg where
  "merge_cfg = \<lparr>
     intra = {(Statement 0, EA_Nop, Statement 2),
              (Statement 1, EA_Assign (STR ''x'') (exp.N 0), Statement 2)},
     calls = {}, cfg_entry = Statement 0, checks = {} \<rparr>"

definition merge_eqs :: "(pp \<times> unit, unit, (ivl, ivl) dg_state) eqsT" where
  "merge_eqs =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
       keyed_cmb_c keyed_extra merge_cfg merge_spec bot bot bot"

lemma merge_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c merge_eqs (Statement 2, ()) \<noteq> None"
  by eval

lemma merge_global_value:
  "map_option (\<lambda>sol. globs (snd sol (Inr ()))) (TD_side_warrowing_apinis_Interp_solve_c merge_eqs (Statement 2, ()))
     = Some (Ivl (Fin 0) (Fin 0) \<squnion> Ivl (Fin 1) (Fin 1))"
  by eval

section \<open>Routed enter regression: one entered frame, keyed and published together\<close>

text \<open>
  \<^const>\<open>routed_cmb_g\<close> selects the callee's context and publishes the callee's
  entry state. Both must read the \<^emph>\<open>same\<close> entered frame: the frame entered
  from the caller's local state \<^bold>\<open>and\<close> the solver's global unknown. A route
  reading anything else -- the caller's own local state, or a frame entered
  against a bottom global -- keys the seed under a context the published value
  does not belong to.

  \<open>w0_spec\<close> makes that observable: its \<^const>\<open>dgs_enter\<close> answers the incoming
  global as the entered local, so the entered frame and the caller's local
  state are different values by construction. \<open>w0_route\<close> is the identity on
  the state it is handed, so the seed key \<^emph>\<open>is\<close> whichever frame the
  generator routes on.
\<close>

datatype w0_gk = W0Global | W0Seed pp ivl

definition w0_spec :: "(ivl, ivl) dg_spec" where
  "w0_spec =
     \<lparr> dgs_skip = \<lambda>d g. (g, d),
       dgs_assign = \<lambda>x e d g. (g, d),
       dgs_special = \<lambda>sc x d g. (g, d),
       dgs_branch = \<lambda>b pol d g. (g, d),
       dgs_body = \<lambda>p d g. (g, d),
       dgs_return = \<lambda>e p d g. (g, d),
       dgs_enter = \<lambda>ci d g. (bot, g),
       dgs_event = \<lambda>ev d g. (g, d),
       dgs_caller_cont = \<lambda>ci dc g. dc,
       dgs_combine_env = \<lambda>ci dc de g. (g, dc \<squnion> de),
       dgs_combine_assign = \<lambda>ci de g p. p \<rparr>"

definition w0_route :: "pp \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> call_action \<Rightarrow> ivl" where
  "w0_route u ctx d ca = d"

text \<open>The caller's local state is \<open>[1,1]\<close> and the solver's global is \<open>[7,7]\<close>, so
  the entered frame is \<open>[7,7]\<close> -- a value the caller's own local state never
  takes.\<close>
definition w0_sigma :: "pp \<times> ivl + w0_gk \<Rightarrow> (ivl, ivl) dg_state" where
  "w0_sigma z =
     (case z of Inl _ \<Rightarrow> DG (Ivl (Fin 1) (Fin 1)) bot
              | Inr W0Global \<Rightarrow> DG bot (Ivl (Fin 7) (Fin 7))
              | Inr (W0Seed _ _) \<Rightarrow> bot)"

text \<open>The call site resolves to the single callee \<open>f\<close>. Stated directly rather than
  through \<^const>\<open>static_resolve\<close>, because this witness builds one call tree by hand
  instead of compiling a program.\<close>

definition w0_resolve :: "pp \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> ivl \<Rightarrow> pname list" where
  "w0_resolve v cc ca d = [STR ''f'']"

definition w0_tree :: "(pp \<times> ivl, w0_gk, (ivl, ivl) dg_state) strategy_tree" where
  "w0_tree =
     routed_cmb_g w0_spec W0Global W0Seed w0_resolve w0_route bot
       (CallEdge None [STR ''p''] []) (Statement 0) (FunctionResult (STR ''f''))"

text \<open>The seed lands at the entered frame's own key, carrying that same frame.\<close>
lemma w0_seed_at_entered_frame:
  "sides_of_rhs w0_tree w0_sigma
     (Inr (W0Seed (FunctionEntry (STR ''f'')) (Ivl (Fin 7) (Fin 7))))
   = DG (Ivl (Fin 7) (Fin 7)) bot"
  unfolding w0_tree_def w0_sigma_def w0_spec_def w0_route_def by eval

text \<open>Nothing is published at the key a caller-state route would have chosen.\<close>
lemma w0_no_seed_at_caller_frame:
  "sides_of_rhs w0_tree w0_sigma
     (Inr (W0Seed (FunctionEntry (STR ''f'')) (Ivl (Fin 1) (Fin 1)))) = bot"
  unfolding w0_tree_def w0_sigma_def w0_spec_def w0_route_def by eval

text \<open>The callee-exit unknown the combine reads back is the same entered
  context, so the return leg and the seed agree on which activation they
  are talking about.\<close>
lemma w0_dep_at_entered_frame:
  "dep_aux w0_sigma w0_tree
   = {Inl (Statement 0, bot), Inr W0Global,
      Inl (FunctionResult (STR ''f''), Ivl (Fin 7) (Fin 7))}"
  unfolding w0_tree_def w0_sigma_def w0_spec_def w0_route_def
  by (simp add: routed_cmb_g_def routed_cmb_g_at_def w0_resolve_def
        Let_def insert_commute)

end
