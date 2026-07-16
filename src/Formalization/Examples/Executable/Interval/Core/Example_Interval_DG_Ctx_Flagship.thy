theory Example_Interval_DG_Ctx_Flagship
  imports
    Example_Interval_DG_IP_Flagship
begin

section \<open>Context-sensitive interval analysis of \<open>twice\<close> (executable)\<close>

text \<open>
  The polyvariant companion to \<open>Example_Interval_DG_IP_Flagship\<close>: the \<^emph>\<open>same\<close>
  generalized D/G generator \<^const>\<open>side_cfg_T_eff_cmp_seed_dg\<close>, instantiated with
  routed context hooks instead of the unit-context ones.  Each call to \<open>twice\<close> is
  analyzed under its own abstract calling context, so the two calls no longer merge:

  \<^item> \<open>twice(3)\<close> is analyzed at context \<open>[3,3]\<close>, giving \<open>#ret = [6,6]\<close> and \<open>x = [6,6]\<close>;
  \<^item> \<open>twice(10)\<close> is analyzed at context \<open>[10,10]\<close>, giving \<open>#ret = [20,20]\<close> and \<open>y = [20,20]\<close>.

  The monovariant flagship merges both calls into \<open>p = [3,10]\<close>, \<open>#ret = [6,20]\<close>.

  Context representation.  A context is the abstract value of the callee's formal
  parameter at entry --- the entry-store digest projected to \<open>''p''\<close>.  For \<open>twice\<close>
  (one formal, two constant arguments) this is finite and stable.  The general
  interval instance needs a canonicalizing / finite routing function; an arbitrary
  interval state is not a safe context key for recursive or widening-heavy programs.

  This theory certifies the executable computation (\<^theory_text>\<open>by eval\<close> on the vendored
  warrowing solver).  The collecting-soundness certificate for the routed solution
  (via \<open>sound_dg_spec.dg_collect_ctx_sound\<close>) is tracked separately in
  \<open>docs/ROUTE_A7_EXECUTABLE_DG_MIGRATION.md\<close>.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  The extended global-key type keeps the two flow-insensitive roles apart.
  \<open>GlobAt\<close> keys a real per-context global slot (unused by \<open>twice\<close>, which has
  no globals); \<open>Seed\<close> keys the callee-entry seed slot at a program point
  under a context.  Pattern matching makes the separation explicit --- the two
  never share a slot.
\<close>

datatype gk = GlobAt "ivl" | Seed pp "ivl"

subsection \<open>The routed context hooks\<close>

definition Spoly :: "(ivl st, ivl st) dg_spec" where
  "Spoly = unit_dg_spec_st ivl_tf_st"

text \<open>The callee-entry local store produced by an \<^const>\<open>EA_Enter\<close> action from a
  caller-local state (globals defaulted to \<open>bot\<close>: \<open>twice\<close> has none).\<close>
definition entered_ivl :: "ivl st \<Rightarrow> edge_action \<Rightarrow> ivl st" where
  "entered_ivl d a = snd (dg_spec_step Spoly a d bot)"

text \<open>The routing function: the context a call selects is the entered value of the
  formal \<open>''p''\<close>.\<close>
definition route_ivl :: "ivl st \<Rightarrow> edge_action \<Rightarrow> ivl" where
  "route_ivl d a = lookup_st (entered_ivl d a) ''p''"

text \<open>Extra per-node trees: a frame-entry seed \<^emph>\<open>read\<close> (of the incoming seed slot)
  and, for every outgoing \<^const>\<open>EA_Enter\<close>, a caller-side routed \<^emph>\<open>publication\<close>
  of the entered store into the callee's seed slot.\<close>
definition extra_ivl ::
  "cfg \<Rightarrow> ivl \<Rightarrow> pp \<Rightarrow> (pp \<times> ivl, gk, (ivl st, ivl st) dg_state) strategy_tree list" where
  "extra_ivl g ctx v =
     (if is_frame_entry g v
        then [QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot))]
        else [])
     @ map (\<lambda>(w, a).
             QueryL (v, ctx) (\<lambda>d.
               Side (Seed w (route_ivl (locals d) a)) (DG bot (entered_ivl (locals d) a))
                 (Answer (DG bot bot))))
           (enter_successor_list g v)"

text \<open>The routing combine: the callee exit is read under the context selected at the
  \<^emph>\<open>same\<close> call site (recomputed from \<open>cc\<close>'s own \<^const>\<open>EA_Enter\<close> edge), so the return
  reads the matching callee context rather than a merge.\<close>
definition cmb_ivl ::
  "cfg \<Rightarrow> ivl \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> ivl, gk, (ivl st, ivl st) dg_state) strategy_tree" where
  "cmb_ivl g ctx dst cc ex =
     QueryL (cc, ctx) (\<lambda>dcl.
       (case enter_successor_list g cc of
          (w, a) # _ \<Rightarrow>
            QueryL (ex, route_ivl (locals dcl) a) (\<lambda>dex.
              Side (GlobAt ctx) (DG bot (fst (dgs_combine Spoly dst (locals dcl) (locals dex) bot)))
                (Answer (DG (snd (dgs_combine Spoly dst (locals dcl) (locals dex) bot)) bot)))
        | [] \<Rightarrow> Answer (DG bot bot)))"

subsection \<open>The routed equation system and its solution\<close>

definition twice_ctx_eqs ::
  "(pp \<times> ivl, gk, (ivl st, ivl st) dg_state) eqsT" where
  "twice_ctx_eqs =
     side_cfg_T_eff_cmp_seed_dg non_enter_predecessor_list GlobAt
       (cmb_ivl twice_cfg) (extra_ivl twice_cfg)
       twice_cfg Spoly bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

text \<open>The main context is \<open>bot\<close> (\<open>main\<close> is the root activation, no formal binds it).\<close>
definition twice_ctx_sol ::
  "(pp \<times> ivl) set \<times> (pp \<times> ivl + gk \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "twice_ctx_sol = TD_side_warrowing_apinis_Interp_solve twice_ctx_eqs (cfg_exit twice_cfg, bot)"

lemma twice_ctx_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c twice_ctx_eqs (cfg_exit twice_cfg, bot) \<noteq> None"
  by eval

subsection \<open>The two calling contexts are distinct\<close>

definition ctx_call1 :: ivl where
  "ctx_call1 = route_ivl (locals (snd twice_ctx_sol (Inl (4, bot))))
                 (EA_Enter [''p''] [IMP2_Syntax.N 3])"

definition ctx_call2 :: ivl where
  "ctx_call2 = route_ivl (locals (snd twice_ctx_sol (Inl (6, bot))))
                 (EA_Enter [''p''] [IMP2_Syntax.N 10])"

lemma contexts_distinct: "ctx_call1 \<noteq> ctx_call2"
  by eval

lemma ctx_call1_val: "ctx_call1 = Ivl (Fin 3) (Fin 3)" by eval
lemma ctx_call2_val: "ctx_call2 = Ivl (Fin 10) (Fin 10)" by eval

subsection \<open>Per-context exact results\<close>

text \<open>Callee entry (node 0) parameter, per context.\<close>
lemma call1_p_at_entry:
  "lookup_st (locals (snd twice_ctx_sol (Inl (0, ctx_call1)))) ''p'' = Ivl (Fin 3) (Fin 3)"
  by eval

lemma call2_p_at_entry:
  "lookup_st (locals (snd twice_ctx_sol (Inl (0, ctx_call2)))) ''p'' = Ivl (Fin 10) (Fin 10)"
  by eval

text \<open>Callee exit (node 3) return channel, per context --- \<^emph>\<open>not\<close> merged.\<close>
lemma call1_ret_at_exit:
  "lookup_st (locals (snd twice_ctx_sol (Inl (3, ctx_call1)))) ''#ret'' = Ivl (Fin 6) (Fin 6)"
  by eval

lemma call2_ret_at_exit:
  "lookup_st (locals (snd twice_ctx_sol (Inl (3, ctx_call2)))) ''#ret'' = Ivl (Fin 20) (Fin 20)"
  by eval

text \<open>Caller destinations after each return.\<close>
lemma x_computed:
  "lookup_st (locals (snd twice_ctx_sol (Inl (5, bot)))) ''x'' = Ivl (Fin 6) (Fin 6)"
  by eval

lemma y_computed:
  "lookup_st (locals (snd twice_ctx_sol (Inl (7, bot)))) ''y'' = Ivl (Fin 20) (Fin 20)"
  by eval

subsection \<open>Seed slots and coverage\<close>

text \<open>Each call publishes the entered store into its own context's seed slot.\<close>
lemma seed_call1:
  "lookup_st (globs (snd twice_ctx_sol (Inr (Seed 0 ctx_call1)))) ''p'' = Ivl (Fin 3) (Fin 3)"
  by eval

lemma seed_call2:
  "lookup_st (globs (snd twice_ctx_sol (Inr (Seed 0 ctx_call2)))) ''p'' = Ivl (Fin 10) (Fin 10)"
  by eval

text \<open>The callee entry is materialized once per routed context and never under the
  main context: the two calls are analyzed separately.\<close>
lemma callee_covered_call1: "(0, ctx_call1) \<in> fst twice_ctx_sol" by eval
lemma callee_covered_call2: "(0, ctx_call2) \<in> fst twice_ctx_sol" by eval
lemma callee_not_under_main: "(0, bot) \<notin> fst twice_ctx_sol" by eval

end
