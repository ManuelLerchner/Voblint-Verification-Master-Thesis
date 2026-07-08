theory Example_Interval_Mode_Digest
  imports
    "Voblint_Analysis.Value_Digest_Reader"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Digest_Keyed_Writer_Sound"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Interval_Side_Soundness"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Compiled interval mode context from the local state (with a loop)\<close>

text \<open>
  The interval sibling of \<open>Example_Sign_Mode_Digest\<close>: the \<^emph>\<open>same\<close> generic
  value-derived digest machinery, at the \<^typ>\<open>ivl\<close> domain instead of \<open>sign\<close>.
  The only domain-specific content is the projection \<open>ivl_decode\<close>, which
  buckets an interval by a numeric threshold; the reader locale
  \<^locale>\<open>value_digest_reader\<close>, the digest generator, and the switching combine are
  reused unchanged.  This is the second dissimilar instance of the kernel, which is
  what makes its genericity a demonstrated fact rather than a claim.

  \<open>main\<close> first runs a \<^bold>\<open>while loop\<close> \<open>i := 0; while (i < 5) { i := i + 1 }\<close> --- the
  interval analysis tracks \<open>i\<close> as a range --- then calls \<open>f\<close> under two contexts
  distinguished by the ordinary local \<open>m\<close> (\<open>m = 1\<close> vs \<open>m = 3\<close>), reading \<open>i\<close> and \<open>m\<close>
  back (\<open>x := i + m\<close>).  The digest keys each global write by the projected \<open>m\<close>, so
  the two writes to \<open>G\<close> stay in separate partitions where the context-blind read merges them.
\<close>

subsection \<open>The finite interval mode (the projection's codomain)\<close>

datatype imode = ILo | IHi

instance imode :: finite
proof
  show "finite (UNIV :: imode set)"
  proof (rule finite_subset[of _ "{ILo, IHi}"])
    show "(UNIV :: imode set) \<subseteq> {ILo, IHi}" using imode.exhaust by blast
    show "finite {ILo, IHi}" by simp
  qed
qed

instantiation imode :: enum
begin
definition "enum_imode = [ILo, IHi]"
definition "enum_all_imode P \<longleftrightarrow> P ILo \<and> P IHi"
definition "enum_ex_imode P \<longleftrightarrow> P ILo \<or> P IHi"
instance
proof
  show "(UNIV :: imode set) = set enum_class.enum"
    using imode.exhaust by (auto simp: enum_imode_def)
qed (auto simp: enum_imode_def enum_all_imode_def enum_ex_imode_def, (metis imode.exhaust)+)
end

text \<open>A \<^class>\<open>show_val\<close> instance so the generic context-clustered GraphViz renderer prints the
  mode partitions.\<close>
instantiation imode :: show_val begin
definition "show_val_imode m = (case m of ILo \<Rightarrow> ''ILo'' | IHi \<Rightarrow> ''IHi'')"
instance ..
end

subsection \<open>Decode: bucket an interval by a numeric threshold (the only ivl-specific content)\<close>

text \<open>\<open>IHi\<close> iff the interval is entirely \<open>\<ge> 2\<close> (lower bound at least \<open>Fin 2\<close>); every
  other interval --- including the unset default \<^const>\<open>ivl_top\<close> --- is \<open>ILo\<close>.\<close>
definition ivl_decode :: "ivl \<Rightarrow> imode" where
  "ivl_decode i = (case i of Ivl l u \<Rightarrow> (if Fin 2 \<le> l then IHi else ILo))"

text \<open>The generic reader, instantiated at the interval domain and the projected local \<open>''m''\<close>.\<close>
interpretation ivl_mode: value_digest_reader ivl_decode "''m''" .

subsection \<open>The source program (procedures + a while loop)\<close>

definition iv_prog :: imp_prog where
  "iv_prog = \<lbrakk>
     int G;

     void f() {
       z := G
     }
     void main() {
       i := 0;
       while (i < 5) { i := i + 1 };
       m := 1;  G := 5;  f();  x := i + m;
       m := 3;  G := 9;  f();  y := i + m
     }
   \<rbrakk>"

definition iv_cfg :: cfg where
  "iv_cfg = compile_prog (prog_table iv_prog) (prog_procs iv_prog) (prog_main iv_prog)"

subsection \<open>Automatic context: project the caller's local \<open>m\<close>\<close>

definition iv_ec :: "pp \<Rightarrow> imode \<Rightarrow> ivl st \<Rightarrow> imode" where
  "iv_ec cc ctx caller = ivl_decode (lookup_st caller ''m'')"

definition iv_prep :: "pp \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "iv_prep cc s = s"

definition iv_dg :: "ivl st \<Rightarrow> imode" where
  "iv_dg s = ivl_decode (lookup_st s ''m'')"

subsection \<open>Context-keyed run (the merge): globals collapse under one context\<close>

definition iv_cmp_eqs :: "(pp \<times> imode, imode, ivl st) eqsT" where
  "iv_cmp_eqs = side_cfg_T_eff_cmp_st id
                  (\<lambda>c cc ex. switching_combine_st iv_prep iv_ec cc ex c)
                  iv_cfg ivl_etf_st bot bot cinit_ivl_st"

definition iv_cmp_solution ::
  "(pp \<times> imode) set \<times> ((pp \<times> imode) + imode \<Rightarrow> ivl st)" where
  "iv_cmp_solution = TD_side_always_join_Interp_solve iv_cmp_eqs (cfg_exit iv_cfg, ILo)"

subsection \<open>Digest-keyed run (the fix): globals stay separated per mode\<close>

definition iv_digest_eqs :: "(pp \<times> imode, imode, ivl st) eqsT" where
  "iv_digest_eqs = side_cfg_T_eff_digest_st iv_dg
                     (\<lambda>c cc ex. switching_combine_digest_st iv_dg iv_prep cc ex c)
                     iv_cfg ivl_etf_st bot bot cinit_ivl_st"

definition iv_digest_solution ::
  "(pp \<times> imode) set \<times> ((pp \<times> imode) + imode \<Rightarrow> ivl st)" where
  "iv_digest_solution = TD_side_always_join_Interp_solve iv_digest_eqs (cfg_exit iv_cfg, ILo)"

lemmas iv_unfold =
  iv_cmp_solution_def iv_cmp_eqs_def iv_digest_solution_def iv_digest_eqs_def
  iv_cfg_def iv_ec_def iv_prep_def iv_dg_def ivl_decode_def

subsection \<open>The while loop is tracked as an interval range\<close>

text \<open>After \<open>i := 0; while (i < 5) { i := i + 1 }\<close> the interval analysis knows \<open>i\<close> is
  exactly \<open>[5, 5]\<close> at the exit --- the loop counter tracked through the fixpoint, the
  guard \<open>i < 5\<close> capping it (\<open>TD_side_always_join_Interp_solve\<close> converges without widening).\<close>
lemma iv_loop_tracked:
  "lookup_st (snd iv_digest_solution (Inl (cfg_exit iv_cfg, ILo))) ''i'' = Ivl (Fin 5) (Fin 5)"
  unfolding iv_unfold by eval

subsection \<open>The solver separates the global into finite mode partitions\<close>

lemma iv_digest_runs: "fst iv_digest_solution \<noteq> {}"
  unfolding iv_unfold by eval

text \<open>Context-blind: under one function context both writes to \<open>G\<close> join into one slot,
  so the read is the imprecise \<open>[0, 9]\<close>.\<close>
lemma iv_cmp_merges:
  "lookup_st (snd iv_cmp_solution (Inr ILo)) ''G'' = Ivl (Fin 0) (Fin 9)"
  unfolding iv_unfold by eval

text \<open>Digest-keyed: the two projected modes keep \<open>G\<close> in separate partitions.  The
  \<open>IHi\<close> partition is the \<^emph>\<open>sharp\<close> \<open>[9, 9]\<close> where the context-blind read only knows \<open>[0, 9]\<close>.\<close>
lemma iv_digest_slot_ILo:
  "lookup_st (snd iv_digest_solution (Inr ILo)) ''G'' = Ivl (Fin 0) (Fin 5)"
  unfolding iv_unfold by eval

lemma iv_digest_slot_IHi:
  "lookup_st (snd iv_digest_solution (Inr IHi)) ''G'' = Ivl (Fin 9) (Fin 9)"
  unfolding iv_unfold by eval

text \<open>The precision payoff on the interval domain, sealed by the solver: the digest
  read at \<open>IHi\<close> is strictly tighter than the context-blind merge.\<close>
theorem iv_digest_separates_the_modes:
  "lookup_st (snd iv_digest_solution (Inr ILo)) ''G'' = Ivl (Fin 0) (Fin 5)
   \<and> lookup_st (snd iv_digest_solution (Inr IHi)) ''G'' = Ivl (Fin 9) (Fin 9)
   \<and> lookup_st (snd iv_cmp_solution (Inr ILo)) ''G'' = Ivl (Fin 0) (Fin 9)"
  using iv_digest_slot_ILo iv_digest_slot_IHi iv_cmp_merges by blast

subsection \<open>The same digest system across the update-rule menu\<close>

text \<open>One \<^const>\<open>run_menu\<close> solves the digest system under every update rule and reads the
  \<open>ILo\<close> partition of \<open>G\<close> --- the whole story in one machine-checked line:
  \<^item> \<open>join\<close> and \<open>per_origin\<close> both keep the partition sharp at \<open>[0, 5]\<close>.  Per-origin
    reproduces the digest separation \<^emph>\<open>without the solver knowing about digests\<close> --- it
    keeps each write origin's contribution separate (the Schwarz clustered discipline).
  \<^item> \<open>warrow\<close> (Apinis warrowing) widens \<^emph>\<open>globals\<close>, and the digest partitions are globals,
    so it widens the slot's upper bound to \<open>+inf\<close> --- \<^term>\<open>Ivl (Fin 0) PlusInf\<close> (the
    widening bot-law pins the lower bound at \<open>0\<close>) --- losing the sharp \<open>[0, 5]\<close>.
  So the value-derived digest is a \<^emph>\<open>join / per-origin\<close> demonstration; global widening is
  the wrong tool for it.  A per-origin \<^emph>\<open>widening\<close> rule would combine both --- loop
  termination without collapsing the digest --- but does not yet code-generate (P11).
  Widening on a \<^emph>\<open>local\<close>, where it belongs, is shown next.\<close>

lemma iv_digest_across_update_rules:
  "run_menu iv_digest_eqs (cfg_exit iv_cfg, ILo) (Inr ILo) ''G''
     = [(STR ''join'',       Ivl (Fin 0) (Fin 5)),
        (STR ''per_origin'', Ivl (Fin 0) (Fin 5)),
        (STR ''warrow'',     Ivl (Fin 0) PlusInf)]"
  unfolding iv_unfold run_menu_def solver_menu_def by eval

subsection \<open>Widening and narrowing on an unbounded loop (backward filter recovers precision)\<close>

text \<open>A loop whose bound is far too large for the join solver to reach by iteration.  The
  warrowing solver \<^bold>\<open>widens\<close> the counter to \<open>[0, \<infinity>)\<close> at the head, then the backward guard
  filter --- the same inverse interval analysis (\<^const>\<open>inv_less_ivl\<close>) the digest run's guards
  use --- \<^bold>\<open>narrows\<close> it back to the exact \<open>[0, 1000000]\<close>, so the exit is the sharp
  \<open>[1000000, 1000000]\<close>.  Neither operator alone gives a terminating \<^emph>\<open>and\<close> precise result.\<close>

definition wide_prog :: "IMP2_Proc.com" where
  "wide_prog = \<lbrakk> x := 0; while (x < 1000000) { x := x + 1 } \<rbrakk>"

definition wide_cfg :: cfg where
  "wide_cfg = compile_prog Map.empty [] wide_prog"

definition wide_eqs :: "(pp, unit, ivl st) eqsT" where
  "wide_eqs = side_cfg_T_eff_st wide_cfg ivl_etf_st bot cinit_ivl_st ()"

definition wide_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "wide_sol = TD_side_warrowing_apinis_Interp_solve wide_eqs (cfg_exit wide_cfg)"

lemmas wide_unfold = wide_sol_def wide_eqs_def wide_cfg_def

text \<open>Widening + narrowing land the exit on the sharp \<open>[1000000, 1000000]\<close> in one solve
  (fractions of a second), where a pure join would need a million iterations.\<close>
lemma wide_loop_widened_then_narrowed:
  "lookup_st (snd wide_sol (Inl (cfg_exit wide_cfg))) ''x'' = Ivl (Fin 1000000) (Fin 1000000)"
  unfolding wide_unfold by eval

subsection \<open>The widening loop, proven sound (not merely evaluated)\<close>

text \<open>The instantiation that certifies the digest run under each update rule (in the sign
  flagship) applies here too: the vendor proves the warrowing solve is a
  \<^const>\<open>part_post_solution\<close>, and the plain-generator transport lifts it to a post-solution of
  the \<^emph>\<open>abstract\<close> interval generator --- the exact fact the analyzer soundness consumes.  So the
  million-iteration loop is not just evaluated to \<open>[1000000, 1000000]\<close>; the warrowing solver's
  whole run is a certified sound over-approximation.  Widening is a proven-sound feature that
  terminates where join cannot.\<close>

lemma wide_solve_c_some:
  "TD_side_warrowing_apinis_Interp_solve_c wide_eqs (cfg_exit wide_cfg) \<noteq> None"
  unfolding wide_eqs_def wide_cfg_def by eval

lemma wide_part_post_solution:
  "part_post_solution wide_eqs (cfg_exit wide_cfg) (snd wide_sol) (fst wide_sol)"
  using TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[OF wide_solve_c_some]
  unfolding wide_sol_def by simp

subsection \<open>Annotated interval GraphViz\<close>

text \<open>The analysis-annotated DOT renderer (\<^const>\<open>annotated_dot_of_prog_lit\<close>) is generic over
  any \<^class>\<open>show_val\<close> domain; \<^typ>\<open>ivl\<close> has that instance, so the interval solution renders with
  no domain-specific tooling --- the interval counterpart of the sign examples' annotated DOT.
  Each CFG node carries its flow-sensitive interval; here the widened loop counter.\<close>

definition wide_dot :: String.literal where
  "wide_dot = annotated_dot_of_prog_lit Map.empty [] wide_prog (snd wide_sol)"

text \<open>@{command ML_val} \<open>writeln (@{code wide_dot})\<close> emits the DOT source.\<close>

text \<open>The \<^emph>\<open>context-sensitive\<close> digest view, the interval counterpart of the sign flagship's
  \<open>mode_digest_dot\<close>: \<^emph>\<open>three\<close> clusters, one per activation (\<open>main\<close> once, \<open>f @ ILo\<close>, \<open>f @ IHi\<close>),
  each \<^bold>\<open>node labelled with its solved local intervals\<close> (all locals, auto-collected) and each cluster
  with its own global partition of \<open>G\<close>.  The two calls are routed by the digest computed from
  the solution (\<open>iv_call_ctx\<close>): the \<open>m=1\<close> call enters \<open>f @ ILo\<close>, the \<open>m=3\<close> call \<open>f @ IHi\<close>,
  both returning into \<open>main\<close>.  Only the labels are interval-specific; the renderer is generic.\<close>

text \<open>\<open>f\<close> is compiled first, so its body is \<open>pp0\<close>/\<open>pp1\<close>; \<open>main\<close> is the rest.\<close>
definition iv_f_pps :: "pp list" where "iv_f_pps = [0, 1]"

definition iv_call_ctx :: "pp \<Rightarrow> imode" where
  "iv_call_ctx cc = iv_dg (snd iv_digest_solution (Inl (cc, ILo)))"

datatype ivl_rctx = IvMain | IvFILo | IvFIHi

definition ivl_rctx_mode :: "ivl_rctx \<Rightarrow> imode" where
  "ivl_rctx_mode r = (case r of IvMain \<Rightarrow> ILo | IvFILo \<Rightarrow> ILo | IvFIHi \<Rightarrow> IHi)"

definition ivl_rctx_key :: "ivl_rctx \<Rightarrow> string" where
  "ivl_rctx_key r = (case r of IvMain \<Rightarrow> ''main'' | IvFILo \<Rightarrow> ''fILo'' | IvFIHi \<Rightarrow> ''fIHi'')"

definition ivl_rctx_label :: "ivl_rctx \<Rightarrow> string" where
  "ivl_rctx_label r = (case r of IvMain \<Rightarrow> ''main'' | IvFILo \<Rightarrow> ''f @ ILo'' | IvFIHi \<Rightarrow> ''f @ IHi'')"

definition iv_f_rctx_of :: "pp \<Rightarrow> ivl_rctx" where
  "iv_f_rctx_of cc = (if iv_call_ctx cc = ILo then IvFILo else IvFIHi)"

text \<open>Node labels come from the generic \<^const>\<open>ctx_debug_state_node_label_auto\<close>: it auto-collects
  the program's locals and prints each node's solved interval, so no hand-written label or
  variable list is needed --- only the per-node state lookup.\<close>
definition iv_node_label :: "pp \<times> ivl_rctx \<Rightarrow> string" where
  "iv_node_label = ctx_debug_state_node_label_auto iv_cfg
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd iv_digest_solution (Inl (p, ivl_rctx_mode r)))"

definition iv_digest_globals :: "ivl_rctx \<Rightarrow> string" where
  "iv_digest_globals r =
     ''G = '' @ show_val (lookup_st (snd iv_digest_solution (Inr (ivl_rctx_mode r))) ''G'')"

definition iv_rmode_nodes :: "(pp \<times> ivl_rctx) list" where
  "iv_rmode_nodes =
     map (\<lambda>p. (p, IvMain)) (filter (\<lambda>p. p \<notin> set iv_f_pps) (sorted_list_of_set (nodes iv_cfg)))
   @ map (\<lambda>p. (p, IvFILo)) iv_f_pps
   @ map (\<lambda>p. (p, IvFIHi)) iv_f_pps"

definition iv_rmode_intra :: "((pp \<times> ivl_rctx) \<times> edge_action \<times> (pp \<times> ivl_rctx)) list" where
  "iv_rmode_intra =
     [((u, IvMain), a, (v, IvMain)). (u, a, v) \<leftarrow> cfg_edges_list iv_cfg,
        a \<noteq> EA_Enter, u \<notin> set iv_f_pps, v \<notin> set iv_f_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list iv_cfg,
        u \<in> set iv_f_pps, v \<in> set iv_f_pps, r \<leftarrow> [IvFILo, IvFIHi]]"

definition iv_rmode_calls :: "((pp \<times> ivl_rctx) \<times> (pp \<times> ivl_rctx)) list" where
  "iv_rmode_calls =
     [((u, IvMain), (v, iv_f_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list iv_cfg, a = EA_Enter]"

definition iv_rmode_returns :: "((pp \<times> ivl_rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> ivl_rctx)) list" where
  "iv_rmode_returns =
     [((ex, iv_f_rctx_of cc), (cc, ex, ret), (ret, IvMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list iv_cfg]"

definition iv_digest_dot :: String.literal where
  "iv_digest_dot = String.implode
     (ctx_debug_graphviz_with_globals
        ivl_rctx_key ivl_rctx_label iv_digest_globals iv_node_label (\<lambda>_. ''shape=box'')
        [IvMain, IvFILo, IvFIHi]
        iv_rmode_nodes iv_rmode_intra iv_rmode_calls iv_rmode_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code iv_digest_dot})\<close> emits the DOT source; \<open>main\<close>'s nodes
  carry the loop counter \<open>i=[5,5]\<close> and the reads \<open>x\<close>/\<open>y\<close>, and the two \<open>f\<close> clusters carry the
  separated globals \<open>G=[0,5]\<close> / \<open>G=[9,9]\<close>.\<close>

theorem wide_abstracts:
  "part_post_solution
     (side_cfg_T_eff wide_cfg ivl_etf (fun_of_st bot) (fun_of_st cinit_ivl_st) ())
     (cfg_exit wide_cfg)
     (fun_of_st \<circ> snd wide_sol) (fst wide_sol)"
proof -
  have pp_st: "part_post_solution
       (side_cfg_T_eff_st wide_cfg ivl_etf_st bot cinit_ivl_st ()) (cfg_exit wide_cfg)
       (snd wide_sol) (fst wide_sol)"
    using wide_part_post_solution unfolding wide_eqs_def by simp
  show ?thesis
    by (rule part_post_solution_st_to_abs_eff_unit_transfer
          [OF ivl_etf_edge_tree ivl_etf_combine_tree
              ivl_etf_st_edge_tree ivl_etf_st_combine_tree ivl_tf_st_commute pp_st])
qed

subsection \<open>Emit the GraphViz sources\<close>

text \<open>Print the DOT for the context-clustered digest run and the annotated widening loop.
  Paste either into Graphviz.\<close>

ML_val \<open>writeln (@{code iv_digest_dot})\<close>
ML_val \<open>writeln (@{code wide_dot})\<close>

end
