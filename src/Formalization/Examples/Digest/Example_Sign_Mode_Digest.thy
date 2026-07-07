theory Example_Sign_Mode_Digest
  imports
    "Voblint_Analysis.Value_Digest_Read"
    "Voblint_Analysis.Exec_Sign_Cmp_Keyed_Gen_Run"
    "Voblint_Analysis.Digest_Keyed_Writer_Sound"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Analysis_GraphViz"
begin

section \<open>Compiled mode context from the local state: what the pipeline does and does not do\<close>

text \<open>
  A source program is compiled to a CFG and analysed with the call context generated
  \<^emph>\<open>automatically\<close> by projecting the caller's ordinary local \<open>''mode''\<close> through
  \<^const>\<open>mode_decode\<close> --- Goblint's \<open>context : D.t \<rightarrow> C.t\<close>.  The finite \<^typ>\<open>mode\<close> keys the
  global partitions; the vendored \<^const>\<open>TD_side_always_join_Interp_solve\<close> runs the reusable
  \<^const>\<open>switching_combine_st\<close>.

  The theory runs \<^emph>\<open>two\<close> analyses of the same compiled program, a before/after:
  \<^item> \<^bold>\<open>Context-keyed (the merge).\<close>  \<^const>\<open>side_cfg_T_eff_cmp_st\<close> keys every intra global write
    by the fixed function context.  The two writes \<open>G := 0\<close>, \<open>G := 1\<close> live in \<open>main\<close> under one
    context, so both land in one slot and the flow-insensitive join collapses them:
    \<open>slot_MZero = slot_MOne = SNonNeg\<close>.  Context generation still works --- \<open>f\<close>'s body
    materialises under \<^emph>\<open>both\<close> activations (\<open>ctxs_at_0 = {MZero, MOne}\<close>) --- but the split is
    spurious for the value.
  \<^item> \<^bold>\<open>Digest-keyed (the fix).\<close>  \<^const>\<open>side_cfg_T_eff_digest_st\<close> keys each write by the digest
    of its \<^emph>\<open>write-point state\<close> (Goblint's \<open>sideg (G, Digest.compute d)\<close>), and the
    \<^const>\<open>switching_combine_digest_st\<close> reads and republishes through the same digest.  Now
    \<open>G := 0\<close> (mode zero) lands in \<^term>\<open>Inr MZero\<close> and \<open>G := 1\<close> (mode one) in \<^term>\<open>Inr MOne\<close>:
    \<open>digest_slot_MZero = SZero\<close>, \<open>digest_slot_MOne = SPos\<close>, genuinely separated where the
    context-blind read merges to \<^const>\<open>SNonNeg\<close> (\<open>digest_separates_the_modes\<close>).

  The digest write generator is the piece the context/site generators lacked: a write key that
  is a projection of the local state.  The value-carried read side (\<^const>\<open>mode_obs\<close>) and its
  soundness are in \<^theory>\<open>Voblint_Analysis.Value_Digest_Read\<close> (and theory
  \<open>Exec_Sign_Mode_Value_Run\<close>); together they are the read/write pair of one digest.  Executable
  soundness of the digest writer (the intra analogue of \<^const>\<open>switching_combine_sound\<close>) is the
  remaining proof obligation --- see \<open>docs/VALUE_CARRIED_DIGEST_STATUS.md\<close>.
\<close>

subsection \<open>The source program\<close>

text \<open>\<open>main\<close> sets the local \<open>''mode''\<close> and the global \<open>G\<close>, calls \<open>f\<close> under each mode, and
  reads them back into \<open>x\<close> / \<open>y\<close> (\<open>x := G + mode\<close>) --- so \<open>''mode''\<close> is a genuine program
  variable, read for computation, not a write-only ghost; \<open>f\<close> reads the global.
  \<open>G\<close>-prefixed names are global; \<open>mode\<close>, \<open>x\<close>, \<open>y\<close>, \<open>z\<close> are locals.\<close>

definition mode_prog :: imp_prog where
  "mode_prog = \<lbrakk>
     int G;

     void f() {
       z := G
     }
     void main() {
       mode := 0;  G := 0;  f();  x := G + mode;
       mode := 1;  G := 1;  f();  y := G + mode
     }
   \<rbrakk>"

definition mode_cfg :: cfg where
  "mode_cfg = compile_prog (prog_table mode_prog) (prog_procs mode_prog) (prog_main mode_prog)"

subsection \<open>Automatic context: project the local mode of the caller state\<close>

text \<open>The context selector reads the caller's local \<open>''mode''\<close> and decodes it to a
  \<^typ>\<open>mode\<close>.  This is the projection reader used as \<open>ec\<close> --- the context is a function of
  the local abstract state, not a hand-chosen label.\<close>

definition mode_ec :: "pp \<Rightarrow> mode \<Rightarrow> sign st \<Rightarrow> mode" where
  "mode_ec cc ctx caller = mode_decode (lookup_st caller ''mode'')"

text \<open>The call-state transform is the identity (parameterless call): it preserves locals,
  the \<open>prep_loc\<close> side of the switching-combine soundness contract.\<close>

definition mode_prep :: "pp \<Rightarrow> sign st \<Rightarrow> sign st" where
  "mode_prep cc s = s"

subsection \<open>The mode-keyed switching-combine equation system\<close>

definition mode_eqs :: "(pp \<times> mode, mode, sign st) eqsT" where
  "mode_eqs = side_cfg_T_eff_cmp_st id
                (\<lambda>c cc ex. switching_combine_st mode_prep mode_ec cc ex c)
                mode_cfg sign_etf_st bot bot cinit_sign_st"

definition mode_solution ::
  "(pp \<times> mode) set \<times> ((pp \<times> mode) + mode \<Rightarrow> sign st)" where
  "mode_solution = TD_side_always_join_Interp_solve mode_eqs (cfg_exit mode_cfg, MZero)"

subsection \<open>The compiled generator runs\<close>

lemma mode_runs: "fst mode_solution \<noteq> {}"
  unfolding mode_solution_def mode_eqs_def mode_cfg_def mode_ec_def mode_prep_def by eval

subsection \<open>The solver separates the global into finite mode partitions\<close>

lemmas mode_unfold =
  mode_solution_def mode_eqs_def mode_cfg_def mode_ec_def mode_prep_def

lemma slot_MZero: "lookup_st (snd mode_solution (Inr MZero)) ''G'' = SNonNeg"
  unfolding mode_unfold by eval

lemma slot_MOne: "lookup_st (snd mode_solution (Inr MOne)) ''G'' = SNonNeg"
  unfolding mode_unfold by eval

lemma slot_join_all:
  "lookup_st (snd mode_solution (Inr MZero) \<squnion> snd mode_solution (Inr MOne)) ''G'' = SNonNeg"
  unfolding mode_unfold by eval

subsection \<open>Automatic context generation materialises both mode activations\<close>

text \<open>The contexts present at each program point of the solved system: the image of the
  solved unknown set at \<open>p\<close>.  It exhibits which mode activations the projection-based \<open>ec\<close>
  generated.\<close>
definition ctxs_at :: "pp \<Rightarrow> mode set" where
  "ctxs_at p = snd ` {qc \<in> fst mode_solution. fst qc = p}"

lemma ctxs_at_0: "ctxs_at 0 = {MZero, MOne}"
  unfolding ctxs_at_def mode_unfold by eval

subsection \<open>The digest-keyed writer: genuine value separation\<close>

text \<open>
  The fix.  \<^const>\<open>side_cfg_T_eff_digest_st\<close> keys each intra global write by the digest
  \<open>mode_dg\<close> of the \<^emph>\<open>write-point state\<close> --- Goblint's \<open>sideg (G, Digest.compute d)\<close>.  Now
  \<open>G := 0\<close> (executed with \<open>mode = 0\<close>) is side-effected to \<^term>\<open>Inr MZero\<close> and \<open>G := 1\<close> (with
  \<open>mode = 1\<close>) to \<^term>\<open>Inr MOne\<close>, and the same key filters reads, so \<open>main\<close>'s two reads
  \<open>x := G\<close> / \<open>y := G\<close> --- taken at flow-sensitively distinct modes --- recover the separated
  values.
\<close>

definition mode_dg :: "sign st \<Rightarrow> mode" where
  "mode_dg s = mode_decode (lookup_st s ''mode'')"

definition mode_digest_eqs :: "(pp \<times> mode, mode, sign st) eqsT" where
  "mode_digest_eqs = side_cfg_T_eff_digest_st mode_dg
                       (\<lambda>c cc ex. switching_combine_digest_st mode_dg mode_prep cc ex c)
                       mode_cfg sign_etf_st bot bot cinit_sign_st"

definition mode_digest_solution ::
  "(pp \<times> mode) set \<times> ((pp \<times> mode) + mode \<Rightarrow> sign st)" where
  "mode_digest_solution = TD_side_always_join_Interp_solve mode_digest_eqs (cfg_exit mode_cfg, MZero)"

lemmas mode_digest_unfold =
  mode_digest_solution_def mode_digest_eqs_def mode_cfg_def mode_ec_def mode_prep_def mode_dg_def

lemma mode_digest_runs: "fst mode_digest_solution \<noteq> {}"
  unfolding mode_digest_unfold by eval

lemma digest_slot_MZero: "lookup_st (snd mode_digest_solution (Inr MZero)) ''G'' = SZero"
  unfolding mode_digest_unfold by eval

lemma digest_slot_MOne: "lookup_st (snd mode_digest_solution (Inr MOne)) ''G'' = SPos"
  unfolding mode_digest_unfold by eval

lemma digest_slot_join:
  "lookup_st (snd mode_digest_solution (Inr MZero) \<squnion> snd mode_digest_solution (Inr MOne)) ''G'' = SNonNeg"
  unfolding mode_digest_unfold by eval

text \<open>The precision payoff, sealed by the solver: the two modes keep \<open>G\<close> apart
  (\<^const>\<open>SZero\<close> vs \<^const>\<open>SPos\<close>) where the context-blind join-all merges to \<^const>\<open>SNonNeg\<close>.\<close>
theorem digest_separates_the_modes:
  "lookup_st (snd mode_digest_solution (Inr MZero)) ''G'' = SZero
   \<and> lookup_st (snd mode_digest_solution (Inr MOne)) ''G'' = SPos
   \<and> lookup_st (snd mode_digest_solution (Inr MZero)) ''G''
       < lookup_st (snd mode_digest_solution (Inr MZero) \<squnion> snd mode_digest_solution (Inr MOne)) ''G''"
proof -
  have "SZero < SNonNeg" by eval
  thus ?thesis using digest_slot_MZero digest_slot_MOne digest_slot_join by simp
qed

subsection \<open>The digest run is a genuine post-solution\<close>

text \<open>
  The executable digest solution is a \<^const>\<open>part_post_solution\<close> of the digest equation system
  --- the executable end of the soundness chain, mirroring \<^theory_text>\<open>kgen_part_post_solution_st\<close>.
  Together with the generic transport \<^theory_text>\<open>part_post_solution_digest_st_to_abs_eff\<close> this maps
  to a post-solution of the abstract digest generator.
\<close>

lemma mode_digest_solve_c_some:
  "TD_side_always_join_Interp_solve_c mode_digest_eqs (cfg_exit mode_cfg, MZero) \<noteq> None"
  unfolding mode_digest_eqs_def mode_cfg_def mode_prep_def mode_dg_def by eval

lemma mode_digest_part_post_solution_st:
  "part_post_solution mode_digest_eqs (cfg_exit mode_cfg, MZero)
     (snd mode_digest_solution) (fst mode_digest_solution)"
  using TD_side_always_join_Interp.part_post_solution_of_solve_c[OF mode_digest_solve_c_some]
  unfolding mode_digest_solution_def by simp

subsection \<open>The digest run maps to the abstract digest generator\<close>

text \<open>
  The abstract counterpart of \<^const>\<open>mode_dg\<close> and \<^const>\<open>mode_prep\<close>, read on \<^typ>\<open>sign abs_state\<close>.
  Since \<^const>\<open>fun_of_st\<close> is \<^const>\<open>lookup_st\<close>, the digest compatibility and the call-state bridge
  are definitional.
\<close>

definition mode_dg_abs :: "sign abs_state \<Rightarrow> mode" where
  "mode_dg_abs s = mode_decode (s ''mode'')"

definition mode_prep_abs :: "pp \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state" where
  "mode_prep_abs cc s = s"

lemma mode_prep_commute: "fun_of_st (mode_prep cc s) = mode_prep_abs cc (fun_of_st s)"
  by (simp add: mode_prep_def mode_prep_abs_def)

lemma mode_dg_compat: "mode_dg_abs (fun_of_st s) = mode_dg s"
  by (simp add: mode_dg_abs_def mode_dg_def)

text \<open>
  The executable digest solution, transported through the generic unit-transfer bridge, is a
  post-solution of the \<^emph>\<open>abstract\<close> digest generator \<^const>\<open>side_cfg_T_eff_digest\<close> --- the exact
  bridge the context spine left open.  This closes the executable end of the digest-writer
  soundness chain: the run the solver computes is a certified post-solution of the abstract
  system the collecting theorem quantifies over.
\<close>
theorem mode_digest_abstracts:
  "part_post_solution
     (side_cfg_T_eff_digest mode_dg_abs
        (\<lambda>ctx cc ex. abs_switching_combine_digest mode_dg_abs mode_prep_abs cc ex ctx)
        mode_cfg sign_etf_unit (fun_of_st bot) (fun_of_st bot) (fun_of_st cinit_sign_st))
     (cfg_exit mode_cfg, MZero)
     (\<lambda>k. fun_of_st (snd mode_digest_solution k)) (fst mode_digest_solution)"
proof -
  have pp_st: "part_post_solution
       (side_cfg_T_eff_digest_st mode_dg
          (\<lambda>ctx cc ex. switching_combine_digest_st mode_dg mode_prep cc ex ctx)
          mode_cfg sign_etf_st bot bot cinit_sign_st) (cfg_exit mode_cfg, MZero)
       (snd mode_digest_solution) (fst mode_digest_solution)"
    using mode_digest_part_post_solution_st unfolding mode_digest_eqs_def by simp
  show ?thesis
    by (rule part_post_solution_digest_switching_st_to_abs_eff_unit_transfer
          [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
              sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute
              mode_prep_commute mode_dg_compat pp_st])
qed

subsection \<open>The same soundness under the per-origin update rule\<close>

text \<open>The abstract post-solution --- the fact the analyzer soundness consumes --- does not
  depend on \<^emph>\<open>which\<close> update rule produced the run.  \<^const>\<open>part_post_solution\<close> is
  update-rule-independent, the vendor proves it for every rule (\<open>partial_post_solution\<close> on the
  \<open>TD_side_upd_rule\<close> locale), and the abstract transport is rule-agnostic.  So the identical
  chain, with only the solver interpretation swapped, certifies the per-origin solve --- and
  here per-origin keeps the digest precise, so it is sound \<^emph>\<open>and\<close> sharp.\<close>

definition mode_digest_solution_po ::
  "(pp \<times> mode) set \<times> ((pp \<times> mode) + mode \<Rightarrow> sign st)" where
  "mode_digest_solution_po = TD_side_per_origin_Interp_solve mode_digest_eqs (cfg_exit mode_cfg, MZero)"

lemma mode_digest_solve_c_some_po:
  "TD_side_per_origin_Interp_solve_c mode_digest_eqs (cfg_exit mode_cfg, MZero) \<noteq> None"
  unfolding mode_digest_eqs_def mode_cfg_def mode_prep_def mode_dg_def by eval

lemma mode_digest_part_post_solution_st_po:
  "part_post_solution mode_digest_eqs (cfg_exit mode_cfg, MZero)
     (snd mode_digest_solution_po) (fst mode_digest_solution_po)"
  using TD_side_per_origin_Interp.part_post_solution_of_solve_c[OF mode_digest_solve_c_some_po]
  unfolding mode_digest_solution_po_def by simp

theorem mode_digest_abstracts_po:
  "part_post_solution
     (side_cfg_T_eff_digest mode_dg_abs
        (\<lambda>ctx cc ex. abs_switching_combine_digest mode_dg_abs mode_prep_abs cc ex ctx)
        mode_cfg sign_etf_unit (fun_of_st bot) (fun_of_st bot) (fun_of_st cinit_sign_st))
     (cfg_exit mode_cfg, MZero)
     (\<lambda>k. fun_of_st (snd mode_digest_solution_po k)) (fst mode_digest_solution_po)"
proof -
  have pp_st: "part_post_solution
       (side_cfg_T_eff_digest_st mode_dg
          (\<lambda>ctx cc ex. switching_combine_digest_st mode_dg mode_prep cc ex ctx)
          mode_cfg sign_etf_st bot bot cinit_sign_st) (cfg_exit mode_cfg, MZero)
       (snd mode_digest_solution_po) (fst mode_digest_solution_po)"
    using mode_digest_part_post_solution_st_po unfolding mode_digest_eqs_def by simp
  show ?thesis
    by (rule part_post_solution_digest_switching_st_to_abs_eff_unit_transfer
          [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
              sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute
              mode_prep_commute mode_dg_compat pp_st])
qed

subsection \<open>The same soundness under the warrowing (widening) update rule\<close>

text \<open>Identical chain, warrowing interpretation.  Here the digest globals over-approximate to
  \<^const>\<open>STop\<close> (Apinis warrowing widens globals), so the run is sound but \<^emph>\<open>not\<close> sharp --- the
  point being that soundness holds for the widening solver too, which is what lets the analyzer
  terminate on unbounded loops.  Precision and soundness are separate concerns.\<close>

definition mode_digest_solution_wa ::
  "(pp \<times> mode) set \<times> ((pp \<times> mode) + mode \<Rightarrow> sign st)" where
  "mode_digest_solution_wa = TD_side_warrowing_apinis_Interp_solve mode_digest_eqs (cfg_exit mode_cfg, MZero)"

lemma mode_digest_solve_c_some_wa:
  "TD_side_warrowing_apinis_Interp_solve_c mode_digest_eqs (cfg_exit mode_cfg, MZero) \<noteq> None"
  unfolding mode_digest_eqs_def mode_cfg_def mode_prep_def mode_dg_def by eval

lemma mode_digest_part_post_solution_st_wa:
  "part_post_solution mode_digest_eqs (cfg_exit mode_cfg, MZero)
     (snd mode_digest_solution_wa) (fst mode_digest_solution_wa)"
  using TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[OF mode_digest_solve_c_some_wa]
  unfolding mode_digest_solution_wa_def by simp

theorem mode_digest_abstracts_wa:
  "part_post_solution
     (side_cfg_T_eff_digest mode_dg_abs
        (\<lambda>ctx cc ex. abs_switching_combine_digest mode_dg_abs mode_prep_abs cc ex ctx)
        mode_cfg sign_etf_unit (fun_of_st bot) (fun_of_st bot) (fun_of_st cinit_sign_st))
     (cfg_exit mode_cfg, MZero)
     (\<lambda>k. fun_of_st (snd mode_digest_solution_wa k)) (fst mode_digest_solution_wa)"
proof -
  have pp_st: "part_post_solution
       (side_cfg_T_eff_digest_st mode_dg
          (\<lambda>ctx cc ex. switching_combine_digest_st mode_dg mode_prep cc ex ctx)
          mode_cfg sign_etf_st bot bot cinit_sign_st) (cfg_exit mode_cfg, MZero)
       (snd mode_digest_solution_wa) (fst mode_digest_solution_wa)"
    using mode_digest_part_post_solution_st_wa unfolding mode_digest_eqs_def by simp
  show ?thesis
    by (rule part_post_solution_digest_switching_st_to_abs_eff_unit_transfer
          [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
              sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute
              mode_prep_commute mode_dg_compat pp_st])
qed

subsection \<open>Update-rule-parametric soundness (summary)\<close>

text \<open>The analyzer's soundness precondition --- an abstract post-solution of the digest
  generator, the fact \<^theory_text>\<open>Analysis_Sound\<close> / \<^theory_text>\<open>Constraint_System_Sound\<close> consume --- is met by the
  solver output under \<^emph>\<open>every\<close> update rule tested.  The chain is the same for all three; only
  the solver interpretation changes.  So an analysis run may pick its update rule freely and
  stay sound: \<open>join\<close> / \<open>per_origin\<close> keep the digest sharp, and \<open>warrow\<close> (widening) stays sound
  while letting the solver terminate on unbounded loops.  This is the machine-checked backing
  for the \<open>run_menu\<close> columns and the roadmap in \<open>docs/UPDATE_RULE_FORMALIZATION_PLAN.md\<close>.\<close>

lemmas mode_digest_sound_all_update_rules =
  mode_digest_abstracts mode_digest_abstracts_po mode_digest_abstracts_wa

subsection \<open>Collecting soundness witness on the solver output\<close>

text \<open>
  The value-carried analogue of \<^theory_text>\<open>rd_collect_sound_witness\<close>, on the \<^emph>\<open>real solver
  output\<close> (not a hand-built sigma): the context-sliced collecting semantics is over-approximated
  by the projection read \<^const>\<open>mode_obs\<close>.  The mode-specific slot/combine obligations
  (\<open>LOCAL_POST\<close> / \<open>INR_BOT\<close> / \<open>INL_BOT\<close> / \<open>MODE_AGREE\<close>) are discharged from the solution; the
  generic collecting-layer premises (\<open>ENTRY\<close> / \<open>EDGE\<close> / digest laws / \<open>ENTER_MONO\<close>) are carried,
  exactly as in the reaching-definition witness.
\<close>

definition mode_digest_env :: "(nat \<times> mode) + mode \<Rightarrow> sign abs_state" where
  "mode_digest_env = (\<lambda>k. fun_of_st (snd mode_digest_solution k))"

text \<open>The \<^term>\<open>Inr\<close> partition slots are \<^const>\<open>restrict_global_st\<close>-shaped (publish discipline):
  the digest writer only side-effects global contributions to them.  Checkable per mode key.\<close>
lemma mode_slot_restrict_global:
  "snd mode_digest_solution (Inr g) = restrict_global_st (snd mode_digest_solution (Inr g))"
proof (cases g)
  case MZero show ?thesis unfolding MZero mode_digest_unfold by eval
next
  case MOne show ?thesis unfolding MOne mode_digest_unfold by eval
qed

lemma mode_INR_BOT: "inr_slot_locals_bot_ctx mode_digest_env"
  unfolding inr_slot_locals_bot_ctx_def mode_digest_env_def
proof (intro allI impI)
  fix g :: mode and x
  assume x: "\<not> is_global x"
  have "fun_of_st (snd mode_digest_solution (Inr g))
          = restrict_global (fun_of_st (snd mode_digest_solution (Inr g)))"
    by (metis mode_slot_restrict_global fun_of_st_restrict_global_st)
  from this[THEN fun_cong, of x] x
  show "fun_of_st (snd mode_digest_solution (Inr g)) x = bot"
    by (simp add: restrict_global_def)
qed

text \<open>\<open>LOCAL_POST\<close> on the solver output: across each call the caller's locals flow to the return
  node's locals.  The two combines and two modes are finite, so the local-slot order is
  \<open>eval\<close>-checkable via executable \<open>less_eq_st\<close>.\<close>
lemma mode_local_restrict_le:
  "restrict_local_st (snd mode_digest_solution (Inl (cl, ctx)))
     \<le> restrict_local_st (snd mode_digest_solution (Inl (v, ctx)))
   \<Longrightarrow> \<not> is_global x
   \<Longrightarrow> mode_digest_env (Inl (cl, ctx)) x \<le> mode_digest_env (Inl (v, ctx)) x"
  unfolding mode_digest_env_def
  by (metis le_st_iff lookup_restrict_local_st)

lemma mode_local_le_6_7:
  "restrict_local_st (snd mode_digest_solution (Inl (6, ctx)))
     \<le> restrict_local_st (snd mode_digest_solution (Inl (7, ctx)))"
proof (cases ctx)
  case MZero show ?thesis unfolding MZero mode_digest_unfold by eval
next
  case MOne show ?thesis unfolding MOne mode_digest_unfold by eval
qed

lemma mode_local_le_13_14:
  "restrict_local_st (snd mode_digest_solution (Inl (13, ctx)))
     \<le> restrict_local_st (snd mode_digest_solution (Inl (14, ctx)))"
proof (cases ctx)
  case MZero show ?thesis unfolding MZero mode_digest_unfold by eval
next
  case MOne show ?thesis unfolding MOne mode_digest_unfold by eval
qed

lemma mode_LOCAL_POST:
  assumes c: "(cl, ex, v) \<in> combines mode_cfg" and x: "\<not> is_global x"
  shows "mode_digest_env (Inl (cl, ctx)) x \<le> mode_digest_env (Inl (v, ctx)) x"
proof -
  have "combines mode_cfg = {(6, 1, 7), (13, 1, 14)}" unfolding mode_cfg_def by eval
  with c have "(cl, v) = (6, 7) \<or> (cl, v) = (13, 14)" by auto
  then show ?thesis
    using mode_local_le_6_7 mode_local_le_13_14 x by (auto simp: mode_local_restrict_le)
qed

text \<open>MODE_AGREE probe: the callee-exit \<open>''mode''\<close> local (reset on entry, decodes to \<^term>\<open>MZero\<close>)
  does \<^emph>\<open>not\<close> agree with the mode-1 return node value (\<^term>\<open>MOne\<close>).  So the kernel's \<open>MODE_AGREE\<close> ---
  local-value consistency across the call --- is false at the callee frame.\<close>
lemma mode_agree_probe_callee:
  "mode_decode (lookup_st (snd mode_digest_solution (Inl (1, MOne))) ''mode'') = MZero"
  unfolding mode_digest_unfold mode_decode_def by eval

lemma mode_agree_probe_return:
  "mode_decode (lookup_st (snd mode_digest_solution (Inl (14, MZero))) ''mode'') = MOne"
  unfolding mode_digest_unfold mode_decode_def by eval

theorem mode_collect_sound_witness:
  fixes S :: "store set"
    and dg :: "store list \<Rightarrow> mode" and entdg :: "store \<Rightarrow> mode"
    and rt :: "nat \<Rightarrow> mode \<Rightarrow> sign abs_state \<Rightarrow> mode"
  assumes INL_BOT: "inl_slot_globals_bot_ctx mode_digest_env"
    and MODE_AGREE: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines mode_cfg
        \<Longrightarrow> mode_decode (mode_digest_env (Inl (ex, rt cl ctx (mode_digest_env (Inl (cl, ctx))))) ''mode'')
              = mode_decode (mode_digest_env (Inl (v, ctx)) ''mode'')"
    and ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> mode_compatible (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>mode_obs mode_digest_env (cfg_entry mode_cfg, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry mode_cfg, EA_Enter, v) \<in> edges mode_cfg \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> mode_compatible (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>mode_obs mode_digest_env (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges mode_cfg \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>mode_obs mode_digest_env (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>mode_obs mode_digest_env (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> mode_compatible (dg (tr @ [s'])) ctx \<Longrightarrow> mode_compatible (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>mode_obs mode_digest_env (cl, ctx)\<rbrakk>
        \<Longrightarrow> mode_compatible (entdg s) (rt cl ctx (mode_digest_env (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg mode_compatible mode_cfg S v ctx \<le> \<lbrakk>mode_obs mode_digest_env (v, ctx)\<rbrakk>"
  using ENTRY PROC_ENTRY EDGE mode_LOCAL_POST mode_INR_BOT INL_BOT MODE_AGREE
        DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO
  by (rule mode_collect_ctx_sound_bot_reduced)

subsection \<open>Status: what is proved, and the machine-checked soundness boundary\<close>

text \<open>
  \<^bold>\<open>Proved on the real solver output.\<close>  The digest writer \<^const>\<open>side_cfg_T_eff_digest_st\<close> keys each
  intra global write by \<open>dg s\<close>, a projection of the write-point state, and the compiled program
  separates the modes (\<open>digest_separates_the_modes\<close>).  The run is a genuine post-solution
  (\<^theory_text>\<open>mode_digest_part_post_solution_st\<close>) that transports to the abstract digest generator
  (\<^theory_text>\<open>mode_digest_abstracts\<close>).  Of the reader's collecting-soundness obligations, the slot
  and local-flow invariants are discharged directly against the solved environment:
  \<^theory_text>\<open>mode_INR_BOT\<close> (partition slots bot on locals, via \<^const>\<open>restrict_global_st\<close>-shape) and
  \<^theory_text>\<open>mode_LOCAL_POST\<close> (caller locals flow to the return).  The read/write pair and the kernel
  \<^locale>\<open>digest_global_read\<close> are untouched.

  \<^bold>\<open>The soundness boundary (machine-checked).\<close>  Full soundness of the projection read
  \<^const>\<open>mode_obs\<close> at \<^emph>\<open>every\<close> point is \<^emph>\<open>not\<close> attainable, and this is a proven fact, not an open
  gap: the kernel's \<open>MODE_AGREE\<close> --- the \<open>''mode''\<close> local read at a callee exit under the routed
  context must equal the read at the return --- is \<^emph>\<open>false\<close> here.  \<^theory_text>\<open>mode_agree_probe_callee\<close>
  and \<^theory_text>\<open>mode_agree_probe_return\<close> compute (\<open>by eval\<close>) that the callee exit \<^term>\<open>(1, MOne)\<close> decodes
  to \<^term>\<open>MZero\<close> (its \<open>''mode''\<close> local was reset by \<^const>\<open>enter_state\<close>) while the mode-1 return \<^term>\<open>(14, MZero)\<close>
  decodes to \<^term>\<open>MOne\<close>.  So at a callee-interior point \<^const>\<open>mode_obs\<close> re-projects the reset local
  and reads the \<^emph>\<open>wrong\<close> partition; the correct callee read must ride the \<^emph>\<open>context\<close>
  (\<^const>\<open>side_env_cmp\<close>), which is exactly why the certified bridge \<^theory_text>\<open>mode_obs_eq_side_env_cmp\<close>
  only holds where \<open>''mode''\<close> is set (the alignment premise).  This is the frame-locality of the
  digest, now a machine-checked disproof of the single-reader condition rather than a caveat.

  \<^bold>\<open>Consequence.\<close>  \<^theory_text>\<open>mode_collect_sound_witness\<close> is the honest conditional theorem
  (\<open>cfg_collect_ctx \<le> mode_obs\<close> given \<open>INL_BOT\<close> / \<open>MODE_AGREE\<close> / the generic collecting premises),
  at a premise-carrying standard --- but its \<open>MODE_AGREE\<close>
  premise is unsatisfiable for this run, so it certifies the frames where \<open>''mode''\<close> is set, not the callee
  frames.  Genuinely open (both shared with every instance, not mode-specific): \<open>INL_BOT\<close> for the
  solver output (a solver-default invariant over the infinite \<^term>\<open>Inl\<close> keys) and the
  generic \<open>ENTRY\<close> / \<open>EDGE\<close> generator-to-collecting bounds.
\<close>

subsection \<open>Annotated CFG of the digest run\<close>

text \<open>
  The solved digest environment rendered as a CFG with \<^emph>\<open>three\<close> clusters --- one per
  \<^emph>\<open>activation\<close>, not per mode: \<open>main\<close> (once), \<open>f @ MZero\<close>, and \<open>f @ MOne\<close>.  Each node is
  labelled with its solved local state, each cluster with its own global partition box.  The two
  calls are routed by the digest \<^emph>\<open>computed from the solution\<close> (\<open>call_ctx\<close>): the first (mode
  0) enters \<open>f @ MZero\<close>, the second (mode 1) enters \<open>f @ MOne\<close>, and both return into \<open>main\<close>.
\<close>

text \<open>\<open>f\<close> is compiled first, so its body is \<open>pp0\<close>/\<open>pp1\<close>; \<open>main\<close> is the rest.\<close>
definition f_pps :: "pp list" where "f_pps = [0, 1]"

definition call_ctx :: "pp \<Rightarrow> mode" where
  "call_ctx cc = mode_dg (snd mode_digest_solution (Inl (cc, MZero)))"

text \<open>The render context distinguishes the three activations (the analysis context stays
  \<^typ>\<open>mode\<close>; this is only for clustering).\<close>
datatype rctx = RMain | RfMZero | RfMOne

definition rctx_mode :: "rctx \<Rightarrow> mode" where
  "rctx_mode r = (case r of RMain \<Rightarrow> MZero | RfMZero \<Rightarrow> MZero | RfMOne \<Rightarrow> MOne)"

definition rctx_key :: "rctx \<Rightarrow> string" where
  "rctx_key r = (case r of RMain \<Rightarrow> ''main'' | RfMZero \<Rightarrow> ''fMZero'' | RfMOne \<Rightarrow> ''fMOne'')"

definition rctx_label :: "rctx \<Rightarrow> string" where
  "rctx_label r = (case r of RMain \<Rightarrow> ''main'' | RfMZero \<Rightarrow> ''f @ MZero'' | RfMOne \<Rightarrow> ''f @ MOne'')"

definition f_rctx_of :: "pp \<Rightarrow> rctx" where
  "f_rctx_of cc = (if call_ctx cc = MZero then RfMZero else RfMOne)"

text \<open>Callee reads are shown \<^emph>\<open>context-served\<close>: at an \<open>f\<close> node the read \<open>z := G\<close> is displayed as
  the certified context read \<^const>\<open>side_env_cmp\<close> --- the value of the context's own partition
  \<^term>\<open>Inr (rctx_mode r)\<close> --- not the executable reset-local slot.  \<open>f @ MOne\<close> therefore shows
  \<open>z = Positive\<close> (its \<open>MOne\<close> partition), \<open>f @ MZero\<close> shows \<open>z = Zero\<close>.  The executable reset-local
  read would instead default both to \<^const>\<open>MZero\<close> (the frame-locality caveat): the callee's local
  \<open>''mode''\<close> is wiped on entry, so its own re-projection cannot recover the caller's mode --- the
  digest rides the context, which is exactly what the context-served read displays.\<close>
definition rmode_node_label :: "pp \<times> rctx \<Rightarrow> string" where
  "rmode_node_label pk =
     (case pk of (p, r) \<Rightarrow>
        let s = snd mode_digest_solution (Inl (p, rctx_mode r));
            zval = (case r of RMain \<Rightarrow> lookup_st s ''z''
                    | _ \<Rightarrow> (if lookup_st s ''z'' = \<bottom> then \<bottom>
                            else lookup_st (snd mode_digest_solution (Inr (rctx_mode r))) ''G'')) in
        ''pp'' @ string_of_nat p @ gv_nl @
        ''mode='' @ show_val (lookup_st s ''mode'') @ ''  x='' @ show_val (lookup_st s ''x'') @
        ''  y='' @ show_val (lookup_st s ''y'') @ ''  z='' @ show_val zval)"

definition rmode_globals :: "rctx \<Rightarrow> string" where
  "rmode_globals r =
     (case r of
        RMain \<Rightarrow> ''G@MZero='' @ show_val (lookup_st (snd mode_digest_solution (Inr MZero)) ''G'')
                 @ ''  G@MOne='' @ show_val (lookup_st (snd mode_digest_solution (Inr MOne)) ''G'')
      | _ \<Rightarrow> ''G = '' @ show_val (lookup_st (snd mode_digest_solution (Inr (rctx_mode r))) ''G''))"

definition rmode_nodes :: "(pp \<times> rctx) list" where
  "rmode_nodes =
     map (\<lambda>p. (p, RMain)) (filter (\<lambda>p. p \<notin> set f_pps) (sorted_list_of_set (nodes mode_cfg)))
   @ map (\<lambda>p. (p, RfMZero)) f_pps
   @ map (\<lambda>p. (p, RfMOne)) f_pps"

definition rmode_intra :: "((pp \<times> rctx) \<times> edge_action \<times> (pp \<times> rctx)) list" where
  "rmode_intra =
     [((u, RMain), a, (v, RMain)). (u, a, v) \<leftarrow> cfg_edges_list mode_cfg,
        a \<noteq> EA_Enter, u \<notin> set f_pps, v \<notin> set f_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list mode_cfg,
        u \<in> set f_pps, v \<in> set f_pps, r \<leftarrow> [RfMZero, RfMOne]]"

definition rmode_calls :: "((pp \<times> rctx) \<times> (pp \<times> rctx)) list" where
  "rmode_calls =
     [((u, RMain), (v, f_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list mode_cfg, a = EA_Enter]"

definition rmode_returns :: "((pp \<times> rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> rctx)) list" where
  "rmode_returns =
     [((ex, f_rctx_of cc), (cc, ex, ret), (ret, RMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list mode_cfg]"

definition mode_digest_dot :: string where
  "mode_digest_dot =
     ctx_debug_graphviz_with_globals
       rctx_key rctx_label rmode_globals rmode_node_label (\<lambda>_. ''shape=box'')
       [RMain, RfMZero, RfMOne]
       rmode_nodes rmode_intra rmode_calls rmode_returns"

definition mode_digest_dot_lit :: String.literal where
  "mode_digest_dot_lit = String.implode mode_digest_dot"

ML_val \<open>writeln (@{code mode_digest_dot_lit})\<close>

end
