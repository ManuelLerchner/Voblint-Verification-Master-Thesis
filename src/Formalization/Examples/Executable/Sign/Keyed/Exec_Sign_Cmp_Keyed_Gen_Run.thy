theory Exec_Sign_Cmp_Keyed_Gen_Run
  imports Voblint_Analysis.Sign_Exec_Sound Voblint_Analysis.Exec_Cmp_Bridge Voblint_Analysis.Solver_Side_RG
begin

section \<open>Executable keyed-global generator run (sign)\<close>

text \<open>
  The executable \<open>_st\<close> sibling of \<^const>\<open>side_cfg_T_eff_cmp\<close>: the same generator over
  the code-generating finite-map state \<^typ>\<open>'a st\<close>.  It mirrors
  \<^const>\<open>side_cfg_T_eff_ctx_st\<close> but keys each context's global writes (and, through the
  keyed combine, its global reads) to the slot \<open>gkey c\<close> via \<^const>\<open>map_gtree\<close>.  Fed to
  the vendored \<^const>\<open>TD_side_always_join_Interp_solve\<close> it runs the real side solver
  over keyed global slots.
\<close>

subsection \<open>A two-call program with a global-derived context\<close>

text \<open>
  \<open>f\<close> transforms the global; \<open>main\<close> calls it under two different global inputs.
  The call context is the surviving global state (\<^const>\<open>restrict_global_st\<close>) --- the
  sound context channel --- so the two activations are keyed apart.
\<close>

definition kgen_prog :: imp_prog where
  "kgen_prog = \<lbrakk>
     int G;

     void f() {
       G := G + G
     }
     void main() {
       G := 0;
       f();
       G := 1;
       f()
     }
   \<rbrakk>"

definition kgen_cfg :: cfg where
  "kgen_cfg = compile_prog (prog_table kgen_prog) (prog_procs kgen_prog) (prog_main kgen_prog)"

text \<open>Context = the surviving global state; the key is the context itself (\<open>gkey = id\<close>).\<close>
definition kgen_ec :: "sign st \<Rightarrow> sign st \<Rightarrow> sign st" where
  "kgen_ec ctx sc = restrict_global_st sc"

text \<open>
  Keyed seeding combine.  Call-enter edges are filtered from the intra fold, so the
  callee-entry global slot is fed here: the combine emits @{term \<open>Side callee\<close>} with
  the caller's globals (the seed), keying the callee's activation apart; the return
  contribution goes to the caller context slot.  This is the combine handling that
  subsumes the excluded enter flow.
\<close>

definition kgen_combine_st ::
  "pp \<Rightarrow> pp \<Rightarrow> sign st \<Rightarrow> (pp \<times> sign st, sign st, sign st) strategy_tree"
where
  "kgen_combine_st cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let caller = sc \<squnion> g;
           callee = kgen_ec ctx caller in
       Side callee (restrict_global_st caller)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st caller \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

definition kgen_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_eqs = side_cfg_T_eff_cmp_st id
                (\<lambda>c cc ex. kgen_combine_st cc ex c)
                kgen_cfg sign_etf_st bot bot cinit_sign_st"

definition kgen_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_solution = TD_side_always_join_Interp_solve kgen_eqs (cfg_exit kgen_cfg, bot)"

subsection \<open>The generator code-generates and runs\<close>

text \<open>The keyed generator solves the program: the solved unknown set is non-empty.\<close>
lemma kgen_runs: "fst kgen_solution \<noteq> {}"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def by eval

subsection \<open>The generated solver result is a post-solution\<close>

lemma kgen_solve_c_some:
  "TD_side_always_join_Interp_solve_c kgen_eqs (cfg_exit kgen_cfg, bot) \<noteq> None"
  unfolding kgen_eqs_def kgen_cfg_def kgen_ec_def by eval

lemma kgen_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(sign st) TYPE(sign st)
     kgen_eqs (cfg_exit kgen_cfg, bot)"
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using kgen_solve_c_some by simp

lemma kgen_part_post_solution_st:
  "part_post_solution kgen_eqs (cfg_exit kgen_cfg, bot)
     (snd kgen_solution) (fst kgen_solution)"
  using TD_side_always_join_Interp.partial_post_solution
      [OF kgen_solve_dom, of "fst kgen_solution" "snd kgen_solution"]
  unfolding kgen_solution_def by simp

lemma side_rg_kgen_combine_st: "side_rg (kgen_combine_st cc ex ctx)"
  unfolding kgen_combine_st_def by (simp add: Let_def)

lemma kgen_side_rg_eqs:
  "side_rg (kgen_eqs z)"
  unfolding kgen_eqs_def
  apply (rule side_rg_side_cfg_T_eff_cmp_st_unit)
   apply (use sign_etf_st_exists_unit in blast)
  apply (rule side_rg_kgen_combine_st)
  done

text \<open>
  The solver post-solution above is executable and concrete.  The direct final
  soundness instantiation is deliberately separated below: the generic keyed read
  theorem requires a finite key type, while this run uses \<typ>\<open>sign st\<close> as the
  context/key.  The reusable bridge point is therefore the post-solution fact plus
  the finite-key theorem schema at the end of this file.
\<close>


subsection \<open>The generated solver materialises keyed global slots\<close>

text \<open>
  The compiled procedure example exercises the real CFG generator, the keyed \<open>_st\<close>
  equation generator, and the vendored side solver.  Call-enter edges are filtered
  from the intra fold and the callee-entry globals are seeded by @{const kgen_combine_st}.
  The context @{const kgen_ec} keys on the surviving global state, which the seed
  recovers, so the pure \<open>G = SZero\<close> activation is analysed precisely (\<open>G = SZero\<close>).
  The second activation's context is derived from the flow-insensitive global
  (\<open>restrict_global_st\<close> of the joined caller state), so it merges to \<open>SNonNeg\<close> --- the
  sharper per-call-site separation is what the finite-context sibling
  \<open>Example_Finite_Sign_Context_Analysis\<close> demonstrates.
\<close>

definition kgen_ctx_zero :: "sign st" where
  "kgen_ctx_zero = Abs_st (SBot, SZero, [])"

definition kgen_ctx_merged :: "sign st" where
  "kgen_ctx_merged = Abs_st (SBot, SZero, [(''G'', SNonNeg)])"

lemma kgen_slot_zero_precise:
  "lookup_st (snd kgen_solution (Inr kgen_ctx_zero)) ''G'' = SZero"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def kgen_ctx_zero_def
  by eval

lemma kgen_slot_merged:
  "lookup_st (snd kgen_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def kgen_ctx_merged_def
  by eval

lemma kgen_join_materialised_slots:
  "lookup_st (snd kgen_solution (Inr kgen_ctx_zero) \<squnion> snd kgen_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def
    kgen_ctx_zero_def kgen_ctx_merged_def
  by eval

theorem kgen_generated_solver_result:
  "fst kgen_solution \<noteq> {}
   \<and> lookup_st (snd kgen_solution (Inr kgen_ctx_zero)) ''G'' = SZero
   \<and> lookup_st (snd kgen_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg
   \<and> lookup_st (snd kgen_solution (Inr kgen_ctx_zero) \<squnion> snd kgen_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def
    kgen_ctx_zero_def kgen_ctx_merged_def
  by eval

subsection \<open>Soundness-facing connection to the generic keyed theorem\<close>

text \<open>
  The abstract theorem below is the direct soundness-facing counterpart of the
  executable generator run.  It applies the generic keyed-global theorem to the
  same compiled CFG and conservative keyed generator shape.  Bridging the concrete
  \<open>kgen_solution\<close> to this abstract post-fixpoint is the remaining executable
  certification step for this value-dependent context run.
\<close>

definition kgen_abs_eqs :: "(pp \<times> 'ctx, 'ctx, sign abs_state) eqsT" where
  "kgen_abs_eqs =
     side_cfg_T_eff_cmp id
       (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_unit cc ex)))
       kgen_cfg sign_etf_unit fresh_frame_sign bot (fun_of_st cinit_sign_st)"

definition kgen_retain_abs_eqs :: "(pp \<times> 'ctx, 'ctx, sign abs_state) eqsT" where
  "kgen_retain_abs_eqs =
     side_cfg_T_eff_cmp id
       (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_retain cc ex)))
       kgen_cfg sign_etf_retain fresh_frame_sign bot (fun_of_st cinit_sign_st)"

theorem kgen_keyed_generator_sound_if_post_fixpoint:
  fixes sigma :: "pp \<times> 'ctx + 'ctx::finite \<Rightarrow> sign abs_state"
  assumes pp: "part_post_solution kgen_abs_eqs x sigma vars"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes inl: "inl_slot_globals_bot_ctx sigma"
  assumes cover_edge: "\<And>u a v. (u, a, v) \<in> edges kgen_cfg \<Longrightarrow> (v, ctx) \<in> vars"
  assumes cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines kgen_cfg \<Longrightarrow> (ret, ctx) \<in> vars"
  assumes cover_entry: "(cfg_entry kgen_cfg, ctx) \<in> vars"
  assumes S_sound: "S \<le> \<lbrakk>fun_of_st cinit_sign_st\<rbrakk>"
  shows "cfg_collect kgen_cfg S v0 \<le> \<lbrakk>side_env_cmp (=) sigma (v0, ctx)\<rbrakk>"
proof -
  have pp': "part_post_solution
      (side_cfg_T_eff_cmp id
        (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_unit cc ex)))
        kgen_cfg sign_etf_unit fresh_frame_sign bot (fun_of_st cinit_sign_st))
      x sigma vars"
    using pp unfolding kgen_abs_eqs_def by simp
  have finE: "finite (edges kgen_cfg)"
    unfolding kgen_cfg_def using compile_prog_finite by simp
  have finC: "finite (combines kgen_cfg)"
    unfolding kgen_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule side_cfg_T_eff_cmp_collect_sound_eq
          [OF sign_sound_etf_unit_framed inr inl S_sound pp' finE finC
              cover_edge cover_comb cover_entry])
qed

theorem kgen_retain_keyed_generator_sound_if_post_fixpoint:
  fixes sigma :: "pp \<times> 'ctx + 'ctx::finite \<Rightarrow> sign abs_state"
  assumes pp: "part_post_solution kgen_retain_abs_eqs x sigma vars"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes inl: "inl_glob_le_keyed_ctx id sigma"
  assumes cover_edge: "\<And>u a v. (u, a, v) \<in> edges kgen_cfg \<Longrightarrow> (v, ctx) \<in> vars"
  assumes cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines kgen_cfg \<Longrightarrow> (ret, ctx) \<in> vars"
  assumes cover_entry: "(cfg_entry kgen_cfg, ctx) \<in> vars"
  assumes S_sound: "S \<le> \<lbrakk>fun_of_st cinit_sign_st\<rbrakk>"
  shows "cfg_collect kgen_cfg S v0 \<le> \<lbrakk>side_env_cmp (=) sigma (v0, ctx)\<rbrakk>"
proof -
  have pp': "part_post_solution
      (side_cfg_T_eff_cmp id
        (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_retain cc ex)))
        kgen_cfg sign_etf_retain fresh_frame_sign bot (fun_of_st cinit_sign_st))
      x sigma vars"
    using pp unfolding kgen_retain_abs_eqs_def by simp
  have finE: "finite (edges kgen_cfg)"
    unfolding kgen_cfg_def using compile_prog_finite by simp
  have finC: "finite (combines kgen_cfg)"
    unfolding kgen_cfg_def using compile_prog_finite by simp
  have comb: "switching_combine_sound_le id
      (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_retain cc ex)))
      kgen_cfg sign_etf_retain fresh_frame_sign bot (fun_of_st cinit_sign_st)"
    using fixed_combine_satisfies_switching_combine_sound_le[OF finC, of id sign_etf_retain fresh_frame_sign bot "fun_of_st cinit_sign_st"]
    by simp
  have single: "{k. (=) ctx k} = {id ctx}"
    by simp
  show ?thesis
    by (rule side_cfg_T_eff_cmp_collect_sound_gen_le
          [where gkey=id
             and cmb="\<lambda>c cc ex. map_gtree (\<lambda>_. c)
                (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_retain cc ex))"
             and g=kgen_cfg
             and etf=sign_etf_retain
             and fresh_frame=fresh_frame_sign
             and gcmp="(=)"
             and ctx=ctx,
           OF sign_sound_etf_retain_framed_le comb single inr inl S_sound pp' finE finC
              cover_edge cover_comb cover_entry])
qed

text \<open>
  This witness \<^emph>\<open>reduces\<close> the slot-relating premise \<^const>\<open>inl_glob_le_keyed_ctx\<close> of
  @{thm [source] kgen_retain_keyed_generator_sound_if_post_fixpoint} to solver
  \<^emph>\<open>exactness\<close>; it is a reframing, not a discharge.  Via @{thm [source]
  inl_glob_le_keyed_ctx_full} it derives the invariant from an exact
  \<^const>\<open>part_solution\<close> (plus the \<open>\<bottom>\<close>-init default outside the solved set): an exact
  retain fixpoint publishes each edge's written global to the keyed slot, so the local
  slot's globals are dominated by it.

  \<^const>\<open>part_solution\<close> is \<^emph>\<open>not\<close> what the vendored side solver provides.  The
  always-join solver interprets locale \<open>TD_side_upd_rule\<close>, which proves only
  \<^const>\<open>part_post_solution\<close> (overapproximation, \<open>eq \<le> \<sigma>(Inl u)\<close>) and applies local
  warrowing \<open>\<nabla>\<Delta>\<close> at widening points, so an exact \<^const>\<open>part_solution\<close> is false in
  general.  The exact-preservation lemmas (\<open>destab_upd_*_preserves_part_solution\<close>) live
  in the un-interpreted locale \<open>TD_side\<close>, which the always-join solver does not
  interpret.  Exactness holds only operationally on warrowing-free (acyclic) runs; it
  is certifiable per run by a decidable reverse-inequality \<open>eval\<close> check that upgrades
  \<^const>\<open>part_post_solution\<close> to \<^const>\<open>part_solution\<close> (see \<open>Exec_Sign_Cmp_Keyed_Retain_Run\<close>).
  So the reduction moves the obligation from a bespoke slot invariant to standard
  solver exactness; it does not eliminate it.
\<close>
theorem kgen_retain_keyed_generator_sound_if_exact_fixpoint:
  fixes sigma :: "pp \<times> 'ctx + 'ctx::finite \<Rightarrow> sign abs_state"
  assumes ps: "part_solution kgen_retain_abs_eqs x sigma vars"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes outside: "\<And>v c. (v, c) \<notin> vars \<Longrightarrow> sigma (Inl (v, c)) = \<bottom>"
  assumes cover_edge: "\<And>u a v. (u, a, v) \<in> edges kgen_cfg \<Longrightarrow> (v, ctx) \<in> vars"
  assumes cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines kgen_cfg \<Longrightarrow> (ret, ctx) \<in> vars"
  assumes cover_entry: "(cfg_entry kgen_cfg, ctx) \<in> vars"
  assumes S_sound: "S \<le> \<lbrakk>fun_of_st cinit_sign_st\<rbrakk>"
  shows "cfg_collect kgen_cfg S v0 \<le> \<lbrakk>side_env_cmp (=) sigma (v0, ctx)\<rbrakk>"
proof -
  have inl: "inl_glob_le_keyed_ctx id sigma"
  proof (rule inl_glob_le_keyed_ctx_full)
    show "\<And>a u. apply_etf sign_etf_retain a u = retain_edge_tree (apply_tf sign_tf a) u"
      by (rule sign_etf_retain_edge_tree)
    show "\<And>cc ex. etf_combine sign_etf_retain cc ex = unit_combine_tree cc ex"
      by (rule sign_etf_retain_combine_tree)
    show "restrict_global bot = \<bottom>" by (rule restrict_global_bot)
    show "restrict_global fresh_frame_sign = \<bottom>"
      by (simp add: restrict_global_def fresh_frame_sign_def fun_eq_iff)
    show "part_solution (side_cfg_T_eff_cmp id
             (\<lambda>c cc ex. map_gtree (\<lambda>_. id c)
                (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_retain cc ex)))
             kgen_cfg sign_etf_retain fresh_frame_sign bot (fun_of_st cinit_sign_st))
           x sigma vars"
      using ps unfolding kgen_retain_abs_eqs_def by simp
    show "\<And>v c. (v, c) \<notin> vars \<Longrightarrow> sigma (Inl (v, c)) = \<bottom>" by (rule outside)
  qed
  have pp: "part_post_solution kgen_retain_abs_eqs x sigma vars"
    using ps by (auto intro: eq_imp_le)
  show ?thesis
    by (rule kgen_retain_keyed_generator_sound_if_post_fixpoint
          [OF pp inr inl cover_edge cover_comb cover_entry S_sound])
qed

end

