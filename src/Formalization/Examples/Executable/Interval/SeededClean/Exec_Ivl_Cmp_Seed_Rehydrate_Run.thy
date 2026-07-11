theory Exec_Ivl_Cmp_Seed_Rehydrate_Run
  imports Exec_Ivl_Cmp_Seed_Clean_Run Voblint_Analysis.Analysis_GraphViz
begin

section \<open>Return rehydration: caller continuation on the seeded-clean (R_read) spine\<close>

text \<open>
  The seeded-clean spine (\<^theory>\<open>Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run\<close>) is
  Goblint-faithful on the \<^emph>\<open>enter\<close> side (the seed copies caller globals into the
  callee-entry local) and reads only the local \<open>D\<close> in the transfer.  Its combine,
  \<^const>\<open>ivl_combine_rread\<close>, returns \<^const>\<open>restrict_local_st\<close> of the merged result:
  it \<^emph>\<open>strips\<close> globals from the caller-local state on return.  A caller that reads a
  global back after the call --- \<open>g := G; h := GH\<close> --- therefore observes \<open>bot\<close>.

  This theory closes that gap with \<^emph>\<open>return rehydration\<close>, Goblint's \<open>Spec.combine\<close>:
  the caller continuation is reconstructed as
  \<^term>\<open>combine_abs_st sc se :: ivl st\<close> --- \<^emph>\<open>locals from the caller\<close> \<open>sc\<close>,
  \<^emph>\<open>globals from the callee exit\<close> \<open>se\<close> --- exactly the abstract mirror of the
  concrete \<^term>\<open>combine_states s t\<close> (\<open><s|t>\<close>).  This is not a \<open>local \<squnion> global\<close> read:
  the transfer is unchanged (still the clean, local-only \<^const>\<open>ivl_etf_clean_st\<close>),
  the callee context is still selected from the caller local (\<^const>\<open>ivl_ec\<close>), and
  the globals folded in are the \<^emph>\<open>callee's returned\<close> globals, not a flow-insensitive
  published slot.

  \<^bold>\<open>Goblint correspondence.\<close>  For a non-relational (per-variable) domain,
  Goblint's \<open>combine_env\<close> / \<open>combine_assign\<close> reconstruct the caller \<open>D.t\<close> by taking
  the caller's locals and the callee's globals (the callee \<open>D.t\<close> carries the updated
  globals).  \<^const>\<open>combine_abs_st\<close> is that reconstruction; it is what the retain and
  unit spines already use structurally.  The only change from the strip combine is
  \<^emph>\<open>not\<close> discarding the reconstructed globals via \<^const>\<open>restrict_local_st\<close>.
\<close>

subsection \<open>The rehydrating combine\<close>

text \<open>Selects the callee context from the caller local (\<^const>\<open>ivl_ec\<close>, R_read),
  seeds the caller globals to the callee entry, and on return rebuilds the caller
  continuation as \<^term>\<open>combine_abs_st sc se\<close> --- keeping the callee's globals in the
  returned local.\<close>

definition ivl_combine_rehydrate ::
  "pp \<Rightarrow> pp \<Rightarrow> ivl st \<Rightarrow> (pp \<times> ivl st, ivl st, ivl st) strategy_tree"
where
  "ivl_combine_rehydrate cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc.
       let callee = ivl_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           Side ctx (restrict_global_st se)
             (Answer (combine_abs_st sc se)))))"

text \<open>The R_read architecture is preserved: the callee context is a function of the
  caller \<^emph>\<open>local\<close> alone (no published-global read), identical to the clean combine's
  selector.\<close>

lemma ivl_combine_rehydrate_context_is_local:
  "ivl_ec ctx sc = restrict_global_st sc"
  by (simp add: ivl_ec_def)

text \<open>The returned caller continuation is the structural combine \<^const>\<open>combine_abs_st\<close>
  --- locals from the caller \<open>sc\<close>, globals from the callee exit \<open>se\<close> --- \<^emph>\<open>not\<close> a
  \<open>local \<squnion> global\<close> read of a published slot.\<close>

lemma ivl_combine_rehydrate_answer:
  "ivl_combine_rehydrate cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc.
       Side (restrict_global_st sc) (restrict_global_st sc)
         (QueryL (ex, restrict_global_st sc) (\<lambda>se.
           Side ctx (restrict_global_st se)
             (Answer (combine_abs_st sc se)))))"
  by (simp add: ivl_combine_rehydrate_def ivl_ec_def Let_def)

text \<open>The reassembled return value: \<^const>\<open>traverse_rhs\<close> collapses the
  \<open>QueryL / Side / Answer\<close> skeleton to the \<^const>\<open>combine_abs_st\<close> continuation ---
  caller locals from \<open>sg (Inl (cc, ctx))\<close>, callee globals from the callee-exit slot
  at the R_read-selected context \<open>restrict_global_st (sg (Inl (cc, ctx)))\<close>.  This is
  the combine tree's \<^const>\<open>combine_abs_st\<close> shape that the generic combine bound
  \<open>Exec_Cmp_Bridge.seeded_clean_comb_bound\<close> dominates by the return slot.\<close>

lemma traverse_ivl_combine_rehydrate:
  "traverse_rhs (ivl_combine_rehydrate cc ex ctx) sg
     = combine_abs_st (sg (Inl (cc, ctx)))
         (sg (Inl (ex, restrict_global_st (sg (Inl (cc, ctx))))))"
  by (simp add: ivl_combine_rehydrate_def ivl_ec_def Let_def)

text \<open>Abstract counterpart with executable context keys.  The callee key is obtained from
  the abstract caller value only through the canonical executable representative of its
  global projection; on values transported by \<open>fun_of_st\<close> this is exactly the executable
  \<open>restrict_global_st\<close> key.\<close>

definition ivl_abs_route_st :: "ivl abs_state \<Rightarrow> ivl st" where
  "ivl_abs_route_st sc = st_of_abs (restrict_global sc)"

lemma ivl_abs_route_st_fun_of_st [simp]:
  "ivl_abs_route_st (fun_of_st sc) = restrict_global_st sc"
  by (metis fun_of_st_restrict_global_st ivl_abs_route_st_def
      st_of_abs_fun_of_st)

definition ivl_combine_rehydrate_abs ::
  "pp \<Rightarrow> pp \<Rightarrow> ivl st \<Rightarrow> (pp \<times> ivl st, ivl st, ivl abs_state) strategy_tree"
where
  "ivl_combine_rehydrate_abs cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc.
       let callee = ivl_abs_route_st sc in
       Side callee (restrict_global sc)
         (QueryL (ex, callee) (\<lambda>se.
           Side ctx (restrict_global se)
             (Answer (combine_abs sc se)))))"

lemma traverse_ivl_combine_rehydrate_abs:
  "traverse_rhs (ivl_combine_rehydrate_abs cc ex ctx) sg
     = combine_abs (sg (Inl (cc, ctx)))
         (sg (Inl (ex, ivl_abs_route_st (sg (Inl (cc, ctx))))))"
  by (simp add: ivl_combine_rehydrate_abs_def Let_def)

lemma traverse_ivl_combine_rehydrate_fun_of_st:
  fixes sigma_st :: "pp \<times> ivl st + ivl st \<Rightarrow> ivl st"
  shows "fun_of_st (traverse_rhs (ivl_combine_rehydrate cc ex ctx) sigma_st)
     = traverse_rhs (ivl_combine_rehydrate_abs cc ex ctx)
         (\<lambda>k. fun_of_st (sigma_st k))"
  by (simp add: ivl_combine_rehydrate_def ivl_combine_rehydrate_abs_def ivl_ec_def Let_def)

lemma sides_ivl_combine_rehydrate_fun_of_st:
  fixes sigma_st :: "pp \<times> ivl st + ivl st \<Rightarrow> ivl st"
  shows "fun_of_st (sides_of_rhs (ivl_combine_rehydrate cc ex ctx) sigma_st k)
     = sides_of_rhs (ivl_combine_rehydrate_abs cc ex ctx)
         (\<lambda>k. fun_of_st (sigma_st k)) k"
  by (cases k) (simp_all add: ivl_combine_rehydrate_def ivl_combine_rehydrate_abs_def ivl_ec_def Let_def bot_fun_def fun_eq_iff)

lemma dep_ivl_combine_rehydrate_fun_of_st:
  fixes sigma_st :: "pp \<times> ivl st + ivl st \<Rightarrow> ivl st"
  shows "dep_aux sigma_st (ivl_combine_rehydrate cc ex ctx)
     = dep_aux (\<lambda>k. fun_of_st (sigma_st k)) (ivl_combine_rehydrate_abs cc ex ctx)"
  by (simp add: ivl_combine_rehydrate_def ivl_combine_rehydrate_abs_def ivl_ec_def Let_def)

lemma traverse_ivl_etf_clean_st_fun_of_st:
  fixes sigma_st :: "pp + unit => ivl st"
  shows "fun_of_st (traverse_rhs (apply_etf_st ivl_etf_clean_st a u) sigma_st)
     = traverse_rhs (apply_etf (clean_etf_of_transfer ivl_tf) a u)
         (\<lambda>k. fun_of_st (sigma_st k))"
  by (cases a)
     (simp_all add: ivl_etf_clean_st_def clean_edge_tree_st_def clean_etf_of_transfer_def
        clean_edge_tree_def Let_def ivl_tf_st_commute ivl_tf_def assign_ivl_def
        fun_of_st_update assume_ivl_st_commute assume_not_ivl_st_commute enter_ivl_st_commute)

lemma sides_ivl_etf_clean_st_fun_of_st:
  fixes sigma_st :: "pp + unit => ivl st"
  shows "fun_of_st (sides_of_rhs (apply_etf_st ivl_etf_clean_st a u) sigma_st k)
     = sides_of_rhs (apply_etf (clean_etf_of_transfer ivl_tf) a u)
         (\<lambda>k. fun_of_st (sigma_st k)) k"
  by (cases a; cases k)
     (simp_all add: ivl_etf_clean_st_def clean_edge_tree_st_def clean_etf_of_transfer_def
        clean_edge_tree_def Let_def ivl_tf_st_commute bot_fun_def fun_eq_iff ivl_tf_def
        assign_ivl_def fun_of_st_update assume_ivl_st_commute assume_not_ivl_st_commute
        enter_ivl_st_commute)

lemma dep_ivl_etf_clean_st_fun_of_st:
  fixes sigma_st :: "pp + unit => ivl st"
  shows "dep_aux sigma_st (apply_etf_st ivl_etf_clean_st a u)
     = dep_aux (\<lambda>k. fun_of_st (sigma_st k))
         (apply_etf (clean_etf_of_transfer ivl_tf) a u)"
  by (cases a)
     (simp_all add: ivl_etf_clean_st_def clean_edge_tree_st_def clean_etf_of_transfer_def
        clean_edge_tree_def Let_def)

lemma part_post_solution_ivl_rehydrate_seed_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution
       (side_cfg_T_eff_cmp_seed_st id (\<lambda>c cc ex. ivl_combine_rehydrate cc ex c)
          frame_seed_st g ivl_etf_clean_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_cmp_seed id (\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c)
          (\<lambda>c. fun_of_st (frame_seed_st c)) g (clean_etf_of_transfer ivl_tf)
          (fun_of_st bot0_st) (fun_of_st s0_st))
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
  by (rule part_post_solution_cmp_seed_st_to_abs_eff
        [OF traverse_ivl_etf_clean_st_fun_of_st sides_ivl_etf_clean_st_fun_of_st
            dep_ivl_etf_clean_st_fun_of_st traverse_ivl_combine_rehydrate_fun_of_st
            sides_ivl_combine_rehydrate_fun_of_st dep_ivl_combine_rehydrate_fun_of_st
            pp_st])

subsection \<open>Soundness of the rehydrated caller continuation (Spec.combine)\<close>

text \<open>
  The crux of the return path: if the caller store \<open>s\<close> is soundly abstracted by the
  caller local \<open>sc\<close> and the callee-exit store \<open>t\<close> by the callee-exit local \<open>se\<close>,
  then Goblint's concrete combine \<open><s|t>\<close> (locals from \<open>s\<close>, globals from \<open>t\<close>) is
  soundly abstracted by the rehydrated continuation \<^term>\<open>combine_abs_st sc se\<close>.
  This is exactly the \<open>COMB\<close> obligation of the generic context-sliced soundness
  theorem \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>
  (@{thm [source] sound_transfer.clean_ctx_collect_rread}), whose conclusion is the
  \<^emph>\<open>local\<close> slot at the return node.  The strip combine cannot discharge it once the
  callee writes a global that is later read: its returned local has that global at
  \<open>bot\<close>, so \<open><s|t>\<close> (carrying the concrete global) escapes the concretisation.
  Rehydration restores exactly the missing globals, and no more.

  It is a pure \<^class>\<open>sound_domain\<close> fact (\<open>combine_states_sound\<close> transported to
  the executable \<^typ>\<open>ivl st\<close> layer via \<open>fun_of_st_combine_abs_st\<close>); it does
  not read a published global slot and so does not reintroduce the \<open>local \<squnion> global\<close>
  join.\<close>

lemma rehydrate_caller_continuation_sound:
  fixes sc se :: "ivl st"
  assumes "s \<in> \<lbrakk>fun_of_st sc\<rbrakk>" and "t \<in> \<lbrakk>fun_of_st se\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>fun_of_st (combine_abs_st sc se)\<rbrakk>"
  using assms by (simp add: fun_of_st_combine_abs_st combine_states_sound)

subsection \<open>A program that reads globals back after the call\<close>

text \<open>The witness program: \<open>f\<close> derives \<open>GH := G + 1\<close>; \<open>main\<close> calls it twice and
  \<^emph>\<open>reads both globals back\<close> into locals \<open>g1,h1\<close> / \<open>g2,h2\<close> after each call.  Under the
  strip combine these reads are \<open>bot\<close>; under rehydration they are the exact points.\<close>

definition rhyd_prog :: imp_prog where
  "rhyd_prog = \<lbrakk>
     int G, GH;

     void f() {
       GH := G + 1
     }
     void main() {
       G := 0;
       f();
       g1 := G;
       h1 := GH;
       G := 10;
       f();
       g2 := G;
       h2 := GH
     }
   \<rbrakk>"

definition rhyd_cfg :: cfg where
  "rhyd_cfg = compile_prog (prog_table rhyd_prog) (prog_procs rhyd_prog) (prog_main rhyd_prog)"

definition rhyd_eqs :: "(pp \<times> ivl st, ivl st, ivl st) eqsT" where
  "rhyd_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. ivl_combine_rehydrate cc ex c)
     restrict_global_st rhyd_cfg ivl_etf_clean_st bot cinit_ivl_st"

definition rhyd_solution ::
  "(pp \<times> ivl st) set \<times> ((pp \<times> ivl st) + ivl st \<Rightarrow> ivl st)" where
  "rhyd_solution = TD_side_always_join_Interp_solve rhyd_eqs (cfg_exit rhyd_cfg, bot)"


lemma rhyd_runs: "fst rhyd_solution \<noteq> {}"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>The read-backs recover the exact points (rehydration, not a read join)\<close>

text \<open>
  \<^const>\<open>rhyd_cfg\<close> nodes: \<open>f = 0 \<rightarrow> 1\<close>; \<open>main\<close> reads back \<open>g1\<close> at \<open>7\<close>, \<open>h1\<close> at \<open>9\<close>,
  \<open>g2\<close> at \<open>15\<close>, \<open>h2\<close> at \<open>17\<close>.  All four are exact points --- the globals are present in
  the caller-local flow because \<^const>\<open>ivl_combine_rehydrate\<close> put them back on return,
  \<^emph>\<open>not\<close> because a read folds in a published global.
\<close>

lemma rhyd_readbacks_exact:
  "lookup_st (snd rhyd_solution (Inl (7,  bot::ivl st))) ''g1'' = Ivl (Fin 0)  (Fin 0)
   \<and> lookup_st (snd rhyd_solution (Inl (9,  bot::ivl st))) ''h1'' = Ivl (Fin 1)  (Fin 1)
   \<and> lookup_st (snd rhyd_solution (Inl (15, bot::ivl st))) ''g2'' = Ivl (Fin 10) (Fin 10)
   \<and> lookup_st (snd rhyd_solution (Inl (17, bot::ivl st))) ''h2'' = Ivl (Fin 11) (Fin 11)"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>Soundness of the read-back values: the concrete run has \<open>g1=0, h1=1, g2=10,
  h2=11\<close>, and each lies in the concretisation of the analyzer's interval.\<close>

lemma rhyd_readbacks_in_gamma:
  "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 0)) \<and> 1 \<in> gamma_ivl (Ivl (Fin 1) (Fin 1))
   \<and> 10 \<in> gamma_ivl (Ivl (Fin 10) (Fin 10)) \<and> 11 \<in> gamma_ivl (Ivl (Fin 11) (Fin 11))"
  by simp

subsection \<open>A concrete twfr witness for the rehydrated readback\<close>

text \<open>The readback of the first call's global happens on the \<^emph>\<open>caller\<close> continuation, past a
  return combine: an explicit \<^const>\<open>twfr\<close> run of \<^const>\<open>rhyd_cfg\<close> that runs \<open>main\<close> to the
  first call (\<open>2 \<to> 3 \<to> 4\<close>, \<open>G := 0\<close>), calls \<open>f\<close> (whose body \<open>GH := G + 1\<close> is opened by
  \<open>start\<close> at the callee entry and spliced back by \<open>combine\<close> at \<open>(4,1,5)\<close>), and reads the
  rehydrated \<open>G\<close> into \<open>g1\<close> (\<open>5 \<to> 6 \<to> 7\<close>).  The terminal store carries \<open>g1 = 0\<close> --- the exact
  point \<open>rhyd_readbacks_exact\<close> assigns node 7.  The store family is the shared \<^const>\<open>gk\<close>
  extended with the derived global \<open>GH\<close>.\<close>

definition gkh where
  "gkh k j = (gk k)(''GH'' := j)"

lemma gkh_G [simp]: "gkh k j ''G'' = k"
  and gkh_GH [simp]: "gkh k j ''GH'' = j"
  and gkh_g1 [simp]: "gkh k j ''g1'' = 0"
  by (simp_all add: gkh_def gk_def)

lemma combine_gk_gkh [simp]: "<gk a|gkh b cc> = gkh b cc"
  by (rule ext) (simp add: combine_states_def gkh_def gk_def IMP2_Globals.is_global_def)

text \<open>The rhyd edges the witness traverses, by \<open>eval\<close>.\<close>

lemma rhyd_e_2_3: "(2, EA_Assign ''G'' (IMP2_Syntax.N 0), 3) \<in> edges rhyd_cfg"
  and rhyd_e_3_4: "(3, EA_Nop, 4) \<in> edges rhyd_cfg"
  and rhyd_e_4_0: "(4, EA_Enter, 0) \<in> edges rhyd_cfg"
  and rhyd_e_0_1: "(0, EA_Assign ''GH'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)), 1) \<in> edges rhyd_cfg"
  and rhyd_e_5_6: "(5, EA_Nop, 6) \<in> edges rhyd_cfg"
  and rhyd_e_6_7: "(6, EA_Assign ''g1'' (IMP2_Syntax.V ''G''), 7) \<in> edges rhyd_cfg"
  unfolding rhyd_cfg_def rhyd_prog_def by eval+

lemma rhyd_c_4_1_5: "(4, 1, 5) \<in> combines rhyd_cfg"
  unfolding rhyd_cfg_def rhyd_prog_def by eval

abbreviation rhyd_combc :: "ivl st \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "rhyd_combc \<equiv> (\<lambda>c1 c2. c1)"

lemma rhyd_wit_readback:
  "\<exists>tr. twfr enterc rhyd_combc rhyd_cfg 2 bot 7 bot tr \<and> tr \<noteq> [] \<and> last tr ''g1'' = 0"
proof -
  have m2: "twfr enterc rhyd_combc rhyd_cfg 2 bot 2 bot [gk 5]" by (rule twfr.start)
  have m3: "twfr enterc rhyd_combc rhyd_cfg 2 bot 3 bot [gk 5, gk 0]"
    using twfr.intra[OF rhyd_e_2_3 _ m2] by (simp add: step_assign_const)
  have m4: "twfr enterc rhyd_combc rhyd_cfg 2 bot 4 bot [gk 5, gk 0, gk 0]"
    using twfr.intra[OF rhyd_e_3_4 _ m3] by (simp add: step_nop)
  have rho: "twfr enterc rhyd_combc rhyd_cfg 0 (enterc bot (gk 0)) 1 (enterc bot (gk 0))
               [gk 0, gkh 0 1]"
  proof -
    have c0: "twfr enterc rhyd_combc rhyd_cfg 0 (enterc bot (gk 0)) 0 (enterc bot (gk 0)) [gk 0]"
      by (rule twfr.start)
    show ?thesis using twfr.intra[OF rhyd_e_0_1 _ c0] by (simp add: gkh_def gk_def)
  qed
  have hd_eq: "hd [gk 0, gkh 0 1] = enter_state (last [gk 5, gk 0, gk 0])" by simp
  let ?t5 = "[gk 5, gk 0, gk 0] @ tl [gk 0, gkh 0 1] @ [<gk 0|gkh 0 1>]"
  have m5: "twfr enterc rhyd_combc rhyd_cfg 2 bot 5 bot ?t5"
    using twfr.combine[OF rhyd_c_4_1_5 rhyd_e_4_0 m4 _ hd_eq] rho by simp
  have m6: "twfr enterc rhyd_combc rhyd_cfg 2 bot 6 bot (?t5 @ [gkh 0 1])"
    using twfr.intra[OF rhyd_e_5_6 _ m5] by simp
  have m7: "twfr enterc rhyd_combc rhyd_cfg 2 bot 7 bot ((?t5 @ [gkh 0 1]) @ [gkh 0 1])"
    using twfr.intra[OF rhyd_e_6_7 _ m6] by (simp add: gkh_def gk_def fun_upd_idem)
  show ?thesis
  proof (intro exI conjI)
    show "twfr enterc rhyd_combc rhyd_cfg 2 bot 7 bot ((?t5 @ [gkh 0 1]) @ [gkh 0 1])"
      by (rule m7)
  qed simp_all
qed

text \<open>\<^bold>\<open>Per-coordinate soundness of the readback.\<close>  The concrete \<^const>\<open>twfr\<close> run reaches the
  readback node 7 with \<open>g1 = 0\<close>, which lies in the concretisation of the analyzer's slot
  there --- \<open>0 \<in> gamma [0,0]\<close>.  Non-vacuous.\<close>

theorem rhyd_wit_readback_sound:
  "\<exists>tr. twfr enterc rhyd_combc rhyd_cfg 2 bot 7 bot tr \<and> tr \<noteq> []
     \<and> last tr ''g1'' \<in> gamma_ivl (lookup_st (snd rhyd_solution (Inl (7, bot))) ''g1'')"
proof -
  obtain tr where w: "twfr enterc rhyd_combc rhyd_cfg 2 bot 7 bot tr" and ne: "tr \<noteq> []"
      and g1: "last tr ''g1'' = 0"
    using rhyd_wit_readback by blast
  have rd: "last tr ''g1'' \<in> gamma_ivl (lookup_st (snd rhyd_solution (Inl (7, bot))) ''g1'')"
    using g1 rhyd_readbacks_exact by simp
  show ?thesis using w ne rd by blast
qed

subsection \<open>The two contexts stay separated (rehydration preserves R_read precision)\<close>

text \<open>The two calling contexts are the callee-selected globals: \<open>{G=[0,0]}\<close> at the
  first site, and \<open>{G=[10,10], GH=[1,1]}\<close> at the second --- rehydration carries the
  first call's derived \<open>GH\<close> into the caller local, so the second context observes it.\<close>

definition rhyd_ctx_lo :: "ivl st" where
  "rhyd_ctx_lo = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 0) (Fin 0)))"

definition rhyd_ctx_hi :: "ivl st" where
  "rhyd_ctx_hi = restrict_global_st
     (update_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 10) (Fin 10))) ''GH'' (Ivl (Fin 1) (Fin 1)))"

text \<open>The callee-exit local (\<^const>\<open>rhyd_cfg\<close> node \<open>1\<close>) is the exact derived point in
  each context, distinct across the two --- the R_read separation of the seeded-clean
  spine survives rehydration.\<close>

lemma rhyd_callee_exit_separated:
  "lookup_st (snd rhyd_solution (Inl (1, rhyd_ctx_lo))) ''GH'' = Ivl (Fin 1) (Fin 1)
   \<and> lookup_st (snd rhyd_solution (Inl (1, rhyd_ctx_hi))) ''GH'' = Ivl (Fin 11) (Fin 11)
   \<and> (Ivl (Fin 1) (Fin 1) :: ivl) \<noteq> Ivl (Fin 11) (Fin 11)"
  unfolding rhyd_solution_def rhyd_eqs_def rhyd_cfg_def rhyd_prog_def
    rhyd_ctx_lo_def rhyd_ctx_hi_def
    ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def clean_edge_tree_st_def
    combine_abs_st_def side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>Context-clustered GraphViz of the solved run\<close>

text \<open>One cluster per activation: \<open>main\<close> (context \<open>bot\<close>, carrying the rehydrated
  read-backs \<open>g1,h1,g2,h2\<close>) and the two copies of \<open>f\<close> at their contexts.  Node labels
  are the generic \<^const>\<open>ctx_debug_state_node_label_auto\<close>; each \<open>f\<close> cluster carries
  its callee-derived global \<open>GH\<close>.\<close>

datatype rhyd_rctx = RhMain | RhFLo | RhFHi

definition rhyd_rctx_ctx :: "rhyd_rctx \<Rightarrow> ivl st" where
  "rhyd_rctx_ctx r = (case r of RhMain \<Rightarrow> bot | RhFLo \<Rightarrow> rhyd_ctx_lo | RhFHi \<Rightarrow> rhyd_ctx_hi)"

definition rhyd_rctx_key :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_rctx_key r = (case r of RhMain \<Rightarrow> ''main'' | RhFLo \<Rightarrow> ''fGlo'' | RhFHi \<Rightarrow> ''fGhi'')"

definition rhyd_rctx_label :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_rctx_label r =
     (case r of RhMain \<Rightarrow> ''main'' | RhFLo \<Rightarrow> ''f @ G=[0,0]'' | RhFHi \<Rightarrow> ''f @ G=[10,10]'')"

definition rhyd_f_pps :: "pp list" where "rhyd_f_pps = [0, 1]"

definition rhyd_node_label :: "pp \<times> rhyd_rctx \<Rightarrow> string" where
  "rhyd_node_label = ctx_debug_state_node_label_auto rhyd_cfg
     (\<lambda>pc. case pc of (p, r) \<Rightarrow> snd rhyd_solution (Inl (p, rhyd_rctx_ctx r)))"

definition rhyd_globals :: "rhyd_rctx \<Rightarrow> string" where
  "rhyd_globals r =
     ''GH = '' @ show_val (lookup_st (snd rhyd_solution (Inr (rhyd_rctx_ctx r))) ''GH'')"

text \<open>A call site's context is the callee-selected global part of its caller local
  (\<^const>\<open>ivl_ec\<close>): node \<open>4\<close> selects \<open>rhyd_ctx_lo\<close>, node \<open>11\<close> selects \<open>rhyd_ctx_hi\<close>.\<close>
definition rhyd_f_rctx_of :: "pp \<Rightarrow> rhyd_rctx" where
  "rhyd_f_rctx_of cc =
     (if restrict_global_st (snd rhyd_solution (Inl (cc, bot))) = rhyd_ctx_lo
      then RhFLo else RhFHi)"

definition rhyd_rmode_nodes :: "(pp \<times> rhyd_rctx) list" where
  "rhyd_rmode_nodes =
     map (\<lambda>p. (p, RhMain)) (filter (\<lambda>p. p \<notin> set rhyd_f_pps) (sorted_list_of_set (nodes rhyd_cfg)))
   @ map (\<lambda>p. (p, RhFLo)) rhyd_f_pps
   @ map (\<lambda>p. (p, RhFHi)) rhyd_f_pps"

definition rhyd_rmode_intra :: "((pp \<times> rhyd_rctx) \<times> edge_action \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_intra =
     [((u, RhMain), a, (v, RhMain)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg,
        a \<noteq> EA_Enter, u \<notin> set rhyd_f_pps, v \<notin> set rhyd_f_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg,
        u \<in> set rhyd_f_pps, v \<in> set rhyd_f_pps, r \<leftarrow> [RhFLo, RhFHi]]"

definition rhyd_rmode_calls :: "((pp \<times> rhyd_rctx) \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_calls =
     [((u, RhMain), (v, rhyd_f_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list rhyd_cfg, a = EA_Enter]"

definition rhyd_rmode_returns ::
  "((pp \<times> rhyd_rctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> rhyd_rctx)) list" where
  "rhyd_rmode_returns =
     [((ex, rhyd_f_rctx_of cc), (cc, ex, ret), (ret, RhMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list rhyd_cfg]"

definition rhyd_dot :: String.literal where
  "rhyd_dot = String.implode
     (ctx_debug_graphviz_with_globals
        rhyd_rctx_key rhyd_rctx_label rhyd_globals rhyd_node_label (\<lambda>_. ''shape=box'')
        [RhMain, RhFLo, RhFHi]
        rhyd_rmode_nodes rhyd_rmode_intra rhyd_rmode_calls rhyd_rmode_returns)"

text \<open>@{command ML_val} \<open>writeln (@{code rhyd_dot})\<close> emits the DOT source: \<open>main\<close>'s
  read-back nodes carry \<open>g1=[0,0]\<close>, \<open>h1=[1,1]\<close>, \<open>g2=[10,10]\<close>, \<open>h2=[11,11]\<close>.\<close>

ML_val \<open>writeln (@{code rhyd_dot})\<close>

text \<open>
  \<^bold>\<open>What this run certifies.\<close>  Return rehydration completes the Goblint-faithful D/G/C
  return path.  The caller continuation is the structural combine
  \<^const>\<open>combine_abs_st\<close> (\<open>Spec.combine\<close>), proved \<open>\<gamma>\<close>-sound in
  \<open>rehydrate_caller_continuation_sound\<close> --- the \<open>COMB\<close> obligation of the generic
  context-sliced theorem, which the strip combine could not discharge once a callee
  global is read back.  The R_read architecture is untouched: the transfer still
  reads only the local (\<^const>\<open>ivl_etf_clean_st\<close>), the context is still selected from
  the caller local (\<open>ivl_combine_rehydrate_context_is_local\<close>), and the reconstructed
  globals are the callee's returned globals, not a \<open>local \<squnion> global\<close> read
  (\<open>ivl_combine_rehydrate_answer\<close>).  Executably, the four read-backs recover the exact
  points (\<open>rhyd_readbacks_exact\<close>, sound by \<open>rhyd_readbacks_in_gamma\<close>); a concrete
  \<^const>\<open>twfr\<close> run past the return combine reaches the first read-back node with the exact
  \<open>g1 = 0\<close> in the analysis slot there (\<open>rhyd_wit_readback_sound\<close>), and the two contexts stay
  separated (\<open>rhyd_callee_exit_separated\<close>).  The strip-combine spine
  (\<^theory>\<open>Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run\<close>) and the retain
  \<open>side_env_cmp\<close> baseline are untouched.  No loop is analysed, so interval widening is
  not engaged.
\<close>

end

