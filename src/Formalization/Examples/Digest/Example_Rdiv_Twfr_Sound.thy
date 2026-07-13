theory Example_Rdiv_Twfr_Sound
  imports
    Example_Interval_Recursion_Rehydrate
    Ivl_Twfr_Common
    "Voblint_Formalization.Compiler_Correctness_Prototype"
begin

section \<open>Recursive interval @{text rdiv}: executable soundness via the twfr witness spine\<close>

text \<open>
  The end-to-end instance of the repaired witness calculus for the shipped recursive
  interval run.  The solver keys stay executable (\<^typ>\<open>ivl st\<close>); only slot \<^emph>\<open>values\<close> are
  transported by \<^const>\<open>fun_of_st\<close> (\<open>rdiv_rehyd_cover_abs_post_fixpoint\<close>).  The activation
  routing keeps globals and abstracts them pointwise, and \<^const>\<open>ivl_abs_route_st\<close> is the
  \<^emph>\<open>same\<close> \<open>ivl st\<close> key the generator's \<^const>\<open>ivl_combine_rehydrate_abs\<close> reads --- no
  reconstruction of a key from an abstract value, no \<^const>\<open>fun_of_st\<close> inverse.
\<close>

subsection \<open>The activation routing\<close>

text \<open>The witness routing is the shared interval activation routing \<^const>\<open>ivl_enterc\<close>: keep
  the entered store's globals, abstract them to point intervals, take the executable
  global-restricted key.  Its correspondence to the generator key and the combine-tree
  dependency set are the run-independent \<^theory>\<open>Voblint_Formalization.Ivl_Twfr_Common\<close>
  lemmas.\<close>

definition rdiv_enterc :: "ivl st \<Rightarrow> store \<Rightarrow> ivl st" where
  "rdiv_enterc = ivl_enterc"

subsection \<open>The run objects\<close>

abbreviation rdiv_sg :: "(pp \<times> ivl st) + ivl st \<Rightarrow> ivl abs_state" where
  "rdiv_sg \<equiv> (\<lambda>k. fun_of_st (snd rdiv_rehyd_cover_solution k))"

abbreviation rdiv_vars :: "(pp \<times> ivl st) set" where
  "rdiv_vars \<equiv> fst rdiv_rehyd_cover_solution"

text \<open>The backward query-membership dischargers (\<open>q_edge\<close> / \<open>q_caller\<close> / \<open>q_callee\<close>) and the
  return combine bound for this run are the run-independent
  \<^theory>\<open>Voblint_Formalization.Ivl_Twfr_Common\<close> lemmas instantiated with \<^const>\<open>rdiv_cfg\<close> and
  \<open>rdiv_rehyd_cover_abs_post_fixpoint\<close>; they are not repeated here.\<close>

subsection \<open>The executable analysis over-approximates the concrete recursive G\<close>

text \<open>The full-store concretisation \<^term>\<open>\<lbrakk>rdiv_sg (Inl (11, bot))\<rbrakk>\<close> of the return slot is
  \<^emph>\<open>empty\<close>: the seeded-clean local slot leaves every unmentioned global (e.g. \<open>''GG''\<close>) at
  \<open>\<bottom>\<close>, and \<^const>\<open>gamma_ivl\<close> of \<open>\<bottom>\<close> is \<open>{}\<close>, so \<^const>\<open>gamma_state\<close> --- which quantifies
  over \<^emph>\<open>all\<close> variable names --- is uninhabited.  The non-vacuous soundness is therefore the
  \<^bold>\<open>per-coordinate\<close> read, exactly as \<open>Trace_Analysis_Sound.reaching_global_read_sound\<close> is
  stated \<open>(last tr) x \<in> gamma (env v x)\<close> for a single variable.  Here the coordinate is the
  program's global \<open>G\<close>: the analysis slot carries \<open>G = [3,3]\<close> and the concrete recursive
  execution \<open>G = 0,1,2,3\<close> terminates with \<open>G = 3\<close>, so \<open>3 \<in> gamma_ivl [3,3]\<close>.\<close>

lemma rdiv_G_slot_11:
  "rdiv_sg (Inl (11, bot)) ''G'' = Ivl (Fin 3) (Fin 3)"
  using rdiv_rehyd_cover_returns_global_to_main by simp

text \<open>The unmentioned global \<open>''GG''\<close> sits at \<open>\<bottom>\<close>, witnessing that the full-store slot is
  empty --- the reason the per-coordinate read is the only non-vacuous statement.\<close>

lemma rdiv_slot_11_unmentioned_global_bot:
  "rdiv_sg (Inl (11, bot)) ''GG'' = bot"
  unfolding rdiv_rehyd_cover_solution_def rdiv_rehyd_cover_eqs_def rdiv_cfg_def rdiv_prog_def
    rdiv_zero_ivl_def ivl_ec_def ivl_combine_rehydrate_def ivl_etf_clean_st_def
    clean_edge_tree_st_def side_cfg_T_eff_cmp_seed_st_def bot_ivl_def by eval

lemma rdiv_slot_11_full_gamma_empty:
  "\<lbrakk>rdiv_sg (Inl (11, bot))\<rbrakk> = {}"
proof -
  have "\<And>s. s ''GG'' \<notin> gamma (rdiv_sg (Inl (11, bot)) ''GG'')"
    by (simp add: rdiv_slot_11_unmentioned_global_bot gamma_ivl_bot)
  thus ?thesis unfolding gamma_state_def by blast
qed

text \<open>\<^bold>\<open>The executable interval analysis soundly over-approximates the concrete recursive
  execution's terminal global.\<close>  The concrete recursion \<open>f\<close> increments \<open>G\<close> from \<open>0\<close> while
  \<open>G < 3\<close>, so it reaches \<open>main\<close>'s continuation (node 11) with \<open>G = 3\<close>; the executable
  analysis assigns \<open>G = [3,3]\<close> there, and \<open>3 \<in> gamma [3,3]\<close>.  Non-vacuous: the concrete
  value \<open>3\<close> is a genuine member.\<close>

theorem rdiv_analysis_G_sound_at_main_cont:
  "(3) \<in> gamma (rdiv_sg (Inl (11, bot)) ''G'')"
  unfolding rdiv_G_slot_11 by simp

subsection \<open>An explicit recursive twfr witness reaching node 11 with G = 3\<close>

text \<open>Non-vacuity: an explicit \<^const>\<open>twfr\<close> run of the shipped \<^const>\<open>rdiv_cfg\<close> that reaches
  \<open>main\<close>'s continuation (node 11) in context \<^const>\<open>bot\<close> with terminal store \<open>G = 3\<close> --- the
  exact concrete value the per-coordinate soundness \<open>rdiv_analysis_G_sound_at_main_cont\<close>
  over-approximates.  The store carries \<open>G\<close> and zeroes every other variable; the recursion
  \<open>f @ G=0,1,2,3\<close> is opened by \<^const>\<open>twfr\<close>'s \<open>start\<close> at each frame entry and spliced back by
  \<open>combine\<close>, which is exactly the return path \<^const>\<open>trace_witness\<close> could not derive for a
  \<open>cfg_entry\<close> without an \<open>EA_Enter\<close> edge.

  The CFG (\<open>sorted_list_of_set (edges rdiv_cfg)\<close> / \<open>combines\<close>):
  edges \<open>(0,[G<3],1) (0,![G<3],5) (1,G:=G+1,2) (2,nop,3) (3,Enter,0) (4,nop,7) (5,G:=G,6)
  (6,nop,7) (8,G:=0,9) (9,nop,10) (10,Enter,0)\<close>; combines \<open>(3,7,4) (10,7,11)\<close>; entry \<open>8\<close>.\<close>

text \<open>The witness uses the shared single-global store family \<^const>\<open>gk\<close> and its concrete
  \<^const>\<open>edge_step\<close> lemmas from \<^theory>\<open>Voblint_Formalization.Twfr_Reach_Read\<close>.  The rdiv edges
  and combines it needs, by \<open>eval\<close>:\<close>

lemma rdiv_e_0_1: "(0, EA_Assume (IMP2_Syntax.bexp.Less (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 3)), 1) \<in> edges rdiv_cfg"
  and rdiv_e_0_5: "(0, EA_AssumeNot (IMP2_Syntax.bexp.Less (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 3)), 5) \<in> edges rdiv_cfg"
  and rdiv_e_1_2: "(1, EA_Assign ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)), 2) \<in> edges rdiv_cfg"
  and rdiv_e_2_3: "(2, EA_Nop, 3) \<in> edges rdiv_cfg"
  and rdiv_e_3_0: "(3, EA_Enter, 0) \<in> edges rdiv_cfg"
  and rdiv_e_4_7: "(4, EA_Nop, 7) \<in> edges rdiv_cfg"
  and rdiv_e_5_6: "(5, EA_Assign ''G'' (IMP2_Syntax.V ''G''), 6) \<in> edges rdiv_cfg"
  and rdiv_e_6_7: "(6, EA_Nop, 7) \<in> edges rdiv_cfg"
  and rdiv_e_8_9: "(8, EA_Assign ''G'' (IMP2_Syntax.N 0), 9) \<in> edges rdiv_cfg"
  and rdiv_e_9_10: "(9, EA_Nop, 10) \<in> edges rdiv_cfg"
  and rdiv_e_10_0: "(10, EA_Enter, 0) \<in> edges rdiv_cfg"
  unfolding rdiv_cfg_def rdiv_prog_def by eval+

lemma rdiv_c_3_7_4: "(3, 7, 4) \<in> combines rdiv_cfg"
  and rdiv_c_10_7_11: "(10, 7, 11) \<in> combines rdiv_cfg"
  unfolding rdiv_cfg_def rdiv_prog_def by eval+

subsection \<open>The recursive witness, built bottom-up\<close>

text \<open>Deepest call \<open>f @ G=3\<close>: the guard \<open>G < 3\<close> fails, so the else branch \<open>0 \<to> 5 \<to> 6 \<to> 7\<close>
  runs with no recursive call --- the base of the witness.\<close>

lemma wit_f3:
  "twfr rdiv_enterc combc rdiv_cfg 0 kc 7 kc [gk 3, gk 3, gk 3, gk 3]"
proof -
  have w0: "twfr rdiv_enterc combc rdiv_cfg 0 kc 0 kc [gk 3]" by (rule twfr.start)
  have w5: "twfr rdiv_enterc combc rdiv_cfg 0 kc 5 kc [gk 3, gk 3]"
    using twfr.intra[OF rdiv_e_0_5 _ w0] by (simp add: step_guard_ge)
  have w6: "twfr rdiv_enterc combc rdiv_cfg 0 kc 6 kc [gk 3, gk 3, gk 3]"
    using twfr.intra[OF rdiv_e_5_6 _ w5] by (simp add: step_assign_id)
  have w7: "twfr rdiv_enterc combc rdiv_cfg 0 kc 7 kc [gk 3, gk 3, gk 3, gk 3]"
    using twfr.intra[OF rdiv_e_6_7 _ w6] by (simp add: step_nop)
  show ?thesis by (rule w7)
qed

text \<open>Every non-base call \<open>f @ G=k\<close> (\<open>k < 3\<close>) runs the then branch \<open>0 \<to> 1 \<to> 2 \<to> 3\<close>
  (incrementing \<open>G\<close> to \<open>k+1\<close>), recurses via \<^const>\<open>twfr\<close> \<open>combine\<close> at \<open>(3,7,4)\<close> with the
  callee summary supplied for the routed context, and returns \<open>4 \<to> 7\<close> carrying the callee's
  \<open>G = 3\<close> back.  The caller projection \<open>combc = (\<lambda>c1 c2. c1)\<close> keeps the return context.\<close>

abbreviation rdiv_combc :: "ivl st \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "rdiv_combc \<equiv> (\<lambda>c1 c2. c1)"

lemma wit_frec:
  assumes k3: "k < 3"
    and callee: "\<And>kc'. \<exists>rho. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc' 7 kc' rho
                    \<and> hd rho = gk (k + 1) \<and> last rho = gk 3"
  shows "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc tr \<and> hd tr = gk k \<and> last tr = gk 3"
proof -
  have w0: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 0 kc [gk k]" by (rule twfr.start)
  have w1: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 1 kc [gk k, gk k]"
    using twfr.intra[OF rdiv_e_0_1 _ w0] k3 by (simp add: step_guard_lt)
  have w2: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 2 kc [gk k, gk k, gk (k + 1)]"
    using twfr.intra[OF rdiv_e_1_2 _ w1] by (simp add: step_assign_incr)
  have w3: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 3 kc [gk k, gk k, gk (k + 1), gk (k + 1)]"
    using twfr.intra[OF rdiv_e_2_3 _ w2] by (simp add: step_nop)
  obtain rho where rho: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 (rdiv_enterc kc (gk (k + 1))) 7
                             (rdiv_enterc kc (gk (k + 1))) rho"
      and hd_rho: "hd rho = gk (k + 1)" and last_rho: "last rho = gk 3"
    using callee[of "rdiv_enterc kc (gk (k + 1))"] by blast
  have last_w3: "last [gk k, gk k, gk (k + 1), gk (k + 1)] = gk (k + 1)" by simp
  have hd_eq: "hd rho = enter_state (last [gk k, gk k, gk (k + 1), gk (k + 1)])"
    using hd_rho by simp
  have wc: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 4 kc
              ([gk k, gk k, gk (k + 1), gk (k + 1)] @ tl rho @ [<gk (k + 1)|last rho>])"
    using twfr.combine[OF rdiv_c_3_7_4 rdiv_e_3_0 w3 _ hd_eq] rho last_w3 by simp
  have last_wc: "last ([gk k, gk k, gk (k + 1), gk (k + 1)] @ tl rho @ [<gk (k + 1)|last rho>]) = gk 3"
    using last_rho by simp
  have w7: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc
              ([gk k, gk k, gk (k + 1), gk (k + 1)] @ tl rho @ [<gk (k + 1)|last rho>] @ [gk 3])"
    using twfr.intra[OF rdiv_e_4_7 _ wc] last_wc by (simp add: step_nop)
  show ?thesis
  proof (intro exI conjI)
    show "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc
            ([gk k, gk k, gk (k + 1), gk (k + 1)] @ tl rho @ [<gk (k + 1)|last rho>] @ [gk 3])"
      by (rule w7)
  qed simp_all
qed

text \<open>The four call summaries, deepest first.  Each is universal in the (routed) context \<open>kc\<close>.\<close>

lemma wit_f2:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc tr \<and> hd tr = gk 2 \<and> last tr = gk 3"
proof (rule wit_frec[where k = 2])
  show "(2::Int.int) < 3" by simp
next
  fix kc'
  show "\<exists>rho. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc' 7 kc' rho
          \<and> hd rho = gk (2 + 1) \<and> last rho = gk 3"
    by (rule exI[where x = "[gk 3, gk 3, gk 3, gk 3]"]) (simp add: wit_f3)
qed

lemma wit_f1:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc tr \<and> hd tr = gk 1 \<and> last tr = gk 3"
proof (rule wit_frec[where k = 1])
  show "(1::Int.int) < 3" by simp
next
  fix kc'
  show "\<exists>rho. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc' 7 kc' rho
          \<and> hd rho = gk (1 + 1) \<and> last rho = gk 3"
    using wit_f2[of kc'] by simp
qed

lemma wit_f0:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc 7 kc tr \<and> hd tr = gk 0 \<and> last tr = gk 3"
proof (rule wit_frec[where k = 0])
  show "(0::Int.int) < 3" by simp
next
  fix kc'
  show "\<exists>rho. twfr rdiv_enterc rdiv_combc rdiv_cfg 0 kc' 7 kc' rho
          \<and> hd rho = gk (0 + 1) \<and> last rho = gk 3"
    using wit_f1[of kc'] by simp
qed

text \<open>\<open>main\<close>: zero \<open>G\<close> (\<open>8 \<to> 9 \<to> 10\<close>), call \<open>f @ G=0\<close>, and splice its return at \<open>(10,7,11)\<close>.
  The top call runs in context \<^const>\<open>bot\<close>, so \<open>combc = (\<lambda>c1 c2. c1)\<close> keeps the continuation
  (node 11) in context \<^const>\<open>bot\<close> --- exactly the analysis slot \<open>rdiv_sg (Inl (11, bot))\<close>.\<close>

lemma wit_main:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot tr \<and> last tr = gk 3"
proof -
  have m8: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 8 bot [gk 0]" by (rule twfr.start)
  have m9: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 9 bot [gk 0, gk 0]"
    using twfr.intra[OF rdiv_e_8_9 _ m8] by (simp add: step_assign_const)
  have m10: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 10 bot [gk 0, gk 0, gk 0]"
    using twfr.intra[OF rdiv_e_9_10 _ m9] by (simp add: step_nop)
  obtain rho where rho: "twfr rdiv_enterc rdiv_combc rdiv_cfg 0 (rdiv_enterc bot (gk 0)) 7
                             (rdiv_enterc bot (gk 0)) rho"
      and hd_rho: "hd rho = gk 0" and last_rho: "last rho = gk 3"
    using wit_f0[of "rdiv_enterc bot (gk 0)"] by blast
  have last_m10: "last [gk 0, gk 0, gk 0] = gk 0" by simp
  have hd_eq: "hd rho = enter_state (last [gk 0, gk 0, gk 0])" using hd_rho by simp
  have wc: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot
              ([gk 0, gk 0, gk 0] @ tl rho @ [<gk 0|last rho>])"
    using twfr.combine[OF rdiv_c_10_7_11 rdiv_e_10_0 m10 _ hd_eq] rho last_m10 by simp
  show ?thesis
  proof (intro exI conjI)
    show "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot
            ([gk 0, gk 0, gk 0] @ tl rho @ [<gk 0|last rho>])"
      by (rule wc)
    show "last ([gk 0, gk 0, gk 0] @ tl rho @ [<gk 0|last rho>]) = gk 3"
      using last_rho by simp
  qed
qed

subsection \<open>Non-vacuity and the end-to-end over-approximation\<close>

text \<open>The explicit witness is non-empty and its terminal \<open>G\<close> is the concrete \<open>3\<close>.\<close>

theorem rdiv_twfr_witness_reaches_main_cont:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot tr \<and> tr \<noteq> [] \<and> last tr ''G'' = 3"
proof -
  obtain tr where w: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot tr" and l: "last tr = gk 3"
    using wit_main by blast
  have "tr \<noteq> []" by (rule twfr_nonempty[OF w])
  moreover have "last tr ''G'' = 3" using l by simp
  ultimately show ?thesis using w by blast
qed

text \<open>\<^bold>\<open>End-to-end, non-vacuous.\<close>  There is a concrete \<^const>\<open>twfr\<close> run of the shipped
  \<^const>\<open>rdiv_cfg\<close> reaching \<open>main\<close>'s continuation (node 11, context \<^const>\<open>bot\<close>) whose terminal
  \<open>G\<close> is soundly contained in the executable interval analysis's slot there (\<open>[3,3]\<close>).  The
  witness exhibits a genuine inhabitant (\<open>G = 3\<close>), so the per-coordinate soundness is not
  vacuous.\<close>

theorem rdiv_witness_G_over_approximated:
  "\<exists>tr. twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma (rdiv_sg (Inl (11, bot)) ''G'')"
proof -
  obtain tr where w: "twfr rdiv_enterc rdiv_combc rdiv_cfg 8 bot 11 bot tr"
      and l: "last tr = gk 3"
    using wit_main by blast
  have rd: "last tr ''G'' \<in> gamma (rdiv_sg (Inl (11, bot)) ''G'')"
    using l rdiv_analysis_G_sound_at_main_cont by simp
  show ?thesis by (rule twfr_reach_read[OF w rd])
qed

end
