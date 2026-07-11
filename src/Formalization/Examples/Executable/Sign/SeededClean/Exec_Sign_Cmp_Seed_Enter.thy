theory Exec_Sign_Cmp_Seed_Enter
  imports Exec_Sign_Cmp_RRead_Split Twfr_Reach_Read
begin

section \<open>Goblint-faithful enter: seed the callee-entry local from the context\<close>

text \<open>
  Stage 2 established that \<^const>\<open>clean_edge_tree_st\<close> (dropping the published-global
  read \<open>\<squnion> g\<close>) is unsound because the callee-entry \<^emph>\<open>local\<close> slot does not contain
  the caller's globals.  This theory attacks the cause rather than the symptom: it
  makes \<open>enter\<close> establish the correct callee-entry local so the transfer no longer
  needs \<open>\<squnion> g\<close>.

  \<^bold>\<open>Where the globals are lost (verified).\<close>  In \<^const>\<open>side_cfg_T_eff_cmp_st\<close> the
  callee-entry unknown \<open>(v, c)\<close> is a frame entry (\<^const>\<open>is_frame_entry\<close>, it has an
  \<^const>\<open>EA_Enter\<close> predecessor).  Its seed is the constant \<open>fresh_frame_st\<close> and the
  enter edge is filtered out (\<^const>\<open>non_enter_predecessor_list\<close>).  For sign,
  \<^const>\<open>fresh_frame_sign\<close> sets globals to \<open>\<bottom>\<close> --- so the callee-entry local carries
  no globals; they are routed to the flow-insensitive \<open>Inr\<close> slot instead, and the
  transfer recovers them with \<open>\<squnion> g\<close>.

  \<^bold>\<open>Goblint's enter.\<close>  \<open>Spec.enter man lv f args\<close> returns the callee \<open>D.t\<close> \<open>v\<close>
  (globals retained in the store in sequential mode), and \<open>sidel (FunctionEntry f,
  fc) v\<close> seeds the callee-entry \<^emph>\<open>local\<close> \<open>(node, context)\<close> unknown with \<open>v\<close>.  The
  callee then reads globals from its own \<open>D.t\<close> --- no separate flow-insensitive
  read.  Our seed must therefore put the caller's globals into the callee-entry
  local; the context \<open>c\<close> (like Goblint's \<open>fc\<close>) is derived from the enter state and
  already encodes those globals.
\<close>

subsection \<open>The seeded generator generalises the constant-frame generator\<close>

text \<open>
  The minimal change: replace the constant frame seed \<open>fresh_frame_st :: 'a st\<close>
  with a context-dependent \<open>frame_seed :: 'c \<Rightarrow> 'a st\<close>.  Everything else is
  identical, so the existing generator is the constant instance
  (\<open>seed_generalises\<close>) and every theorem about \<^const>\<open>side_cfg_T_eff_cmp_st\<close>
  transfers for free.
\<close>

text \<open>The seeded generator \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> and
  @{thm [source] seed_generalises} are domain-generic
  (\<^theory>\<open>Voblint_Analysis.Exec_Cmp_Bridge\<close>, beside
  \<^const>\<open>side_cfg_T_eff_cmp_st\<close>); Sign and interval both instantiate them.\<close>

subsection \<open>Why the seed removes the need for the published-global read\<close>

text \<open>
  The abstract principle: the clean and retain transfers coincide exactly when the
  local slot already dominates the published global --- then \<open>\<squnion> g\<close> is redundant.
  The seed's job is to establish that domination at the callee entry.
\<close>

lemma clean_eq_retain_if_local_dominates:
  assumes "sg (Inr ()) \<le> sg (Inl u)"
  shows "etf_full (clean_edge_tree f u) sg = etf_full (retain_edge_tree f u) sg"
  using assms by (simp add: etf_full_clean_edge_tree etf_full_retain_edge_tree sup.absorb1)

text \<open>
  The faithful seed injects exactly the context's globals: \<^const>\<open>restrict_global_st\<close>
  is idempotent, so seeding a callee at context \<open>c = restrict_global_st (caller)\<close>
  with \<open>restrict_global_st c\<close> delivers precisely the caller's flow-sensitive globals
  to the entry local.
\<close>

lemma faithful_seed_idem: "restrict_global_st (restrict_global_st ctx) = restrict_global_st ctx"
  by (rule restrict_global_st_idem)

subsection \<open>Executable: the seed makes the clean transfer sound\<close>

text \<open>
  The seeded generator on \<open>prog2\<close> (\<open>f(){G:=G+1}; main(){G:=0; f()}\<close>, the Stage-2
  counterexample), with the \<^emph>\<open>clean\<close> transfer and the R_read combine, and the
  faithful seed \<^const>\<open>restrict_global_st\<close>.
\<close>

definition seed_clean_sol :: "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "seed_clean_sol = TD_side_always_join_Interp_solve
     (side_cfg_T_eff_cmp_seed_st id (\<lambda>c cc ex. kgen_combine_rread cc ex c)
        restrict_global_st cfg2 sign_etf_clean_st bot cinit_sign_st) (cfg_exit cfg2, bot)"

lemma seed_clean_runs: "fst seed_clean_sol \<noteq> {}"
  unfolding seed_clean_sol_def cfg2_def prog2_def kgen_ec_def kgen_combine_rread_def
    sign_etf_clean_st_def clean_edge_tree_st_def side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>
  The three soundness-facing facts, \<open>by eval\<close>: with the seed the callee-entry local
  carries the caller's global (\<open>G = SZero\<close>), the clean transfer \<^emph>\<open>reads that local\<close>
  and computes the increment (\<open>G:=G+1\<close> gives \<open>SPos\<close> at the callee exit --- where the
  \<^emph>\<open>unseeded\<close> clean run left it \<open>SBot\<close>, \<open>clean2_loses_increment_retain_keeps\<close>), and
  the observed global at \<open>main\<close>'s exit is \<^const>\<open>SNonNeg\<close> --- it captures the concrete
  \<open>G = 1\<close>, so the clean transfer is now sound here.
\<close>

lemma seed_clean_sound_on_prog2:
  "lookup_st (snd seed_clean_sol (Inl (0, Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd seed_clean_sol (Inl (1, Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SPos
   \<and> lookup_st (snd seed_clean_sol (Inr (bot::sign st))) ''G'' = SNonNeg"
  unfolding seed_clean_sol_def cfg2_def prog2_def kgen_ec_def kgen_combine_rread_def
    sign_etf_clean_st_def clean_edge_tree_st_def side_cfg_T_eff_cmp_seed_st_def by eval

subsection \<open>A concrete twfr witness and the per-coordinate soundness\<close>

text \<open>The callee assignment edge \<open>0 \<to> 1\<close> (\<open>f\<close>'s \<open>G := G + 1\<close>), by \<open>eval\<close>.\<close>

lemma seed_e_0_1:
  "(0, EA_Assign ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)), 1) \<in> edges cfg2"
  unfolding cfg2_def prog2_def by eval

text \<open>The callee frame of the activation is opened by \<^const>\<open>twfr\<close>'s \<open>start\<close> at \<open>f\<close>'s entry
  (node 0) in the seeded context, executes \<open>G := G + 1\<close> reading the seeded \<open>G = 0\<close> and reaches
  the callee exit (node 1) with \<open>G = 1\<close>.  The store is the shared \<^const>\<open>gk\<close> family.\<close>

lemma seed_wit:
  "twfr enterc combc cfg2 0 (Abs_st (SBot, SBot, [(''G'', SZero)])) 1
     (Abs_st (SBot, SBot, [(''G'', SZero)])) [gk 0, gk 1]"
proof -
  have w0: "twfr enterc combc cfg2 0 (Abs_st (SBot, SBot, [(''G'', SZero)])) 0
              (Abs_st (SBot, SBot, [(''G'', SZero)])) [gk 0]"
    by (rule twfr.start)
  show ?thesis using twfr.intra[OF seed_e_0_1 _ w0] by (simp add: step_assign_incr)
qed

text \<open>\<^bold>\<open>Per-coordinate soundness.\<close>  A concrete \<^const>\<open>twfr\<close> execution reaches the callee exit
  and its terminal \<open>G\<close> lies in the concretisation of the analyzer's slot there --- the slot
  is \<^const>\<open>SPos\<close> (\<open>seed_clean_sound_on_prog2\<close>) and \<open>1 \<in> gamma_sign SPos\<close>.  Non-vacuous: the
  concrete increment is a genuine member; contrast the flow-insensitive \<^const>\<open>Inr\<close> global
  \<^const>\<open>SNonNeg\<close>, which also admits \<open>1\<close>.\<close>

theorem seed_wit_sound:
  "\<exists>tr. twfr enterc combc cfg2 0 (Abs_st (SBot, SBot, [(''G'', SZero)])) 1
          (Abs_st (SBot, SBot, [(''G'', SZero)])) tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma_sign (lookup_st
          (snd seed_clean_sol (Inl (1, Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'')"
proof -
  have rd: "last [gk 0, gk 1] ''G'' \<in> gamma_sign (lookup_st
              (snd seed_clean_sol (Inl (1, Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'')"
    using seed_clean_sound_on_prog2 by simp
  show ?thesis by (rule twfr_reach_read[OF seed_wit rd])
qed

text \<open>
  \<^bold>\<open>Verdict.\<close>  The refactor works on the go/no-go program.  Seeding the callee-entry
  local from the context (\<open>side_cfg_T_eff_cmp_seed_st\<close> with \<^const>\<open>restrict_global_st\<close>)
  puts the caller's globals into the callee \<^emph>\<open>local\<close> slot --- Goblint's \<open>sidel
  (FunctionEntry f, fc) v\<close> --- so the clean transfer \<open>f(local)\<close> reads them without
  consulting the published \<open>Inr\<close> slot, and the result is sound where the unseeded
  clean transfer was not.  The context is unchanged (still the precise point
  \<open>{G:SZero}\<close>), so Stage-1 precision is preserved.  Existing runs are untouched:
  \<open>seed_generalises\<close> recovers the shipped generator as the constant-seed instance.

  \<^bold>\<open>Per-coordinate soundness (proved).\<close>  A concrete \<^const>\<open>twfr\<close> execution reaches the
  callee exit in the seeded context and its terminal \<open>G = 1\<close> lies in the analyzer's slot
  \<^const>\<open>SPos\<close> there (\<open>seed_wit_sound\<close>), so the seeded clean transfer is sound on this run ---
  not merely a go/no-go witness.  The soundness is \<^emph>\<open>context-relative\<close>: the entry local
  carries the \<^emph>\<open>precise\<close> per-context global (sharper than the flow-insensitive \<open>Inr\<close> slot,
  which \<open>clean_eq_retain_if_local_dominates\<close> does not cover), so the statement is against the
  context-sliced slot, not the flat one.  The generic context-sliced soundness this run
  instances is the seeded analogue of \<^const>\<open>sound_effectful_transfer\<close>; the retain (\<open>\<squnion> g\<close>)
  analyzer remains the sound shipped baseline for the flow-insensitive read.
\<close>

end
