theory Exec_Sign_Cmp_Seed_Enter
  imports Exec_Sign_Cmp_RRead_Split
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

lemma increment_in_gamma: "1 \<in> gamma_sign SNonNeg" "1 \<notin> gamma_sign SZero"
  by simp_all

text \<open>
  \<^bold>\<open>Verdict.\<close>  The refactor works on the go/no-go program.  Seeding the callee-entry
  local from the context (\<open>side_cfg_T_eff_cmp_seed_st\<close> with \<^const>\<open>restrict_global_st\<close>)
  puts the caller's globals into the callee \<^emph>\<open>local\<close> slot --- Goblint's \<open>sidel
  (FunctionEntry f, fc) v\<close> --- so the clean transfer \<open>f(local)\<close> reads them without
  consulting the published \<open>Inr\<close> slot, and the result is sound where the unseeded
  clean transfer was not.  The context is unchanged (still the precise point
  \<open>{G:SZero}\<close>), so Stage-1 precision is preserved.  Existing runs are untouched:
  \<open>seed_generalises\<close> recovers the shipped generator as the constant-seed instance.

  \<^bold>\<open>Remaining obligation (next stage).\<close>  This is an executable go/no-go witness, not
  yet a proof.  The seeded clean transfer's soundness is inherently
  \<^emph>\<open>context-relative\<close>: the entry local carries the \<^emph>\<open>precise\<close> per-context global
  (sharper than the flow-insensitive \<open>Inr\<close> slot, which \<open>clean_eq_retain_if_local_dominates\<close>
  does not cover), so the soundness statement is against the context-sliced
  \<^const>\<open>cfg_collect_ctx\<close>, not flat \<^const>\<open>cfg_collect\<close>.  The full proof --- a seeded
  analogue of \<^const>\<open>sound_effectful_transfer\<close> discharged from the entry invariant
  \<open>entry-local \<sqsupseteq> globals(context)\<close> --- is the next slice; the retain (\<open>\<squnion> g\<close>)
  analyzer remains the sound shipped baseline until then.
\<close>

end
