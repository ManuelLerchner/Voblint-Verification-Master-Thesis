theory Exec_Sign_Cmp_RRead_Split
  imports Exec_Sign_Cmp_Keyed_Retain_EnterMono Voblint_Analysis.Clean_RRead_Sound
begin

section \<open>The D/G/C read split: R_read / G_read / Obs\<close>

text \<open>\<^bold>\<open>Role: regression / counterexample.\<close> The headline \<open>clean_transfer_unsound\<close>
  intentionally proves that the naive clean transfer is \<^emph>\<open>not\<close> sound, motivating the
  R_read boundary.  A guardrail, not a soundness spine.\<close>
text \<open>
  The three reads the Goblint \<open>Spec.context\<close> boundary distinguishes already exist
  as constants in the keyed stack; this theory makes the split explicit and pins
  down --- machine-checked --- where the \<open>fctx\<close> obstruction of
  \<open>Exec_Sign_Cmp_Keyed_Retain_EnterMono\<close> actually lives.

    \<^item> \<^bold>\<open>R_read\<close> = \<^const>\<open>route_read_cmp\<close> \<open>sg (v,ctx) = sg (Inl (v,ctx))\<close> --- the local
      routing slot, read for context selection (Goblint's \<open>man.local\<close> D.t).
    \<^item> \<^bold>\<open>G_read\<close> = \<^const>\<open>glob_env_cmp\<close> \<open>gcmp ctx sg\<close> --- the published global read
      (Goblint's \<open>man.global\<close> G.t).
    \<^item> \<^bold>\<open>Obs\<close> = \<^const>\<open>side_env_cmp\<close> = R_read \<open>\<squnion>\<close> G_read --- the semantic observation
      read the soundness conclusion is stated against.

  The current \<open>ENTER_MONO\<close> quantifies its entering store over \<^bold>\<open>Obs\<close>; the
  Goblint-faithful routing decision reads \<^bold>\<open>R_read\<close> only.
\<close>

lemma obs_is_rread_join_gread:
  "side_env_cmp gcmp sg (v, ctx) = route_read_cmp sg (v, ctx) \<squnion> glob_env_cmp gcmp ctx sg"
  unfolding side_env_cmp_def route_read_cmp_def by simp

lemma rread_le_obs:
  "route_read_cmp sg (cl, ctx) \<le> side_env_cmp gcmp sg (cl, ctx)"
  unfolding side_env_cmp_def route_read_cmp_def by simp

subsection \<open>ENTER_MONO over R_read is a sound relaxation of ENTER_MONO over Obs\<close>

text \<open>
  Because \<open>Obs = R_read \<squnion> G_read \<ge> R_read\<close>, the R_read concretisation is contained
  in the Obs concretisation.  Hence the R_read variant of \<open>ENTER_MONO\<close> quantifies
  over a \<^emph>\<open>smaller\<close> store set: it is implied by --- strictly weaker than --- the
  current Obs obligation.  The read split can therefore only relax the routing
  obligation, never strengthen it; migrating the kernel to route over R_read is
  the safe direction.
\<close>

lemma enter_mono_rread_of_obs:
  assumes OBS: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_cmp gcmp sg (cl, ctx)\<rbrakk>
                  \<Longrightarrow> cmp (entdg s) (rt cl ctx (route_read_cmp sg (cl, ctx)))"
  assumes s: "s \<in> \<lbrakk>route_read_cmp sg (cl, ctx)\<rbrakk>"
  shows "cmp (entdg s) (rt cl ctx (route_read_cmp sg (cl, ctx)))"
proof -
  have "\<lbrakk>route_read_cmp sg (cl, ctx)\<rbrakk> \<subseteq> \<lbrakk>side_env_cmp gcmp sg (cl, ctx)\<rbrakk>"
    by (rule gamma_state_mono[OF rread_le_obs])
  with s show ?thesis by (blast intro: OBS)
qed

section \<open>The read-site split alone does not dissolve the obstruction\<close>

text \<open>
  Restating \<open>ENTER_MONO\<close> over R_read is necessary but not sufficient for the
  \<^emph>\<open>retain\<close> run: its local slot is \<^emph>\<open>already\<close> polluted by the flow-insensitive
  global, at the transfer (write) site --- upstream of any read.  The retain
  transfer folds the published global \<open>sg (Inr ())\<close> into the local at \<^emph>\<open>every\<close>
  edge:
\<close>

lemma retain_transfer_remerges_global:
  "eq (retain_edge_tree_st f) u sg = f (sg (Inl u) \<squnion> sg (Inr ()))"
  by (rule traverse_retain_edge_tree_st)

text \<open>
  So a precise pre-call local is coarsened by the very next edge.  In the retain
  run of \<open>kgen_cfg\<close>, the local \<open>G\<close> is a point \<^const>\<open>SZero\<close> after \<open>G := 0\<close> (pp 3)
  but the intervening \<^const>\<open>EA_Nop\<close> re-merges the flow-insensitive slot
  (\<^const>\<open>SNonNeg\<close>), so at the actual call site (pp 4, the caller \<open>cc\<close> of the
  combine) the local is already \<^const>\<open>SNonNeg\<close> --- no read-site choice recovers a
  point.
\<close>

lemma retain_caller_local_polluted:
  "lookup_st (snd kgen_retain_solution (Inl (4, bot::sign st))) ''G'' = SNonNeg
   \<and> lookup_st (snd kgen_retain_solution (Inl (3, bot::sign st))) ''G'' = SZero"
  unfolding kgen_retain_solution_def kgen_retain_eqs_def kgen_cfg_def kgen_ec_def
  by eval

section \<open>The write-site split: sequential-faithful transfer + R_read combine\<close>

text \<open>
  The split must move to the \<^emph>\<open>write\<close> and \<^emph>\<open>selection\<close> sites.  \<open>clean_edge_tree_st\<close>
  is the sequential-Goblint-faithful transfer: it keeps globals flow-sensitively
  in the local (retained in the \<open>Answer\<close> slot, published to the \<open>Inr\<close> slot) but does
  \<^emph>\<open>not\<close> read the published global back into the local at each edge (\<open>res = f su\<close>,
  not \<open>f (su \<squnion> g)\<close>).  \<open>kgen_combine_rread\<close> then selects the callee context from
  the \<^emph>\<open>local\<close> \<open>sc\<close> (R_read) alone, not from \<open>sc \<squnion> g\<close> --- exactly Goblint computing
  \<open>context\<close> from the enter-produced local D.t.
\<close>

text \<open>The clean executable edge \<^const>\<open>clean_edge_tree_st\<close> is domain-generic
  (\<^theory>\<open>Voblint_Analysis.Exec_Bridge\<close>); Sign only names the instance.\<close>

definition sign_etf_clean_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_clean_st = \<lparr>
    etf_st_nop        = clean_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. clean_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. clean_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. clean_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = clean_edge_tree_st (sign_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

definition kgen_combine_rread :: "pp \<Rightarrow> pp \<Rightarrow> sign st \<Rightarrow> (pp \<times> sign st, sign st, sign st) strategy_tree" where
  "kgen_combine_rread cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let callee = kgen_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st sc \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

definition kgen_rread_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_rread_eqs = side_cfg_T_eff_cmp_st id
                      (\<lambda>c cc ex. kgen_combine_rread cc ex c)
                      kgen_cfg sign_etf_clean_st bot bot cinit_sign_st"

definition kgen_rread_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_rread_solution = TD_side_always_join_Interp_solve kgen_rread_eqs (cfg_exit kgen_cfg, bot)"

lemma kgen_rread_runs: "fst kgen_rread_solution \<noteq> {}"
  unfolding kgen_rread_solution_def kgen_rread_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def by eval

subsection \<open>Obstruction dissolved: distinct point contexts\<close>

text \<open>
  Under the write-site split the caller-local slots are points --- \<^const>\<open>SZero\<close> at
  the first call site (pp 4), \<^const>\<open>SPos\<close> at the second (pp 7) --- so routing off
  the local sees the precise per-call-site global.
\<close>

lemma kgen_rread_caller_locals_points:
  "lookup_st (snd kgen_rread_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd kgen_rread_solution (Inl (7, bot::sign st))) ''G'' = SPos"
  unfolding kgen_rread_solution_def kgen_rread_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def by eval

text \<open>
  Consequently the two value-distinct activations no longer share a context: the
  callee context slots are the \<^emph>\<open>points\<close> \<open>{G:SZero}\<close> and \<open>{G:SPos}\<close>, where the
  retain run merged both into the single coarse \<^const>\<open>SNonNeg\<close> slot
  (\<open>retain_keyed_merged_G\<close>).
\<close>

lemma kgen_rread_contexts_points:
  "lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos"
  unfolding kgen_rread_solution_def kgen_rread_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def by eval

text \<open>
  These two point contexts separate the values the obstruction's coarse read
  conflated: \<open>0\<close> lands in the \<open>{G:SZero}\<close> context, \<open>2\<close> in the \<open>{G:SPos}\<close> context.
  Each context's read is entry-digest-uniform --- the converse of
  \<open>read_admits_two_point_classes\<close> --- so \<open>ENTER_MONO\<close> over R_read holds where the
  Obs read failed.
\<close>

lemma rread_contexts_separate_values:
  "0 \<in> gamma_sign SZero \<and> 2 \<notin> gamma_sign SZero
   \<and> 2 \<in> gamma_sign SPos \<and> 0 \<notin> gamma_sign SPos"
  by simp

text \<open>
  \<^bold>\<open>Stage-1 verdict.\<close>  The read-split at the \<^emph>\<open>read\<close> site (\<open>ENTER_MONO\<close> over R_read
  vs Obs) is a sound relaxation (\<open>enter_mono_rread_of_obs\<close>) but cannot by itself
  dissolve the \<open>fctx\<close> obstruction, because the retain local slot is polluted at the
  transfer (\<open>retain_caller_local_polluted\<close>).  The obstruction has two write-site
  sources, both a re-merge of the published global \<open>g = sg (Inr ctx)\<close>: the transfer
  \<open>f (su \<squnion> g)\<close> and the combine's context input \<open>sc \<squnion> g\<close>.  Applying the split at
  both --- \<^const>\<open>clean_edge_tree_st\<close> and \<^const>\<open>kgen_combine_rread\<close> --- yields distinct
  point contexts and dissolves the obstruction (\<open>kgen_rread_contexts_points\<close>).

  \<^bold>\<open>Next go/no-go (Stage 2).\<close>  The remaining obligation is \<^emph>\<open>soundness\<close> of the
  write-site split: is dropping \<open>\<squnion> g\<close> sound against \<^const>\<open>cfg_collect\<close>?  Stage 2
  (below) answers \<^emph>\<open>no\<close> for this equation-system architecture, so the kernel
  \<open>ENTER_MONO\<close>/\<open>CMP_SOUND\<close> are \<^emph>\<open>not\<close> migrated to R_read.
\<close>

section \<open>Stage 2: the clean transfer is unsound\<close>

text \<open>
  Stage 1 dissolved the \<^emph>\<open>precision\<close> obstruction by dropping the published-global
  re-read from the transfer (\<open>res = f su\<close>, not \<open>f (su \<squnion> g)\<close>).  The Stage-2
  question is \<^emph>\<open>soundness\<close>, and the answer is negative: the \<open>\<squnion> g\<close> is the
  load-bearing channel by which globals reach the transfer.  In this equation
  system globals live in the flow-insensitive \<open>Inr\<close> slot; the combine seeds a
  callee's globals \<^emph>\<open>there\<close> (via \<open>Side\<close>), and the enter edge is filtered from the
  intra fold, so a callee-entry \<^emph>\<open>local\<close> slot carries \<open>\<bottom>\<close> on globals.  Both
  \<^const>\<open>unit_edge_tree\<close> and \<^const>\<open>retain_edge_tree\<close> read \<open>su \<squnion> g\<close>; only the clean
  transfer omits it, and therefore cannot see any global a procedure reads.

  This is not the Goblint \<^emph>\<open>sequential\<close> discipline (where globals sit
  flow-sensitively in the local \<open>D.t\<close> and \<open>enter\<close> copies them into the callee
  \<open>D.t\<close>).  Our seed routes globals to the flow-insensitive \<open>Inr\<close> slot --- the
  earlyglobs / multithreaded channel --- so the \<open>\<squnion> g\<close> read is mandatory for
  soundness here.  A clean transfer becomes sound only after co-changing the
  \<open>enter\<close>/seed to deliver globals through the callee \<^emph>\<open>local\<close> slot; that is a
  generator/kernel change, out of scope.
\<close>

subsection \<open>Program-independent refutation: the clean transfer breaks the soundness contract\<close>

text \<open>
  The abstract clean transfer and the exact predicate
  \<^const>\<open>sound_effectful_transfer\<close> the collecting-soundness theorems consume.  The
  assign obligation quantifies the incoming store over
  \<open>\<lbrakk>\<sigma>(Inl u) \<squnion> glob_env \<sigma>\<rbrakk>\<close> (local \<squnion> global), whereas the clean image
  \<open>etf_collecting_full = etf_full \<squnion> glob_env\<close> re-joins only the \<^emph>\<open>old\<close> global; the
  assigned value, computed on the local (where a callee-entry global is \<open>\<bottom>\<close>), is
  dropped.\<close>

text \<open>The clean edge tree and the clean transfer constructor are domain-generic
  (\<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>); Sign only names the instance.\<close>

definition sign_etf_clean :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf_clean = clean_etf_of_transfer sign_tf"

text \<open>Witness: a state whose global slot carries \<open>G = SZero\<close> while the local
  routing slot has \<open>G = \<bottom>\<close> --- exactly the callee-entry shape the seed produces.\<close>

definition cw :: "nat + unit \<Rightarrow> sign abs_state" where
  "cw = (\<lambda>k. case k of Inl _ \<Rightarrow> (\<lambda>x. if x = ''G'' then SBot else STop)
                     | Inr _ \<Rightarrow> (\<lambda>x. if x = ''G'' then SZero else SBot))"

lemma sbot_bot: "(SBot::sign) = \<bottom>" by eval

lemma sign_joins: "SBot \<squnion> SZero = SZero" "STop \<squnion> SBot = STop" by eval+

lemma cw_inr: "inr_slot_locals_bot cw"
  by (auto simp: inr_slot_locals_bot_def cw_def is_global_def sbot_bot)

lemma cw_mem: "(\<lambda>_. 0) \<in> \<lbrakk>cw (Inl 0) \<squnion> glob_env cw\<rbrakk>"
  by (auto simp: gamma_state_def glob_env_unit cw_def sup_fun_def sign_joins)

lemma cw_image_G:
  "etf_collecting_full (etf_assign sign_etf_clean ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)) u) cw ''G'' = SZero"
proof -
  have tf: "tf_assign sign_tf ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1))
              (\<lambda>x. if x = ''G'' then SBot else STop) ''G'' = SBot"
    by eval
  show ?thesis
    unfolding sign_etf_clean_def clean_etf_of_transfer_def
    by (simp add: etf_collecting_full_def etf_full_clean_edge_tree glob_env_unit cw_def tf sign_joins)
qed

text \<open>
  The refutation.  A callee-entry state (global \<open>G = SZero\<close> in the published slot,
  \<open>G = \<bottom>\<close> in the local) with a concrete store \<open>G = 0\<close>: the assign \<open>G := G + 1\<close>
  produces \<open>G = 1\<close> concretely, but the clean transfer's collecting image is
  \<open>SZero\<close> (it computed the increment on the local \<open>\<bottom>\<close> and recovered only the old
  global), and \<open>1 \<notin> gamma_sign SZero = {0}\<close>.
\<close>

theorem clean_transfer_unsound: "\<not> sound_effectful_transfer sign_etf_clean"
proof
  assume "sound_effectful_transfer sign_etf_clean"
  then have A: "\<And>\<sigma> u s x e. inr_slot_locals_bot \<sigma> \<Longrightarrow> s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk> \<Longrightarrow>
        s(x := IMP2_Expr.aval e s) \<in> \<lbrakk>etf_collecting_full (etf_assign sign_etf_clean x e u) \<sigma>\<rbrakk>"
    unfolding sound_effectful_transfer_def by blast
  let ?e = "Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)"
  let ?img = "etf_collecting_full (etf_assign sign_etf_clean ''G'' ?e 0) cw"
  have "((\<lambda>_. 0)(''G'' := IMP2_Expr.aval ?e (\<lambda>_. 0))) \<in> \<lbrakk>?img\<rbrakk>"
    by (rule A[OF cw_inr cw_mem])
  moreover have "IMP2_Expr.aval ?e (\<lambda>_. 0) = 1" by simp
  ultimately have M: "((\<lambda>_. 0)(''G'' := 1)) \<in> \<lbrakk>?img\<rbrakk>" by simp
  from M have "\<forall>x. ((\<lambda>_. 0)(''G'' := 1)) x \<in> gamma_sign (?img x)"
    by (simp add: gamma_state_def)
  then have "((\<lambda>_. 0)(''G'' := 1)) ''G'' \<in> gamma_sign (?img ''G'')" by (rule spec)
  then show False by (simp add: cw_image_G)
qed

subsection \<open>Executable manifestation: a callee that reads a global loses it\<close>

text \<open>
  The same failure, executable and end-to-end.  \<open>prog2\<close> is
  \<open>int G; void f() { G := G + 1 } void main() { G := 0; f() }\<close> --- concretely
  \<open>G = 1\<close> at \<open>main\<close>'s exit.  The clean run's observed global there is \<^const>\<open>SZero\<close>
  (\<open>1 \<notin> gamma_sign SZero\<close>), while the sound retain run reports \<^const>\<open>SNonNeg\<close>
  (\<open>1 \<in> gamma_sign SNonNeg\<close>).  \<open>kgen\<close>'s \<open>G := G + G\<close> body only \<^emph>\<open>looked\<close> sound under
  the clean transfer because the seed passed through a fixpoint of \<open>+\<close>; a genuine
  read of \<open>G\<close> exposes the loss.\<close>

definition prog2 :: imp_prog where
  "prog2 = \<lbrakk> int G; void f() { G := G + 1 } void main() { G := 0; f() } \<rbrakk>"

definition cfg2 :: cfg where
  "cfg2 = compile_prog (prog_table prog2) (prog_procs prog2) (prog_main prog2)"

definition clean2_sol :: "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "clean2_sol = TD_side_always_join_Interp_solve
     (side_cfg_T_eff_cmp_st id (\<lambda>c cc ex. kgen_combine_rread cc ex c)
        cfg2 sign_etf_clean_st bot bot cinit_sign_st) (cfg_exit cfg2, bot)"

definition retain2_sol :: "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "retain2_sol = TD_side_always_join_Interp_solve
     (side_cfg_T_eff_cmp_st id (\<lambda>c cc ex. kgen_combine_st cc ex c)
        cfg2 sign_etf_retain_st bot bot cinit_sign_st) (cfg_exit cfg2, bot)"

lemma clean2_loses_increment_retain_keeps:
  "lookup_st (snd clean2_sol (Inr (bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd retain2_sol (Inr (bot::sign st))) ''G'' = SNonNeg"
  unfolding clean2_sol_def retain2_sol_def cfg2_def prog2_def kgen_ec_def
    kgen_combine_rread_def kgen_combine_st_def sign_etf_clean_st_def clean_edge_tree_st_def
    sign_etf_retain_st_def by eval

lemma increment_separates: "1 \<notin> gamma_sign SZero" "1 \<in> gamma_sign SNonNeg"
  by simp_all

text \<open>
  \<^bold>\<open>Stage-2 verdict.\<close>  \<^const>\<open>clean_edge_tree_st\<close> is \<^emph>\<open>unsound\<close>: program-independently
  it violates \<^const>\<open>sound_effectful_transfer\<close> (\<open>clean_transfer_unsound\<close>), and
  executably it drops a callee's global read (\<open>clean2_loses_increment_retain_keeps\<close>).
  The Stage-1 precision fix and this soundness failure are the \<^emph>\<open>same\<close> mechanism:
  reading the published global from the \<open>Inr\<close> slot.  Per the migration go/no-go,
  \<open>ENTER_MONO\<close>/\<open>CMP_SOUND\<close> are \<^bold>\<open>not\<close> migrated to R_read.  The exact missing
  invariant for a sound flow-sensitive-global transfer: the callee-entry \<^emph>\<open>local\<close>
  slot must be seeded with the caller's globals --- which the current filtered
  enter / \<open>Inr\<close>-seed does not establish and cannot without a generator change.
\<close>

end
