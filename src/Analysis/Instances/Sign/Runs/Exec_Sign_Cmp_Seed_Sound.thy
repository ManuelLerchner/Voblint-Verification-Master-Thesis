theory Exec_Sign_Cmp_Seed_Sound
  imports Exec_Sign_Cmp_Seed_Enter
begin

section \<open>Sign instantiates the generic seeded-clean R_read spine\<close>

text \<open>
  Sign is a thin instantiation of the domain-generic seeded-clean spine
  \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>: \<^const>\<open>sign_etf_clean\<close> is
  \<^term>\<open>clean_etf_of_transfer sign_tf\<close>, and the context-sliced soundness theorems
  are the interpretations of the generic ones at @{thm sign_is_sound_transfer}.  The
  five R_read obligations, the flat theorem \<open>clean_cfg_collect_rread\<close>, and the trace
  kernel \<open>clean_ctx_trace_rread\<close> live generically; here we surface the two theorems
  the executable examples consume and the glue lemma the seeded-generator reduction
  needs.
\<close>

lemma apply_etf_sign_etf_clean:
  "apply_etf sign_etf_clean a u = clean_edge_tree (apply_tf sign_tf a) u"
  unfolding sign_etf_clean_def clean_etf_of_transfer_def by (cases a) simp_all

text \<open>Context-sliced collecting soundness for Sign against \<^const>\<open>cfg_collect_ctx\<close>:
  the conclusion is the per-context local slot \<open>sg (Inl (v, ctx))\<close> (R_read).  The seed
  obligations \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> correspond to Goblint \<open>Spec.enter\<close>, \<open>ENTER_MONO\<close>
  to \<open>Spec.context\<close>, and \<open>COMB\<close> to \<open>Spec.combine\<close>.\<close>

lemmas clean_ctx_collect_rread = sound_transfer.clean_ctx_collect_rread[OF sign_is_sound_transfer]

text \<open>Its executable head-digest reduction: the three digest-propagation obligations
  are discharged generically, leaving the seed / context / combine bundle.\<close>

lemmas clean_ctx_collect_rread_head = sound_transfer.clean_ctx_collect_rread_head[OF sign_is_sound_transfer]

section \<open>Executable seeded-clean run on the two-call program\<close>

text \<open>
  The Goblint-faithful spine end to end on \<^const>\<open>kgen_prog\<close>
  (\<open>f(){G:=G+G}; main(){G:=0; f(); G:=1; f()}\<close>): the \<^emph>\<open>seeded\<close> generator
  \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> with the faithful seed \<^const>\<open>restrict_global_st\<close>,
  the \<^emph>\<open>clean\<close> transfer \<^const>\<open>sign_etf_clean_st\<close>, and the R_read combine
  \<^const>\<open>kgen_combine_rread\<close>, fed to the vendored side solver.
\<close>

definition kgen_seed_clean_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_seed_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. kgen_combine_rread cc ex c)
     restrict_global_st kgen_cfg sign_etf_clean_st bot cinit_sign_st"

definition kgen_seed_clean_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_seed_clean_solution = TD_side_always_join_Interp_solve kgen_seed_clean_eqs (cfg_exit kgen_cfg, bot)"

lemma kgen_seed_clean_runs: "fst kgen_seed_clean_solution \<noteq> {}"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>
  The seed puts the caller's global into the callee-entry \<^emph>\<open>local\<close>: the caller-local
  slots at the two call sites (pp 4, pp 7) are the points \<^const>\<open>SZero\<close> and
  \<^const>\<open>SPos\<close> --- the clean transfer read them, not the published slot.
\<close>

lemma kgen_seed_clean_caller_locals:
  "lookup_st (snd kgen_seed_clean_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inl (7, bot::sign st))) ''G'' = SPos"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>The two activations land in separate point contexts \<open>{G:SZero}\<close>, \<open>{G:SPos}\<close>.\<close>

lemma kgen_seed_clean_precision:
  "lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

section \<open>Precision witnesses: the global-derived context split\<close>

text \<open>
  The two-call program \<open>kgen_cfg\<close> calls a procedure at two sites where the global
  \<open>G\<close> holds value-distinct signs.  Under the \<^emph>\<open>retain\<close> run the two activations
  share one keyed context slot, joining to the non-point \<^const>\<open>SNonNeg\<close>
  (\<open>retain_keyed_merged_G\<close>) --- the \<open>fctx\<close> obstruction.  Under the seeded-clean /
  R_read run they land in \<^emph>\<open>separate point contexts\<close> \<open>{G:SZero}\<close> and \<open>{G:SPos}\<close>
  (\<open>kgen_rread_contexts_points\<close>): the global-derived context split the retain read
  could not express.
\<close>

lemma sign_strict_precision: "SZero < SNonNeg" "SPos < SNonNeg" "SZero \<noteq> SPos"
  by eval+

text \<open>
  \<^bold>\<open>Strict precision, machine-backed.\<close>  The seeded-clean context slots are
  \<^emph>\<open>strictly\<close> below the retain merged slot: the first call context reads \<open>G = SZero\<close>,
  the second \<open>G = SPos\<close>, each a point strictly under the retain \<^const>\<open>SNonNeg\<close>.  The
  \<^const>\<open>SNonNeg\<close> obstruction (\<open>read_admits_two_point_classes\<close>) is gone.
\<close>

theorem rread_strictly_sharper_than_retain:
  "lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos
   \<and> lookup_st (snd kgen_retain_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg
   \<and> SZero < SNonNeg \<and> SPos < SNonNeg"
  using kgen_rread_contexts_points retain_keyed_merged_G sign_strict_precision by simp

section \<open>Executable reduction: the intra-edge bound is a generator theorem\<close>

text \<open>
  The kernel's \<open>EDGE_BOUND\<close> is not an \<open>eval\<close> witness --- it follows from the
  \<^emph>\<open>structure\<close> of the seeded generator for \<^emph>\<open>any\<close> post-solution.  The abstract
  seeded generator \<open>side_cfg_T_eff_cmp_seed\<close> (the \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close>
  image over \<^typ>\<open>'a abs_state\<close>): its right-hand side at \<open>(v, ctx)\<close> is the fold
  \<^const>\<open>side_rhs_fold_ctx\<close> of the intra contributions and the combine contributions.
  Because the fold is a join, each intra summand is dominated by it, and a
  \<^const>\<open>part_post_solution\<close> caps it at the local slot.  For the clean transfer the
  intra summand's traverse is exactly \<open>apply_tf sign_tf a\<close> of the \<^emph>\<open>predecessor
  local slot\<close> --- so the kernel's \<open>EDGE_BOUND\<close> falls out with no \<open>'g :: finite\<close> and
  no per-run evaluation.
\<close>


lemma traverse_apply_etf_clean:
  "traverse_rhs (apply_etf sign_etf_clean a u) sg = apply_tf sign_tf a (sg (Inl u))"
  by (simp add: apply_etf_sign_etf_clean clean_edge_tree_def Let_def)

text \<open>The clean intra summand traverses to the base transfer of the predecessor's
  \<^emph>\<open>per-context local\<close> slot --- \<^const>\<open>map_gtree\<close>/\<^const>\<open>map_ltree\<close> only relabel
  unknowns, so no \<open>'g :: finite\<close> global read is involved.\<close>

lemma traverse_intra_clean:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf sign_etf_clean a u))) sg
   = apply_tf sign_tf a (sg (Inl (u, ctx)))"
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree traverse_apply_etf_clean)

lemma edge_in_non_enter_pred:
  assumes "finite (edges g)" and "(u, a, v) \<in> edges g" and "a \<noteq> EA_Enter"
  shows "(u, a) \<in> set (non_enter_predecessor_list g v)"
proof (rule non_enter_predecessor_list_mem[OF _ assms(3)])
  have "(u, a, v) \<in> set (cfg_edges_list g)" using assms(1,2) set_cfg_edges_list by blast
  thus "(u, a) \<in> set (predecessor_list g v)"
    unfolding predecessor_list_def by (force intro: rev_image_eqI)
qed

text \<open>
  \<^bold>\<open>The intra-edge bound, from the post-solution.\<close>  For every non-enter edge
  \<open>(u, a, v)\<close> with \<open>(v, ctx)\<close> solved, the base transfer of the predecessor local slot
  is bounded by the successor local slot --- the kernel's \<open>EDGE_BOUND\<close> hypothesis,
  discharged.  (Enter edges are filtered from the intra fold and covered by the seed,
  a separate obligation.)
\<close>

theorem seeded_clean_edge_bound:
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g sign_etf_clean bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> edges g" and ne: "a \<noteq> EA_Enter"
  shows "apply_tf sign_tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
proof -
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf sign_etf_clean a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
               \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>)"
  have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
    by (rule edge_in_non_enter_pred[OF fin e ne])
  have summand: "map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf sign_etf_clean a u))
                   \<in> set (?intra @ ?comb)"
    using mem by (force intro: rev_image_eqI)
  have "apply_tf sign_tf a (sg (Inl (u, ctx)))
        = traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf sign_etf_clean a u))) sg"
    by (rule traverse_intra_clean[symmetric])
  also have "\<dots> \<le> side_acc_ctx ?acc0 sg (?intra @ ?comb)"
    by (rule traverse_le_side_acc_ctx[OF summand])
  also have "\<dots> = eq (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g sign_etf_clean bot0 s0) (v, ctx) sg"
    by (rule eq_side_cfg_T_eff_cmp_seed[symmetric])
  also have "\<dots> \<le> sg (Inl (v, ctx))"
    using part_post_solution_imp_se_constraint_holds[OF pp cov]
    by (simp add: se_constraint_holds_def)
  finally show ?thesis .
qed

text \<open>
  \<^bold>\<open>Status of the concrete-run reduction.\<close>  \<open>seeded_clean_edge_bound\<close> discharges the
  kernel's \<open>EDGE_BOUND\<close> for every intra edge of any seeded-clean post-solution, with
  no \<open>'g :: finite\<close> and no per-run \<open>eval\<close>.  What remains to feed the concrete
  executable run \<open>kgen_seed_clean_solution\<close> into \<open>clean_ctx_collect_rread\<close>: the
  \<^typ>\<open>sign st\<close>-to-\<^typ>\<open>sign abs_state\<close> transport of its \<^const>\<open>part_post_solution\<close>
  (mirroring \<open>part_post_solution_cmp_st_to_abs_eff\<close> for the seeded generator), the
  enter-edge / \<open>COMB\<close> bounds, and the value-digest \<open>ENTER_MONO\<close>.  The precision
  witnesses (\<open>kgen_seed_clean_precision\<close>, \<open>kgen_seed_clean_caller_locals\<close>) confirm the
  run satisfies these on the two-call program.
\<close>

text \<open>
  \<^bold>\<open>What is certified.\<close>  The clean (Goblint-sequential) transfer, which reads only
  the local slot, is \<^emph>\<open>sound\<close> when soundness is measured against the local read:
  the five per-edge obligations (\<open>clean_rread_*\<close>) hold unconditionally; the flat
  theorem \<open>clean_cfg_collect_rread\<close> lifts them to \<^const>\<open>cfg_collect\<close>; and
  \<open>clean_ctx_collect_rread\<close> gives the context-sensitive statement against
  \<^const>\<open>cfg_collect_ctx\<close> with the conclusion at the per-context local slot
  \<open>sg (Inl (v, ctx))\<close>.  This is the read split the \<open>Keyed_Retain_EnterMono\<close>
  obstruction identified as the fix, and it clears \<^emph>\<open>both\<close> obstructions the retain
  spine hit: no \<open>'g :: finite\<close> quotient (the local read ignores \<open>Inr\<close>), and
  \<open>ENTER_MONO\<close> over the local read (decoupled from the coarse published global).
  The retain (\<open>\<squnion> g\<close>) / \<^const>\<open>side_env_cmp\<close> spine is untouched --- it remains the
  sound conservative baseline for the Obs conclusion.

  \<^bold>\<open>The entry invariant, explicitly.\<close>  \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> are exactly
  \<^emph>\<open>callee-entry local \<sqsupseteq> context-specific caller stores\<close> (globals included): every
  store reaching the entry in context \<open>ctx\<close> lies in \<open>\<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>\<close>.
  The Goblint-faithful seed \<open>side_cfg_T_eff_cmp_seed_st\<close> with
  \<^const>\<open>restrict_global_st\<close> establishes it per context
  (\<open>seed_clean_sound_on_prog2\<close>).  \<open>EDGE_BOUND\<close> then propagates it reading only the
  local, and \<open>clean_ctx_collect_rread\<close> concludes soundness --- \<^emph>\<open>without\<close> the
  \<open>local \<squnion> global\<close> recovery.

  \<^bold>\<open>Remaining obligation.\<close>  \<open>EDGE_BOUND\<close> (intra) is now a generator theorem
  (\<open>seeded_clean_edge_bound\<close>).  What remains to feed the concrete executable run into
  \<open>clean_ctx_collect_rread\<close>: the \<^typ>\<open>sign st\<close>-to-\<^typ>\<open>sign abs_state\<close> transport of the
  run's \<^const>\<open>part_post_solution\<close>, the enter-edge / \<open>COMB\<close> bounds, and the
  value-digest \<open>ENTER_MONO\<close> --- the precision witnesses
  (\<open>kgen_rread_contexts_points\<close>, \<open>seed_clean_sound_on_prog2\<close>) already show the run
  meets them on the two-call program.
\<close>

end
