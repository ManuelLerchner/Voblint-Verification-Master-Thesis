theory Exec_Sign_Cmp_Keyed_Retain_Run
  imports Exec_Sign_Cmp_Keyed_Gen_Run
begin

section \<open>Executable keyed-global generator run on the retain path (sign)\<close>

text \<open>
  The retain sibling of \<open>Exec_Sign_Cmp_Keyed_Gen_Run\<close>.  It reuses the two-call
  program \<^const>\<open>kgen_cfg\<close> and the value-derived combine \<^const>\<open>kgen_combine_st\<close>, but
  runs the vendored side solver over the executable \<^emph>\<open>retain\<close> transfer
  \<^const>\<open>retain_edge_tree_st\<close>: intra edges keep the written global in the local
  \<open>Answer\<close> instead of erasing it.  This exercises the executable retain bridge and the
  R_read discipline: the combine selects the callee context from the retained local
  global, not the flow-insensitive joined global slot.
\<close>

subsection \<open>The executable retain transfer\<close>

definition sign_etf_retain_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_retain_st = \<lparr>
    etf_st_nop        = retain_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. retain_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. retain_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. retain_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = retain_edge_tree_st (sign_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

lemma sign_etf_retain_st_edge_tree:
  "apply_etf_st sign_etf_retain_st a u = retain_edge_tree_st (sign_tf_st a) u"
  unfolding sign_etf_retain_st_def by (cases a) simp_all

lemma sign_etf_retain_st_combine_tree:
  "etf_combine_st sign_etf_retain_st cc ex = unit_combine_tree_st cc ex"
  unfolding sign_etf_retain_st_def by simp

lemma side_rg_sign_etf_retain_st_edge: "side_rg (apply_etf_st sign_etf_retain_st a u)"
  by (simp add: sign_etf_retain_st_edge_tree side_rg_retain_edge_tree_st)

subsection \<open>The generated retain solver run\<close>

definition kgen_retain_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_retain_eqs = side_cfg_T_eff_cmp_st id
                       (\<lambda>c cc ex. kgen_combine_st cc ex c)
                       kgen_cfg sign_etf_retain_st bot bot cinit_sign_st"

definition kgen_retain_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_retain_solution = TD_side_always_join_Interp_solve kgen_retain_eqs (cfg_exit kgen_cfg, bot)"

text \<open>The retain generator solves the program: the solved unknown set is non-empty.\<close>
lemma kgen_retain_runs: "fst kgen_retain_solution \<noteq> {}"
  unfolding kgen_retain_solution_def kgen_retain_eqs_def kgen_cfg_def kgen_ec_def by eval

subsection \<open>The retain output is a partial post-solution\<close>

lemma kgen_retain_solve_c_some:
  "TD_side_always_join_Interp_solve_c kgen_retain_eqs (cfg_exit kgen_cfg, bot) \<noteq> None"
  unfolding kgen_retain_eqs_def kgen_cfg_def kgen_ec_def by eval

lemma kgen_retain_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(sign st) TYPE(sign st)
     kgen_retain_eqs (cfg_exit kgen_cfg, bot)"
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using kgen_retain_solve_c_some by simp

lemma kgen_retain_part_post_solution:
  "part_post_solution kgen_retain_eqs (cfg_exit kgen_cfg, bot)
     (snd kgen_retain_solution) (fst kgen_retain_solution)"
  using TD_side_always_join_Interp.partial_post_solution
      [OF kgen_retain_solve_dom, of "fst kgen_retain_solution" "snd kgen_retain_solution"]
  unfolding kgen_retain_solution_def by simp

text \<open>
  Status of the keyed invariant.  The abstract witness
  @{thm [source] kgen_retain_keyed_generator_sound_if_exact_fixpoint} \<^emph>\<open>reduces\<close> the
  slot-relating \<^const>\<open>inl_glob_le_keyed_ctx\<close> to solver exactness: via
  @{thm [source] inl_glob_le_keyed_ctx_full} it derives the invariant from an exact
  \<^const>\<open>part_solution\<close> plus the \<open>\<bottom>\<close>-init default outside the solved set.  This is a
  reframing, not a discharge: \<^const>\<open>part_solution\<close> is \<^emph>\<open>not\<close> what the vendored side
  solver provides.  The always-join solver (\<open>TD_side_always_join_Interp\<close>) interprets
  locale \<open>TD_side_upd_rule\<close>, which proves only \<^const>\<open>part_post_solution\<close> (overapproximation)
  and applies local warrowing at widening points --- exact \<^const>\<open>part_solution\<close> is
  false in general and its preservation lemmas live in the un-interpreted \<open>TD_side\<close>
  locale.  Exactness holds only operationally on this warrowing-free (acyclic) run ---
  and here that is now \<^emph>\<open>proved\<close>, not asserted: \<open>kgen_retain_part_solution\<close> (below)
  upgrades the vendored \<^const>\<open>part_post_solution\<close> to an exact \<^const>\<open>part_solution\<close> via
  the decidable reverse-inequality \<open>eval\<close> check \<open>kgen_retain_exact_eqs\<close>.

  What remains to wire this exact run into the abstract soundness witness
  @{thm [source] kgen_retain_keyed_generator_sound_if_exact_fixpoint} is the generic
  executable-to-abstract bridge: relate the concrete \<open>_st\<close> solution to the abstract
  \<^const>\<open>part_solution\<close> over \<^typ>\<open>sign abs_state\<close> (via \<^const>\<open>fun_of_st\<close>), and reify the
  finitely-many occurring contexts into the \<^class>\<open>finite\<close> key type the abstract
  keyed theorem requires (this run keys on \<^typ>\<open>sign st\<close>, which is not \<^class>\<open>finite\<close>).
  Both are pre-existing and shared with the publish run \<open>Exec_Sign_Cmp_Keyed_Gen_Run\<close>;
  neither is retain-specific.
\<close>

subsection \<open>Precision: the local slot retains the flow-sensitive global\<close>

text \<open>
  The retain-specific payoff, machine-checked.  Under the retain transfer the callee
  activation's local slot carries the written global \<open>G\<close> (\<^const>\<open>SPos\<close> for the second
  call), where the publish run of \<open>Exec_Sign_Cmp_Keyed_Gen_Run\<close> erases it to
  \<^const>\<open>SBot\<close>.  This is the R_read precision the retain discipline recovers: context
  selection reading the local slot sees the precise per-call-site global.
\<close>

lemma kgen_retain_local_keeps_global:
  "\<exists>vk \<in> fst kgen_retain_solution.
     lookup_st (snd kgen_retain_solution (Inl vk)) ''G'' \<noteq> SBot"
  unfolding kgen_retain_solution_def kgen_retain_eqs_def kgen_cfg_def kgen_ec_def
  by eval

text \<open>
  The contrast: the publish run of \<open>Exec_Sign_Cmp_Keyed_Gen_Run\<close> erases \<open>G\<close> from
  \<^emph>\<open>every\<close> local slot --- the \<open>inl_slot_globals_bot_ctx\<close> invariant --- so a context
  read off the local slot there sees nothing.  Retain is the strict refinement that
  makes the R_read discipline informative.
\<close>
lemma kgen_publish_local_erases_global:
  "\<forall>vk \<in> fst kgen_solution. lookup_st (snd kgen_solution (Inl vk)) ''G'' = SBot"
  unfolding kgen_solution_def kgen_eqs_def kgen_cfg_def kgen_ec_def
  by eval

text \<open>
  The per-run exactness certificate.  The vendored always-join solver exposes only
  \<^const>\<open>part_post_solution\<close> (\<open>eq \<le> \<sigma>(Inl u)\<close>), but this run is warrowing-free, so at
  every solved slot the stored local value \<^emph>\<open>equals\<close> its right-hand side.  The reverse
  inequality is a finite, decidable \<open>eval\<close> check over the concrete solution; equality
  and order on \<^typ>\<open>sign st\<close> code-generate through the finite-map representation.
\<close>
lemma kgen_retain_exact_eqs:
  "\<forall>u \<in> fst kgen_retain_solution.
     eq kgen_retain_eqs u (snd kgen_retain_solution) = snd kgen_retain_solution (Inl u)"
  unfolding kgen_retain_solution_def kgen_retain_eqs_def kgen_cfg_def kgen_ec_def
  by eval

text \<open>
  Upgrading \<^const>\<open>part_post_solution\<close> to the exact \<^const>\<open>part_solution\<close>: the
  dependency-closure and side-subsumption conjuncts come verbatim from the vendored
  post-solution; only the equation is strengthened, by @{thm [source]
  kgen_retain_exact_eqs}.  So the concrete retain run \<^emph>\<open>is\<close> an exact solution --- the
  operational exactness on which the abstract reduction rests, here machine-checked
  with no assumption.
\<close>
lemma kgen_retain_part_solution:
  "part_solution kgen_retain_eqs (cfg_exit kgen_cfg, bot)
     (snd kgen_retain_solution) (fst kgen_retain_solution)"
  using kgen_retain_part_post_solution kgen_retain_exact_eqs by auto

end
