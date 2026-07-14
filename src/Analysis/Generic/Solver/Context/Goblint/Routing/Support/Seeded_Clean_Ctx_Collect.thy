theory Seeded_Clean_Ctx_Collect
  imports Seed_EnterMono_Lift Exec_Cmp_Bridge
begin

section \<open>Generic entry-side reduction for the seeded-clean context spine\<close>

text \<open>
  The return (\<open>COMB\<close>) obligation of the seeded-clean kernel
  \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close> is closed generically
  (\<open>combine_abs_bound_sound\<close> + \<open>seeded_clean_comb_bound\<close>).  This theory closes the
  \<^emph>\<open>entry\<close> side: the intra edge bound and the seed bound are read off any
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> post-solution (domain-generic, no \<open>eval\<close>), and the
  value-digest routing \<open>ENTER_MONO\<close> is derived from the \<^locale>\<open>point_digest\<close>
  capability rather than left as a raw semantic premise.
\<close>

subsection \<open>Clean-transfer traverse, domain-generic\<close>

text \<open>The clean edge tree traverses to the base transfer of the read local slot;
  \<^const>\<open>map_gtree\<close> / \<^const>\<open>map_ltree\<close> only relabel unknowns, so the context-relabelled
  intra summand traverses to the base transfer of the per-context local slot.  These
  are the domain-generic forms of the sign-specific \<open>traverse_apply_etf_clean\<close> /
  \<open>traverse_intra_clean\<close>.\<close>

lemma traverse_clean_edge_tree:
  "traverse_rhs (clean_edge_tree f u) sg = f (sg (Inl u))"
  by (simp add: clean_edge_tree_def Let_def)

lemma traverse_apply_etf_clean:
  "traverse_rhs (apply_etf (clean_etf_of_transfer tf) a u) sg = apply_tf tf a (sg (Inl u))"
  by (simp add: apply_etf_clean_etf traverse_clean_edge_tree)

lemma traverse_intra_clean:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u))) sg
   = apply_tf tf a (sg (Inl (u, ctx)))"
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree traverse_apply_etf_clean)

subsection \<open>The intra edge bound and the seed bound, from any post-solution\<close>

lemma edge_in_non_enter_pred:
  assumes "finite (edges g)" and "(u, a, v) \<in> edges g" and "a \<noteq> EA_Enter"
  shows "(u, a) \<in> set (non_enter_predecessor_list g v)"
proof (rule non_enter_predecessor_list_mem[OF _ assms(3)])
  have "(u, a, v) \<in> set (cfg_edges_list g)" using assms(1,2) set_cfg_edges_list by blast
  thus "(u, a) \<in> set (predecessor_list g v)"
    unfolding predecessor_list_def by (force intro: rev_image_eqI)
qed

text \<open>The kernel's \<open>EDGE_BOUND\<close> (non-enter): the base transfer of the predecessor
  local slot is dominated by the successor local slot, for any seeded-clean
  post-solution.  Enter edges are filtered from the intra fold and covered by the
  seed.\<close>

theorem seeded_clean_edge_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> edges g" and ne: "a \<noteq> EA_Enter"
  shows "apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
proof -
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
               \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>)"
  have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
    by (rule edge_in_non_enter_pred[OF fin e ne])
  have summand: "map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u))
                   \<in> set (?intra @ ?comb)"
    using mem by (force intro: rev_image_eqI)
  have "apply_tf tf a (sg (Inl (u, ctx)))
        = traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u))) sg"
    by (rule traverse_intra_clean[symmetric])
  also have "\<dots> \<le> side_acc_ctx ?acc0 sg (?intra @ ?comb)"
    by (rule traverse_le_side_acc_ctx[OF summand])
  also have "\<dots> = eq (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) (v, ctx) sg"
    by (rule eq_side_cfg_T_eff_cmp_seed[symmetric])
  also have "\<dots> \<le> sg (Inl (v, ctx))"
    using part_post_solution_imp_se_constraint_holds[OF pp cov]
    by (simp add: se_constraint_holds_def)
  finally show ?thesis .
qed

text \<open>The seed bound: at every reached frame-entry the context seed sits below the
  entry local slot --- the order half of \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>.\<close>

theorem seeded_clean_seed_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and fe: "is_frame_entry g v"
  shows "frame_seed ctx \<le> sg (Inl (v, ctx))"
proof -
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf (clean_etf_of_transfer tf) a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
               \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>)"
  have "frame_seed ctx \<le> ?acc0" using fe by simp
  also have "?acc0 \<le> side_acc_ctx ?acc0 sg (?intra @ ?comb)"
    by (rule side_acc_ctx_ge_acc)
  also have "\<dots> = eq (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) (v, ctx) sg"
    by (rule eq_side_cfg_T_eff_cmp_seed[symmetric])
  also have "\<dots> \<le> sg (Inl (v, ctx))"
    using part_post_solution_imp_se_constraint_holds[OF pp cov]
    by (simp add: se_constraint_holds_def)
  finally show ?thesis .
qed

subsection \<open>The ENTER_MONO connection: from point routing to the kernel obligation\<close>

text \<open>
  \<^const>\<open>enter_state\<close> keeps the globals of the caller store
  (\<open>enter_state s = (\<lambda>n. if is_global n then s n else 0)\<close>), so it preserves the
  routing projection whenever \<open>proj_var\<close> is a global.
\<close>

lemma enter_state_proj:
  assumes "is_global proj_var"
  shows "enter_state s proj_var = s proj_var"
  using assms by (simp add: enter_state_def)

context point_digest
begin

text \<open>
  \<^bold>\<open>The missing generic connection.\<close>  The seeded-clean kernel's \<open>ENTER_MONO\<close>
  (Goblint \<open>Spec.context\<close>) is

    \<open>s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk> \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))\<close>.

  For a value-keyed head digest that decodes the routing global through the point
  abstraction and encodes it into the context key --- \<open>f s = enc (decode (s proj_var))\<close>,
  \<open>rt cl ctx L = enc (L proj_var)\<close>, \<open>cmp = (=)\<close> --- this is discharged \<^emph>\<open>as a theorem\<close>
  at a point routing slot: \<open>enter_mono_point\<close> gives the routing equation
  \<open>decode (s proj_var) = sg (Inl (cl, ctx)) proj_var\<close>, and \<^const>\<open>enter_state\<close> preserves
  the global \<open>proj_var\<close>.  \<open>ENTER_MONO\<close> is no longer a raw semantic premise: it reduces
  to the single point-routing condition \<open>is_point (sg (Inl (cl, ctx)) proj_var)\<close> plus
  \<open>is_global proj_var\<close>.
\<close>

lemma enter_mono_kernel:
  fixes sg :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a abs_state" and enc :: "'a \<Rightarrow> 'k"
  assumes glob: "is_global proj_var"
    and pt: "is_point (sg (Inl (cl, ctx)) proj_var)"
    and s: "s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>"
  shows "enc (decode (enter_state s proj_var)) = enc (sg (Inl (cl, ctx)) proj_var)"
proof -
  have "decode (enter_state s proj_var) = decode (s proj_var)"
    using enter_state_proj[OF glob] by simp
  also have "\<dots> = sg (Inl (cl, ctx)) proj_var"
    by (rule enter_mono_point[where sg = sg and cl = cl and ctx = ctx and proj_var = proj_var, OF pt s])
  finally show ?thesis by simp
qed

end

section \<open>Status: the per-obligation reductions are closed; the final assembly is blocked
  by a trace-digest gap\<close>

text \<open>
  \<^bold>\<open>What is closed generically.\<close>  Every per-obligation reduction of the seeded-clean
  kernel \<open>clean_ctx_collect_rread(_head)_bound\<close>
  (\<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>) is now a domain-generic theorem read off
  any \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> post-solution:

    \<^item> \<open>EDGE_BOUND\<close> (non-enter): \<open>seeded_clean_edge_bound\<close>;
    \<^item> the seed order-half of \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>: \<open>seeded_clean_seed_bound\<close>;
    \<^item> \<open>COMB_BOUND\<close>: \<open>Exec_Cmp_Bridge.seeded_clean_comb_bound\<close> +
      \<open>combine_abs_bound_sound\<close> (the abstract combine bound the rehydrating combine meets);
    \<^item> \<open>ENTER_MONO\<close>: \<open>point_digest.enter_mono_kernel\<close> --- discharged \<^emph>\<open>as a theorem\<close> from
      the point-routing condition, no longer a raw semantic premise.

  \<^bold>\<open>The single remaining blocker --- a trace-digest / enter-edge gap.\<close>  Assembling these
  into \<open>cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>\<close> requires a digest
  \<open>dg\<close> that assigns a \<^emph>\<open>callee-entry-reaching\<close> trace the \<^emph>\<open>callee\<close> context.  The kernel's
  \<^const>\<open>head_digest\<close> (\<open>dg tr = f (hd tr)\<close>) and the retain spine's
  \<open>entry_store_dg\<close> (\<open>= {hd tr}\<close>) both read the \<^emph>\<open>whole trace head\<close>.  A nested callee
  entry \<open>v\<close> is reached in \<^const>\<open>trace_witness\<close> only through the \<open>edge\<close> rule on an
  \<^const>\<open>EA_Enter\<close> edge \<open>(u, EA_Enter, v)\<close>, extending the \<^emph>\<open>caller\<close> trace \<open>tau\<close> by
  \<open>enter_state (last tau)\<close>; its head-digest is therefore the \<^emph>\<open>caller\<close> context.  The
  seeded generator, by contrast, seeds \<open>v\<close> at the \<^emph>\<open>callee\<close> context
  (\<^const>\<open>restrict_global_st\<close> of the caller slot), so \<open>sg (Inl (v, caller_ctx)) = \<bottom>\<close>.
  The kernel's \<open>EDGE_BOUND\<close> at the enter edge then demands
  \<open>apply_tf tf EA_Enter (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx)) = \<bottom>\<close>, i.e.\
  \<open>tf_enter tf (caller slot) = \<bottom>\<close> --- false.

  \<^bold>\<open>Why the retain infrastructure does not transfer.\<close>  The retain spine closes
  \<open>cfg_collect_ctx\<close> precisely because it \<^emph>\<open>uses the transfer at enter edges\<close>
  (\<open>entry_store_ec ctx a = edge_collect EA_Enter \<lbrakk>a\<rbrakk>\<close>): the enter edge flows
  \<open>tf_enter\<close> into the callee under the caller context.  The clean seeded generator
  \<^emph>\<open>replaces\<close> that enter transfer with the seed to obtain the R_read local-only precision ---
  which is exactly why the enter-edge \<open>EDGE_BOUND\<close> no longer holds for it.

  \<^bold>\<open>The single missing generic result\<close> is therefore a \<^emph>\<open>context-switching R_read trace
  digest\<close>: a \<open>dg\<close> / \<open>cmp\<close> that (a) assigns a callee-entry-reaching trace the callee
  context \<^const>\<open>restrict_global\<close> of the enter store, matching the seed; (b) still
  satisfies \<open>DG_INTRA\<close> / \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close> across the \<^const>\<open>trace_witness\<close>
  \<open>edge\<close> rule at \<^const>\<open>EA_Enter\<close> steps; and (c) reduces the enter-edge \<open>EDGE_BOUND\<close> to
  the seed bound \<open>seeded_clean_seed_bound\<close> rather than to a false \<open>tf_enter\<close> bound.  It
  is the clean-spine analogue of the retain spine's \<open>entry_store_dg\<close> / \<open>entry_store_ec\<close>
  model, and it is not built here.  With it, the four reductions above and the generic
  solver post-fixpoint close \<open>cfg_collect_ctx \<subseteq> \<gamma>(solution)\<close> for the seeded-clean
  spine at every domain.
\<close>

end
