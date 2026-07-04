theory TD_Side_Eff_Ctx_Sound
  imports TD_Side_Tree TD_Side_Eff_Sound TD_Side_Eff_Soundness
    "Voblint_CFG.CFG_Collect_Trace"
begin

section \<open>Context-indexed effectful soundness via the monovariant pullback\<close>

text \<open>
  The context-indexed equation system indexes the local unknown by a context
  \<open>c\<close>: the unknown type is \<open>pp \<times> 'c + 'g\<close> rather than \<open>pp + 'g\<close>.  Along a
  context-preserving routing -- intra edges always keep the context (the unknown
  \<open>(v, c)\<close> queries \<open>(u, c)\<close> via \<open>map_ltree (\<lambda>w. (w, c))\<close>), and the conservative
  combine relabels the monovariant combine -- the whole context-indexed soundness
  reduces to the monovariant theorem.

  The reduction is a single environment pullback.  \<open>pull_ctx c \<sigma>\<close> reads the
  context-indexed environment \<open>\<sigma>\<close> at the fixed context \<open>c\<close>: locals map
  \<open>Inl u \<mapsto> \<sigma> (Inl (u, c))\<close>, globals \<open>Inr g \<mapsto> \<sigma> (Inr g)\<close>.  Its type is exactly
  the monovariant unknown environment \<open>pp + 'g \<Rightarrow> abs_state\<close>, so every monovariant
  construction (\<open>side_env\<close>, \<open>glob_env\<close>, \<open>etf_full\<close>) and the soundness theorem
  \<open>post_fixpoint_sound_at_eff\<close> apply at \<open>pull_ctx c \<sigma>\<close> unchanged.  The local query
  of a relabelled tree commutes with the pullback
  (\<open>traverse_map_ltree_pull\<close>, from \<open>traverse_rhs_map_ltree\<close>), so a context post-fixpoint
  feeds the monovariant premises at the pullback.

  The precision payoff (the unknown \<open>\<sigma> (Inl (v, c))\<close> being strictly below the
  monovariant join over all contexts) lives in the value-dependent semantic
  combine, which routes the callee-exit query to a context computed from the
  queried caller value (cf. \<open>unit_combine_tree_ctx\<close>).  That routing reads \<open>\<sigma>\<close> at
  two different contexts, so it does not factor through a single pullback; its
  soundness is a separate argument.  This theory settles the context-preserving
  case and gives \<open>side_env_ctx\<close> / \<open>inr_slot_locals_bot_ctx\<close> the soundness chain reads.
\<close>

subsection \<open>The context pullback of the unknown environment\<close>

definition pull_ctx ::
  "'c \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
       \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state)"
where
  "pull_ctx ctx \<sigma> = \<sigma> \<circ> map_sum (\<lambda>w. (w, ctx)) id"

lemma pull_ctx_Inl: "pull_ctx ctx \<sigma> (Inl u) = \<sigma> (Inl (u, ctx))"
  by (simp add: pull_ctx_def)

lemma pull_ctx_Inr: "pull_ctx ctx \<sigma> (Inr g) = \<sigma> (Inr g)"
  by (simp add: pull_ctx_def)

text \<open>
  Local query of a context-preserving relabelled tree commutes with the pullback:
  evaluating \<open>map_ltree (\<lambda>w. (w, ctx)) t\<close> against \<open>\<sigma>\<close> equals evaluating \<open>t\<close>
  against \<open>pull_ctx ctx \<sigma>\<close>.  Direct from \<open>traverse_rhs_map_ltree\<close>.
\<close>

lemma traverse_map_ltree_pull:
  "traverse_rhs (map_ltree (\<lambda>w. (w, ctx)) t) \<sigma> = traverse_rhs t (pull_ctx ctx \<sigma>)"
  by (simp add: traverse_rhs_map_ltree pull_ctx_def comp_def)

subsection \<open>Context-indexed analyzer environment and the local-bot invariant\<close>

definition side_env_ctx ::
  "(pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> pp \<times> 'c \<Rightarrow> 'a abs_state"
where
  "side_env_ctx \<sigma> p = side_env (pull_ctx (snd p) \<sigma>) (fst p)"

lemma side_env_ctx_pull:
  "side_env_ctx \<sigma> (v, ctx) = side_env (pull_ctx ctx \<sigma>) v"
  by (simp add: side_env_ctx_def)

definition inr_slot_locals_bot_ctx ::
  "(pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> bool"
where
  "inr_slot_locals_bot_ctx \<sigma> =
     (\<forall>g. \<forall>x. \<not> is_global x \<longrightarrow> \<sigma> (Inr g) x = bot)"

text \<open>
  The local-bot invariant only constrains the global slots, which the pullback
  copies verbatim, so it transports to every context's pullback.
\<close>

lemma inr_slot_locals_bot_pull_ctx:
  "inr_slot_locals_bot_ctx \<sigma> \<Longrightarrow> inr_slot_locals_bot (pull_ctx ctx \<sigma>)"
  by (simp add: inr_slot_locals_bot_ctx_def inr_slot_locals_bot_def pull_ctx_Inr)

definition inl_slot_globals_bot_ctx ::
  "(pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> bool"
where
  "inl_slot_globals_bot_ctx \<sigma> =
     (\<forall>v. \<forall>x. is_global x \<longrightarrow> \<sigma> (Inl v) x = bot)"

subsection \<open>Local post-fixpoint bound at the pullback\<close>

text \<open>
  The local half of the per-edge bound, transported to the context world.  At a
  context post-fixpoint (\<open>eq \<dots> (w, ctx) \<sigma> \<le> \<sigma> (Inl (w, ctx))\<close>) the intra tree
  for an edge \<open>(u, a, w)\<close> is one of the trees contributing to the unknown
  \<open>(w, ctx)\<close>, so \<open>post_sol_tree_le_ctx\<close> bounds its denotation; rewriting the
  context-preserving relabel through \<open>traverse_map_ltree_pull\<close> yields the local
  bound on \<open>apply_etf etf a u\<close> against the pullback.  This is the context analogue
  of the \<open>loc\<close> step inside \<open>etf_combined_le_eff\<close>.
\<close>

lemma step_local_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes post:
    "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (w, ctx) \<sigma> \<le> \<sigma> (Inl (w, ctx))"
  assumes e: "(u, a, w) \<in> edges g"
  assumes fin: "finite (edges g)"
  shows "traverse_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> \<sigma> (Inl (w, ctx))"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have memtree:
    "map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u)
       \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u))
                   (predecessor_list g w)
              @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g w))"
    using mem by force
  have "traverse_rhs (map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u)) \<sigma>
          \<le> \<sigma> (Inl (w, ctx))"
    by (rule post_sol_tree_le_ctx[OF post memtree])
  thus ?thesis by (simp add: traverse_map_ltree_pull)
qed

subsection \<open>Global side bound at the pullback\<close>

text \<open>
  The side (global) aggregation commutes with the context-preserving relabel:
  \<open>map_ltree\<close> leaves the \<open>QueryG\<close> / \<open>Side\<close> nodes untouched, so the per-name side
  map of \<open>map_ltree h t\<close> against \<open>\<sigma>\<close> is that of \<open>t\<close> against the pulled-back
  environment.  Mirrors \<open>traverse_rhs_map_ltree\<close> on the side component.
\<close>

text \<open>
  Stated pointwise at a global slot \<open>Inr gg\<close>: the full side maps live over
  different unknown types (\<open>pp \<times> 'c + 'g\<close> vs \<open>pp + 'g\<close>), but their global slots
  share the type \<open>'g\<close>, and only those carry side contributions.
\<close>

lemma sides_map_ltree_pull_Inr:
  fixes t :: "(pp, 'g, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  shows "sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) t) \<sigma> (Inr gg)
         = sides_of_rhs t (pull_ctx ctx \<sigma>) (Inr gg)"
  by (induction t) (auto simp: Let_def pull_ctx_def)

text \<open>
  A contributing tree's per-name side contribution sits below the context fold's,
  and the fold's below the packaged RHS tree's (the entry \<open>Side\<close> wrapper only adds,
  at slot \<open>gseed\<close>).  Context analogues of \<open>sides_le_side_rhs_fold_eff_edge\<close> and
  \<open>sides_fold_le_side_cfg_T_eff\<close>, simpler because the context fold runs one list.
\<close>

lemma sides_le_side_rhs_fold_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "t \<in> set ts \<Longrightarrow>
         sides_of_rhs t \<sigma> (Inr gg)
           \<le> sides_of_rhs (side_rhs_fold_ctx acc ts) \<sigma> (Inr gg)"
proof (induction ts arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons t' ts)
  from Cons.prems consider (hd) "t = t'" | (tl) "t \<in> set ts" by auto
  then show ?case
  proof cases
    case hd
    show ?thesis unfolding hd side_rhs_fold_ctx.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule sup_ge1)
  next
    case tl
    have ih: "sides_of_rhs t \<sigma> (Inr gg)
            \<le> sides_of_rhs
                 (side_rhs_fold_ctx (acc \<squnion> traverse_rhs t' \<sigma>) ts) \<sigma> (Inr gg)"
      by (rule Cons.IH[OF tl])
    show ?thesis unfolding side_rhs_fold_ctx.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule le_supI2[OF ih])
  qed
qed

lemma sides_fold_le_side_cfg_T_eff_ctx:
  shows "sides_of_rhs (side_rhs_fold_ctx
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                (predecessor_list g v)
            @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))
           \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (v, ctx))
             \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_ctx_def
  by (cases "v = cfg_entry g") (auto simp: Let_def fun_upd_def)

lemma side_post_solution_le_global_ctx:
  assumes pp: "part_post_solution (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (v, ctx))
           \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v
  have "sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (v, ctx)) \<sigma> \<le> \<sigma>"
    by auto
  thus ?thesis by (rule le_funD)
qed

subsection \<open>Per-edge closure of a context post-solution\<close>

text \<open>
  The context analogue of \<open>etf_combined_le_eff\<close>: a context post-solution closes
  every intra edge.  The local part is \<open>step_local_le_ctx\<close>; the global part runs
  the side chain \<open>sides_map_ltree_pull_Inr\<close> \<open>\<rightarrow>\<close> \<open>sides_le_side_rhs_fold_ctx\<close>
  \<open>\<rightarrow>\<close> \<open>sides_fold_le_side_cfg_T_eff_ctx\<close> \<open>\<rightarrow>\<close> \<open>side_post_solution_le_global_ctx\<close>,
  then reassembles \<open>etf_full\<close> against the pullback.  This directly discharges the
  \<open>step_le\<close> premise of \<open>post_fixpoint_sound_at_ctx_pull\<close>.
\<close>

lemma etf_combined_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) x \<sigma> vars"
      and v: "(w, ctx) \<in> vars"
      and e: "(u, a, w) \<in> edges g"
      and fin: "finite (edges g)"
  shows "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (w, ctx)"
proof -
  have posteq: "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (w, ctx) \<sigma>
                  \<le> \<sigma> (Inl (w, ctx))"
    using pp v by auto
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have memtree:
    "map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u)
       \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u))
                   (predecessor_list g w)
              @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g w))"
    using mem by force
  have loc: "traverse_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> \<sigma> (Inl (w, ctx))"
    by (rule step_local_le_ctx[OF posteq e fin])
  have glob_name:
    "\<And>gg. sides_of_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>) (Inr gg)
            \<le> (pull_ctx ctx \<sigma>) (Inr gg)"
  proof -
    fix gg
    have "sides_of_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>) (Inr gg)
          = sides_of_rhs (map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u)) \<sigma> (Inr gg)"
      by (simp add: sides_map_ltree_pull_Inr)
    also have "\<dots> \<le> sides_of_rhs
                 (side_rhs_fold_ctx
                    (if w = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                    (map (\<lambda>(u, a). map_ltree (\<lambda>w'. (w', ctx)) (apply_etf etf a u))
                         (predecessor_list g w)
                     @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g w)))
                 \<sigma> (Inr gg)"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (w, ctx))
                      \<sigma> (Inr gg)"
      by (rule sides_fold_le_side_cfg_T_eff_ctx)
    also have "\<dots> \<le> \<sigma> (Inr gg)"
      by (rule side_post_solution_le_global_ctx[OF pp v])
    also have "\<dots> = (pull_ctx ctx \<sigma>) (Inr gg)" by (simp add: pull_ctx_Inr)
    finally show "sides_of_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>) (Inr gg)
                    \<le> (pull_ctx ctx \<sigma>) (Inr gg)" .
  qed
  have glob: "all_sides (apply_etf etf a u) (pull_ctx ctx \<sigma>)
                \<le> glob_env (pull_ctx ctx \<sigma>)"
  proof -
    have "all_sides (apply_etf etf a u) (pull_ctx ctx \<sigma>)
          \<le> glob_env (sides_of_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>))"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env (pull_ctx ctx \<sigma>)"
      by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  have "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>)
        = traverse_rhs (apply_etf etf a u) (pull_ctx ctx \<sigma>)
          \<squnion> all_sides (apply_etf etf a u) (pull_ctx ctx \<sigma>)"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl (w, ctx)) \<squnion> glob_env (pull_ctx ctx \<sigma>)"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env_ctx \<sigma> (w, ctx)"
    by (simp add: side_env_ctx_pull side_env_def pull_ctx_Inl)
  finally show ?thesis .
qed

subsection \<open>Per-combine closure for the conservative builder\<close>

text \<open>
  The combine analogue of \<open>etf_combined_le_ctx\<close>, for the conservative combine
  builder \<open>cmb c cc ex = map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)\<close> (the
  context-preserving relabel of the monovariant combine).  The semantic combine
  builder routes the callee-exit query value-dependently and does not factor
  through the single pullback, so it is excluded here.  Same structure: local via
  \<open>post_sol_tree_le_ctx\<close>, global via the side chain.
\<close>

lemma combine_conservative_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx
                    (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
                    g etf bot0 s0 gseed) x \<sigma> vars"
      and v: "(ret, ctx) \<in> vars"
      and e: "(cc, ex, ret) \<in> combines g"
      and finC: "finite (combines g)"
  shows "etf_full (etf_combine etf cc ex) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (ret, ctx)"
proof -
  let ?cmb = "\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)"
  have posteq: "eq (side_cfg_T_eff_ctx ?cmb g etf bot0 s0 gseed) (ret, ctx) \<sigma>
                  \<le> \<sigma> (Inl (ret, ctx))"
    using pp v by auto
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g ret)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have memtree:
    "map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex)
       \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                   (predecessor_list g ret)
              @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret))"
    using mem by force
  have loc: "traverse_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)
               \<le> \<sigma> (Inl (ret, ctx))"
  proof -
    have "traverse_rhs (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex)) \<sigma>
            \<le> \<sigma> (Inl (ret, ctx))"
      by (rule post_sol_tree_le_ctx[OF posteq memtree])
    thus ?thesis by (simp add: traverse_map_ltree_pull)
  qed
  have glob_name:
    "\<And>gg. sides_of_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>) (Inr gg)
            \<le> (pull_ctx ctx \<sigma>) (Inr gg)"
  proof -
    fix gg
    have "sides_of_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>) (Inr gg)
          = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex)) \<sigma> (Inr gg)"
      by (simp add: sides_map_ltree_pull_Inr)
    also have "\<dots> \<le> sides_of_rhs
                 (side_rhs_fold_ctx
                    (if ret = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                    (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                         (predecessor_list g ret)
                     @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret)))
                 \<sigma> (Inr gg)"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_ctx ?cmb g etf bot0 s0 gseed (ret, ctx))
                      \<sigma> (Inr gg)"
      by (rule sides_fold_le_side_cfg_T_eff_ctx)
    also have "\<dots> \<le> \<sigma> (Inr gg)"
      by (rule side_post_solution_le_global_ctx[OF pp v])
    also have "\<dots> = (pull_ctx ctx \<sigma>) (Inr gg)" by (simp add: pull_ctx_Inr)
    finally show "sides_of_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>) (Inr gg)
                    \<le> (pull_ctx ctx \<sigma>) (Inr gg)" .
  qed
  have glob: "all_sides (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)
                \<le> glob_env (pull_ctx ctx \<sigma>)"
  proof -
    have "all_sides (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)
          \<le> glob_env (sides_of_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>))"
      by (rule all_sides_le_glob_env_sides)
    also have "\<dots> \<le> glob_env (pull_ctx ctx \<sigma>)"
      by (rule glob_env_mono_Inr) (rule glob_name)
    finally show ?thesis .
  qed
  have "etf_full (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)
        = traverse_rhs (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)
          \<squnion> all_sides (etf_combine etf cc ex) (pull_ctx ctx \<sigma>)"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl (ret, ctx)) \<squnion> glob_env (pull_ctx ctx \<sigma>)"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env_ctx \<sigma> (ret, ctx)"
    by (simp add: side_env_ctx_pull side_env_def pull_ctx_Inl)
  finally show ?thesis .
qed

subsection \<open>Entry closure of a context post-solution\<close>

text \<open>
  Context analogue of \<open>s0_le_side_env_entry_eff\<close>: at the entry unknown
  \<open>(cfg_entry g, ctx)\<close> the local fold seeds \<open>restrict_local s0\<close> (below the local
  unknown by \<open>side_acc_ctx_ge_acc\<close>) and the wrapping \<open>Side gseed\<close> seeds
  \<open>restrict_global s0\<close> into slot \<open>gseed\<close> (below \<open>glob_env\<close> of the pullback), so
  \<open>s0\<close> sits below the combined context env at the entry.
\<close>

lemma s0_le_side_env_ctx_entry:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) x \<sigma> vars"
      and entry_in: "(cfg_entry g, ctx) \<in> vars"
  shows "s0 \<le> side_env_ctx \<sigma> (cfg_entry g, ctx)"
proof -
  let ?ent = "cfg_entry g"
  have eqle: "eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (?ent, ctx) \<sigma>
                \<le> \<sigma> (Inl (?ent, ctx))"
    using pp entry_in by auto
  have rl: "restrict_local s0 \<le> \<sigma> (Inl (?ent, ctx))"
  proof -
    have ge: "bot0 \<squnion> restrict_local s0
                \<le> eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (?ent, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_ctx by (simp add: side_acc_ctx_ge_acc)
    have "restrict_local s0 \<le> bot0 \<squnion> restrict_local s0" by simp
    also have "\<dots> \<le> eq (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed) (?ent, ctx) \<sigma>"
      by (rule ge)
    also have "\<dots> \<le> \<sigma> (Inl (?ent, ctx))" by (rule eqle)
    finally show ?thesis .
  qed
  have rgeq: "sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (?ent, ctx))
                \<sigma> (Inr gseed)
              = sides_of_rhs (side_rhs_fold_ctx (bot0 \<squnion> restrict_local s0)
                  (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                       (predecessor_list g ?ent)
                   @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g ?ent)))
                  \<sigma> (Inr gseed)
                \<squnion> restrict_global s0"
    unfolding side_cfg_T_eff_ctx_def by (simp add: Let_def)
  have rg: "restrict_global s0 \<le> \<sigma> (Inr gseed)"
  proof -
    have "restrict_global s0
          \<le> sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (?ent, ctx))
              \<sigma> (Inr gseed)"
      unfolding rgeq by (rule sup_ge2)
    also have "\<dots> \<le> \<sigma> (Inr gseed)"
      by (rule side_post_solution_le_global_ctx[OF pp entry_in])
    finally show ?thesis .
  qed
  have gseed_le: "\<sigma> (Inr gseed) \<le> glob_env (pull_ctx ctx \<sigma>)"
    using glob_env_upper[of "pull_ctx ctx \<sigma>" gseed] by (simp add: pull_ctx_Inr)
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "\<dots> \<le> \<sigma> (Inl (?ent, ctx)) \<squnion> \<sigma> (Inr gseed)"
    using rl rg by (rule sup_mono)
  also have "\<dots> \<le> \<sigma> (Inl (?ent, ctx)) \<squnion> glob_env (pull_ctx ctx \<sigma>)"
    using gseed_le by (rule sup_mono[OF order_refl])
  also have "\<dots> = side_env_ctx \<sigma> (?ent, ctx)"
    by (simp add: side_env_ctx_pull side_env_def pull_ctx_Inl)
  finally show ?thesis .
qed

subsection \<open>Coverage transport: the conservative system is the relabelled monovariant one\<close>

text \<open>
  The dependency aggregation commutes with the relabel: \<open>map_ltree\<close> tags each
  \<open>QueryL\<close> target with the relabel and leaves \<open>QueryG\<close>, so the queried-unknown
  set of \<open>map_ltree h t\<close> is the relabel-image of that of \<open>t\<close> against the pullback.
\<close>

lemma dep_aux_map_ltree:
  "dep_aux \<sigma> (map_ltree h t)
   = map_sum h id ` dep_aux (\<lambda>z. \<sigma> (map_sum h id z)) t"
  by (induction t) auto

text \<open>
  The conservative context system at \<open>(v, c)\<close> is exactly the monovariant RHS at
  \<open>v\<close>, relabelled \<open>u \<mapsto> (u, c)\<close> -- contexts are fully decoupled.  This is the
  transport key: every monovariant structural fact lifts to the context system by
  a uniform relabel.  General version of the \<open>'c = unit\<close> collapse
  \<open>side_cfg_T_eff_ctx_collapses_unit\<close>.
\<close>

lemma side_cfg_T_eff_ctx_conservative_eq:
  "side_cfg_T_eff_ctx
     (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
     g etf bot0 s0 gseed (v, ctx)
   = map_ltree (\<lambda>w. (w, ctx)) (side_cfg_T_eff g etf bot0 s0 gseed v)"
proof -
  have fold:
    "side_rhs_fold_ctx acc0
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) (predecessor_list g v)
         @ map (\<lambda>(cc, ex). map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))
               (combine_predecessor_list g v))
     = map_ltree (\<lambda>w. (w, ctx))
         (side_rhs_fold_eff etf acc0 (predecessor_list g v)
            (combine_predecessor_list g v))" for acc0 v
    by (simp add: map_ltree_side_rhs_fold_eff)
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    thus ?thesis
      unfolding side_cfg_T_eff_ctx_def side_cfg_T_eff_def make_side_rhs_tree_eff_def
      by (simp add: fold Let_def)
  next
    case False
    thus ?thesis
      unfolding side_cfg_T_eff_ctx_def side_cfg_T_eff_def make_side_rhs_tree_eff_def
      by (simp add: fold Let_def)
  qed
qed

text \<open>
  Single dependency step transports: if \<open>y\<close> is a local dependency of the
  monovariant unknown \<open>x\<close> at the pullback, then \<open>(y, ctx)\<close> is a local dependency
  of the conservative context unknown \<open>(x, ctx)\<close>.  From \<open>dep_aux_map_ltree\<close> +
  \<open>side_cfg_T_eff_ctx_conservative_eq\<close>.
\<close>

lemma step_dep_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes "y \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) (pull_ctx ctx \<sigma>) x"
  shows "(y, ctx) \<in> dep\<^sub>L
           (side_cfg_T_eff_ctx
              (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
              g etf bot0 s0 gseed) \<sigma> (x, ctx)"
proof -
  from assms
  have y_in: "Inl y \<in> dep_aux (pull_ctx ctx \<sigma>) (side_cfg_T_eff g etf bot0 s0 gseed x)"
    by (simp add: dep\<^sub>L_def dep_def)
  have "Inl (y, ctx) \<in> map_sum (\<lambda>w. (w, ctx)) id `
          dep_aux (pull_ctx ctx \<sigma>) (side_cfg_T_eff g etf bot0 s0 gseed x)"
    using y_in by (auto intro: rev_image_eqI)
  also have "map_sum (\<lambda>w. (w, ctx)) id `
               dep_aux (pull_ctx ctx \<sigma>) (side_cfg_T_eff g etf bot0 s0 gseed x)
             = dep_aux \<sigma> (map_ltree (\<lambda>w. (w, ctx)) (side_cfg_T_eff g etf bot0 s0 gseed x))"
    by (simp add: dep_aux_map_ltree pull_ctx_def comp_def)
  also have "\<dots> = dep_aux \<sigma>
                   (side_cfg_T_eff_ctx
                      (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
                      g etf bot0 s0 gseed (x, ctx))"
    by (simp add: side_cfg_T_eff_ctx_conservative_eq)
  finally show ?thesis by (simp add: dep\<^sub>L_def dep_def)
qed

text \<open>
  Lift the single step to the transitive dependency relation: the embedding
  \<open>v \<mapsto> (v, ctx)\<close> is a graph homomorphism of the dependency relation, so it carries
  transitive dependencies at the pullback to transitive dependencies of the
  conservative context system.
\<close>

lemma trans_dep_ctx_embed_rel:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes "(v0, w) \<in> {(u, d). d \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed)
                                      (pull_ctx ctx \<sigma>) u}\<^sup>+"
  shows "((v0, ctx), (w, ctx)) \<in> {(u, d). d \<in> dep\<^sub>L
           (side_cfg_T_eff_ctx
              (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
              g etf bot0 s0 gseed) \<sigma> u}\<^sup>+"
  using assms
proof (induction rule: trancl_induct)
  case (base y)
  have "(y, ctx) \<in> dep\<^sub>L
          (side_cfg_T_eff_ctx
             (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
             g etf bot0 s0 gseed) \<sigma> (v0, ctx)"
    using base by (auto intro: step_dep_ctx)
  hence "((v0, ctx), (y, ctx)) \<in> {(u, d). d \<in> dep\<^sub>L
           (side_cfg_T_eff_ctx
              (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
              g etf bot0 s0 gseed) \<sigma> u}" by simp
  thus ?case by (rule r_into_trancl)
next
  case (step y z)
  have "(z, ctx) \<in> dep\<^sub>L
          (side_cfg_T_eff_ctx
             (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
             g etf bot0 s0 gseed) \<sigma> (y, ctx)"
    using step.hyps(2) by (auto intro: step_dep_ctx)
  hence "((y, ctx), (z, ctx)) \<in> {(u, d). d \<in> dep\<^sub>L
           (side_cfg_T_eff_ctx
              (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
              g etf bot0 s0 gseed) \<sigma> u}" by simp
  with step.IH show ?case by (rule trancl_into_trancl)
qed

text \<open>
  Backward IP reachability lands in the conservative context solver's dependency
  cone at the chosen context: every node reachable to \<open>v0\<close> in the CFG has its
  \<open>ctx\<close>-copy in the solved stable set \<open>vars\<close>.  The monovariant cone lemma
  (\<open>cfg_reaches_imp_trans_dep_or_eq_side_eff\<close>) runs at the pullback; the transport
  (\<open>trans_dep_ctx_embed_rel\<close>) lifts its conclusion to the context system, and the
  generic dependency closure of a post-solution
  (\<open>part_post_solution_implies_trans_dep_subsumed\<close>) lands it in \<open>vars\<close>.  The
  monovariant dependency contracts (\<open>edge_dep\<close> / \<open>comb_dep\<close> / \<open>*_static\<close>) suffice
  because the conservative context trees are uniform relabels.
\<close>

lemma side_cone_in_vars_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx
                    (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
                    g etf bot0 s0 gseed) (v0, ctx) \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes reach: "cfg_reaches g w v0"
  shows "(w, ctx) \<in> vars"
proof -
  have v0v: "(v0, ctx) \<in> vars" using pp by auto
  consider (eq) "w = v0"
    | (td) "w \<in> trans_dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed) (pull_ctx ctx \<sigma>) v0"
    using cfg_reaches_imp_trans_dep_or_eq_side_eff[OF fin finC edge_dep comb_dep1
            comb_dep2 edge_static comb_static reach] by blast
  thus ?thesis
  proof cases
    case eq thus ?thesis using v0v by simp
  next
    case td
    have rel: "(v0, w) \<in> {(u, d). d \<in> dep\<^sub>L (side_cfg_T_eff g etf bot0 s0 gseed)
                                       (pull_ctx ctx \<sigma>) u}\<^sup>+"
      using td by simp
    have "(w, ctx) \<in> trans_dep\<^sub>L
            (side_cfg_T_eff_ctx
               (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
               g etf bot0 s0 gseed) \<sigma> (v0, ctx)"
      using trans_dep_ctx_embed_rel[OF rel] by simp
    moreover have "trans_dep\<^sub>L
            (side_cfg_T_eff_ctx
               (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
               g etf bot0 s0 gseed) \<sigma> (v0, ctx) \<subseteq> vars"
      using part_post_solution_implies_trans_dep_subsumed[OF pp] by simp
    ultimately show ?thesis by blast
  qed
qed

subsection \<open>Context soundness for context-preserving routing\<close>

context sound_effectful_transfer
begin

text \<open>
  Context-indexed collecting soundness, reduced to \<open>post_fixpoint_sound_at_eff\<close>
  at the pullback.  Given the monovariant per-edge / per-combine / entry
  post-fixpoint bounds phrased against \<open>side_env_ctx \<sigma> (\<dots>, ctx)\<close> and the
  pulled-back environment \<open>pull_ctx ctx \<sigma>\<close>, the combined context env of \<open>\<sigma>\<close>
  over-approximates the IP collecting semantics at \<open>(v0, ctx)\<close>.  Because the
  bound lands \<open>cfg_collect\<close> (the unrefined collecting set) it is, for the
  context-preserving routing, exactly the monovariant guarantee carried at each
  context copy; the context-refined sharpening \<open>cfg_collect_ctx\<close> follows by its
  subset law.
\<close>

theorem post_fixpoint_sound_at_ctx_pull:
  fixes g :: cfg and \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp and ctx :: 'c
  assumes inr: "inr_slot_locals_bot_ctx \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (w, ctx)"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf c ex) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (ret, ctx)"
  assumes entry_le: "s0 \<le> side_env_ctx \<sigma> (cfg_entry g, ctx)"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_ctx \<sigma> (v0, ctx)\<rbrakk>"
proof -
  have main: "cfg_collect g S v0 \<le> \<lbrakk>side_env (pull_ctx ctx \<sigma>) v0\<rbrakk>"
  proof (rule post_fixpoint_sound_at_eff
           [OF inr_slot_locals_bot_pull_ctx[OF inr] S_sound])
    fix u a w assume e: "(u, a, w) \<in> edges g"
    show "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>)
            \<le> side_env (pull_ctx ctx \<sigma>) w"
      using step_le[OF e] by (simp add: side_env_ctx_pull)
  next
    fix c ex ret assume cm: "(c, ex, ret) \<in> combines g"
    show "etf_full (etf_combine etf c ex) (pull_ctx ctx \<sigma>)
            \<le> side_env (pull_ctx ctx \<sigma>) ret"
      using combine_le[OF cm] by (simp add: side_env_ctx_pull)
  next
    show "s0 \<le> side_env (pull_ctx ctx \<sigma>) (cfg_entry g)"
      using entry_le by (simp add: side_env_ctx_pull)
  qed
  show ?thesis using main by (simp add: side_env_ctx_pull)
qed

text \<open>
  End-to-end conservative-routing context soundness from a context post-solution.
  The conservative combine builder relabels the monovariant combine, so both the
  per-edge (\<open>etf_combined_le_ctx\<close>) and per-combine (\<open>combine_conservative_le_ctx\<close>)
  closures and the entry closure (\<open>s0_le_side_env_ctx_entry\<close>) discharge the
  premises of \<open>post_fixpoint_sound_at_ctx_pull\<close>.  The coverage hypotheses
  (\<open>cover_edge\<close> / \<open>cover_comb\<close> / \<open>cover_entry\<close>: the solved stable set \<open>vars\<close>
  contains every edge target, combine return, and the entry at context \<open>ctx\<close>) are
  the \<open>solve_dom\<close>-style assumption the project carries everywhere; for the
  monovariant spine they are discharged by the backward-cone pruning
  (\<open>side_cone_in_vars_eff\<close>), whose context port is future work.  At \<open>'c = unit\<close>
  this recovers the monovariant guarantee at the single context.
\<close>

theorem post_fixpoint_sound_at_ctx_conservative:
  fixes g :: cfg and \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp and ctx :: 'c
  assumes inr: "inr_slot_locals_bot_ctx \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx
                    (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
                    g etf bot0 s0 gseed) x \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
  assumes cover_comb: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
  assumes cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_ctx \<sigma> (v0, ctx)\<rbrakk>"
proof (rule post_fixpoint_sound_at_ctx_pull[OF inr S_sound])
  fix u a w assume e: "(u, a, w) \<in> edges g"
  show "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (w, ctx)"
    by (rule etf_combined_le_ctx[OF pp cover_edge[OF e] e fin])
next
  fix c ex ret assume cm: "(c, ex, ret) \<in> combines g"
  show "etf_full (etf_combine etf c ex) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (ret, ctx)"
    by (rule combine_conservative_le_ctx[OF pp cover_comb[OF cm] cm finC])
next
  show "s0 \<le> side_env_ctx \<sigma> (cfg_entry g, ctx)"
    by (rule s0_le_side_env_ctx_entry[OF pp cover_entry])
qed

text \<open>
  Exit-rooted, coverage-discharged context soundness: the solver-facing theorem.
  The backward-cone pruning discharges the \<open>cover_*\<close> hypotheses --
  \<open>side_cone_in_vars_ctx\<close> shows every edge target / combine return on the cone of
  the exit has its \<open>ctx\<close>-copy in the solved stable set \<open>vars\<close> -- so only the
  monovariant dependency / static contracts (\<open>edge_dep\<close> / \<open>comb_dep\<close> / \<open>*_static\<close>)
  and an entry-coverage hypothesis remain.  Context analogue of
  \<open>side_collect_sound_exit_pruned_eff\<close>; \<open>'c = unit\<close> recovers it.
\<close>

theorem side_collect_sound_exit_pruned_ctx:
  fixes g :: cfg and \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set" and ctx :: 'c
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx
                    (\<lambda>c cc ex. map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))
                    g etf bot0 s0 gseed) (cfg_exit g, ctx) \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes inr: "inr_slot_locals_bot_ctx \<sigma>"
  shows "cfg_collect g S (cfg_exit g) \<le> \<lbrakk>side_env_ctx \<sigma> (cfg_exit g, ctx)\<rbrakk>"
proof -
  define pg where "pg = prune_cfg g"
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges pg
       \<Longrightarrow> etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (w, ctx)"
  proof -
    fix u a w assume e_pg: "(u, a, w) \<in> edges pg"
    have e_pg2: "(u, a, w) \<in> edges (prune_to g (cfg_exit g))"
      using e_pg by (simp add: pg_def prune_cfg_def)
    have ed_g: "(u, a, w) \<in> edges g" using e_pg2 by auto
    have w_cone: "cfg_reaches g w (cfg_exit g)" using e_pg2 by (simp add: cone_def)
    have wv: "(w, ctx) \<in> vars"
      by (rule side_cone_in_vars_ctx[OF pp fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static w_cone])
    show "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (w, ctx)"
      by (rule etf_combined_le_ctx[OF pp wv ed_g fin])
  qed
  have combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines pg \<Longrightarrow>
       etf_full (etf_combine etf c ex) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (ret, ctx)"
  proof -
    fix c ex ret assume cmb: "(c, ex, ret) \<in> combines pg"
    have cmb2: "(c, ex, ret) \<in> combines (prune_to g (cfg_exit g))"
      using cmb by (simp add: pg_def prune_cfg_def)
    have uce_g: "(c, ex, ret) \<in> combines g" using cmb2 by auto
    have r_cone: "cfg_reaches g ret (cfg_exit g)" using cmb2 by (simp add: cone_def)
    have rv: "(ret, ctx) \<in> vars"
      by (rule side_cone_in_vars_ctx[OF pp fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static r_cone])
    show "etf_full (etf_combine etf c ex) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (ret, ctx)"
      by (rule combine_conservative_le_ctx[OF pp rv uce_g finC])
  qed
  have entry_pg: "S \<le> \<lbrakk>side_env_ctx \<sigma> (cfg_entry pg, ctx)\<rbrakk>"
    using entry by (simp add: pg_def prune_cfg_def)
  have collect_pg: "cfg_collect pg S (cfg_exit g) \<le> \<lbrakk>side_env_ctx \<sigma> (cfg_exit g, ctx)\<rbrakk>"
    by (rule post_fixpoint_sound_at_ctx_pull[OF inr entry_pg step_le combine_le order_refl])
  have frame: "cfg_collect g S (cfg_exit g) \<subseteq> cfg_collect pg S (cfg_exit g)"
    using cfg_collect_prune_exit[of g S] by (simp add: pg_def)
  show ?thesis using frame collect_pg by blast
qed

end

subsection \<open>Semantic combine soundness contract (unit-global domain)\<close>

text \<open>
  The genuinely value-dependent combine.  Unlike the conservative builder, the
  semantic combine \<open>unit_combine_tree_ctx ec cc ex ctx\<close> queries the callee exit at
  a context \<open>ec ctx sc\<close> computed from the queried caller value \<open>sc\<close>, so its
  reassembly cannot be expressed as a pullback of the pp-typed \<open>etf_full\<close>.  Its
  full reassembled state at the unit global is \<open>etf_full_ctx_unit t \<sigma> =
  traverse_rhs t \<sigma> \<squnion> sides_of_rhs t \<sigma> (Inr ())\<close> (local Answer joined with the
  single global Side), which is polymorphic in the unknown type and so applies to
  the \<open>pp \<times> 'c\<close> combine tree directly.

  \<open>unit_combine_tree_ctx_sound\<close> is the smallest soundness contract: a caller store
  sound for the caller unknown \<open>(cc, ctx)\<close> and a callee-exit store sound for the
  callee unknown at the value-derived context \<open>(ex, ec ctx sc)\<close> combine
  (\<open><s|t>\<close>) into a store sound for the reassembled combine -- exactly the shape the
  witness-soundness combine case consumes (cf. the monovariant
  \<open>etf_sound_combine\<close>).  Pure \<open>combine_states_sound\<close>, value dependence isolated in
  the callee unknown index.
\<close>

definition etf_full_ctx_unit ::
  "(pp \<times> 'c, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> (pp \<times> 'c + unit \<Rightarrow> 'a abs_state) \<Rightarrow> 'a abs_state"
where
  "etf_full_ctx_unit t \<sigma> = traverse_rhs t \<sigma> \<squnion> sides_of_rhs t \<sigma> (Inr ())"

lemma etf_full_ctx_unit_combine_tree_ctx:
  "etf_full_ctx_unit (unit_combine_tree_ctx ec cc ex ctx) \<sigma>
   = \<langle>\<sigma> (Inl (cc, ctx)) \<squnion> \<sigma> (Inr ()) |
      \<sigma> (Inl (ex, ec ctx (\<sigma> (Inl (cc, ctx)) \<squnion> \<sigma> (Inr ())))) \<squnion> \<sigma> (Inr ())\<rangle>"
  unfolding etf_full_ctx_unit_def unit_combine_tree_ctx_def
  by (simp add: Let_def restrict_local_combine_eq restrict_global_combine_eq
        restrict_combine combine_abs_def)

lemma unit_combine_tree_ctx_sound:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma> (Inl (cc, ctx)) \<squnion> \<sigma> (Inr ())\<rbrakk>"
  assumes tc: "t \<in> \<lbrakk>\<sigma> (Inl (ex, ec ctx (\<sigma> (Inl (cc, ctx)) \<squnion> \<sigma> (Inr ())))) \<squnion> \<sigma> (Inr ())\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>etf_full_ctx_unit (unit_combine_tree_ctx ec cc ex ctx) \<sigma>\<rbrakk>"
  unfolding etf_full_ctx_unit_combine_tree_ctx
  using sc tc by (rule combine_states_sound)

text \<open>
  At the unit global the context env is the local unknown joined with the single
  global slot -- the form the combine contract reads.
\<close>

lemma side_env_ctx_unit_eq:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "side_env_ctx \<sigma> (v, ctx) = \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr ())"
  by (simp add: side_env_ctx_pull side_env_def pull_ctx_Inl pull_ctx_Inr glob_env_unit)

lemma combine_semantic_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx (\<lambda>ctx cc ex. unit_combine_tree_ctx ec cc ex ctx)
                    g etf bot0 s0 ()) x \<sigma> vars"
      and v: "(ret, ctx) \<in> vars"
      and e: "(cc, ex, ret) \<in> combines g"
      and finC: "finite (combines g)"
  shows "etf_full_ctx_unit (unit_combine_tree_ctx ec cc ex ctx) \<sigma>
         \<le> side_env_ctx \<sigma> (ret, ctx)"
proof -
  let ?cmb = "\<lambda>ctx cc ex. unit_combine_tree_ctx ec cc ex ctx"
  let ?t = "unit_combine_tree_ctx ec cc ex ctx"
  have posteq: "eq (side_cfg_T_eff_ctx ?cmb g etf bot0 s0 ()) (ret, ctx) \<sigma>
                  \<le> \<sigma> (Inl (ret, ctx))"
    using pp v by auto
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g ret)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have memtree:
    "?t \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                   (predecessor_list g ret)
              @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret))"
    using mem by force
  have loc: "traverse_rhs ?t \<sigma> \<le> \<sigma> (Inl (ret, ctx))"
    by (rule post_sol_tree_le_ctx[OF posteq memtree])
  have glob: "sides_of_rhs ?t \<sigma> (Inr ()) \<le> \<sigma> (Inr ())"
  proof -
    have "sides_of_rhs ?t \<sigma> (Inr ())
          \<le> sides_of_rhs
              (side_rhs_fold_ctx
                (if ret = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                     (predecessor_list g ret)
                 @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret)))
              \<sigma> (Inr ())"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_ctx ?cmb g etf bot0 s0 () (ret, ctx))
                      \<sigma> (Inr ())"
      by (rule sides_fold_le_side_cfg_T_eff_ctx)
    also have "\<dots> \<le> \<sigma> (Inr ())"
      by (rule side_post_solution_le_global_ctx[OF pp v])
    finally show ?thesis .
  qed
  have "etf_full_ctx_unit ?t \<sigma> \<le> \<sigma> (Inl (ret, ctx)) \<squnion> \<sigma> (Inr ())"
    unfolding etf_full_ctx_unit_def using loc glob by (rule sup_mono)
  also have "\<dots> = side_env_ctx \<sigma> (ret, ctx)"
    by (simp add: side_env_ctx_unit_eq)
  finally show ?thesis .
qed

text \<open>
  The semantic-combine case of the context witness-soundness induction, isolated
  as a standalone lemma.  Given the caller and callee induction hypotheses -- the
  caller trace lands in the caller unknown \<open>(cl, ctx)\<close> and the callee-exit trace
  in the callee unknown at the value-derived context \<open>(ex, ec ctx sc)\<close> with
  \<open>sc = \<sigma> (Inl (cl, ctx))\<close> the queried caller value -- plus the combine
  post-fixpoint bound at the return unknown \<open>(v, ctx)\<close>, the combined return state
  \<open><last tau|last rho>\<close> is sound at \<open>(v, ctx)\<close>.  The combine contract
  (\<open>unit_combine_tree_ctx_sound\<close>) does the value-dependent merge; the bound carries
  it to the return unknown.  This is the genuinely value-dependent step the
  conservative routing could not reach; it plugs into \<open>trace_witness_ctx.induct\<close>
  as the \<open>combine\<close> case.
\<close>

lemma combine_case_ctx_sound:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::sound_domain abs_state"
  assumes caller: "last tau \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>"
  assumes callee: "last rho \<in> \<lbrakk>side_env_ctx \<sigma> (ex, ec ctx (side_env_ctx \<sigma> (cl, ctx)))\<rbrakk>"
  assumes bound: "etf_full_ctx_unit (unit_combine_tree_ctx ec cl ex ctx) \<sigma>
                    \<le> side_env_ctx \<sigma> (v, ctx)"
  shows "<last tau|last rho> \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
proof -
  have "<last tau|last rho>
          \<in> \<lbrakk>etf_full_ctx_unit (unit_combine_tree_ctx ec cl ex ctx) \<sigma>\<rbrakk>"
  proof (rule unit_combine_tree_ctx_sound)
    show "last tau \<in> \<lbrakk>\<sigma> (Inl (cl, ctx)) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      using caller by (simp only: side_env_ctx_unit_eq)
    show "last rho \<in> \<lbrakk>\<sigma> (Inl (ex, ec ctx (\<sigma> (Inl (cl, ctx)) \<squnion> \<sigma> (Inr ())))) \<squnion> \<sigma> (Inr ())\<rbrakk>"
      using callee by (simp only: side_env_ctx_unit_eq)
  qed
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

subsection \<open>Semantic-context soundness via the trace collecting semantics\<close>

text \<open>
  The full lift threads the analyzer context through the plain trace witness with
  the analyzer context as a UNIVERSALLY quantified parameter, filtered by digest
  compatibility \<open>cmp (dg tr) ctx\<close> --- exactly the shape of \<open>cfg_collect_ctx\<close> (B0).
  This avoids the false equality \<open>c2 = ec c1 (sigma (Inl (cl,c1)))\<close> that an
  incremental \<open>trace_witness_ctx\<close> induction would demand (it collapses \<open>ec\<close> to a
  constant / monovariant routing).  The two genuine digest-propagation steps are
  isolated as separate lemmas below; the combine return step is discharged by the
  already-proved \<open>combine_case_ctx_sound\<close>.
\<close>

text \<open>
  Prefix compatibility: a digest compatible on a combine (return) trace is
  compatible on its caller prefix.  For an entry-state digest the return restores
  the caller's activation, so \<open>dg\<close> of the combined trace equals \<open>dg\<close> of the caller.
\<close>
lemma prefix_compat_return:
  fixes dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  assumes dg_return: "\<And>tau rho. dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  assumes compat: "cmp (dg (tau @ tl rho @ [<last tau|last rho>])) ctx"
  shows "cmp (dg tau) ctx"
  using compat by (simp add: dg_return)

text \<open>
  Callee-entry compatibility: when the callee trace starts at the enter-state of a
  caller-final store that the analyzer soundly covers at \<open>(cl, ctx)\<close>, the callee
  digest is compatible with the value-derived callee context
  \<open>ec ctx (sigma (Inl (cl,ctx)))\<close>.  This bundles two instance facts: \<open>dg\<close> of a
  freshly entered callee depends only on its entry store (\<open>dg_callee\<close>), and the
  abstract entry context is monotone w.r.t. the concretization (\<open>enter_mono\<close>).
  The genuinely value-dependent soundness step.
\<close>
lemma callee_entry_compat:
  fixes dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and ec :: "'c \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'c"
    and entdg :: "store \<Rightarrow> 'c"
    and \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a abs_state"
  assumes dg_callee: "\<And>tau rho. hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
  assumes enter_mono:
    "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk> \<Longrightarrow> cmp (entdg s) (ec ctx (\<sigma> (Inl (cl, ctx))))"
  assumes hd: "hd rho = enter_state (last tau)"
  assumes caller: "last tau \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>"
  shows "cmp (dg rho) (ec ctx (\<sigma> (Inl (cl, ctx))))"
proof -
  have "dg rho = entdg (last tau)" using dg_callee[OF hd] .
  thus ?thesis using enter_mono[OF caller] by simp
qed

text \<open>
  Semantic-context soundness.  Parametric in the abstract context machinery
  (\<open>dg\<close>, \<open>cmp\<close>, \<open>ec\<close>, \<open>entdg\<close>) and a solution \<open>sigma\<close>, given:
  per-step analyzer soundness at a FIXED context (\<open>ENTRY\<close>/\<open>PROC_ENTRY\<close>/\<open>EDGE\<close>),
  the semantic combine post-fixpoint bound (\<open>COMB_BOUND\<close>), digest stability under
  intra/return steps (\<open>DG_INTRA\<close>/\<open>DG_RETURN\<close>), and the callee-entry compatibility
  primitives (\<open>DG_CALLEE\<close>/\<open>ENTER_MONO\<close>) --- every trace reaching \<open>v\<close> whose digest is
  \<open>cmp\<close>-compatible with \<open>ctx\<close> ends in a store covered by the analyzer at \<open>(v, ctx)\<close>.
  \<open>'c = unit\<close> with a trivial \<open>cmp\<close> recovers the monovariant guarantee.
\<close>
theorem post_fixpoint_sound_at_ctx_semantic:
  fixes \<sigma> :: "pp \<times> 'c + unit \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and ec :: "'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_ctx \<sigma> (u, ctx)\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
    and COMB_BOUND: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> etf_full_ctx_unit (unit_combine_tree_ctx ec cl ex ctx) \<sigma> \<le> side_env_ctx \<sigma> (v, ctx)"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (ec ctx (side_env_ctx \<sigma> (cl, ctx)))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
proof -
  from wit have "cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
  proof (induction arbitrary: ctx rule: trace_witness.induct)
    case (entry v s)
    have "s \<in> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
      using ENTRY entry.hyps entry.prems by blast
    thus ?case using entry.hyps by simp
  next
    case (proc_entry v s)
    have "s \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
      using PROC_ENTRY proc_entry.hyps proc_entry.prems by blast
    thus ?case by simp
  next
    case (edge u a v tr s')
    have tr_ne: "tr \<noteq> []" using edge.hyps(2) by (rule trace_witness_nonempty)
    have ctr: "cmp (dg tr) ctx"
      by (rule DG_INTRA[OF tr_ne edge.prems])
    have lt: "last tr \<in> \<lbrakk>side_env_ctx \<sigma> (u, ctx)\<rbrakk>" using edge.IH[OF ctr] .
    have "s' \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>" using EDGE edge.hyps lt by blast
    thus ?case by simp
  next
    case (combine cl ex v tau rho)
    have tau_ne: "tau \<noteq> []" using combine.hyps(2) by (rule trace_witness_nonempty)
    have rho_ne: "rho \<noteq> []" using combine.hyps(3) by (rule trace_witness_nonempty)
    have ctau: "cmp (dg tau) ctx"
      using combine.prems DG_RETURN[OF tau_ne, of rho] by simp
    have caller_sound: "last tau \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>"
      using combine.IH(1)[OF ctau] .
    have crho: "cmp (dg rho) (ec ctx (side_env_ctx \<sigma> (cl, ctx)))"
      \<comment> \<open>the body of @{thm callee_entry_compat}, inlined to dodge the
          higher-order @{term ec}/@{term cmp} unifier ambiguity an \<open>OF\<close> hits\<close>
    proof -
      have "dg rho = entdg (last tau)" using DG_CALLEE[OF rho_ne combine.hyps(4)] .
      thus ?thesis using ENTER_MONO[OF caller_sound] by simp
    qed
    have callee_sound: "last rho \<in> \<lbrakk>side_env_ctx \<sigma> (ex, ec ctx (side_env_ctx \<sigma> (cl, ctx)))\<rbrakk>"
      using combine.IH(2)[OF crho] .
    have bound: "etf_full_ctx_unit (unit_combine_tree_ctx ec cl ex ctx) \<sigma>
                   \<le> side_env_ctx \<sigma> (v, ctx)"
      using COMB_BOUND[OF combine.hyps(1)] .
    have "<last tau|last rho> \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
      using combine_case_ctx_sound[OF caller_sound callee_sound bound] .
    thus ?case
      by (metis last_appendR snoc_eq_iff_butlast)
  qed
  thus ?thesis using compat by blast
qed

subsection \<open>Concrete entry-store context instance\<close>

definition entry_store_dg :: "store list \<Rightarrow> store set" where
  "entry_store_dg tr = {hd tr}"

definition entry_store_ec :: "store set \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> store set" where
  "entry_store_ec ctx a = edge_collect EA_Enter \<lbrakk>a\<rbrakk>"

definition entry_store_entdg :: "store \<Rightarrow> store set" where
  "entry_store_entdg s = {enter_state s}"

lemma entry_store_dg_intra:
  assumes "tr \<noteq> []"
  assumes "entry_store_dg (tr @ [s']) \<subseteq> ctx"
  shows "entry_store_dg tr \<subseteq> ctx"
  using assms unfolding entry_store_dg_def by (cases tr) auto

lemma entry_store_dg_return:
  assumes "tau \<noteq> []"
  shows "entry_store_dg (tau @ tl rho @ [<last tau|last rho>]) = entry_store_dg tau"
  using assms unfolding entry_store_dg_def by (cases tau) auto

lemma entry_store_dg_callee:
  assumes "rho \<noteq> []"
  assumes "hd rho = enter_state (last tau)"
  shows "entry_store_dg rho = entry_store_entdg (last tau)"
  using assms unfolding entry_store_dg_def entry_store_entdg_def by simp

lemma entry_store_enter_mono:
  assumes "s \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk>"
  shows "entry_store_entdg s \<subseteq> entry_store_ec ctx (side_env_ctx \<sigma> (cl, ctx))"
  using assms unfolding entry_store_entdg_def entry_store_ec_def by auto

lemma entry_store_edge_sound_ctx:
  fixes \<sigma> :: "pp \<times> store set + unit \<Rightarrow> 'a::sound_domain abs_state"
  assumes stf: "sound_effectful_transfer etf"
  assumes inr: "inr_slot_locals_bot_ctx \<sigma>"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx (\<lambda>ctx cc ex. unit_combine_tree_ctx entry_store_ec cc ex ctx)
                    g etf bot0 s0 ()) x \<sigma> vars"
  assumes cover: "(v, ctx) \<in> vars"
  assumes edge: "(u, a, v) \<in> edges g"
  assumes fin: "finite (edges g)"
  assumes step: "edge_step a s = Some s'"
  assumes src: "s \<in> \<lbrakk>side_env_ctx \<sigma> (u, ctx)\<rbrakk>"
  shows "s' \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
proof -
  let ?cmb = "\<lambda>ctx cc ex. unit_combine_tree_ctx entry_store_ec cc ex ctx"
  have src_pull: "s \<in> \<lbrakk>side_env (pull_ctx ctx \<sigma>) u\<rbrakk>"
    using src by (simp add: side_env_ctx_pull)
  have step_mem: "s' \<in> edge_collect a {s}"
    using step by (simp add: edge_collect_single)
  have step_full: "s' \<in> \<lbrakk>etf_collecting_full (apply_etf etf a u) (pull_ctx ctx \<sigma>)\<rbrakk>"
  proof -
    have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>side_env (pull_ctx ctx \<sigma>) u\<rbrakk>"
      using src_pull edge_collect_mono[of "{s}" "\<lbrakk>side_env (pull_ctx ctx \<sigma>) u\<rbrakk>" a] by auto
    thus ?thesis
      using step_mem
        TD_Side_Eff_Sound.sound_effectful_transfer.edge_collect_etf_sound
          [OF stf inr_slot_locals_bot_pull_ctx[OF inr]]
      by blast
  qed
  have full_le: "etf_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (v, ctx)"
    by (rule etf_combined_le_ctx[OF pp cover edge fin])
  have collect_le_pull:
    "etf_collecting_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env (pull_ctx ctx \<sigma>) v"
    by (rule etf_collecting_full_le_side_env[OF full_le[unfolded side_env_ctx_pull]])
  have collect_le: "etf_collecting_full (apply_etf etf a u) (pull_ctx ctx \<sigma>) \<le> side_env_ctx \<sigma> (v, ctx)"
    using collect_le_pull by (simp add: side_env_ctx_pull)
  show ?thesis using gamma_state_mono[OF collect_le] step_full by blast
qed

theorem semantic_entry_store_ctx_analysis_sound:
  fixes \<sigma> :: "pp \<times> store set + unit \<Rightarrow> 'a::sound_domain abs_state"
  assumes stf: "sound_effectful_transfer etf"
  assumes inr: "inr_slot_locals_bot_ctx \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_ctx (\<lambda>ctx cc ex. unit_combine_tree_ctx entry_store_ec cc ex ctx)
                    g etf bot0 s0 ()) x \<sigma> vars"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cover_entry: "\<And>ctx. (cfg_entry g, ctx) \<in> vars"
  assumes cover_edge: "\<And>ctx u a v. (u, a, v) \<in> edges g \<Longrightarrow> (v, ctx) \<in> vars"
  assumes cover_comb: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g \<Longrightarrow> (v, ctx) \<in> vars"
  shows "cfg_collect_ctx entry_store_dg (\<subseteq>) g S v ctx \<le> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
proof -
  have trace_sound:
    "\<And>tr. trace_witness g S v tr \<Longrightarrow> entry_store_dg tr \<subseteq> ctx
      \<Longrightarrow> last tr \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
  proof (rule post_fixpoint_sound_at_ctx_semantic)
    fix ctx s assume sS: "s \<in> S" and compat: "entry_store_dg [s] \<subseteq> ctx"
    have "s \<in> \<lbrakk>s0\<rbrakk>" using S_sound sS by blast
    moreover have "s0 \<le> side_env_ctx \<sigma> (cfg_entry g, ctx)"
      by (rule s0_le_side_env_ctx_entry[OF pp cover_entry])
    ultimately show "s \<in> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
      using gamma_state_mono by blast
  next
    fix ctx v s
    assume enter: "(cfg_entry g, EA_Enter, v) \<in> edges g"
      and s_ent: "s \<in> enter_state ` S"
      and compat: "entry_store_dg [s] \<subseteq> ctx"
    obtain s0c where s0c: "s0c \<in> S" and s: "s = enter_state s0c"
      using s_ent by blast
    have src0: "s0c \<in> \<lbrakk>s0\<rbrakk>" using S_sound s0c by blast
    have entry_le: "s0 \<le> side_env_ctx \<sigma> (cfg_entry g, ctx)"
      by (rule s0_le_side_env_ctx_entry[OF pp cover_entry])
    have src: "s0c \<in> \<lbrakk>side_env_ctx \<sigma> (cfg_entry g, ctx)\<rbrakk>"
      using gamma_state_mono[OF entry_le] src0 by blast
    have step: "edge_step EA_Enter s0c = Some s" using s by simp
    show "s \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
      by (rule entry_store_edge_sound_ctx[OF stf inr pp cover_edge[OF enter] enter fin step src])
  next
    fix ctx u a v tr s'
    assume edge: "(u, a, v) \<in> edges g"
      and step: "edge_step a (last tr) = Some s'"
      and src: "last tr \<in> \<lbrakk>side_env_ctx \<sigma> (u, ctx)\<rbrakk>"
    show "s' \<in> \<lbrakk>side_env_ctx \<sigma> (v, ctx)\<rbrakk>"
      by (rule entry_store_edge_sound_ctx[OF stf inr pp cover_edge[OF edge] edge fin step src])
  next
    fix ctx cl ex v
    assume comb: "(cl, ex, v) \<in> combines g"
    show "etf_full_ctx_unit (unit_combine_tree_ctx entry_store_ec cl ex ctx) \<sigma> \<le> side_env_ctx \<sigma> (v, ctx)"
      by (rule combine_semantic_le_ctx[OF pp cover_comb[OF comb] comb finC])
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> entry_store_dg (tr @ [s']) \<subseteq> ctx \<Longrightarrow> entry_store_dg tr \<subseteq> ctx"
      by (rule entry_store_dg_intra)
  next
    show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> entry_store_dg (tau @ tl rho @ [<last tau|last rho>]) = entry_store_dg tau"
      by (rule entry_store_dg_return)
  next
    show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> entry_store_dg rho = entry_store_entdg (last tau)"
      by (rule entry_store_dg_callee)
  next
    show "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx \<sigma> (cl, ctx)\<rbrakk> \<Longrightarrow> entry_store_entdg s \<subseteq> entry_store_ec ctx (side_env_ctx \<sigma> (cl, ctx))"
      by (rule entry_store_enter_mono)
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using trace_sound by auto
qed

end
