theory TD_Side_Eff_Cmp_Gen
  imports TD_Side_Eff_Cmp_Pull
begin

section \<open>Keyed-global generator: routing global writes by context\<close>

text \<open>
  The concrete generator behind the keyed pullback soundness of
  \<open>TD_Side_Eff_Cmp_Pull\<close>.  The context generator \<^const>\<open>side_cfg_T_eff_ctx\<close> relabels
  only the \<^emph>\<open>local\<close> unknowns of a per-edge tree (\<^const>\<open>map_ltree\<close>: \<open>QueryL\<close>
  targets), leaving \<open>QueryG\<close> / \<open>Side\<close> global keys fixed --- so all contexts write
  the same global slot and no per-context global is recoverable.

  A keyed generator must \<^emph>\<open>also\<close> route the global writes: within a procedure the
  context \<open>c\<close> is fixed, so every global \<open>Side\<close> under \<open>c\<close> is sent to the keyed slot
  \<open>gkey c\<close>.  \<open>map_gtree\<close> performs the missing global-key relabelling
  (the \<open>QueryG\<close> / \<open>Side\<close> analogue of \<^const>\<open>map_ltree\<close>); \<open>traverse_rhs_map_gtree\<close>
  shows it commutes with the denotation under the matching \<^const>\<open>map_sum\<close>-pullback
  of the global slots, exactly as \<open>traverse_rhs_map_ltree\<close> does on the local side.
\<close>

subsection \<open>Relabelling global keys\<close>

primrec map_gtree ::
  "('g \<Rightarrow> 'h) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'h, 'd) strategy_tree" where
  "map_gtree r (Answer d) = Answer d"
| "map_gtree r (QueryL y f) = QueryL y (\<lambda>d. map_gtree r (f d))"
| "map_gtree r (QueryG y f) = QueryG (r y) (\<lambda>d. map_gtree r (f d))"
| "map_gtree r (Side y d t) = Side (r y) d (map_gtree r t)"

text \<open>
  The denotation of a global-relabelled tree is the original read against the
  \<^const>\<open>map_sum\<close>-pullback that reroutes the global slots by \<open>r\<close>; locals are
  untouched.  Global side (\<open>QueryG\<close>) reads at key \<open>r y\<close> exactly match reading the
  pulled-back environment at \<open>y\<close>.  Mirrors \<open>traverse_rhs_map_ltree\<close>.
\<close>

lemma traverse_rhs_map_gtree:
  "traverse_rhs (map_gtree r t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum id r z))"
  by (induction t) auto

subsection \<open>The keyed generator\<close>

text \<open>
  \<open>side_cfg_T_eff_cmp\<close> is \<^const>\<open>side_cfg_T_eff_ctx_seeded\<close>'s keyed sibling: the
  intra per-edge trees are relabelled locally by context (\<^const>\<open>map_ltree\<close>) and
  their global writes routed to the keyed slot \<^term>\<open>gkey c\<close> (\<^const>\<open>map_gtree\<close>).
  The entry seed writes the initial globals to the entry context's key.  The
  combine builder \<open>cmb\<close> stays a parameter, exactly as in the context generator ---
  the value-dependent semantic combine is supplied per instance.
\<close>

definition side_cfg_T_eff_cmp ::
  "('c \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>);
            intra = map (\<lambda>(u, a).
                          map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global s0) t else t)"

text \<open>
  Denotation at \<open>(v, ctx)\<close>: the entry \<open>Side\<close> wrapper is denotation-transparent, so
  the unknown's value is the \<^const>\<open>side_acc_ctx\<close> fold over the keyed intra trees
  and the combine trees.  Mirrors \<open>eq_side_cfg_T_eff_ctx_seeded\<close>.
\<close>

lemma eq_side_cfg_T_eff_cmp:
  "eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx
       ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)) \<sigma>
       (map (\<lambda>(u, a).
              map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_cmp_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

text \<open>
  The reaching-definitions writer-keyed variant routes intra-edge global writes to
  the target program point's writer key.  The reader context still indexes local
  unknowns; only the Side target of the unit-global edge tree changes from
  \<open>gkey ctx\<close> to \<open>site v\<close>.
\<close>
definition side_cfg_T_eff_cmp_site ::
  "(pp \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>);
            intra = map (\<lambda>(u, a).
                          map_gtree (\<lambda>_. site v)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (site v) (restrict_global s0) t else t)"

lemma eq_side_cfg_T_eff_cmp_site:
  "eq (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx
       ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)) \<sigma>
       (map (\<lambda>(u, a).
              map_gtree (\<lambda>_. site v)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_cmp_site_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

text \<open>
  Return-aware site-keyed variant.  The target program point is passed to the
  combine builder, so combine-side \<^const>\<open>Side\<close> nodes can use the same writer
  key as the equation endpoint when an instance needs that routing.
\<close>
definition side_cfg_T_eff_cmp_site_ret ::
  "(pp \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_cmp_site_ret site cmb g etf fresh_frame bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>);
            intra = map (\<lambda>(u, a).
                          map_gtree (\<lambda>_. site v)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c v cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (site v) (restrict_global s0) t else t)"

lemma eq_side_cfg_T_eff_cmp_site_ret:
  "eq (side_cfg_T_eff_cmp_site_ret site cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx
       ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)) \<sigma>
       (map (\<lambda>(u, a).
              map_gtree (\<lambda>_. site v)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). cmb ctx v cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_cmp_site_ret_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

subsection \<open>Routing: the keyed intra tree reads the context / keyed-slot pullback\<close>

text \<open>
  Composing the two relabel commutes: a keyed intra tree denotes \<^const>\<open>apply_etf\<close>
  read against the environment that reroutes locals to their context copy
  (\<open>w \<mapsto> (w, ctx)\<close>) and the transfer's global slot to the context key \<open>gkey ctx\<close>.
  This is the local half of routing correctness --- it exhibits, as a \<^const>\<open>map_sum\<close>
  pullback, precisely which slots a keyed edge tree consults.  Tying it to the
  \<^const>\<open>pull_cmp\<close> bound of \<open>post_fixpoint_sound_at_cmp_pull\<close> then needs the global
  side-aggregation bound and the key-compatibility side condition \<open>gcmp ctx (gkey ctx)\<close>.
\<close>

lemma traverse_intra_cmp:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
   = traverse_rhs t (\<lambda>z. \<sigma> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z))"
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp o_def)

subsection \<open>The keyed intra pullback and its side commutes\<close>

text \<open>
  \<open>pull_gk\<close> is the (unit-global) environment a keyed intra tree reads: locals
  at the context copy, the transfer's single global slot at the context key
  \<open>gkey ctx\<close>.  It is the keyed generator's analogue of \<^const>\<open>pull_ctx\<close> --- \<^const>\<open>apply_etf\<close>
  is \<^typ>\<open>unit\<close>-global, so keying happens by which \<^emph>\<open>keyed\<close> slot the single unit
  slot is mapped to, namely \<open>gkey ctx\<close>.
\<close>

definition pull_gk ::
  "('c \<Rightarrow> 'g) \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state)"
where
  "pull_gk gkey ctx \<sigma> = (\<lambda>z. \<sigma> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z))"

lemma pull_gk_Inl: "pull_gk gkey ctx \<sigma> (Inl w) = \<sigma> (Inl (w, ctx))"
  by (simp add: pull_gk_def)

lemma pull_gk_Inr: "pull_gk gkey ctx \<sigma> (Inr y) = \<sigma> (Inr (gkey ctx))"
  by (simp add: pull_gk_def)

text \<open>The intra tree denotes \<^const>\<open>apply_etf\<close> against \<^const>\<open>pull_gk\<close> (restating \<open>traverse_intra_cmp\<close>).\<close>
lemma traverse_intra_pull_gk:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
   = traverse_rhs t (pull_gk gkey ctx \<sigma>)"
  by (simp add: traverse_intra_cmp pull_gk_def)

text \<open>
  The side commutes: \<^const>\<open>map_ltree\<close> leaves \<open>QueryG\<close> / \<open>Side\<close> keys fixed, so its
  per-name side map is the original read against the local pullback; \<^const>\<open>map_gtree\<close>
  with a constant relabel concentrates every \<^typ>\<open>unit\<close> \<open>Side\<close> at \<open>r ()\<close>.  Composed,
  a keyed intra tree's contribution at slot \<open>gkey ctx\<close> is the transfer's unit-slot
  contribution read against \<^const>\<open>pull_gk\<close>.
\<close>

lemma sides_map_ltree_Inr:
  "sides_of_rhs (map_ltree h t) \<sigma> (Inr gg)
   = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum h id z)) (Inr gg)"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_unit:
  fixes t :: "('x, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  shows "sides_of_rhs (map_gtree r t) \<sigma> (Inr (r ()))
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id r z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_off:
  "k \<notin> range r \<Longrightarrow> sides_of_rhs (map_gtree r t) \<sigma> (Inr k) = bot"
  by (induction t) (auto simp: Let_def)

lemma sides_intra_pull_gk:
  fixes t :: "(pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  shows "sides_of_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
           (Inr (gkey ctx))
         = sides_of_rhs t (pull_gk gkey ctx \<sigma>) (Inr ())"
proof -
  have "sides_of_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
          (Inr ((\<lambda>_. gkey ctx) ()))
        = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) t)
            (\<lambda>z. \<sigma> (map_sum id (\<lambda>_. gkey ctx) z)) (Inr ())"
    by (rule sides_map_gtree_unit)
  also have "\<dots> = sides_of_rhs t
            (\<lambda>z'. (\<lambda>z. \<sigma> (map_sum id (\<lambda>_. gkey ctx) z)) (map_sum (\<lambda>w. (w, ctx)) id z'))
            (Inr ())"
    by (rule sides_map_ltree_Inr)
  also have "\<dots> = sides_of_rhs t (pull_gk gkey ctx \<sigma>) (Inr ())"
    by (simp add: pull_gk_def sum.map_comp o_def)
  finally show ?thesis by simp
qed

subsection \<open>Post-fixpoint global bounds for the keyed generator\<close>

text \<open>
  Mirrors \<open>sides_fold_le_side_cfg_T_eff_ctx\<close> / \<open>side_post_solution_le_global_ctx\<close>:
  the entry \<open>Side\<close> wrapper (at key \<open>gkey ctx\<close>) only adds to the fold's contribution,
  and a post-solution's global side never exceeds the corresponding slot.
\<close>

lemma sides_fold_le_side_cfg_T_eff_cmp:
  shows "sides_of_rhs (side_rhs_fold_ctx
           ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
            \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>))
           (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                (non_enter_predecessor_list g v)
            @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))
           \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (v, ctx))
             \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_cmp_def
  by (cases "v = cfg_entry g") (auto simp: Let_def fun_upd_def)

lemma side_post_solution_le_global_cmp:
  assumes pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (v, ctx))
           \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v
  have "sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (v, ctx)) \<sigma> \<le> \<sigma>"
    by auto
  thus ?thesis by (rule le_funD)
qed

subsection \<open>Routing correctness: the keyed edge bound\<close>

text \<open>
  The keyed analogue of \<open>etf_combined_le_ctx\<close> and the crux of generator soundness:
  at a post-fixpoint of \<^const>\<open>side_cfg_T_eff_cmp\<close> the reassembled per-edge transfer,
  read against \<^const>\<open>pull_gk\<close>, sits below the pulled-back read at the edge target.
  The local part is the traverse bound (\<open>traverse_intra_pull_gk\<close> + the post-fixpoint);
  the global part runs the side chain \<open>sides_intra_pull_gk\<close> \<open>\<rightarrow>\<close>
  \<open>sides_le_side_rhs_fold_ctx\<close> \<open>\<rightarrow>\<close> \<open>sides_fold_le_side_cfg_T_eff_cmp\<close> \<open>\<rightarrow>\<close>
  \<open>side_post_solution_le_global_cmp\<close>, landing the keyed slot \<open>gkey ctx\<close>.  Because
  \<^const>\<open>apply_etf\<close> is \<^typ>\<open>unit\<close>-global, \<^const>\<open>all_sides\<close> is that single slot's
  contribution, so no per-key join is needed.
\<close>

lemma side_cfg_T_eff_cmp_edge_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
      and e: "(u, a, v) \<in> edges g"
      and ane: "a \<noteq> EA_Enter"
      and fin: "finite (edges g)"
  shows "etf_full (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
           \<le> side_env (pull_gk gkey ctx \<sigma>) v"
proof -
  have posteq: "eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>
                  \<le> \<sigma> (Inl (v, ctx))"
    using pp v by auto
  have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
    using e ane
    by (simp add: non_enter_predecessor_list_def set_predecessor_list[OF fin] predecessors_def)
  have memtree:
    "map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
       \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                   (non_enter_predecessor_list g v)
              @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
    using mem by force
  have loc: "traverse_rhs (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
               \<le> \<sigma> (Inl (v, ctx))"
  proof -
    have "traverse_rhs (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
            = traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) \<sigma>"
      by (rule traverse_intra_pull_gk[symmetric])
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp by (rule traverse_le_side_acc_ctx[OF memtree])
    also have "\<dots> \<le> \<sigma> (Inl (v, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have glob: "all_sides (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
                \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "all_sides (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
            = sides_of_rhs (apply_etf etf a u) (pull_gk gkey ctx \<sigma>) (Inr ())"
      by (rule all_sides_eq_sides_Inr_unit)
    also have "\<dots> = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                     (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) \<sigma> (Inr (gkey ctx))"
      by (rule sides_intra_pull_gk[symmetric])
    also have "\<dots> \<le> sides_of_rhs (side_rhs_fold_ctx
                     ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                      \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>))
                     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                          (non_enter_predecessor_list g v)
                      @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))
                     \<sigma> (Inr (gkey ctx))"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (v, ctx))
                     \<sigma> (Inr (gkey ctx))"
      by (rule sides_fold_le_side_cfg_T_eff_cmp)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))"
      by (rule side_post_solution_le_global_cmp[OF pp v])
    finally show ?thesis .
  qed
  have "etf_full (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
        = traverse_rhs (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
          \<squnion> all_sides (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (gkey ctx))"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env (pull_gk gkey ctx \<sigma>) v"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed


subsection \<open>Site-keyed edge bound\<close>

text \<open>
  The def-site-keyed analogue of @{thm [source] side_cfg_T_eff_cmp_edge_le}: each intra
  edge into \<open>v\<close> publishes to the single slot \<^term>\<open>Inr (site v)\<close> (the target's writer
  key), so the per-edge transfer, read through @{const pull_gk} with the constant keyer
  \<^term>\<open>\<lambda>_. site v\<close>, sits below \<^term>\<open>\<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (site v))\<close>.  Mirrors the
  cmp proof; the two helpers below are the site instances of
  @{thm [source] sides_fold_le_side_cfg_T_eff_cmp} and
  @{thm [source] side_post_solution_le_global_cmp}.
\<close>

lemma sides_fold_le_side_cfg_T_eff_cmp_site:
  shows "sides_of_rhs (side_rhs_fold_ctx
           ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
            \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>))
           (map (\<lambda>(u, a). map_gtree (\<lambda>_. site v)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                (non_enter_predecessor_list g v)
            @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))
           \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0 (v, ctx))
             \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_cmp_site_def
  by (cases "v = cfg_entry g") (auto simp: Let_def fun_upd_def)

lemma side_post_solution_le_global_site:
  assumes pp: "part_post_solution (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0 (v, ctx))
           \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v
  have "sides_of_rhs (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0 (v, ctx)) \<sigma> \<le> \<sigma>"
    by auto
  thus ?thesis by (rule le_funD)
qed

lemma side_cfg_T_eff_cmp_site_edge_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes pp: "part_post_solution (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
      and e: "(u, a, v) \<in> edges g"
      and ane: "a \<noteq> EA_Enter"
      and fin: "finite (edges g)"
  shows "etf_full (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
           \<le> side_env (pull_gk (\<lambda>_. site v) ctx \<sigma>) v"
proof -
  have posteq: "eq (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>
                  \<le> \<sigma> (Inl (v, ctx))"
    using pp v by auto
  have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
    using e ane
    by (simp add: non_enter_predecessor_list_def set_predecessor_list[OF fin] predecessors_def)
  have memtree:
    "map_gtree (\<lambda>_. site v) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
       \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. site v)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                   (non_enter_predecessor_list g v)
              @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
    using mem by force
  have loc: "traverse_rhs (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
               \<le> \<sigma> (Inl (v, ctx))"
  proof -
    have "traverse_rhs (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
            = traverse_rhs (map_gtree (\<lambda>_. site v)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) \<sigma>"
      by (rule traverse_intra_pull_gk[where gkey = "\<lambda>_. site v", symmetric])
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp_site by (rule traverse_le_side_acc_ctx[OF memtree])
    also have "\<dots> \<le> \<sigma> (Inl (v, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have glob: "all_sides (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
                \<le> \<sigma> (Inr (site v))"
  proof -
    have "all_sides (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
            = sides_of_rhs (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>) (Inr ())"
      by (rule all_sides_eq_sides_Inr_unit)
    also have "\<dots> = sides_of_rhs (map_gtree (\<lambda>_. site v)
                     (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) \<sigma> (Inr (site v))"
      by (rule sides_intra_pull_gk[where gkey = "\<lambda>_. site v", symmetric])
    also have "\<dots> \<le> sides_of_rhs (side_rhs_fold_ctx
                     ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                      \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>))
                     (map (\<lambda>(u, a). map_gtree (\<lambda>_. site v)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                          (non_enter_predecessor_list g v)
                      @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))
                     \<sigma> (Inr (site v))"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_cmp_site site cmb g etf fresh_frame bot0 s0 (v, ctx))
                     \<sigma> (Inr (site v))"
      by (rule sides_fold_le_side_cfg_T_eff_cmp_site)
    also have "\<dots> \<le> \<sigma> (Inr (site v))"
      by (rule side_post_solution_le_global_site[OF pp v])
    finally show ?thesis .
  qed
  have "etf_full (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
        = traverse_rhs (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)
          \<squnion> all_sides (apply_etf etf a u) (pull_gk (\<lambda>_. site v) ctx \<sigma>)"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (site v))"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env (pull_gk (\<lambda>_. site v) ctx \<sigma>) v"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed

lemma inr_slot_locals_bot_pull_gk:
  assumes "inr_slot_locals_bot_ctx \<sigma>"
  shows "inr_slot_locals_bot (pull_gk gkey ctx \<sigma>)"
  using assms
  by (simp add: inr_slot_locals_bot_ctx_def inr_slot_locals_bot_def pull_gk_Inr)

lemma inl_slot_globals_bot_pull_gk:
  assumes "inl_slot_globals_bot_ctx \<sigma>"
  shows "inl_slot_globals_bot (pull_gk gkey ctx \<sigma>)"
  using assms
  by (simp add: inl_slot_globals_bot_ctx_def inl_slot_globals_bot_def pull_gk_Inl)

text \<open>
  The retain keyed invariant: every context copy's local globals sit below that
  context's keyed slot.  It is the keyed analogue of @{const inl_glob_le_glob_env},
  and @{const inl_slot_globals_bot_ctx} implies it.  Its pullback is exactly the
  @{const inl_glob_le_glob_env} the weak enter contract needs.
\<close>
definition inl_glob_le_keyed_ctx ::
  "('c \<Rightarrow> 'g) \<Rightarrow> (pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> bool"
where
  "inl_glob_le_keyed_ctx gkey \<sigma> =
     (\<forall>v ctx. \<forall>x. is_global x \<longrightarrow> \<sigma> (Inl (v, ctx)) x \<le> \<sigma> (Inr (gkey ctx)) x)"

lemma inl_slot_globals_bot_ctx_le_keyed:
  "inl_slot_globals_bot_ctx \<sigma> \<Longrightarrow> inl_glob_le_keyed_ctx gkey \<sigma>"
  by (auto simp: inl_slot_globals_bot_ctx_def inl_glob_le_keyed_ctx_def)

lemma inl_glob_le_glob_env_pull_gk:
  assumes "inl_glob_le_keyed_ctx gkey \<sigma>"
  shows "inl_glob_le_glob_env (pull_gk gkey ctx \<sigma>)"
  using assms
  by (simp add: inl_glob_le_keyed_ctx_def inl_glob_le_glob_env_def
        glob_env_unit pull_gk_Inl pull_gk_Inr)

subsection \<open>The retain keyed invariant is derivable from an exact solution\<close>

text \<open>
  \<^const>\<open>inl_glob_le_keyed_ctx\<close> is not an axiom: it is the globals-projection of the
  exact-fixpoint property.  At an exact \<^const>\<open>part_solution\<close> each retain edge
  publishes its written global to the keyed slot (the intra tree's \<open>Side\<close>), while its
  full result --- globals included --- is the local Answer.  So the local slot's
  globals are a sub-join of what the keyed slot accumulates, hence dominated by it.
  A mere \<^const>\<open>part_post_solution\<close> is insufficient: it bounds the equation \<^emph>\<open>below\<close>
  the local slot but leaves the local slot itself unbounded \<^emph>\<open>above\<close>, so an
  adversarial post-solution can inflate a local global past the keyed slot.  The
  vendored always-join side solver returns an exact \<^const>\<open>part_solution\<close> (no
  widening), so the invariant holds at every reachable slot.
\<close>

lemma restrict_global_sup:
  "restrict_global (a \<squnion> b)
     = restrict_global a \<squnion> restrict_global (b :: 'a::bounded_semilattice_sup_bot abs_state)"
  by (rule ext) (simp add: restrict_global_def sup_fun_def)

lemma restrict_global_bot:
  "restrict_global (\<bottom> :: 'a::bounded_semilattice_sup_bot abs_state) = \<bottom>"
  by (rule ext) (simp add: restrict_global_def bot_fun_def)

lemma restrict_global_restrict_local_bot:
  "restrict_global (restrict_local (s :: 'a::bounded_semilattice_sup_bot abs_state)) = \<bottom>"
  by (rule ext) (simp add: restrict_global_def restrict_local_def bot_fun_def)

text \<open>
  Fold lemma: the global part of a \<^const>\<open>side_rhs_fold_ctx\<close> traverse is dominated by
  the seed's global part joined with the fold's aggregated side, provided every folded
  tree's traverse-global is dominated by its own side.  Straight induction over the
  fold with \<open>traverse_seqcomp\<close> / \<open>sides_of_rhs_seqcomp_at\<close>.
\<close>
lemma restrict_global_traverse_side_rhs_fold_ctx_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and ts :: "(pp \<times> 'c, 'g, 'a abs_state) strategy_tree list"
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr gg)"
  shows "restrict_global (traverse_rhs (side_rhs_fold_ctx acc ts) \<sigma>)
           \<le> restrict_global acc \<squnion> sides_of_rhs (side_rhs_fold_ctx acc ts) \<sigma> (Inr gg)"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  show ?case by (simp add: bot_fun_def)
next
  case (Cons t ts)
  let ?acc' = "acc \<squnion> traverse_rhs t \<sigma>"
  have hyp_t: "restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr gg)"
    using Cons.prems by simp
  have ih: "restrict_global (traverse_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma>)
              \<le> restrict_global ?acc' \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma> (Inr gg)"
    by (rule Cons.IH) (use Cons.prems in simp)
  have eq_tr: "traverse_rhs (side_rhs_fold_ctx acc (t # ts)) \<sigma>
                 = traverse_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma>"
    by (simp add: traverse_seqcomp)
  have eq_sd: "sides_of_rhs (side_rhs_fold_ctx acc (t # ts)) \<sigma> (Inr gg)
                 = sides_of_rhs t \<sigma> (Inr gg)
                   \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma> (Inr gg)"
    by (simp add: sides_of_rhs_seqcomp_at)
  have acc'_le: "restrict_global ?acc' \<le> restrict_global acc \<squnion> sides_of_rhs t \<sigma> (Inr gg)"
    by (simp add: hyp_t restrict_global_sup sup.coboundedI2)
  have "restrict_global (traverse_rhs (side_rhs_fold_ctx acc (t # ts)) \<sigma>)
          \<le> restrict_global ?acc' \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma> (Inr gg)"
    using ih unfolding eq_tr .
  also have "\<dots> \<le> (restrict_global acc \<squnion> sides_of_rhs t \<sigma> (Inr gg))
                  \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc' ts) \<sigma> (Inr gg)"
    by (rule sup_mono[OF acc'_le order_refl])
  also have "\<dots> = restrict_global acc \<squnion> sides_of_rhs (side_rhs_fold_ctx acc (t # ts)) \<sigma> (Inr gg)"
    using eq_sd sup_assoc by auto
  finally show ?case .
qed

text \<open>Per-tree domination for a keyed retain intra edge: traverse-global \<^emph>\<open>equals\<close> the keyed side.\<close>
lemma restrict_global_traverse_retain_intra:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma>)
         = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma> (Inr (gkey ctx))"
proof -
  have "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma>)
        = restrict_global (traverse_rhs (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>))"
    by (simp add: traverse_intra_pull_gk)
  also have "\<dots> = all_sides (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>)"
    by (simp add: traverse_retain_edge_tree all_sides_retain_edge_tree)
  also have "\<dots> = sides_of_rhs (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>) (Inr ())"
    by (rule all_sides_eq_sides_Inr_unit)
  also have "\<dots> = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma> (Inr (gkey ctx))"
    by (rule sides_intra_pull_gk[symmetric])
  finally show ?thesis .
qed

text \<open>Per-tree domination for a keyed fixed-combine tree: its traverse has no global part.\<close>
lemma restrict_global_traverse_unit_combine_intra:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex))) \<sigma>) = \<bottom>"
proof -
  have "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex))) \<sigma>)
        = restrict_global (traverse_rhs (unit_combine_tree cc ex) (pull_gk gkey ctx \<sigma>))"
    by (simp add: traverse_intra_pull_gk)
  also have "\<dots> = \<bottom>"
    by (simp add: traverse_unit_combine_tree restrict_global_restrict_local_bot)
  finally show ?thesis .
qed

text \<open>
  The reduction: for the retain fixed-combine keyed system, an exact
  \<^const>\<open>part_solution\<close> satisfies the keyed invariant at every reachable slot.  This
  discharges the standing assumption of the retain keyed witness from the exact
  solver output, leaving no non-derived solver obligation.
\<close>
theorem part_solution_imp_inl_glob_le_keyed_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes retain_edge: "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and retain_comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and bot0_glob: "restrict_global bot0 = \<bottom>"
    and frame_glob: "restrict_global fresh_frame = \<bottom>"
    and ps: "part_solution (side_cfg_T_eff_cmp gkey
                (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                    (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                g etf fresh_frame bot0 s0) x \<sigma> vars"
    and v: "(v, ctx) \<in> vars"
    and y: "is_global y"
  shows "\<sigma> (Inl (v, ctx)) y \<le> \<sigma> (Inr (gkey ctx)) y"
proof -
  let ?cmb = "\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))"
  let ?T = "side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)"
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                        (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g v)"
  have exact: "eq ?T (v, ctx) \<sigma> = \<sigma> (Inl (v, ctx))" using ps v by auto
  have hyp: "\<And>t. t \<in> set (?intra @ ?comb)
             \<Longrightarrow> restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr (gkey ctx))"
  proof -
    fix t assume t: "t \<in> set (?intra @ ?comb)"
    show "restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr (gkey ctx))"
    proof (cases "t \<in> set ?intra")
      case True
      then obtain u a where
        "t = map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))"
        by auto
      thus ?thesis
        by (simp add: retain_edge restrict_global_traverse_retain_intra)
    next
      case False
      with t have "t \<in> set ?comb" by simp
      then obtain cc ex where
        "t = map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))"
        by auto
      thus ?thesis
        by (simp add: retain_comb restrict_global_traverse_unit_combine_intra)
    qed
  qed
  have acc0_glob: "restrict_global ?acc0 = \<bottom>"
    using bot0_glob frame_glob
    by (simp add: restrict_global_sup restrict_global_restrict_local_bot restrict_global_bot
          split: if_split)
  have fold_eq: "traverse_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> = eq ?T (v, ctx) \<sigma>"
    by (simp add: eq_side_cfg_T_eff_cmp traverse_side_rhs_fold_ctx)
  have sides_le: "sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))
                    \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))
            \<le> sides_of_rhs (?T (v, ctx)) \<sigma> (Inr (gkey ctx))"
      by (rule sides_fold_le_side_cfg_T_eff_cmp)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))"
      by (rule side_post_solution_le_global_cmp[OF _ v]) (use ps in auto)
    finally show ?thesis .
  qed
  have fun_le: "restrict_global (eq ?T (v, ctx) \<sigma>) \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "restrict_global (eq ?T (v, ctx) \<sigma>)
            \<le> restrict_global ?acc0
              \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))"
      by (metis (no_types, lifting) fold_eq hyp restrict_global_traverse_side_rhs_fold_ctx_le)
    also have "\<dots> = sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))"
      by (simp add: acc0_glob)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))" by (rule sides_le)
    finally show ?thesis .
  qed
  have "\<sigma> (Inl (v, ctx)) y = restrict_global (eq ?T (v, ctx) \<sigma>) y"
    using y exact by (simp add: restrict_global_def)
  also have "\<dots> \<le> \<sigma> (Inr (gkey ctx)) y" using fun_le by (rule le_funD)
  finally show ?thesis .
qed

text \<open>
  Packaged as the invariant on a covering variable set: on any \<open>vars\<close> closed under the
  reachable slots, the exact retain solution satisfies \<^const>\<open>inl_glob_le_keyed_ctx\<close>
  pointwise.  (The full unconditional \<^const>\<open>inl_glob_le_keyed_ctx\<close> additionally needs
  the solver's \<open>\<bottom>\<close>-default outside \<open>vars\<close>, where both sides are \<open>\<bottom>\<close>.)
\<close>
lemma inl_glob_le_keyed_ctx_on_vars:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and "restrict_global bot0 = \<bottom>" and "restrict_global fresh_frame = \<bottom>"
    and "part_solution (side_cfg_T_eff_cmp gkey
           (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
               (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
           g etf fresh_frame bot0 s0) x \<sigma> vars"
    and "\<And>v ctx. (v, ctx) \<in> vars"
  shows "inl_glob_le_keyed_ctx gkey \<sigma>"
  unfolding inl_glob_le_keyed_ctx_def
  using part_solution_imp_inl_glob_le_keyed_ctx[OF assms(1-5)] assms(6) by blast

text \<open>
  The realistic full form.  Exactness gives the invariant on the solved set
  \<open>vars\<close>; the solver's \<open>\<bottom>\<close>-init default gives it outside \<open>vars\<close> --- an unsolved
  local slot keeps the initial \<open>\<bottom>\<close>, dominated by anything.  Together they discharge
  the full \<^const>\<open>inl_glob_le_keyed_ctx\<close> from the fixpoint shape alone, with no
  standalone slot-relating assumption.  Both inputs are intrinsic properties of the
  solver output (exact fixpoint, \<open>\<bottom>\<close> default), not semantic assertions about the
  analysis.
\<close>
lemma inl_glob_le_keyed_ctx_full:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes retain_edge: "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and retain_comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and bot0_glob: "restrict_global bot0 = \<bottom>"
    and frame_glob: "restrict_global fresh_frame = \<bottom>"
    and ps: "part_solution (side_cfg_T_eff_cmp gkey
                (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                    (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                g etf fresh_frame bot0 s0) x \<sigma> vars"
    and outside: "\<And>v ctx. (v, ctx) \<notin> vars \<Longrightarrow> \<sigma> (Inl (v, ctx)) = \<bottom>"
  shows "inl_glob_le_keyed_ctx gkey \<sigma>"
  unfolding inl_glob_le_keyed_ctx_def
proof (intro allI impI)
  fix v ctx x assume glob: "is_global x"
  show "\<sigma> (Inl (v, ctx)) x \<le> \<sigma> (Inr (gkey ctx)) x"
  proof (cases "(v, ctx) \<in> vars")
    case True
    show ?thesis
      by (rule part_solution_imp_inl_glob_le_keyed_ctx
            [OF retain_edge retain_comb bot0_glob frame_glob ps True glob])
  next
    case False
    then have "\<sigma> (Inl (v, ctx)) = \<bottom>" by (rule outside)
    then show ?thesis by simp
  qed
qed

text \<open>
  The call-enter edge is filtered out of the intra fold, so its bound is not read
  off the fold.  Instead the framed transfer contract bounds the enter transfer by
  the fresh frame joined with the globals, and the frame-entry seed places that
  fresh frame below the callee-entry local unknown; the preserved globals land in
  the keyed slot.  This is the routing bound for the filtered enter edges.
\<close>

lemma side_cfg_T_eff_cmp_enter_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes frm: "sound_effectful_transfer_framed etf fresh_frame"
      and pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
      and e: "(u, EA_Enter, v) \<in> edges g"
      and fin: "finite (edges g)"
      and inr: "inr_slot_locals_bot_ctx \<sigma>"
      and inl: "inl_slot_globals_bot_ctx \<sigma>"
  shows "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
           \<le> side_env (pull_gk gkey ctx \<sigma>) v"
proof -
  have fe: "is_frame_entry g v"
  proof -
    have "(u, EA_Enter) \<in> set (predecessor_list g v)"
      using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
    hence "(u, EA_Enter) \<in> set (enter_predecessor_list g v)"
      by (rule enter_predecessor_list_mem)
    thus ?thesis by (auto simp: is_frame_entry_def)
  qed
  have posteq: "eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>
                  \<le> \<sigma> (Inl (v, ctx))"
    using pp v by auto
  have ff: "fresh_frame \<le> \<sigma> (Inl (v, ctx))"
  proof -
    have "fresh_frame \<le> (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)"
      using fe by simp
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp by (rule side_acc_ctx_ge_acc)
    also have "\<dots> \<le> \<sigma> (Inl (v, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have enter_le: "etf_full (etf_enter etf u) (pull_gk gkey ctx \<sigma>)
                    \<le> fresh_frame \<squnion> glob_env (pull_gk gkey ctx \<sigma>)"
  proof -
    have "inr_slot_locals_bot (pull_gk gkey ctx \<sigma>)"
      by (rule inr_slot_locals_bot_pull_gk[OF inr])
    moreover have "inl_slot_globals_bot (pull_gk gkey ctx \<sigma>)"
      by (rule inl_slot_globals_bot_pull_gk[OF inl])
    ultimately show ?thesis
      using sound_effectful_transfer_framed.etf_enter_framed_le[OF frm] by blast
  qed
  have "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
        = etf_full (etf_enter etf u) (pull_gk gkey ctx \<sigma>)" by simp
  also have "\<dots> \<le> fresh_frame \<squnion> glob_env (pull_gk gkey ctx \<sigma>)" by (rule enter_le)
  also have "\<dots> = fresh_frame \<squnion> \<sigma> (Inr (gkey ctx))"
    by (simp add: glob_env_unit pull_gk_Inr)
  also have "\<dots> \<le> \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (gkey ctx))"
    by (rule sup_mono[OF ff order_refl])
  also have "\<dots> = side_env (pull_gk gkey ctx \<sigma>) v"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed

text \<open>
  Retain enter bound: the same routing bound under the weaker framed contract
  @{locale sound_effectful_transfer_framed_le} and the retain keyed invariant
  @{const inl_glob_le_keyed_ctx}.  Identical to @{thm [source] side_cfg_T_eff_cmp_enter_le}
  except the enter step pulls back @{const inl_glob_le_glob_env} instead of
  @{const inl_slot_globals_bot} and invokes the weak-premise enter contract.
\<close>
lemma side_cfg_T_eff_cmp_enter_le_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes frm: "sound_effectful_transfer_framed_le etf fresh_frame"
      and pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
      and e: "(u, EA_Enter, v) \<in> edges g"
      and fin: "finite (edges g)"
      and inr: "inr_slot_locals_bot_ctx \<sigma>"
      and inl: "inl_glob_le_keyed_ctx gkey \<sigma>"
  shows "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
           \<le> side_env (pull_gk gkey ctx \<sigma>) v"
proof -
  have fe: "is_frame_entry g v"
  proof -
    have "(u, EA_Enter) \<in> set (predecessor_list g v)"
      using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
    hence "(u, EA_Enter) \<in> set (enter_predecessor_list g v)"
      by (rule enter_predecessor_list_mem)
    thus ?thesis by (auto simp: is_frame_entry_def)
  qed
  have posteq: "eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>
                  \<le> \<sigma> (Inl (v, ctx))"
    using pp v by auto
  have ff: "fresh_frame \<le> \<sigma> (Inl (v, ctx))"
  proof -
    have "fresh_frame \<le> (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)"
      using fe by simp
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp by (rule side_acc_ctx_ge_acc)
    also have "\<dots> \<le> \<sigma> (Inl (v, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have enter_le: "etf_full (etf_enter etf u) (pull_gk gkey ctx \<sigma>)
                    \<le> fresh_frame \<squnion> glob_env (pull_gk gkey ctx \<sigma>)"
  proof -
    have "inr_slot_locals_bot (pull_gk gkey ctx \<sigma>)"
      by (rule inr_slot_locals_bot_pull_gk[OF inr])
    moreover have "inl_glob_le_glob_env (pull_gk gkey ctx \<sigma>)"
      by (rule inl_glob_le_glob_env_pull_gk[OF inl])
    ultimately show ?thesis
      using sound_effectful_transfer_framed_le.etf_enter_framed_glob_le[OF frm] by blast
  qed
  have "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
        = etf_full (etf_enter etf u) (pull_gk gkey ctx \<sigma>)" by simp
  also have "\<dots> \<le> fresh_frame \<squnion> glob_env (pull_gk gkey ctx \<sigma>)" by (rule enter_le)
  also have "\<dots> = fresh_frame \<squnion> \<sigma> (Inr (gkey ctx))"
    by (simp add: glob_env_unit pull_gk_Inr)
  also have "\<dots> \<le> \<sigma> (Inl (v, ctx)) \<squnion> \<sigma> (Inr (gkey ctx))"
    by (rule sup_mono[OF ff order_refl])
  also have "\<dots> = side_env (pull_gk gkey ctx \<sigma>) v"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed

text \<open>
  The combine analogue, for the conservative keyed combine builder
  \<open>cmb c cc ex = map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))\<close>.
  Same proof shape as the edge bound, over \<^const>\<open>etf_combine\<close> and the combine
  predecessor list.
\<close>

lemma side_cfg_T_eff_cmp_combine_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp gkey
                    (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                        (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                    g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(ret, ctx) \<in> vars"
      and e: "(cc, ex, ret) \<in> combines g"
      and finC: "finite (combines g)"
  shows "etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
           \<le> side_env (pull_gk gkey ctx \<sigma>) ret"
proof -
  let ?cmb = "\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))"
  have posteq: "eq (side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0) (ret, ctx) \<sigma>
                  \<le> \<sigma> (Inl (ret, ctx))"
    using pp v by auto
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g ret)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have memtree:
    "map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))
       \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                   (non_enter_predecessor_list g ret)
              @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret))"
    using mem by force
  have loc: "traverse_rhs (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
               \<le> \<sigma> (Inl (ret, ctx))"
  proof -
    have "traverse_rhs (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
            = traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))) \<sigma>"
      by (rule traverse_intra_pull_gk[symmetric])
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0) (ret, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp by (rule traverse_le_side_acc_ctx[OF memtree])
    also have "\<dots> \<le> \<sigma> (Inl (ret, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have glob: "all_sides (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
                \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "all_sides (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
            = sides_of_rhs (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>) (Inr ())"
      by (rule all_sides_eq_sides_Inr_unit)
    also have "\<dots> = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                     (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))) \<sigma> (Inr (gkey ctx))"
      by (rule sides_intra_pull_gk[symmetric])
    also have "\<dots> \<le> sides_of_rhs (side_rhs_fold_ctx
                     ((if ret = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                      \<squnion> (if is_frame_entry g ret then fresh_frame else \<bottom>))
                     (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                          (non_enter_predecessor_list g ret)
                      @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret)))
                     \<sigma> (Inr (gkey ctx))"
      by (rule sides_le_side_rhs_fold_ctx[OF memtree])
    also have "\<dots> \<le> sides_of_rhs (side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0 (ret, ctx))
                     \<sigma> (Inr (gkey ctx))"
      by (rule sides_fold_le_side_cfg_T_eff_cmp)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))"
      by (rule side_post_solution_le_global_cmp[OF pp v])
    finally show ?thesis .
  qed
  have "etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
        = traverse_rhs (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
          \<squnion> all_sides (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)"
    by (simp add: etf_full_def)
  also have "\<dots> \<le> \<sigma> (Inl (ret, ctx)) \<squnion> \<sigma> (Inr (gkey ctx))"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env (pull_gk gkey ctx \<sigma>) ret"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed

subsection \<open>Entry bound, the read invariant, and the compat collapse\<close>


text \<open>
  With each context compatible with exactly its own key (\<open>{k. gcmp ctx k} = {gkey ctx}\<close>)
  the filtered read is the single keyed slot, so the keyed read at \<^const>\<open>pull_gk\<close>
  coincides with the \<open>cmp\<close>-filtered read \<^const>\<open>side_env_cmp\<close>.
\<close>

lemma side_env_pull_gk_eq_cmp:
  assumes "{k. gcmp ctx k} = {gkey ctx}"
  shows "side_env (pull_gk gkey ctx \<sigma>) v = side_env_cmp gcmp \<sigma> (v, ctx)"
proof -
  have "glob_env_cmp gcmp ctx \<sigma> = \<sigma> (Inr (gkey ctx))"
    using assms by (rule glob_env_cmp_singleton)
  thus ?thesis
    by (simp add: side_env_def side_env_cmp_def glob_env_unit pull_gk_Inl pull_gk_Inr)
qed

lemma s0_le_side_env_cmp_entry:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and entry_in: "(cfg_entry g, ctx) \<in> vars"
  shows "s0 \<le> side_env (pull_gk gkey ctx \<sigma>) (cfg_entry g)"
proof -
  let ?ent = "cfg_entry g"
  have eqle: "eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (?ent, ctx) \<sigma>
                \<le> \<sigma> (Inl (?ent, ctx))"
    using pp entry_in by auto
  have rl: "restrict_local s0 \<le> \<sigma> (Inl (?ent, ctx))"
  proof -
    have "restrict_local s0
            \<le> (if ?ent = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
              \<squnion> (if is_frame_entry g ?ent then fresh_frame else \<bottom>)"
      by (simp add: le_supI1)
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) (?ent, ctx) \<sigma>"
      unfolding eq_side_cfg_T_eff_cmp by (rule side_acc_ctx_ge_acc)
    also have "\<dots> \<le> \<sigma> (Inl (?ent, ctx))" by (rule eqle)
    finally show ?thesis .
  qed
  have rgeq: "sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (?ent, ctx))
                \<sigma> (Inr (gkey ctx))
              = sides_of_rhs (side_rhs_fold_ctx
                  ((if ?ent = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g ?ent then fresh_frame else \<bottom>))
                  (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                          (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                       (non_enter_predecessor_list g ?ent)
                   @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g ?ent)))
                  \<sigma> (Inr (gkey ctx))
                \<squnion> restrict_global s0"
    unfolding side_cfg_T_eff_cmp_def by (simp add: Let_def)
  have rg: "restrict_global s0 \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "restrict_global s0
          \<le> sides_of_rhs (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0 (?ent, ctx))
              \<sigma> (Inr (gkey ctx))"
      unfolding rgeq by (rule sup_ge2)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))"
      by (rule side_post_solution_le_global_cmp[OF pp entry_in])
    finally show ?thesis .
  qed
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "\<dots> \<le> \<sigma> (Inl (?ent, ctx)) \<squnion> \<sigma> (Inr (gkey ctx))"
    using rl rg by (rule sup_mono)
  also have "\<dots> = side_env (pull_gk gkey ctx \<sigma>) ?ent"
    by (simp add: side_env_def glob_env_unit pull_gk_Inl pull_gk_Inr)
  finally show ?thesis .
qed

subsection \<open>The value-dependent (switching) combine contract\<close>

text \<open>
  The combine enters the soundness theorem below at exactly one place --- the
  combine branch of the underlying \<open>post_fixpoint_sound_at_eff\<close> obligation.  For
  the context-\<^emph>\<open>fixed\<close> combine that branch is discharged by
  \<open>side_cfg_T_eff_cmp_combine_le\<close>.  A value-\<^emph>\<open>dependent\<close> (switching)
  combine --- one that \<open>Side\<close>s callee globals to a slot computed from the queried
  caller state --- is not covered by that lemma, so its post-solutions are not
  post-fixpoints of the fixed system.  \<open>switching_combine_sound\<close> names precisely
  the obligation any combine must supply for the theorem to go through: whatever
  generator combine produced \<open>\<sigma>\<close>, the keyed read at \<open>(ret, ctx)\<close> still
  over-approximates the semantic combine \<^const>\<open>etf_combine\<close>.
\<close>

definition switching_combine_sound ::
  "('c \<Rightarrow> 'g::finite) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> bool"
where
  "switching_combine_sound gkey cmb g etf fresh_frame bot0 s0 \<equiv>
     (\<forall>(\<sigma> :: pp \<times> 'c + 'g \<Rightarrow> 'a abs_state) x vars ctx cc ex ret.
        part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars
        \<longrightarrow> inl_slot_globals_bot_ctx \<sigma>
        \<longrightarrow> (ret, ctx) \<in> vars
        \<longrightarrow> (cc, ex, ret) \<in> combines g
        \<longrightarrow> etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
              \<le> side_env (pull_gk gkey ctx \<sigma>) ret)"

text \<open>
  The certified context-fixed combine satisfies the contract, via the very kernel
  lemma the generalized theorem consumes in the combine branch.  This is the
  degenerate (context-preserving) instance --- Seidl 2026 eq. (6) with
  \<open>context d c = c\<close> --- and keeps every existing caller of the theorem working.
\<close>

lemma fixed_combine_satisfies_switching_combine_sound:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "finite (combines g)"
  shows "switching_combine_sound gkey
           (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
           g etf fresh_frame bot0 s0"
  unfolding switching_combine_sound_def
  by (blast intro: side_cfg_T_eff_cmp_combine_le[OF _ _ _ assms])

text \<open>
  The retain companion of @{const switching_combine_sound}: the combine bound holds
  under the weaker @{const inl_glob_le_keyed_ctx} premise.  The combine bound itself
  never reads the local-global invariant, so the certified fixed combine satisfies
  it by the same @{thm [source] side_cfg_T_eff_cmp_combine_le}.
\<close>
definition switching_combine_sound_le ::
  "('c \<Rightarrow> 'g::finite) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> bool"
where
  "switching_combine_sound_le gkey cmb g etf fresh_frame bot0 s0 \<equiv>
     (\<forall>(\<sigma> :: pp \<times> 'c + 'g \<Rightarrow> 'a abs_state) x vars ctx cc ex ret.
        part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars
        \<longrightarrow> inl_glob_le_keyed_ctx gkey \<sigma>
        \<longrightarrow> (ret, ctx) \<in> vars
        \<longrightarrow> (cc, ex, ret) \<in> combines g
        \<longrightarrow> etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
              \<le> side_env (pull_gk gkey ctx \<sigma>) ret)"

lemma fixed_combine_satisfies_switching_combine_sound_le:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes "finite (combines g)"
  shows "switching_combine_sound_le gkey
           (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
           g etf fresh_frame bot0 s0"
  unfolding switching_combine_sound_le_def
  by (blast intro: side_cfg_T_eff_cmp_combine_le[OF _ _ _ assms])

subsection \<open>Generator soundness: cmp-filtered context collecting soundness\<close>

text \<open>
  The keyed generator is sound.  With each context reading exactly its own keyed
  slot, a post-fixpoint of \<^const>\<open>side_cfg_T_eff_cmp\<close> (conservative combine builder)
  over-approximates the IP collecting semantics at every program point, read
  through the \<open>cmp\<close>-filtered \<^const>\<open>side_env_cmp\<close>.  The three per-edge / per-combine /
  entry bounds discharge \<open>post_fixpoint_sound_at_eff\<close> at \<^const>\<open>pull_gk\<close>; the
  \<open>single\<close> compat collapse rewrites the monovariant read at \<^const>\<open>pull_gk\<close> into the
  keyed read.  This is \<open>post_fixpoint_sound_at_ctx_conservative\<close>'s keyed sibling.
\<close>

theorem side_cfg_T_eff_cmp_collect_sound_gen:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes stf: "sound_effectful_transfer_framed etf fresh_frame"
    and comb_sound: "switching_combine_sound gkey cmb g etf fresh_frame bot0 s0"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr: "inr_slot_locals_bot_ctx \<sigma>"
    and inl: "inl_slot_globals_bot_ctx \<sigma>"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp \<sigma> (v0, ctx)\<rbrakk>"
proof -
  have stf_base: "sound_effectful_transfer etf"
    using stf by (simp add: sound_effectful_transfer_framed_def)
  have main: "cfg_collect g S v0 \<le> \<lbrakk>side_env (pull_gk gkey ctx \<sigma>) v0\<rbrakk>"
  proof (rule sound_effectful_transfer.post_fixpoint_sound_at_eff
           [OF stf_base inr_slot_locals_bot_pull_gk[OF inr] S_sound])
    fix u a w assume e: "(u, a, w) \<in> edges g"
    show "etf_full (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
            \<le> side_env (pull_gk gkey ctx \<sigma>) w"
    proof (cases "a = EA_Enter")
      case True
      with e have e': "(u, EA_Enter, w) \<in> edges g" by simp
      have "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
              \<le> side_env (pull_gk gkey ctx \<sigma>) w"
        by (rule side_cfg_T_eff_cmp_enter_le[OF stf pp cover_edge[OF e] e' finE inr inl])
      thus ?thesis using True by simp
    next
      case False
      show ?thesis
        by (rule side_cfg_T_eff_cmp_edge_le[OF pp cover_edge[OF e] e False finE])
    qed
  next
    fix c ex ret assume cm: "(c, ex, ret) \<in> combines g"
    show "etf_full (etf_combine etf c ex) (pull_gk gkey ctx \<sigma>)
            \<le> side_env (pull_gk gkey ctx \<sigma>) ret"
      using comb_sound cover_comb[OF cm] cm pp inl
      unfolding switching_combine_sound_def by blast
  next
    show "s0 \<le> side_env (pull_gk gkey ctx \<sigma>) (cfg_entry g)"
      by (rule s0_le_side_env_cmp_entry[OF pp cover_entry])
  qed
  have eq: "side_env (pull_gk gkey ctx \<sigma>) v0 = side_env_cmp gcmp \<sigma> (v0, ctx)"
    using single by (rule side_env_pull_gk_eq_cmp)
  show ?thesis using main eq by simp
qed

text \<open>
  The retain sibling of @{thm [source] side_cfg_T_eff_cmp_collect_sound_gen}: the
  collecting-soundness bound under the weak framed contract
  @{locale sound_effectful_transfer_framed_le} and the retain keyed invariant
  @{const inl_glob_le_keyed_ctx}.  Identical proof; only the enter sub-case uses
  @{thm [source] side_cfg_T_eff_cmp_enter_le_le}.  A retain Sign spine (local slots
  carrying globals) discharges this where the publish theorem's
  @{const inl_slot_globals_bot_ctx} premise fails.
\<close>
theorem side_cfg_T_eff_cmp_collect_sound_gen_le:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes stf: "sound_effectful_transfer_framed_le etf fresh_frame"
    and comb_sound: "switching_combine_sound_le gkey cmb g etf fresh_frame bot0 s0"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr: "inr_slot_locals_bot_ctx \<sigma>"
    and inl: "inl_glob_le_keyed_ctx gkey \<sigma>"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp \<sigma> (v0, ctx)\<rbrakk>"
proof -
  have stf_base: "sound_effectful_transfer etf"
    using stf by (simp add: sound_effectful_transfer_framed_le_def)
  have main: "cfg_collect g S v0 \<le> \<lbrakk>side_env (pull_gk gkey ctx \<sigma>) v0\<rbrakk>"
  proof (rule sound_effectful_transfer.post_fixpoint_sound_at_eff
           [OF stf_base inr_slot_locals_bot_pull_gk[OF inr] S_sound])
    fix u a w assume e: "(u, a, w) \<in> edges g"
    show "etf_full (apply_etf etf a u) (pull_gk gkey ctx \<sigma>)
            \<le> side_env (pull_gk gkey ctx \<sigma>) w"
    proof (cases "a = EA_Enter")
      case True
      with e have e': "(u, EA_Enter, w) \<in> edges g" by simp
      have "etf_full (apply_etf etf EA_Enter u) (pull_gk gkey ctx \<sigma>)
              \<le> side_env (pull_gk gkey ctx \<sigma>) w"
        by (rule side_cfg_T_eff_cmp_enter_le_le[OF stf pp cover_edge[OF e] e' finE inr inl])
      thus ?thesis using True by simp
    next
      case False
      show ?thesis
        by (rule side_cfg_T_eff_cmp_edge_le[OF pp cover_edge[OF e] e False finE])
    qed
  next
    fix c ex ret assume cm: "(c, ex, ret) \<in> combines g"
    show "etf_full (etf_combine etf c ex) (pull_gk gkey ctx \<sigma>)
            \<le> side_env (pull_gk gkey ctx \<sigma>) ret"
      using comb_sound cover_comb[OF cm] cm pp inl
      unfolding switching_combine_sound_le_def by blast
  next
    show "s0 \<le> side_env (pull_gk gkey ctx \<sigma>) (cfg_entry g)"
      by (rule s0_le_side_env_cmp_entry[OF pp cover_entry])
  qed
  have eq: "side_env (pull_gk gkey ctx \<sigma>) v0 = side_env_cmp gcmp \<sigma> (v0, ctx)"
    using single by (rule side_env_pull_gk_eq_cmp)
  show ?thesis using main eq by simp
qed

text \<open>
  The certified corollary: with the context-fixed combine the switching contract
  is discharged by \<open>fixed_combine_satisfies_switching_combine_sound\<close>, so the
  original collecting-soundness statement holds unchanged --- every existing caller
  is unaffected by the generalization above.
\<close>

corollary side_cfg_T_eff_cmp_collect_sound:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes stf: "sound_effectful_transfer_framed etf fresh_frame"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr: "inr_slot_locals_bot_ctx \<sigma>"
    and inl: "inl_slot_globals_bot_ctx \<sigma>"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp gkey
                  (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                      (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                  g etf fresh_frame bot0 s0) x \<sigma> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp \<sigma> (v0, ctx)\<rbrakk>"
proof (rule side_cfg_T_eff_cmp_collect_sound_gen)
  show "sound_effectful_transfer_framed etf fresh_frame" by (rule stf)
  show "switching_combine_sound gkey
          (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
          g etf fresh_frame bot0 s0"
    by (rule fixed_combine_satisfies_switching_combine_sound[OF finC])
  show "{k. gcmp ctx k} = {gkey ctx}" by (rule single)
  show "inr_slot_locals_bot_ctx \<sigma>" by (rule inr)
  show "inl_slot_globals_bot_ctx \<sigma>" by (rule inl)
  show "S \<le> \<lbrakk>s0\<rbrakk>" by (rule S_sound)
  show "part_post_solution
          (side_cfg_T_eff_cmp gkey
             (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                 (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
             g etf fresh_frame bot0 s0) x \<sigma> vars"
    by (rule pp)
  show "finite (edges g)" by (rule finE)
  show "finite (combines g)" by (rule finC)
  show "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars" by (rule cover_edge)
  show "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars" by (rule cover_comb)
  show "(cfg_entry g, ctx) \<in> vars" by (rule cover_entry)
qed

text \<open>
  The canonical instantiation: the context \<^emph>\<open>is\<close> the key (\<open>gkey = id\<close>) and each
  context reads exactly its own slot by equality (\<open>gcmp = (=)\<close>) --- the natural
  per-context keying, matching the \<open>cmp = (=)\<close> of the concrete witnesses.  The
  single-key compat \<open>{k. ctx = k} = {ctx}\<close> holds definitionally, so it drops out.
\<close>

corollary side_cfg_T_eff_cmp_collect_sound_eq:
  fixes \<sigma> :: "pp \<times> 'g + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes stf: "sound_effectful_transfer_framed etf fresh_frame"
    and inr: "inr_slot_locals_bot_ctx \<sigma>"
    and inl: "inl_slot_globals_bot_ctx \<sigma>"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp id
                  (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
                      (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                  g etf fresh_frame bot0 s0) x \<sigma> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp (=) \<sigma> (v0, ctx)\<rbrakk>"
proof -
  have pp': "part_post_solution
               (side_cfg_T_eff_cmp id
                  (\<lambda>c cc ex. map_gtree (\<lambda>_. id c)
                      (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                  g etf fresh_frame bot0 s0) x \<sigma> vars"
    using pp by simp
  show ?thesis
    by (rule side_cfg_T_eff_cmp_collect_sound
          [OF stf _ inr inl S_sound pp' finE finC cover_edge cover_comb cover_entry]) auto
qed

end
