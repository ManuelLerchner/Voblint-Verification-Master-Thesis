theory TD_Side_Eff_Keyed_Gen
  imports TD_Side_Eff_Ctx_Shared TD_Side_Eff_Sound
begin

section \<open>Keyed-global generator: routing global writes by context\<close>

text \<open>
  The concrete functional keyed generator: it routes global writes by context.
  The context generator \<^const>\<open>side_cfg_T_eff_ctx\<close> relabels
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

lemma dep_aux_map_ltree:
  "dep_aux \<sigma> (map_ltree h t)
   = map_sum h id ` dep_aux (\<lambda>z. \<sigma> (map_sum h id z)) t"
  by (induction t arbitrary: \<sigma>) auto

subsection \<open>The keyed generator\<close>

text \<open>
  \<open>side_cfg_T_eff_keyed\<close> is \<^const>\<open>side_cfg_T_eff_ctx_seeded\<close>'s keyed sibling: the
  intra per-edge trees are relabelled locally by context (\<^const>\<open>map_ltree\<close>) and
  their global writes routed to the keyed slot \<^term>\<open>gkey c\<close> (\<^const>\<open>map_gtree\<close>).
  The entry seed writes the initial globals to the entry context's key.  The
  combine builder \<open>cmb\<close> stays a parameter, exactly as in the context generator ---
  the value-dependent semantic combine is supplied per instance.
\<close>

definition side_cfg_T_eff_keyed ::
  "('c \<Rightarrow> 'g)
   \<Rightarrow> ('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>);
            intra = map (\<lambda>(u, a).
                          map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex, dst). cmb c dst cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global s0) t else t)"

text \<open>
  Denotation at \<open>(v, ctx)\<close>: the entry \<open>Side\<close> wrapper is denotation-transparent, so
  the unknown's value is the \<^const>\<open>side_acc_ctx\<close> fold over the keyed intra trees
  and the combine trees.  Mirrors \<open>eq_side_cfg_T_eff_ctx_seeded\<close>.
\<close>

lemma eq_side_cfg_T_eff_keyed:
  "eq (side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx
       ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)) \<sigma>
       (map (\<lambda>(u, a).
              map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_keyed_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

definition side_cfg_T_eff_keyed_seed ::
  "('c \<Rightarrow> 'g)
   \<Rightarrow> ('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
        \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a abs_state) \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_keyed_seed gkey cmb frame_seed g etf bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed c else \<bottom>);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex, dst). cmb c dst cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global s0) t else t)"

lemma eq_side_cfg_T_eff_keyed_seed:
  "eq (side_cfg_T_eff_keyed_seed gkey cmb frame_seed g etf bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>))
       \<sigma>
       (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
             (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v))"
  by (simp add: side_cfg_T_eff_keyed_seed_def Let_def traverse_side_rhs_fold_ctx)

text \<open>
  A constant frame seed collapses the seeded generator to the fixed-frame generator:
  the two definitions differ only in \<open>frame_seed c\<close> vs \<open>fresh_frame\<close>.  This is the
  reduction that lets fixed-frame post-fixpoint theorems consume seeded-generator
  post-fixpoints whenever the seed does not depend on the context.
\<close>

lemma side_cfg_T_eff_keyed_seed_const:
  "side_cfg_T_eff_keyed_seed gkey cmb (\<lambda>_. fr) g etf bot0 s0
     = side_cfg_T_eff_keyed gkey cmb g etf fr bot0 s0"
  unfolding side_cfg_T_eff_keyed_seed_def side_cfg_T_eff_keyed_def by simp


subsection \<open>Routing: the keyed intra tree reads the context / keyed-slot pullback\<close>

text \<open>
  Composing the two relabel commutes: a keyed intra tree denotes \<^const>\<open>apply_etf\<close>
  read against the environment that reroutes locals to their context copy
  (\<open>w \<mapsto> (w, ctx)\<close>) and the transfer's global slot to the context key \<open>gkey ctx\<close>.
  This is the local half of routing correctness --- it exhibits, as a \<^const>\<open>map_sum\<close>
  pullback, precisely which slots a keyed edge tree consults.
\<close>

lemma traverse_intra_keyed:
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

text \<open>The intra tree denotes \<^const>\<open>apply_etf\<close> against \<^const>\<open>pull_gk\<close> (restating \<open>traverse_intra_keyed\<close>).\<close>
lemma traverse_intra_pull_gk:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
   = traverse_rhs t (pull_gk gkey ctx \<sigma>)"
  by (simp add: traverse_intra_keyed pull_gk_def)

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
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (map_gtree r t) \<sigma> (Inr (r ()))
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id r z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_unit_gen:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (map_gtree (\<lambda>_. ()) t) \<sigma> (Inr ())
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id (\<lambda>_. ()) z)) (Inr ())"
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

lemma sides_fold_le_side_cfg_T_eff_keyed:
  shows "sides_of_rhs (side_rhs_fold_ctx
           ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
            \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>))
           (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                             (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                (non_enter_predecessor_list g v)
            @ map (\<lambda>(cc, ex, dst). cmb ctx dst cc ex) (combine_predecessor_list g v)))
           \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0 (v, ctx))
             \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_keyed_def
  by (cases "v = cfg_entry g") (auto simp: Let_def fun_upd_def)

lemma side_post_solution_le_global_keyed:
  assumes pp: "part_post_solution (side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
      and v: "(v, ctx) \<in> vars"
  shows "sides_of_rhs (side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0 (v, ctx))
           \<sigma> (Inr gg) \<le> \<sigma> (Inr gg)"
proof -
  from pp v
  have "sides_of_rhs (side_cfg_T_eff_keyed gkey cmb g etf fresh_frame bot0 s0 (v, ctx)) \<sigma> \<le> \<sigma>"
    by auto
  thus ?thesis by (rule le_funD)
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
  The keyed snapshot invariant: every context copy's local globals sit below that
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

subsection \<open>Global-domination helpers for exact solutions\<close>

text \<open>
  Generic ingredients for deriving \<^const>\<open>inl_glob_le_keyed_ctx\<close> from an exact
  \<^const>\<open>part_solution\<close>: restriction algebra, the fold-level global bound, and
  per-tree domination for the fixed combine.  An analysis whose local Answers
  carry globals combines these with a per-edge domination fact for its own tree
  shape to discharge the invariant from the solver output alone (see the retain
  analysis for the packaged reduction).
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

text \<open>Per-tree domination for a keyed fixed-combine tree: its traverse has no global part.\<close>
lemma restrict_global_traverse_unit_combine_intra:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree dst cc ex))) \<sigma>) = \<bottom>"
proof -
  have "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree dst cc ex))) \<sigma>)
        = restrict_global (traverse_rhs (unit_combine_tree dst cc ex) (pull_gk gkey ctx \<sigma>))"
    by (simp add: traverse_intra_pull_gk)
  also have "\<dots> = \<bottom>"
    by (simp add: traverse_unit_combine_tree restrict_global_restrict_local_bot)
  finally show ?thesis .
qed


end
