theory Exec_Cmp_Bridge
  imports Exec_Ctx_Bridge TD_Side_Eff_Cmp_Gen
begin

section \<open>Executable keyed-global equation-system generator\<close>

text \<open>
  Executable \<open>_st\<close> mirror of \<^const>\<open>side_cfg_T_eff_cmp\<close>.  The local
  reindexing is the context relabel \<open>w \<mapsto> (w, c)\<close>; \<^const>\<open>map_gtree\<close>
  routes all global reads and writes of the unit-global transfer tree to the
  context key \<open>gkey c\<close>.
\<close>

definition side_cfg_T_eff_cmp_st ::
  "('c \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_cmp_st gkey cmb g etf fresh_frame_st bot0_st s0_st =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
                   \<squnion> (if is_frame_entry g v then fresh_frame_st else \<bottom>);
            intra = map (\<lambda>(u, a).
                          map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf_st etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global_st s0_st) t else t)"

lemma eq_side_cfg_T_eff_cmp_st:
  "eq (side_cfg_T_eff_cmp_st gkey cmb g etf fresh_frame_st bot0_st s0_st) (v, ctx) \<sigma> =
     traverse_rhs
       (side_rhs_fold_ctx_st
          ((if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
           \<squnion> (if is_frame_entry g v then fresh_frame_st else \<bottom>))
          (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                          (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf a u)))
               (non_enter_predecessor_list g v)
           @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))) \<sigma>"
  unfolding side_cfg_T_eff_cmp_st_def
  by (simp add: Let_def)

text \<open>
  The \<^emph>\<open>seeded\<close> executable generator: the minimal change from
  \<^const>\<open>side_cfg_T_eff_cmp_st\<close> is a context-dependent frame seed
  \<open>frame_seed :: 'c \<Rightarrow> 'a st\<close> replacing the constant \<open>fresh_frame_st\<close>.  With the
  faithful seed \<^const>\<open>restrict_global_st\<close> it delivers the caller's globals into the
  callee-entry \<^emph>\<open>local\<close> slot (Goblint's \<open>sidel (FunctionEntry f, fc) v\<close>), so a
  clean transfer reading only that slot sees them.  Domain-generic --- Sign and
  interval both instantiate it.
\<close>

definition side_cfg_T_eff_cmp_seed_st ::
  "('c \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a st) \<Rightarrow> cfg \<Rightarrow> (unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_cmp_seed_st gkey cmb frame_seed g etf bot0_st s0_st =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
                   \<squnion> (if is_frame_entry g v then frame_seed c else \<bottom>);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf_st etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global_st s0_st) t else t)"

lemma seed_generalises:
  "side_cfg_T_eff_cmp_st gkey cmb g etf ff bot0 s0
     = side_cfg_T_eff_cmp_seed_st gkey cmb (\<lambda>_. ff) g etf bot0 s0"
  unfolding side_cfg_T_eff_cmp_st_def side_cfg_T_eff_cmp_seed_st_def by simp

text \<open>
  The abstract seeded generator: the \<^typ>\<open>'a abs_state\<close> image of
  \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close>, mirroring \<^const>\<open>side_cfg_T_eff_cmp\<close>'s relation
  to \<^const>\<open>side_cfg_T_eff_cmp_st\<close>.  Kept here so the executable-to-abstract transport
  can name both generators.
\<close>

definition side_cfg_T_eff_cmp_seed ::
  "('c \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a abs_state) \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed c else \<bottom>);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global s0) t else t)"

lemma eq_side_cfg_T_eff_cmp_seed:
  "eq (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) (v, ctx) sg
   = side_acc_ctx ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>))
       sg
       (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
             (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
  by (simp add: side_cfg_T_eff_cmp_seed_def Let_def traverse_side_rhs_fold_ctx)

text \<open>
  The combine analogue of the intra edge bound (\<open>seeded_clean_edge_bound\<close>): every
  combine predecessor \<open>(cc, ex)\<close> of a reached return node \<open>(v, ctx)\<close> contributes its
  reassembled tree value \<^term>\<open>traverse_rhs (cmb ctx cc ex) sg\<close> as a summand of the
  seeded fold, so the post-solution dominates it.  This is the \<open>COMB\<close> half of the
  seeded-clean kernel's return obligation, read straight off any
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> post-solution --- combine-generic (the combine tree
  \<open>cmb\<close> is a free parameter; its \<^const>\<open>combine_abs\<close> shape is a separate per-combine
  fact).
\<close>

lemma seeded_clean_comb_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes finC: "finite (combines g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) x sg vars"
    and cov: "(v, ctx) \<in> vars"
    and c: "(cc, ex, v) \<in> combines g"
  shows "traverse_rhs (cmb ctx cc ex) sg \<le> sg (Inl (v, ctx))"
proof -
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
               \<squnion> (if is_frame_entry g v then frame_seed ctx else \<bottom>)"
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g v)"
    using c by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have summand: "cmb ctx cc ex \<in> set (?intra @ ?comb)" using mem by force
  have "traverse_rhs (cmb ctx cc ex) sg \<le> side_acc_ctx ?acc0 sg (?intra @ ?comb)"
    by (rule traverse_le_side_acc_ctx[OF summand])
  also have "\<dots> = eq (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0) (v, ctx) sg"
    by (rule eq_side_cfg_T_eff_cmp_seed[symmetric])
  also have "\<dots> \<le> sg (Inl (v, ctx))"
    using part_post_solution_imp_se_constraint_holds[OF pp cov]
    by (simp add: se_constraint_holds_def)
  finally show ?thesis .
qed

lemma eq_side_cfg_T_eff_cmp_seed_st:
  "eq (side_cfg_T_eff_cmp_seed_st gkey cmb frame_seed_st g etf bot0_st s0_st) (v, ctx) sg =
     traverse_rhs
       (side_rhs_fold_ctx_st
          ((if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
           \<squnion> (if is_frame_entry g v then frame_seed_st ctx else \<bottom>))
          (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                          (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf a u)))
               (non_enter_predecessor_list g v)
           @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))) sg"
  unfolding side_cfg_T_eff_cmp_seed_st_def
  by (simp add: Let_def)

lemma side_rg_map_ltree:
  assumes "side_rg t"
  shows "side_rg (map_ltree r t)"
  using assms by (induction t) simp_all

lemma side_rg_side_rhs_fold_ctx_st:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> side_rg t"
  shows "side_rg (side_rhs_fold_ctx_st acc ts)"
  using assms
  by (induction ts arbitrary: acc) (auto intro: side_rg_seqcomp)
lemma side_rg_map_gtree:
  assumes "side_rg t"
  shows "side_rg (map_gtree r t)"
  using assms by (induction t) simp_all

lemma side_rg_side_cfg_T_eff_cmp_st_unit:
  assumes edge_st: "\<And>a u. \<exists>f. apply_etf_st etf_st a u = unit_edge_tree_st f u"
  assumes comb: "\<And>ctx cc ex. side_rg (cmb ctx cc ex)"
  shows "side_rg (side_cfg_T_eff_cmp_st gkey cmb g etf_st fresh_frame_st bot0_st s0_st z)"
proof (cases z)
  case (Pair v ctx)
  have intra: "\<And>u a. side_rg (map_gtree (\<lambda>_. gkey ctx)
      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))"
  proof -
    fix u a
    obtain f where f: "apply_etf_st etf_st a u = unit_edge_tree_st f u"
      using edge_st by blast
    show "side_rg (map_gtree (\<lambda>_. gkey ctx)
      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))"
      unfolding f
      by (intro side_rg_map_gtree side_rg_map_ltree side_rg_unit_edge_tree_st)
  qed
  have fold: "\<And>acc v. side_rg (side_rhs_fold_ctx_st acc
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))
          (non_enter_predecessor_list g v)
       @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))"
    by (rule side_rg_side_rhs_fold_ctx_st) (auto simp: intra comb split: prod.splits)
  show ?thesis
    unfolding Pair side_cfg_T_eff_cmp_st_def
    by (simp add: Let_def fold)
qed


section \<open>Keyed value-dependent (switching) combine\<close>

text \<open>
  The keyed sibling of \<^const>\<open>unit_combine_tree_ctx_st\<close>: a value-dependent
  combine that routes the callee-entry globals and the callee-exit read to a
  \<^emph>\<open>switched\<close> context slot \<open>callee_ctx = ec cc ctx caller\<close> computed from the
  queried caller state.  It is the executable shape behind the precise
  finite-context runs (Route A, Seidl 2026 eq. 6).  \<open>prep\<close> is the call-state
  transform applied before the context is read (the identity for a plain call,
  a global overwrite for a call that fixes an argument); \<open>ec\<close> is the context
  selector.  Both are kept abstract so the finite-context instance supplies
  them.  The global key is the context itself (\<open>gkey = id\<close>), so \<open>QueryG ctx\<close> and
  the \<open>Side callee_ctx\<close> writes land in per-context slots.
\<close>

definition switching_combine_st ::
  "(pp \<Rightarrow> 'a st \<Rightarrow> 'a st) \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a st \<Rightarrow> 'c)
   \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c, 'c, ('a::bounded_semilattice_sup_bot) st) strategy_tree"
where
  "switching_combine_st prep ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let caller = prep cc (sc \<squnion> g);
           callee_ctx = ec cc ctx caller in
       Side callee_ctx (restrict_global_st caller)
         (QueryL (ex, callee_ctx) (\<lambda>se.
           let res = restrict_local_st caller \<squnion> restrict_global_st se in
           Side callee_ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

text \<open>
  The abstract mirror over \<^typ>\<open>'a abs_state\<close>.  \<open>prep\<close> and \<open>ec\<close> are honest
  abstract functions (not the executable-inverse \<^const>\<open>st_of_abs\<close> hack), so this
  tree is a genuine abstract object usable in the soundness contract; the bridge
  below relates it to \<^const>\<open>switching_combine_st\<close> under commutation hypotheses
  discharged per instance.
\<close>

definition abs_switching_combine ::
  "(pp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c)
   \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c, 'c, ('a::bounded_semilattice_sup_bot) abs_state) strategy_tree"
where
  "abs_switching_combine prep ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let caller = prep cc (sc \<squnion> g);
           callee_ctx = ec cc ctx caller in
       Side callee_ctx (restrict_global caller)
         (QueryL (ex, callee_ctx) (\<lambda>se.
           let res = restrict_local caller \<squnion> restrict_global se in
           Side callee_ctx (restrict_global res)
             (Answer (restrict_local res))))))"

lemma side_rg_switching_combine_st:
  "side_rg (switching_combine_st prep ec cc ex ctx)"
  unfolding switching_combine_st_def by (simp add: Let_def)

text \<open>
  Bridge to the abstract combine.  Under commutation of the call-state transform
  and the context selector with \<^const>\<open>fun_of_st\<close>, the executable combine's
  denotation is the \<^const>\<open>fun_of_st\<close>-image of the abstract combine's.  The
  commutation hypotheses are the per-instance obligations (discharged for the
  sign instance downstream).
\<close>

lemma traverse_switching_combine_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes ec: "\<And>cc ctx s. ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)"
  shows "fun_of_st (traverse_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st)
         = traverse_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
             (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding switching_combine_st_def abs_switching_combine_def
  by (simp del: fun_of_st_sup
      add: Let_def o_def prep ec restrict_local_combine_eq fun_of_st_sup[symmetric])

lemma sides_switching_combine_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes ec: "\<And>cc ctx s. ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)"
  shows "fun_of_st (sides_of_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st k)
         = sides_of_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
             (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (cases k)
  case (Inl x)
  then show ?thesis
    unfolding switching_combine_st_def abs_switching_combine_def
    by (simp add: Let_def bot_fun_def)
next
  case (Inr g)
  then show ?thesis
    unfolding switching_combine_st_def abs_switching_combine_def
    by (simp add: Let_def o_def prep ec restrict_global_combine_eq
          bot_fun_def[symmetric])
qed

lemma dep_switching_combine_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes ec: "\<And>cc ctx s. ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)"
  shows "dep_aux \<sigma>_st (switching_combine_st prep_st ec_st cc ex ctx)
         = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (abs_switching_combine prep_abs ec_abs cc ex ctx)"
  unfolding switching_combine_st_def abs_switching_combine_def
  by (simp add: Let_def o_def prep ec)


section \<open>The switching combine satisfies the soundness contract\<close>

text \<open>
  The abstract switching combine discharges \<^const>\<open>switching_combine_sound\<close>
  under two per-instance conditions: the transfer's combine is the semantic
  \<^const>\<open>unit_combine_tree\<close> (the unit-global shape shared by the sign and mixed
  transfers), and the call-state transform \<^term>\<open>prep\<close> preserves locals (an
  argument-fixing call overwrites globals only).  The semantic combine reads the
  callee exit \<^emph>\<open>only\<close> through \<^const>\<open>restrict_global\<close> of a local slot, which the
  \<^const>\<open>inl_slot_globals_bot_ctx\<close> invariant forces to \<^term>\<open>bot\<close>; the callee's
  own global writes are routed to the switched slot \<^term>\<open>callee_ctx\<close>, which
  \<^term>\<open>pull_gk gkey ctx\<close> (reading only the caller key) never consults.  So the
  callee-context switch, invisible to the contract's read, does not obstruct the
  bound.
\<close>

lemma restrict_global_inl_bot:
  assumes "inl_slot_globals_bot sigma"
  shows "restrict_global (sigma (Inl v)) = bot"
  using assms unfolding inl_slot_globals_bot_def restrict_global_def
  by (auto simp: bot_fun_def)

lemma restrict_global_sup:
  "restrict_global (A \<squnion> B) = restrict_global A \<squnion> restrict_global B"
  by (rule ext) (simp add: restrict_global_def sup_fun_def)

lemma traverse_abs_switching_combine:
  "traverse_rhs (abs_switching_combine prep ec cc ex ctx) sigma
   = restrict_local (prep cc (sigma (Inl (cc, ctx)) \<squnion> sigma (Inr ctx)))"
  unfolding abs_switching_combine_def by (simp add: Let_def restrict_local_combine_eq)

text \<open>
  The combine analogue of \<open>side_cfg_T_eff_cmp_combine_le\<close> for the switching
  combine: the two conditions above plus the read invariant discharge the
  \<open>loc\<close> / \<open>glob\<close> bounds a post-solution must satisfy.
\<close>

lemma abs_switching_combine_le:
  fixes sigma :: "pp \<times> ('c::finite) + 'c \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
      and prep_loc: "\<And>cc s. restrict_local s \<le> restrict_local (prep cc s)"
      and gk: "gkey ctx = ctx"
      and pp: "part_post_solution
                 (side_cfg_T_eff_cmp gkey (\<lambda>c cc ex. abs_switching_combine prep ec cc ex c)
                    g etf fresh_frame bot0 s0) x sigma vars"
      and v: "(ret, ctx) \<in> vars"
      and e: "(cc, ex, ret) \<in> combines g"
      and finC: "finite (combines g)"
      and inl: "inl_slot_globals_bot_ctx sigma"
  shows "etf_full (etf_combine etf cc ex) (pull_gk gkey ctx sigma)
           \<le> side_env (pull_gk gkey ctx sigma) ret"
proof -
  let ?cmb = "\<lambda>c cc ex. abs_switching_combine prep ec cc ex c"
  let ?P = "pull_gk gkey ctx sigma"
  have Pl: "?P (Inl w) = sigma (Inl (w, ctx))" for w by (rule pull_gk_Inl)
  have Pr: "?P (Inr y) = sigma (Inr ctx)" for y by (simp add: pull_gk_Inr gk)
  have posteq: "eq (side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0) (ret, ctx) sigma
                  \<le> sigma (Inl (ret, ctx))"
    using pp v by auto
  have mem: "(cc, ex) \<in> set (combine_predecessor_list g ret)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have memtree:
    "?cmb ctx cc ex
       \<in> set (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                       (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                   (non_enter_predecessor_list g ret)
              @ map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g ret))"
    using mem by force
  have loc: "restrict_local (?P (Inl cc) \<squnion> ?P (Inr ())) \<le> sigma (Inl (ret, ctx))"
  proof -
    have "restrict_local (?P (Inl cc) \<squnion> ?P (Inr ()))
            = restrict_local (sigma (Inl (cc, ctx)) \<squnion> sigma (Inr ctx))"
      by (simp add: Pl Pr)
    also have "\<dots> \<le> restrict_local (prep cc (sigma (Inl (cc, ctx)) \<squnion> sigma (Inr ctx)))"
      by (rule prep_loc)
    also have "\<dots> = traverse_rhs (?cmb ctx cc ex) sigma"
      by (simp add: traverse_abs_switching_combine)
    also have "\<dots> \<le> eq (side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0) (ret, ctx) sigma"
      unfolding eq_side_cfg_T_eff_cmp by (rule traverse_le_side_acc_ctx[OF memtree])
    also have "\<dots> \<le> sigma (Inl (ret, ctx))" by (rule posteq)
    finally show ?thesis .
  qed
  have glob: "restrict_global (?P (Inl ex) \<squnion> ?P (Inr ())) \<le> sigma (Inr ctx)"
  proof -
    have "inl_slot_globals_bot ?P" by (rule inl_slot_globals_bot_pull_gk[OF inl])
    hence g0: "restrict_global (?P (Inl ex)) = bot" by (rule restrict_global_inl_bot)
    have "restrict_global (?P (Inl ex) \<squnion> ?P (Inr ()))
            = restrict_global (?P (Inl ex)) \<squnion> restrict_global (?P (Inr ()))"
      by (rule restrict_global_sup)
    also have "\<dots> = restrict_global (?P (Inr ()))" using g0 by simp
    also have "\<dots> \<le> ?P (Inr ())" by (simp add: restrict_global_def le_fun_def)
    also have "\<dots> = sigma (Inr ctx)" by (simp add: Pr)
    finally show ?thesis .
  qed
  have "etf_full (etf_combine etf cc ex) ?P
        = restrict_local (?P (Inl cc) \<squnion> ?P (Inr ()))
          \<squnion> restrict_global (?P (Inl ex) \<squnion> ?P (Inr ()))"
    unfolding comb by (simp add: etf_full_unit_combine_tree combine_abs_def restrict_combine)
  also have "\<dots> \<le> sigma (Inl (ret, ctx)) \<squnion> sigma (Inr ctx)"
    using loc glob by (rule sup_mono)
  also have "\<dots> = side_env ?P ret"
    by (simp add: side_env_def glob_env_unit Pl Pr)
  finally show ?thesis .
qed

text \<open>
  Hence the switching combine satisfies the kernel's combine-soundness contract
  \<^const>\<open>switching_combine_sound\<close>, so \<open>side_cfg_T_eff_cmp_collect_sound_gen\<close>
  certifies the precise finite-context run with the value-dependent combine ---
  not only the context-fixed one.
\<close>

lemma abs_switching_combine_satisfies_switching_combine_sound:
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
      and prep_loc: "\<And>cc s. restrict_local s \<le> restrict_local (prep cc s)"
      and gk: "\<And>ctx. gkey ctx = ctx"
      and finC: "finite (combines g)"
  shows "switching_combine_sound gkey (\<lambda>c cc ex. abs_switching_combine prep ec cc ex c)
           g etf fresh_frame bot0 s0"
  unfolding switching_combine_sound_def
proof (intro allI impI)
  fix sigma and x vars ctx cc ex ret
  assume pp: "part_post_solution
                (side_cfg_T_eff_cmp gkey (\<lambda>c cc ex. abs_switching_combine prep ec cc ex c)
                   g etf fresh_frame bot0 s0) x sigma vars"
     and inl: "inl_slot_globals_bot_ctx sigma"
     and v: "(ret, ctx) \<in> vars"
     and e: "(cc, ex, ret) \<in> combines g"
  show "etf_full (etf_combine etf cc ex) (pull_gk gkey ctx sigma)
          \<le> side_env (pull_gk gkey ctx sigma) ret"
    by (rule abs_switching_combine_le[OF comb prep_loc gk pp v e finC inl])
qed


section \<open>Transport: \<open>_st\<close> post-solution to its \<open>fun_of_st\<close>-image abstract system\<close>

text \<open>
  Generic \<^const>\<open>map_gtree\<close> companions of the \<^const>\<open>map_ltree\<close> transport helpers
  in \<open>Exec_Ctx_Bridge\<close>.  Traverse and dependency are clean \<^const>\<open>map_sum\<close>
  pullbacks; sides needs the constant-relabel unit lemmas because \<^const>\<open>map_gtree\<close>
  reroutes global slots.
\<close>

lemma sides_map_gtree_unit_gen:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (map_gtree r t) \<sigma> (Inr (r ()))
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id r z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_off_gen:
  "k \<notin> range r \<Longrightarrow> sides_of_rhs (map_gtree r t) \<sigma> (Inr k) = \<bottom>"
  by (induction t) (auto simp: Let_def)

lemma dep_aux_map_gtree:
  "dep_aux \<sigma> (map_gtree r t)
   = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) auto

lemma traverse_map_gtree_st_fun_of_st:
  assumes tr:
    "\<And>\<sigma>_st. fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  shows "fun_of_st (traverse_rhs (map_gtree r t_st) \<sigma>_st)
       = traverse_rhs (map_gtree r t_abs) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding traverse_rhs_map_gtree
  by (simp add: tr o_def)

lemma dep_map_gtree_st_fun_of_st:
  assumes dep:
    "\<And>\<sigma>_st. dep_aux \<sigma>_st t_st
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  shows "dep_aux \<sigma>_st (map_gtree r t_st)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (map_gtree r t_abs)"
  by (simp add: dep_aux_map_gtree dep o_def)

text \<open>
  The transport itself, parametric in the keyed generator's data: the executable
  and abstract edge transfers (related by the three edge bridges), the global key
  \<open>gkey\<close>, and the combine builders \<open>cmb_st\<close> / \<open>cmb_abs\<close> (related by the three
  combine bridges).  The switching combine of A3 is the instance whose combine
  bridges are \<open>traverse_\<close>/\<open>sides_\<close>/\<open>dep_switching_combine_st_fun_of_st\<close>.
\<close>

context
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st fresh_frame_st :: "'a st"
  fixes gkey :: "'c \<Rightarrow> 'g"
  fixes cmb_st :: "'c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree"
  fixes cmb_abs :: "'c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
       = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
  assumes tr_comb:
    "\<And>ctx cc ex \<sigma>_st. fun_of_st (traverse_rhs (cmb_st ctx cc ex) \<sigma>_st)
       = traverse_rhs (cmb_abs ctx cc ex) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_comb:
    "\<And>ctx cc ex \<sigma>_st k. fun_of_st (sides_of_rhs (cmb_st ctx cc ex) \<sigma>_st k)
       = sides_of_rhs (cmb_abs ctx cc ex) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_comb:
    "\<And>ctx cc ex \<sigma>_st. dep_aux \<sigma>_st (cmb_st ctx cc ex)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (cmb_abs ctx cc ex)"
begin

private lemma keyed_intra_traverse_rel:
  "fun_of_st (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st)
   = traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  by (rule traverse_map_gtree_st_fun_of_st[OF traverse_map_ltree_st_fun_of_st[OF tr_edge]])

private lemma keyed_intra_dep_rel:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))"
  by (rule dep_map_gtree_st_fun_of_st[OF dep_aux_map_ltree_st_eq[OF dep_edge]])

private lemma keyed_intra_sides_rel:
  "fun_of_st (sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st k)
   = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (cases k)
  case (Inl x)
  then show ?thesis by (simp add: bot_fun_def)
next
  case (Inr h)
  show ?thesis
  proof (cases "h = gkey ctx")
    case True
    have st: "sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st (Inr (gkey ctx))
              = sides_of_rhs (apply_etf_st etf_st a u)
                  (\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z)) (Inr ())"
      by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. gkey ctx"] sides_map_ltree_Inr
            sum.map_comp o_def)
    have abs: "sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k)) (Inr (gkey ctx))
              = sides_of_rhs (apply_etf etf a u)
                  (\<lambda>z. fun_of_st (\<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z))) (Inr ())"
      by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. gkey ctx"] sides_map_ltree_Inr
            sum.map_comp o_def)
    show ?thesis
      unfolding Inr True st abs
      using sd_edge[where a=a and u=u
              and \<sigma>_st="\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z)" and k="Inr ()"]
      by (simp add: o_def)
  next
    case False
    then have "h \<notin> range (\<lambda>_::unit. gkey ctx)" by simp
    then show ?thesis
      using Inr by (simp add: sides_map_gtree_off_gen bot_fun_def)
  qed
qed

private lemma cmp_tree_traverse_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  using mem
  by (auto intro: keyed_intra_traverse_rel
           simp: tr_comb in_set_zip split: prod.splits)

private lemma cmp_tree_sides_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  using mem
  by (auto intro: keyed_intra_sides_rel
           simp: sd_comb in_set_zip split: prod.splits)

private lemma cmp_tree_dep_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  using mem
  by (auto simp: keyed_intra_dep_rel dep_comb in_set_zip split: prod.splits)

private lemma cmp_fold_traverse_rel:
  "fun_of_st (traverse_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st)
   = traverse_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k))"
proof (rule side_rhs_fold_ctx_st_traverse_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule cmp_tree_traverse_rel)
qed simp

private lemma cmp_fold_sides_rel:
  "fun_of_st (sides_of_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st k)
   = sides_of_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (rule side_rhs_fold_ctx_st_sides_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st k. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    by (rule cmp_tree_sides_rel)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule cmp_tree_traverse_rel)
qed simp

private lemma cmp_fold_dep_rel:
  "dep_aux \<sigma>_st
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
proof (rule dep_aux_side_rhs_fold_ctx_st_eq)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
    by (rule cmp_tree_dep_rel)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule cmp_tree_traverse_rel)
qed simp

lemma fun_of_st_eq_side_cfg_T_eff_cmp_st:
  "fun_of_st
     (eq (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st) (v, ctx) \<sigma>_st)
   = eq (side_cfg_T_eff_cmp gkey cmb_abs g etf
           (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st)) (v, ctx)
       (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding eq_side_cfg_T_eff_cmp_st eq_side_cfg_T_eff_cmp
  by (simp add: Let_def traverse_side_rhs_fold_ctx cmp_fold_traverse_rel
        bot_fun_def[symmetric])

lemma fun_of_st_sides_side_cfg_T_eff_cmp_st:
  "fun_of_st
     (sides_of_rhs (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st (v, ctx)) \<sigma>_st k)
   = sides_of_rhs
       (side_cfg_T_eff_cmp gkey cmb_abs g etf
          (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  unfolding side_cfg_T_eff_cmp_st_def side_cfg_T_eff_cmp_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def cmp_fold_sides_rel bot_fun_def[symmetric])

lemma dep_aux_side_cfg_T_eff_cmp_st_eq:
  "dep_aux \<sigma>_st (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st (v, ctx))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (side_cfg_T_eff_cmp gkey cmb_abs g etf
          (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))"
  unfolding side_cfg_T_eff_cmp_st_def side_cfg_T_eff_cmp_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def cmp_fold_dep_rel bot_fun_def[symmetric])

text \<open>
  The transport theorem: a post-solution of the executable keyed generator maps,
  under \<^const>\<open>fun_of_st\<close>, to a post-solution of its abstract image.  Its proof is
  the standard three-obligation replay (dependency containment, RHS bound, side
  bound), each discharged by \<^const>\<open>fun_of_st\<close>-monotonicity against the eq / sides /
  dep bridges.
\<close>

theorem part_post_solution_cmp_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_cmp gkey cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof (rule part_post_solution_st_to_abs_transport[OF _ _ _ pp_st])
  fix v \<sigma>
  show "fun_of_st (eq (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st) v \<sigma>)
        = eq (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st)) v (\<lambda>k. fun_of_st (\<sigma> k))"
    using fun_of_st_eq_side_cfg_T_eff_cmp_st[where v="fst v" and ctx="snd v"]
    by (cases v) simp
next
  fix v \<sigma> k
  show "fun_of_st (sides_of_rhs (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st v) \<sigma> k)
        = sides_of_rhs (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
    using fun_of_st_sides_side_cfg_T_eff_cmp_st[where v="fst v" and ctx="snd v" and k=k]
    by (cases v) simp
next
  fix v \<sigma>
  show "dep_aux \<sigma> (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st v)
        = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v)"
    using dep_aux_side_cfg_T_eff_cmp_st_eq[where v="fst v" and ctx="snd v"]
    by (cases v) simp
qed

lemma fun_of_st_eq_side_cfg_T_eff_cmp_seed_st:
  "fun_of_st
     (eq (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st) (v, ctx) \<sigma>_st)
   = eq (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
           (fun_of_st bot0_st) (fun_of_st s0_st)) (v, ctx)
       (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding eq_side_cfg_T_eff_cmp_seed_st eq_side_cfg_T_eff_cmp_seed
  by (simp add: Let_def traverse_side_rhs_fold_ctx cmp_fold_traverse_rel bot_fun_def[symmetric])

lemma fun_of_st_sides_side_cfg_T_eff_cmp_seed_st:
  "fun_of_st
     (sides_of_rhs (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st (v, ctx)) \<sigma>_st k)
   = sides_of_rhs
       (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
          (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  unfolding side_cfg_T_eff_cmp_seed_st_def side_cfg_T_eff_cmp_seed_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def cmp_fold_sides_rel bot_fun_def[symmetric])

lemma dep_aux_side_cfg_T_eff_cmp_seed_st_eq:
  "dep_aux \<sigma>_st (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st (v, ctx))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
          (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))"
  unfolding side_cfg_T_eff_cmp_seed_st_def side_cfg_T_eff_cmp_seed_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def cmp_fold_dep_rel bot_fun_def[symmetric])

text \<open>
  The seeded transport: a post-solution of the executable seeded generator maps, under
  \<^const>\<open>fun_of_st\<close>, to a post-solution of its abstract image, the frame seed
  \<^term>\<open>frame_seed_st\<close> carried to \<^term>\<open>\<lambda>c. fun_of_st (frame_seed_st c)\<close>.  Mirror of
  @{thm [source] part_post_solution_cmp_st_to_abs_eff}; the context-dependent seed is the
  only difference from the constant-frame keyed generator.
\<close>

theorem part_post_solution_cmp_seed_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
              (fun_of_st bot0_st) (fun_of_st s0_st))
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof (rule part_post_solution_st_to_abs_transport[OF _ _ _ pp_st])
  fix v \<sigma>
  show "fun_of_st (eq (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st) v \<sigma>)
        = eq (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
                (fun_of_st bot0_st) (fun_of_st s0_st)) v (\<lambda>k. fun_of_st (\<sigma> k))"
    using fun_of_st_eq_side_cfg_T_eff_cmp_seed_st[where v="fst v" and ctx="snd v"]
    by (cases v) simp
next
  fix v \<sigma> k
  show "fun_of_st (sides_of_rhs (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st v) \<sigma> k)
        = sides_of_rhs (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
                (fun_of_st bot0_st) (fun_of_st s0_st) v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
    using fun_of_st_sides_side_cfg_T_eff_cmp_seed_st[where v="fst v" and ctx="snd v" and k=k]
    by (cases v) simp
next
  fix v \<sigma>
  show "dep_aux \<sigma> (side_cfg_T_eff_cmp_seed_st gkey cmb_st frame_seed_st g etf_st bot0_st s0_st v)
        = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (side_cfg_T_eff_cmp_seed gkey cmb_abs (\<lambda>c. fun_of_st (frame_seed_st c)) g etf
                (fun_of_st bot0_st) (fun_of_st s0_st) v)"
    using dep_aux_side_cfg_T_eff_cmp_seed_st_eq[where v="fst v" and ctx="snd v"]
    by (cases v) simp
qed

text \<open>
  The exact companion of @{thm [source] part_post_solution_cmp_st_to_abs_eff}: an exact
  \<^const>\<open>part_solution\<close> of the executable keyed generator maps, under \<^const>\<open>fun_of_st\<close>,
  to an exact \<^const>\<open>part_solution\<close> of its abstract image.  Same three commutation
  bridges, routed through @{thm [source] part_solution_st_to_abs_transport}.
\<close>

theorem part_solution_cmp_st_to_abs_eff:
  assumes ps_st:
    "part_solution (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_solution
           (side_cfg_T_eff_cmp gkey cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof (rule part_solution_st_to_abs_transport[OF _ _ _ ps_st])
  fix v \<sigma>
  show "fun_of_st (eq (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st) v \<sigma>)
        = eq (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st)) v (\<lambda>k. fun_of_st (\<sigma> k))"
    using fun_of_st_eq_side_cfg_T_eff_cmp_st[where v="fst v" and ctx="snd v"]
    by (cases v) simp
next
  fix v \<sigma> k
  show "fun_of_st (sides_of_rhs (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st v) \<sigma> k)
        = sides_of_rhs (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
    using fun_of_st_sides_side_cfg_T_eff_cmp_st[where v="fst v" and ctx="snd v" and k=k]
    by (cases v) simp
next
  fix v \<sigma>
  show "dep_aux \<sigma> (side_cfg_T_eff_cmp_st gkey cmb_st g etf_st fresh_frame_st bot0_st s0_st v)
        = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (side_cfg_T_eff_cmp gkey cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v)"
    using dep_aux_side_cfg_T_eff_cmp_st_eq[where v="fst v" and ctx="snd v"]
    by (cases v) simp
qed

end


text \<open>
  The switching-combine instance: for a unit-transfer edge and honest abstract
  \<open>prep\<close> / \<open>ec\<close> commuting with \<^const>\<open>fun_of_st\<close>, a post-solution of the executable
  keyed generator whose combine is \<^const>\<open>switching_combine_st\<close> transports to a
  post-solution of the abstract generator with \<^const>\<open>abs_switching_combine\<close>.
  This is the concrete object A5 discharges the switching-combine contract for.
\<close>

lemma part_post_solution_cmp_switching_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st fresh_frame_st :: "'a st"
  fixes gkey :: "'c \<Rightarrow> 'c"
  fixes prep_st :: "pp \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes prep_abs :: "pp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes ec_st :: "pp \<Rightarrow> 'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  fixes ec_abs :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes ec: "\<And>cc ctx s. ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)"
  assumes pp_st:
    "part_post_solution
       (side_cfg_T_eff_cmp_st gkey
          (\<lambda>ctx cc ex. switching_combine_st (prep_st) (ec_st) cc ex ctx)
          g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_cmp gkey
          (\<lambda>ctx cc ex. abs_switching_combine (prep_abs) (ec_abs) cc ex ctx)
          g etf (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute Let_def)
  have sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
     = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using sides_apply_etf_st_unit_transfer[OF edge_st edge comb comb_st commute]
    by (simp add: o_def)
  have dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
     = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  have tr_comb:
    "\<And>ctx cc ex \<sigma>_st.
       fun_of_st (traverse_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st)
       = traverse_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using prep ec by (rule traverse_switching_combine_st_fun_of_st)
  have sd_comb:
    "\<And>ctx cc ex \<sigma>_st k.
       fun_of_st (sides_of_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st k)
       = sides_of_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using prep ec by (rule sides_switching_combine_st_fun_of_st)
  have dep_comb:
    "\<And>ctx cc ex \<sigma>_st.
       dep_aux \<sigma>_st (switching_combine_st prep_st ec_st cc ex ctx)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (abs_switching_combine prep_abs ec_abs cc ex ctx)"
    using prep ec by (rule dep_switching_combine_st_fun_of_st)
  show ?thesis
    by (rule part_post_solution_cmp_st_to_abs_eff
          [OF tr_edge sd_edge dep_edge tr_comb sd_comb dep_comb pp_st])
qed

text \<open>
  The exact companion of the switching-combine transport: an exact \<^const>\<open>part_solution\<close>
  of the executable switching-combine generator maps, under \<^const>\<open>fun_of_st\<close>, to an exact
  \<^const>\<open>part_solution\<close> of its abstract \<^const>\<open>abs_switching_combine\<close> image.  Same six
  commutation facts, routed through @{thm [source] part_solution_cmp_st_to_abs_eff}.
\<close>

lemma part_solution_cmp_switching_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st fresh_frame_st :: "'a st"
  fixes gkey :: "'c \<Rightarrow> 'c"
  fixes prep_st :: "pp \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes prep_abs :: "pp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes ec_st :: "pp \<Rightarrow> 'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  fixes ec_abs :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes ec: "\<And>cc ctx s. ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)"
  assumes ps_st:
    "part_solution
       (side_cfg_T_eff_cmp_st gkey
          (\<lambda>ctx cc ex. switching_combine_st (prep_st) (ec_st) cc ex ctx)
          g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_solution
       (side_cfg_T_eff_cmp gkey
          (\<lambda>ctx cc ex. abs_switching_combine (prep_abs) (ec_abs) cc ex ctx)
          g etf (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute Let_def)
  have sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
     = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using sides_apply_etf_st_unit_transfer[OF edge_st edge comb comb_st commute]
    by (simp add: o_def)
  have dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
     = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  have tr_comb:
    "\<And>ctx cc ex \<sigma>_st.
       fun_of_st (traverse_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st)
       = traverse_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using prep ec by (rule traverse_switching_combine_st_fun_of_st)
  have sd_comb:
    "\<And>ctx cc ex \<sigma>_st k.
       fun_of_st (sides_of_rhs (switching_combine_st prep_st ec_st cc ex ctx) \<sigma>_st k)
       = sides_of_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using prep ec by (rule sides_switching_combine_st_fun_of_st)
  have dep_comb:
    "\<And>ctx cc ex \<sigma>_st.
       dep_aux \<sigma>_st (switching_combine_st prep_st ec_st cc ex ctx)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (abs_switching_combine prep_abs ec_abs cc ex ctx)"
    using prep ec by (rule dep_switching_combine_st_fun_of_st)
  show ?thesis
    by (rule part_solution_cmp_st_to_abs_eff
          [OF tr_edge sd_edge dep_edge tr_comb sd_comb dep_comb ps_st])
qed


end

