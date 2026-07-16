section \<open>Executable transport for the native D/G spine\<close>

text \<open>
  The reusable bridge that lets the verified always-join solver run on the
  carrier-opaque D/G equation system and certify the computed result against the
  abstract \<open>sound_dg_spec\<close> soundness endpoints.

  The abstract analysis state \<open>'a abs_state\<close> (\<open>vname \<Rightarrow> 'a\<close>) does not
  code-generate.  The executable two-region association-list quotient
  \<open>'a st\<close> (\<open>Voblint_Analysis.Exec_St\<close>) does, and \<open>fun_of_st\<close>
  is the refinement morphism back to \<open>'a abs_state\<close>.  This theory lifts that
  morphism to the D/G product carrier \<open>('a st, 'b st) dg_state\<close> and proves the
  structural commutation lemmas the equation-system transport needs.

  Because the D/G lattice operations on \<open>('a, 'b) dg_state\<close> are all
  componentwise (\<open>Voblint_Analysis.DG_Framework\<close>), the executable carrier
  inherits every solver-required operation --- \<open>\<le>\<close>, \<open>\<squnion>\<close>, \<open>\<bottom>\<close>, \<open>=\<close>, widening ---
  componentwise from the \<open>'a st\<close> instances for free.
\<close>

theory Exec_DG_Bridge
  imports
    "Voblint_Analysis.DG_Soundness"
    "Voblint_Analysis.Exec_Bridge"
    "Voblint_Analysis.TD_Side_Eff_Cmp_Gen"
begin

subsection \<open>The combined warrowing arity for the executable state\<close>

text \<open>
  The always-join solver does not perform genuine widening for a finite domain
  such as Sign, but the vendored \<open>TD.TD_side\<close> locale still fixes a warrowing
  value lattice, so its value type is constrained by \<open>bounded_warrowing\<close>.
  The base spine runs the solver at \<open>'a st\<close>, which needs only the separate
  \<open>warrowing\<close> arity (\<open>Voblint_Analysis.Exec_St\<close>).  The D/G carrier needs
  \<open>('a, 'b) dg_state\<close> in \<open>warrowing\<close>, which \<open>Voblint_Analysis.DG_Framework\<close>
  provides only bundled as \<open>bounded_warrowing\<close>, requiring both components in
  \<open>bounded_warrowing\<close>.  That combined arity for \<open>st\<close> was not previously
  registered; it follows solely from the already declared
  \<open>st :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot\<close> and
  \<open>st :: (bounded_warrowing) warrowing\<close> instances (a trivial \<open>..\<close>).

  It is placed here rather than in \<open>Voblint_Analysis.Exec_St\<close> to keep it next
  to its sole DG consumer and avoid a core-theory rebuild; it is a generally-valid
  instance that could later migrate upstream.
\<close>

instance st :: (bounded_warrowing) bounded_warrowing ..

subsection \<open>The product refinement morphism\<close>

definition fun_of_dg_st ::
  "(('a::bot) st, ('b::bot) st) dg_state \<Rightarrow> ('a abs_state, 'b abs_state) dg_state"
where
  "fun_of_dg_st d = DG (fun_of_st (locals d)) (fun_of_st (globs d))"

lemma fun_of_dg_st_simps [simp]:
  "locals (fun_of_dg_st d) = fun_of_st (locals d)"
  "globs (fun_of_dg_st d) = fun_of_st (globs d)"
  "fun_of_dg_st (DG a b) = DG (fun_of_st a) (fun_of_st b)"
  by (simp_all add: fun_of_dg_st_def)

lemma fun_of_dg_st_bot [simp]:
  "fun_of_dg_st (bot :: ('a::bounded_semilattice_sup_bot st,
                         'b::bounded_semilattice_sup_bot st) dg_state) = bot"
  by (simp add: fun_of_dg_st_def bot_dg_state_def fun_of_st_bot bot_fun_def)

lemma fun_of_dg_st_sup:
  "fun_of_dg_st ((a::('c::bounded_semilattice_sup_bot st,
                      'd::bounded_semilattice_sup_bot st) dg_state) \<squnion> b)
     = fun_of_dg_st a \<squnion> fun_of_dg_st b"
  by (simp add: fun_of_dg_st_def sup_dg_state_def fun_of_st_sup)

lemma fun_of_dg_st_mono:
  "(a::('c::bounded_semilattice_sup_bot st, 'd::bounded_semilattice_sup_bot st) dg_state) \<le> b
     \<Longrightarrow> fun_of_dg_st a \<le> fun_of_dg_st b"
  by (auto simp: fun_of_dg_st_def less_eq_dg_state_def fun_of_st_mono)

subsection \<open>Executable unit (diagonal) step and combine\<close>

text \<open>
  The executable mirrors of \<open>unit_step\<close> / \<open>unit_combine_step\<close>
  (\<open>Voblint_Analysis.DG_Framework\<close>), operating on \<open>'a st\<close>, together with
  their commutation through \<open>fun_of_st\<close>.  These are domain-agnostic: any
  executable transfer mirror \<open>tf_st\<close> commuting with \<open>apply_tf tf\<close> yields a
  commuting DG step.
\<close>

definition unit_step_st ::
  "(('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st) \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st \<times> 'a st"
where
  "unit_step_st f d g = (let res = f (d \<squnion> g) in (restrict_global_st res, restrict_local_st res))"

definition unit_combine_step_st ::
  "(vname option \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st \<times> 'a st)"
where
  "unit_combine_step_st dst dc de g =
     (let res = combine_collect_abs_st dst (dc \<squnion> g) (de \<squnion> g)
      in (restrict_global_st res, restrict_local_st res))"

lemma unit_step_st_commute:
  assumes "\<And>s. fun_of_st (f_st s) = f_abs (fun_of_st s)"
  shows "map_prod fun_of_st fun_of_st (unit_step_st f_st d g)
           = unit_step f_abs (fun_of_st d) (fun_of_st g)"
  by (simp add: unit_step_st_def unit_step_def assms fun_of_st_sup
                fun_of_st_restrict_local_st fun_of_st_restrict_global_st Let_def)

lemma unit_combine_step_st_commute:
  "map_prod fun_of_st fun_of_st (unit_combine_step_st dst dc de g)
     = unit_combine_step dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  by (simp add: unit_combine_step_st_def unit_combine_step_def fun_of_st_sup
                fun_of_st_restrict_local_st fun_of_st_restrict_global_st Let_def
                restrict_local_combine_eq restrict_global_combine_eq)

definition unit_dg_spec_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st) \<Rightarrow> ('a st, 'a st) dg_spec"
where
  "unit_dg_spec_st tf_st = \<lparr>
    dgs_nop        = unit_step_st (tf_st EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_st (tf_st (EA_Assign x e))),
    dgs_assume     = (\<lambda>b. unit_step_st (tf_st (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step_st (tf_st (EA_AssumeNot b))),
    dgs_enter      = (\<lambda>xs es. unit_step_st (tf_st (EA_Enter xs es))),
    dgs_combine    = unit_combine_step_st
  \<rparr>"

lemma dg_spec_step_unit_st:
  "dg_spec_step (unit_dg_spec_st tf_st) a = unit_step_st (tf_st a)"
  unfolding unit_dg_spec_st_def by (cases a) simp_all

subsection \<open>Per-tree traversal commutation\<close>

text \<open>
  The D/G edge and combine trees have closed-form traversals
  (\<open>Voblint_Analysis.DG_Framework\<close>): the local Answer carries \<open>snd (step \<dots>)\<close>
  and no global, so \<open>fun_of_dg_st\<close> commutes with the traversal precisely when
  the analysis step commutes componentwise.
\<close>

lemma traverse_dg_edge_tree_commute:
  assumes H: "\<And>d g. map_prod fun_of_st fun_of_st (step_st d g)
                     = step_abs (fun_of_st d) (fun_of_st g)"
  shows "fun_of_dg_st (traverse_rhs (dg_edge_tree step_st u) \<sigma>_st)
           = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st \<circ> \<sigma>_st)"
proof -
  have "snd (step_abs (fun_of_st (locals (\<sigma>_st (Inl u)))) (fun_of_st (globs (\<sigma>_st (Inr ())))))
        = fun_of_st (snd (step_st (locals (\<sigma>_st (Inl u))) (globs (\<sigma>_st (Inr ())))))"
    using H[of "locals (\<sigma>_st (Inl u))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_edge_tree fun_of_st_bot bot_fun_def)
qed

lemma traverse_dg_combine_tree_commute:
  assumes H: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (comb_st dst dc de g)
                        = comb_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  shows "fun_of_dg_st (traverse_rhs (dg_combine_tree comb_st dst cc ex) \<sigma>_st)
           = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st \<circ> \<sigma>_st)"
proof -
  have "snd (comb_abs dst (fun_of_st (locals (\<sigma>_st (Inl cc)))) (fun_of_st (locals (\<sigma>_st (Inl ex))))
              (fun_of_st (globs (\<sigma>_st (Inr ())))))
        = fun_of_st (snd (comb_st dst (locals (\<sigma>_st (Inl cc))) (locals (\<sigma>_st (Inl ex)))
              (globs (\<sigma>_st (Inr ())))))"
    using H[of dst "locals (\<sigma>_st (Inl cc))" "locals (\<sigma>_st (Inl ex))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_combine_tree fun_of_st_bot bot_fun_def)
qed

subsection \<open>Wrapped-tree commutation and the accumulator fold\<close>

text \<open>
  The generator re-keys each tree with \<open>map_gtree\<close> / \<open>map_ltree\<close> to place
  local unknowns at \<open>(pp, c)\<close> and global unknowns at \<open>gkey c\<close>.  Those relabellings
  are transparent to \<open>fun_of_dg_st\<close>: it acts on values, they act on unknown
  keys, and the per-tree commutation is stated for an arbitrary valuation.
\<close>

lemma traverse_wrapped_edge_commute:
  assumes H: "\<And>d g. map_prod fun_of_st fun_of_st (step_st d g)
                     = step_abs (fun_of_st d) (fun_of_st g)"
  shows "fun_of_dg_st (traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st (traverse_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_edge_tree_commute)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

text \<open>
  \<open>side_acc_dg\<close> folds the local Answers of a tree list; the fold commutes with
  \<open>fun_of_st\<close> whenever the trees commute pointwise (given as a \<open>list_all2\<close>
  so both the transported accumulator and the unchanged unknown structure thread
  through the induction).
\<close>

lemma side_acc_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st))
           ts_st ts_abs"
  shows "fun_of_st (side_acc_dg acc_st \<sigma>_st ts_st)
           = side_acc_dg (fun_of_st acc_st) (fun_of_dg_st \<circ> \<sigma>_st) ts_abs"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hl: "fun_of_st (locals (traverse_rhs t_st \<sigma>_st))
              = locals (traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_simps(1))
  have h: "fun_of_st (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st))
           = fun_of_st acc_st \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st))"
    by (simp add: fun_of_st_sup hl)
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg.simps(2))
qed

lemma traverse_wrapped_combine_commute:
  assumes H: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (comb_st dst dc de g)
                        = comb_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  shows "fun_of_dg_st (traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st (traverse_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_combine_tree_commute)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

subsection \<open>The executable D/G equation generator\<close>

text \<open>
  The executable generator is the same polymorphic seeded-CMP generator
  (\<open>side_cfg_T_eff_cmp_seed_dg\<close>) the abstract \<open>sound_dg_spec.dg_gen\<close> uses,
  instantiated at an \<open>'a st\<close>-valued analysis spec.  Unit context (\<open>gkey = (\<lambda>_. ())\<close>),
  no procedure-entry seed (\<open>frame_seed = (\<lambda>_. bot)\<close>).
\<close>

definition dg_cmb_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> unit \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_of S ctx dst cc ex = map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx)) (dg_spec_combine_tree S dst cc ex))"

text \<open>The combine predecessors of \<open>v\<close>, each wrapped into a unit-context
  strategy tree.  One name for the tuple-destructuring map reused across the
  eq / sides / dep commutation goals below.\<close>
abbreviation dg_combine_trees where
  "dg_combine_trees S g v \<equiv>
     map (\<lambda>(cc, ex, dst). dg_cmb_of S () dst cc ex) (combine_predecessor_list g v)"

definition dg_gen_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) eqsT"
where
  "dg_gen_of S g bot0 s0d s0g =
     side_cfg_T_eff_cmp_seed_dg predecessor_list (\<lambda>_. ()) (dg_cmb_of S) (\<lambda>_ _. []) g S bot0 s0d s0g"

subsection \<open>Side-effect commutation for the generator\<close>

lemma sides_of_rhs_Inl_bot: "sides_of_rhs t \<sigma> (Inl a) = bot"
  by (induction t arbitrary: \<sigma>) (auto simp: Let_def)

lemma sides_dg_edge_tree_commute:
  assumes H: "\<And>d g. map_prod fun_of_st fun_of_st (step_st d g) = step_abs (fun_of_st d) (fun_of_st g)"
  shows "fun_of_dg_st (sides_of_rhs (dg_edge_tree step_st u) \<tau>_st k)
       = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (step_abs (fun_of_st (locals (\<tau>_st (Inl u)))) (fun_of_st (globs (\<tau>_st (Inr ())))))
        = fun_of_st (fst (step_st (locals (\<tau>_st (Inl u))) (globs (\<tau>_st (Inr ())))))"
    using H[of "locals (\<tau>_st (Inl u))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_edge_tree_Inr fun_of_dg_st_def fun_of_st_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: sides_dg_edge_tree_Inl fun_of_dg_st_bot)
qed

lemma sides_dg_combine_tree_commute:
  assumes H: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (comb_st dst dc de g)
                        = comb_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  shows "fun_of_dg_st (sides_of_rhs (dg_combine_tree comb_st dst cc ex) \<tau>_st k)
       = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (comb_abs dst (fun_of_st (locals (\<tau>_st (Inl cc)))) (fun_of_st (locals (\<tau>_st (Inl ex)))) (fun_of_st (globs (\<tau>_st (Inr ())))))
        = fun_of_st (fst (comb_st dst (locals (\<tau>_st (Inl cc))) (locals (\<tau>_st (Inl ex))) (globs (\<tau>_st (Inr ())))))"
    using H[of dst "locals (\<tau>_st (Inl cc))" "locals (\<tau>_st (Inl ex))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_combine_tree_Inr fun_of_dg_st_def fun_of_st_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: dg_combine_tree_def fun_of_dg_st_bot)
qed

lemma sides_wrap_reduce:
  "sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk t)) \<sigma> (Inr gk)
     = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum lk (\<lambda>_. gk) z)) (Inr ())"
  apply (subst sides_map_gtree_unit[where r="\<lambda>_. gk", simplified])
  apply (subst sides_map_ltree_Inr)
  apply (simp add: sum.map_comp o_def)
  done

lemma sides_wrapped_edge_commute:
  assumes H: "\<And>d g. map_prod fun_of_st fun_of_st (step_st d g) = step_abs (fun_of_st d) (fun_of_st g)"
  shows "fun_of_dg_st (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st (sides_of_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_edge_tree_commute)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_bot)
  qed
qed

lemma sides_wrapped_combine_commute:
  assumes H: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (comb_st dst dc de g)
                        = comb_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  shows "fun_of_dg_st (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st (sides_of_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_combine_tree_commute)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_bot)
  qed
qed

lemma sides_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k))
           ts_st ts_abs"
  shows "fun_of_dg_st (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st k)
           = sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) (fun_of_dg_st \<circ> \<sigma>_st) k"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: fun_of_dg_st_bot bot_fun_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have sd: "fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih: "fun_of_dg_st (sides_of_rhs (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st k)
          = sides_of_rhs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st))) ts_abs) (fun_of_dg_st \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp fun_of_dg_st_sup sd ih comp_def)
qed

subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

lemma dep_aux_dg_edge_tree: "dep_aux \<sigma> (dg_edge_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_tree_def dep_aux_def)

lemma dep_aux_dg_combine_tree: "dep_aux \<sigma> (dg_combine_tree comb dst cc ex) = {Inl cc, Inl ex, Inr ()}"
  by (auto simp: dg_combine_tree_def dep_aux_def)

lemma dep_aux_Side: "dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t"
  by (simp add: dep_aux_def)

lemma dep_aux_map_gtree:
  "dep_aux \<sigma> (map_gtree r t) = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) (auto simp: dep_aux_def)

lemma dep_aux_wrapped_edge_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_edge_tree)

lemma dep_aux_wrapped_combine_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_combine_tree)

lemma dep_aux_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs) ts_st ts_abs"
  shows "dep_aux \<sigma>_st (side_rhs_fold_dg acc_st ts_st) = dep_aux \<sigma>_abs (side_rhs_fold_dg acc_abs ts_abs)"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: dep_aux_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hd: "dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs" using Cons.hyps(1) by simp
  have ih: "dep_aux \<sigma>_st (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st)
          = dep_aux \<sigma>_abs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) ts_abs)"
    by (rule Cons.IH)
  show ?case by (simp add: dep_aux_seqcomp hd ih)
qed

subsection \<open>Bundled per-tree transport relation\<close>

text \<open>
  \<open>dg_tree_st_commute \<sigma>_st t_st t_abs\<close> is the reusable transport contract for a
  single strategy tree: its executable denotation, its side-effect map, and its
  static dependencies all agree (through \<open>fun_of_dg_st\<close>) with the abstract tree
  read against the pushed-forward valuation \<open>fun_of_dg_st \<circ> \<sigma>_st\<close>.  It bundles
  the three commutation obligations the equation-system transport threads through
  the accumulator fold.

  The intra per-edge trees are discharged generically below from a componentwise
  analysis step.  The opaque \<open>cmb\<close>/\<open>extra\<close> trees --- whose \<^const>\<open>Side\<close> targets
  may be computed inside a \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> continuation (a routed
  callee seed) --- are supplied by the instance as bundled hypotheses; the bridge
  never assumes their side targets are syntactically fixed.

  The context is bound as \<open>ctx\<close>, never \<open>c\<close>: an unqualified \<open>c\<close> is captured by the
  imported constant \<open>state.c\<close>, which silently pins these theorems to a single
  context and produces a proof that only looks polymorphic.
\<close>

definition dg_tree_st_commute ::
  "('u + 'k \<Rightarrow> (('a::bounded_semilattice_sup_bot) st, ('b::bounded_semilattice_sup_bot) st) dg_state)
   \<Rightarrow> ('u, 'k, ('a st, 'b st) dg_state) strategy_tree
   \<Rightarrow> ('u, 'k, ('a abs_state, 'b abs_state) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute \<sigma>_st t_st t_abs \<longleftrightarrow>
     fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)
   \<and> (\<forall>k. fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k)
   \<and> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st \<circ> \<sigma>_st) t_abs"

lemma dg_tree_st_commute_trav:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_sides:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_dep:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st \<circ> \<sigma>_st) t_abs"
  by (simp add: dg_tree_st_commute_def)

text \<open>The intra per-edge tree, relabelled by an arbitrary global key \<open>gk\<close> and
  local relabel \<open>lk\<close>, satisfies the bundled relation whenever the analysis step
  commutes componentwise.\<close>

lemma dg_tree_st_commute_wrapped_edge:
  assumes H: "\<And>d g. map_prod fun_of_st fun_of_st (step_st d g) = step_abs (fun_of_st d) (fun_of_st g)"
  shows "dg_tree_st_commute \<sigma>_st
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  unfolding dg_tree_st_commute_def
  by (intro conjI allI
        traverse_wrapped_edge_commute[where step_st=step_st and step_abs=step_abs, OF H]
        sides_wrapped_edge_commute[where step_st=step_st and step_abs=step_abs, OF H]
        dep_aux_wrapped_edge_eq)

subsection \<open>Per-node tree-list transport for the generator\<close>

text \<open>
  The concatenated per-node tree list --- intra predecessors, combine trees, and
  \<open>extra\<close> trees --- transports elementwise.  Intra edges follow from \<open>Hstep\<close>;
  the combine and extra trees are the instance's bundled hypotheses.
\<close>

lemma seed_dg_list_commute:
  assumes Hstep: "\<And>a d g'. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g')"
      and Hcmb: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (cmb_st c' dst cc ex) (cmb_abs c' dst cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st c' w) (extra_abs c' w)"
  shows "list_all2 (dg_tree_st_commute \<sigma>_st)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ex, dst). cmb_st ctx dst cc ex) (combine_predecessor_list g v)
      @ extra_st ctx v)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ex, dst). cmb_abs ctx dst cc ex) (combine_predecessor_list g v)
      @ extra_abs ctx v)"
proof -
  have edge_elem: "\<And>u a. dg_tree_st_commute \<sigma>_st
        (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u)))
        (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u)))"
    unfolding apply_dg_spec_def
    by (rule dg_tree_st_commute_wrapped_edge[where step_st="dg_spec_step S_st a" and step_abs="dg_spec_step S_abs a" for a, OF Hstep])
  show ?thesis
    by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl
                   edge_elem Hcmb Hextra split_beta)
qed

text \<open>Projections of the bundled list relation onto the shapes the accumulator
  fold, side fold, and dependency fold each expect.\<close>

lemma dg_list_commute_trav:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st (traverse_rhs t_st \<sigma>_st)
                    = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_travsides:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)
              \<and> (\<forall>k. fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_dep:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st \<circ> \<sigma>_st) t_abs) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

subsection \<open>Equation-system transport for the generic generator\<close>

text \<open>
  The generic transport theorems below carry the executable D/G post-solution to
  the abstract one over unknowns \<^typ>\<open>pp \<times> 'c\<close> with arbitrary global key type
  \<^typ>\<open>'k\<close>.  They fix only the analysis-step commutation \<open>Hstep\<close>; the routed
  combine and enter-seed trees enter through the bundled hypotheses \<open>Hcmb\<close> /
  \<open>Hextra\<close>, so a computed \<^const>\<open>Side\<close> target transports without being pinned.
\<close>

lemma eq_seed_dg_commute:
  assumes Hstep: "\<And>a d g'. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g')"
      and Hcmb: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (cmb_st c' dst cc ex) (cmb_abs c' dst cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st c' w) (extra_abs c' w)"
  shows "fun_of_dg_st (eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) (v, ctx) \<sigma>_st)
       = eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
               (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) (v, ctx) (fun_of_dg_st \<circ> \<sigma>_st)"
proof -
  have la: "list_all2 (\<lambda>t_st t_abs. fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st))
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ex, dst). cmb_st ctx dst cc ex) (combine_predecessor_list g v) @ extra_st ctx v)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ex, dst). cmb_abs ctx dst cc ex) (combine_predecessor_list g v) @ extra_abs ctx v)"
    by (rule dg_list_commute_trav[OF seed_dg_list_commute[OF Hstep Hcmb Hextra]])
  show ?thesis
    unfolding eq_side_cfg_T_eff_cmp_seed_dg
    by (simp add: fun_of_st_bot bot_fun_def side_acc_dg_commute[OF la] fun_of_st_sup flip: bot_fun_def)
qed

lemma sides_seed_dg_commute:
  assumes Hstep: "\<And>a d g'. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g')"
      and Hcmb: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (cmb_st c' dst cc ex) (cmb_abs c' dst cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st c' w) (extra_abs c' w)"
  shows "fun_of_dg_st (sides_of_rhs
             (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g (v, ctx)) \<sigma>_st k)
       = sides_of_rhs
             (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
                (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g) (v, ctx)) (fun_of_dg_st \<circ> \<sigma>_st) k"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. fun_of_dg_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st \<circ> \<sigma>_st) k))
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ex, dst). cmb_st ctx dst cc ex) (combine_predecessor_list g w) @ extra_st ctx w)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ex, dst). cmb_abs ctx dst cc ex) (combine_predecessor_list g w) @ extra_abs ctx w)"
    by (rule dg_list_commute_travsides[OF seed_dg_list_commute[OF Hstep Hcmb Hextra]])
  have fold: "\<And>w acc_st k. fun_of_dg_st (sides_of_rhs (side_rhs_fold_dg acc_st
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
          @ map (\<lambda>(cc, ex, dst). cmb_st ctx dst cc ex) (combine_predecessor_list g w) @ extra_st ctx w)) \<sigma>_st k)
     = sides_of_rhs (side_rhs_fold_dg (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
          @ map (\<lambda>(cc, ex, dst). cmb_abs ctx dst cc ex) (combine_predecessor_list g w) @ extra_abs ctx w))
          (fun_of_dg_st \<circ> \<sigma>_st) k"
    by (rule sides_side_rhs_fold_dg_commute[OF la])
  have seed: "fun_of_dg_st (DG bot s0g) = DG bot (fun_of_st s0g)"
    by (simp add: fun_of_dg_st_def fun_of_st_bot bot_fun_def)
  show ?thesis
    unfolding side_cfg_T_eff_cmp_seed_dg_def Let_def
    by (simp add: Let_def fun_upd_apply fun_of_dg_st_sup seed fold fun_of_st_sup flip: bot_fun_def)
qed

lemma dep_seed_dg_eq:
  assumes Hstep: "\<And>a d g'. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g')"
      and Hcmb: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (cmb_st c' dst cc ex) (cmb_abs c' dst cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st c' w) (extra_abs c' w)"
  shows "dep_aux \<sigma>_st (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g (v, ctx))
       = dep_aux (fun_of_dg_st \<circ> \<sigma>_st)
           (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs bot0' s0d' s0g' (v, ctx))"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st \<circ> \<sigma>_st) t_abs)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ex, dst). cmb_st ctx dst cc ex) (combine_predecessor_list g w) @ extra_st ctx w)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ex, dst). cmb_abs ctx dst cc ex) (combine_predecessor_list g w) @ extra_abs ctx w)"
    by (rule dg_list_commute_dep[OF seed_dg_list_commute[OF Hstep Hcmb Hextra]])
  show ?thesis
    unfolding side_cfg_T_eff_cmp_seed_dg_def Let_def
    by (simp add: dep_aux_Side dep_aux_side_rhs_fold_dg_commute[OF la])
qed

subsection \<open>The post-solution transport theorem\<close>

text \<open>
  A partial post-solution of the executable context-indexed D/G equation system,
  mapped value-wise through \<open>fun_of_dg_st\<close>, is a partial post-solution of the
  abstract system over the same unknown set --- unknown identity, \<open>vars\<close>, and
  dependencies are unchanged; only the equation values transport.  The routed
  combine and enter-seed trees transport through the bundled \<open>Hcmb\<close> / \<open>Hextra\<close>
  hypotheses, so the dynamic \<^const>\<open>Side\<close> targets are carried over faithfully.
\<close>

theorem part_post_solution_seed_dg_st_to_abs:
  assumes Hstep: "\<And>a d g'. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g')"
      and Hcmb: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (cmb_st c' dst cc ex) (cmb_abs c' dst cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute \<sigma>_st) (extra_st c' w) (extra_abs c' w)"
      and pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
              (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) x (fun_of_dg_st \<circ> \<sigma>_st) vars"
proof (intro conjI ballI)
  show "x \<in> vars" using pp by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have dl: "dep\<^sub>L (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u \<subseteq> vars"
    using pp u by simp
  have "dep_aux (fun_of_dg_st \<circ> \<sigma>_st)
          (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g) (v, c))
      = dep_aux \<sigma>_st (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g (v, c))"
    by (rule dep_seed_dg_eq[OF Hstep Hcmb Hextra, symmetric])
  hence "dep\<^sub>L (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) (fun_of_dg_st \<circ> \<sigma>_st) u
       = dep\<^sub>L (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u"
    unfolding dep\<^sub>L_def dep_def uv by simp
  thus "dep\<^sub>L (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) (fun_of_dg_st \<circ> \<sigma>_st) u \<subseteq> vars"
    using dl by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st
              \<le> \<sigma>_st (Inl u)" using pp u by simp
  have "eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) u (fun_of_dg_st \<circ> \<sigma>_st)
      = fun_of_dg_st (eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st)"
    unfolding uv by (simp add: eq_seed_dg_commute[OF Hstep Hcmb Hextra])
  also have "\<dots> \<le> fun_of_dg_st (\<sigma>_st (Inl u))" using le by (rule fun_of_dg_st_mono)
  finally show "eq (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g)) u (fun_of_dg_st \<circ> \<sigma>_st)
              \<le> (fun_of_dg_st \<circ> \<sigma>_st) (Inl u)" by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "sides_of_rhs (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st
              \<le> \<sigma>_st" using pp u by simp
  show "sides_of_rhs (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g) u) (fun_of_dg_st \<circ> \<sigma>_st) \<le> fun_of_dg_st \<circ> \<sigma>_st"
  proof (rule le_funI)
    fix k
    have "sides_of_rhs (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g) u) (fun_of_dg_st \<circ> \<sigma>_st) k
        = fun_of_dg_st (sides_of_rhs (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st k)"
      unfolding uv by (simp add: sides_seed_dg_commute[OF Hstep Hcmb Hextra])
    also have "\<dots> \<le> fun_of_dg_st (\<sigma>_st k)"
      using le[THEN le_funD] by (rule fun_of_dg_st_mono)
    finally show "sides_of_rhs (side_cfg_T_eff_cmp_seed_dg pred_sel gkey cmb_abs extra_abs g S_abs
             (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g) u) (fun_of_dg_st \<circ> \<sigma>_st) k
                \<le> (fun_of_dg_st \<circ> \<sigma>_st) k" by simp
  qed
qed

subsection \<open>The monovariant (unit-context) specialisation\<close>

text \<open>
  The original monovariant D/G bridge is now the \<open>unit\<close>-context instance of the
  generic transport: no procedure-entry seed (\<open>extra = \<lambda>_ _. []\<close>), a single global
  slot (\<open>gkey = \<lambda>_. ()\<close>), and the intra predecessors merged directly
  (\<open>pred_sel = predecessor_list\<close>).  The combine tree \<open>dg_cmb_of S\<close> discharges the
  bundled \<open>Hcmb\<close> obligation from the analysis-level combine commutation.
\<close>

lemma dg_tree_st_commute_dg_cmb_of:
  assumes Hcomb: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (dgs_combine S_st dst dc de g)
                            = dgs_combine S_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  shows "dg_tree_st_commute \<sigma>_st (dg_cmb_of S_st c' dst cc ex) (dg_cmb_of S_abs c' dst cc ex)"
  unfolding dg_tree_st_commute_def dg_cmb_of_def dg_spec_combine_tree_def
  by (intro conjI allI
        traverse_wrapped_combine_commute[where comb_st="dgs_combine S_st" and comb_abs="dgs_combine S_abs", OF Hcomb]
        sides_wrapped_combine_commute[where comb_st="dgs_combine S_st" and comb_abs="dgs_combine S_abs", OF Hcomb]
        dep_aux_wrapped_combine_eq)

theorem part_post_solution_dg_st_to_abs:
  assumes Hstep: "\<And>a d g. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g)
                          = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g)"
      and Hcomb: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (dgs_combine S_st dst dc de g)
                            = dgs_combine S_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
      and pp: "part_post_solution (dg_gen_of S_st g bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution (dg_gen_of S_abs g (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g))
           x (fun_of_dg_st \<circ> \<sigma>_st) vars"
proof -
  have hc: "\<And>c' dst cc ex. dg_tree_st_commute \<sigma>_st (dg_cmb_of S_st c' dst cc ex) (dg_cmb_of S_abs c' dst cc ex)"
    by (rule dg_tree_st_commute_dg_cmb_of[OF Hcomb])
  from pp have pp':
    "part_post_solution (side_cfg_T_eff_cmp_seed_dg predecessor_list (\<lambda>_. ()) (dg_cmb_of S_st) (\<lambda>_ _. [])
                           g S_st bot0 s0d s0g) x \<sigma>_st vars"
    unfolding dg_gen_of_def .
  show ?thesis
    unfolding dg_gen_of_def
    by (rule part_post_solution_seed_dg_st_to_abs[OF Hstep hc _ pp']) simp
qed

end
