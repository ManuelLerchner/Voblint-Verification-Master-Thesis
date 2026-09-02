theory Exec_DG_Generator
  imports
    Exec_DG_Refines
    "Voblint_Core.DG_LTR_Sound"
begin

section \<open>The executable equation generator and its transport\<close>

text \<open>
  The generator that turns a compiled CFG into an executable D/G equation system, and the
  transport of one node's equation --- value, side effects and dependencies --- through the
  readback. \<open>dg_reader_commute_gen\<close> states that transport once for an arbitrary pair
  of readers preserving \<open>bot\<close> and \<open>(\<squnion>)\<close>; every concrete readback in the pipeline is one of
  its instances.
\<close>

subsection \<open>The executable D/G equation generator\<close>

text \<open>
  The executable generator is the same polymorphic seeded keyed generator
  (\<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>) every routed instance uses, with its
  intra hook instantiated at the specification's own compiled edge tree.
  Unit context (\<open>gkey = (\<lambda>_. ())\<close>), no procedure-entry seed
  (\<open>frame_seed = (\<lambda>_. bot)\<close>).
\<close>

definition dg_cmb_at_of ::
  "(pp \<times> unit, unit, unit, 'd::bounded_semilattice_sup_bot,
     'h::bounded_semilattice_sup_bot) dg_spec
     \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pname
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_at_of S ctx ca cc p =
     dg_spec_combine_tree S (call_info_of ca p) (Inl (cc, ctx)) (Inl (FunctionResult p, ctx)) (\<lambda>_. ())"

definition dg_cmb_of ::
  "(pp \<times> unit, unit, unit, 'd::bounded_semilattice_sup_bot,
     'h::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> cfg
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_of S g route ctx ca cc v =
     side_rhs_fold_dg bot (map (dg_cmb_at_of S ctx ca cc) (static_targets g v cc ca))"

definition dg_extra_of ::
  "(pp \<times> unit, unit, unit, 'd::bounded_semilattice_sup_bot,
     'h::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> cfg
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree list"
where
  "dg_extra_of S g route ctx v =
     map (\<lambda>(cl, ca).
       transfer_tree
         (dgs_enter S (call_info_of ca (case v of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined)))
         (Inl (cl, ctx)) (\<lambda>_. ())) (entry_call_list g v)"

definition dg_gen_of ::
  "(pp \<times> unit, unit, unit, 'd::bounded_semilattice_sup_bot,
     'h::bounded_semilattice_sup_bot) dg_spec \<Rightarrow> cfg \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) eqsT"
where
  "dg_gen_of S g bot0 s0d s0g =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. ())
       (\<lambda>_ _ _ _. ()) (\<lambda>c src a. dg_spec_edge_tree S a src (\<lambda>_. ()))
       (dg_cmb_of S g) (dg_extra_of S g) g bot0 s0d s0g"

subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

lemma dep_aux_Side: "dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t"
  by (simp add: dep_aux_def)

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

subsection \<open>Carrier-generic whole-CFG commute\<close>

text \<open>
  The commute facts below only ever use that a readback preserves \<open>bot\<close> and \<open>(\<squnion>)\<close>; no
  proof in the chain inspects \<open>fun_of_resolved_st_q_for\<close> or \<open>abs_state\<close> itself.
  \<open>dg_reader_commute_gen\<close> factors that out: a pair of local/global readers \<open>Floc\<close>/\<open>Fglob\<close>
  satisfying those two laws, from which every whole-tree and whole-equation-system commute
  fact in this chain is proved once.  The raw readback \<open>fun_of_dg_st_for\<close> and the
  reachability-lifted readback are both thin instances of the same engine.
\<close>

definition fun_of_dg_st_gen ::
  "('a \<Rightarrow> 'a2) \<Rightarrow> ('b \<Rightarrow> 'b2) \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a2, 'b2) dg_state"
where
  "fun_of_dg_st_gen Floc Fglob d = DG (Floc (locals d)) (Fglob (globs d))"

lemma fun_of_dg_st_gen_simps [simp]:
  "locals (fun_of_dg_st_gen Floc Fglob d) = Floc (locals d)"
  "globs (fun_of_dg_st_gen Floc Fglob d) = Fglob (globs d)"
  "fun_of_dg_st_gen Floc Fglob (DG a b) = DG (Floc a) (Fglob b)"
  by (simp_all add: fun_of_dg_st_gen_def)

locale dg_reader_commute_gen =
  fixes Floc :: "'a::bounded_semilattice_sup_bot \<Rightarrow> 'a2::bounded_semilattice_sup_bot"
    and Fglob :: "'b::bounded_semilattice_sup_bot \<Rightarrow> 'b2::bounded_semilattice_sup_bot"
  assumes Floc_bot: "Floc bot = bot"
      and Floc_sup: "\<And>x y. Floc (x \<squnion> y) = Floc x \<squnion> Floc y"
      and Fglob_bot: "Fglob bot = bot"
      and Fglob_sup: "\<And>x y. Fglob (x \<squnion> y) = Fglob x \<squnion> Fglob y"
begin

lemma Floc_mono: "x \<le> y \<Longrightarrow> Floc x \<le> Floc y"
  by (metis Floc_sup le_iff_sup)

lemma Fglob_mono: "x \<le> y \<Longrightarrow> Fglob x \<le> Fglob y"
  by (metis Fglob_sup le_iff_sup)

lemma fun_of_dg_st_gen_bot [simp]:
  "fun_of_dg_st_gen Floc Fglob (bot :: ('a,'b) dg_state) = bot"
  by (simp add: bot_dg_state_def Floc_bot Fglob_bot)

lemma fun_of_dg_st_gen_sup:
  "fun_of_dg_st_gen Floc Fglob (a \<squnion> b :: ('a,'b) dg_state)
     = fun_of_dg_st_gen Floc Fglob a \<squnion> fun_of_dg_st_gen Floc Fglob b"
  by (simp add: sup_dg_state_def Floc_sup Fglob_sup)

lemma fun_of_dg_st_gen_mono:
  "(a :: ('a,'b) dg_state) \<le> b \<Longrightarrow> fun_of_dg_st_gen Floc Fglob a \<le> fun_of_dg_st_gen Floc Fglob b"
  by (auto simp: less_eq_dg_state_def Floc_mono Fglob_mono)

subsubsection \<open>Bundled per-tree transport relation\<close>

definition dg_tree_st_commute ::
  "('u + 'k \<Rightarrow> ('a,'b) dg_state) \<Rightarrow> ('u, 'k, ('a,'b) dg_state) strategy_tree
    \<Rightarrow> ('u, 'k, ('a2,'b2) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute \<sigma>_st t_st t_abs \<longleftrightarrow>
     fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
   \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k)
   \<and> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"

lemma dg_tree_st_commute_trav:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_sides:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_dep:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
     \<Longrightarrow> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"
  by (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_trav:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st)
                    = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_travsides:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
              \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)

lemma dg_list_commute_dep:
  "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st
                    = dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_def)


subsubsection \<open>Classifier-parametric fold transport\<close>

lemma side_acc_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))
           ts_st ts_abs"
  shows "Floc (side_acc_dg acc_st \<sigma>_st ts_st)
           = side_acc_dg (Floc acc_st) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) ts_abs"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hl: "Floc (locals (traverse_rhs t_st \<sigma>_st))
              = locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_gen_simps(1))
  have h: "Floc (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st))
           = Floc acc_st \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    by (simp add: Floc_sup hl)
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg.simps(2))
qed

lemma sides_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k))
           ts_st ts_abs"
  shows "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st k)
           = sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: bot_fun_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have sd: "fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih: "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st k)
          = sides_of_rhs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))) ts_abs) (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp fun_of_dg_st_gen_sup sd ih comp_def)
qed


subsubsection \<open>Routed heterogeneous CALL/COMB transport\<close>

text \<open>
  \<^const>\<open>routed_cmb_g\<close>/\<^const>\<open>routed_extra_g\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>)
  are the canonical heterogeneous routing shape: parametric only in a routing
  function \<open>route\<close> and a seed-key injection \<open>seed_key\<close>, with the seed payload
  carried on the \<open>locals\<close> half so \<open>'D\<close>/\<open>'G\<close> stay independent. The two lemmas
  below feed this generic engine's \<open>Hcmb\<close>/\<open>Hextra\<close> obligations directly, so any
  context-sensitive analysis instantiating \<open>cmb\<close>/\<open>extra\<close> at those constants
  discharges CALL/COMB transport once here rather than re-deriving its own
  tree-commute reasoning.

  The specification's own enter and combine now appear inside the routed tree as
  compiled sub-trees, so their transport hypotheses are themselves tree commutes
  rather than pair-shaped equations on a retired \<open>'dg \<times> 'dl\<close> transfer -- and
  \<open>caller_cont\<close> needs no hypothesis at all, since
  \<^const>\<open>dg_spec_combine_transfer\<close> already runs it inside the combine sub-tree.
  Sequencing them is what \<open>dg_tree_st_commute_seqcomp\<close> does: a bind commutes when
  its head commutes and its continuation commutes at the head's answer.
\<close>

lemma dg_tree_st_commute_seqcomp:
  assumes head: "dg_tree_st_commute \<sigma>_st t_st t_abs"
    and tail: "dg_tree_st_commute \<sigma>_st (k_st (traverse_rhs t_st \<sigma>_st))
                 (k_abs (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)))"
  shows "dg_tree_st_commute \<sigma>_st (t_st \<bind> k_st) (t_abs \<bind> k_abs)"
  using head tail
  unfolding dg_tree_st_commute_def
  by (simp add: dep_aux_seqcomp fun_of_dg_st_gen_sup)

lemma dg_tree_st_commute_answer:
  "dg_tree_st_commute \<sigma>_st (answer d) (answer (fun_of_dg_st_gen Floc Fglob d))"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_read_local:
  "dg_tree_st_commute \<sigma>_st (read_local x) (read_local x)"
  by (simp add: dg_tree_st_commute_def)

text \<open>A local-only transfer compiles to a single answer, so its commute is the
  readback equation on the pure function alone -- no tree reasoning, and no
  hypothesis about the global half beyond the reader's own \<open>bot\<close> law.\<close>

lemma dg_tree_st_commute_local_transfer:
  assumes "Floc (f d) = F (Floc d)"
  shows "dg_tree_st_commute \<sigma>_st
           (sp_run_with (\<lambda>x. DG x bot) (local_transfer f (mk_dg_man d gk)))
           (sp_run_with (\<lambda>x. DG x bot) (local_transfer F (mk_dg_man (Floc d) gk)))"
  by (simp add: dg_tree_st_commute_def local_transfer_def mk_dg_man_def
      fun_of_dg_st_gen_def bot_dg_state_def assms Floc_bot Fglob_bot)

lemma dg_tree_st_commute_local_combine_transfer:
  assumes "Floc (f d de) = F (Floc d) (Floc de)"
  shows "dg_tree_st_commute \<sigma>_st
           (sp_run_with (\<lambda>x. DG x bot) (local_combine_transfer f (mk_dg_man d gk) de))
           (sp_run_with (\<lambda>x. DG x bot)
              (local_combine_transfer F (mk_dg_man (Floc d) gk) (Floc de)))"
  by (simp add: dg_tree_st_commute_def local_combine_transfer_def mk_dg_man_def
      fun_of_dg_st_gen_def bot_dg_state_def assms Floc_bot Fglob_bot)

lemma dg_tree_st_commute_QueryL:
  assumes cont: "dg_tree_st_commute \<sigma>_st (k_st (\<sigma>_st (Inl x)))
                   (k_abs (fun_of_dg_st_gen Floc Fglob (\<sigma>_st (Inl x))))"
  shows "dg_tree_st_commute \<sigma>_st (QueryL x k_st) (QueryL x k_abs)"
  using cont unfolding dg_tree_st_commute_def by (simp add: comp_def)

lemma dg_tree_st_commute_side_effect:
  assumes cont: "dg_tree_st_commute \<sigma>_st t_st t_abs"
  shows "dg_tree_st_commute \<sigma>_st (side_effect y d t_st)
           (side_effect y (fun_of_dg_st_gen Floc Fglob d) t_abs)"
proof -
  have sides: "\<And>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_effect y d t_st) \<sigma>_st k)
      = sides_of_rhs (side_effect y (fun_of_dg_st_gen Floc Fglob d) t_abs)
          (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  proof -
    fix k
    show "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (side_effect y d t_st) \<sigma>_st k)
        = sides_of_rhs (side_effect y (fun_of_dg_st_gen Floc Fglob d) t_abs)
            (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
      using dg_tree_st_commute_sides[OF cont]
      by (cases "k = Inr y") (simp_all add: Let_def fun_of_dg_st_gen_sup)
  qed
  show ?thesis
    using cont sides unfolding dg_tree_st_commute_def
    by (simp add: dep_aux_Side)
qed

lemma dg_tree_st_commute_side_rhs_fold_dg:
  assumes la: "list_all2 (dg_tree_st_commute \<sigma>_st) ts_st ts_abs"
  shows "dg_tree_st_commute \<sigma>_st
           (side_rhs_fold_dg acc_st ts_st) (side_rhs_fold_dg (Floc acc_st) ts_abs)"
proof -
  have dep: "(\<Union>t\<in>set ts_st. dep_aux \<sigma>_st t)
      = (\<Union>t\<in>set ts_abs. dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t)"
    using dg_list_commute_dep[OF la]
    by (induction rule: list_all2_induct) (auto simp: comp_def)
  show ?thesis
    unfolding dg_tree_st_commute_def
    by (simp add: traverse_side_rhs_fold_dg Fglob_bot dep_aux_side_rhs_fold_dg_char dep
          side_acc_dg_commute[OF dg_list_commute_trav[OF la]]
          sides_side_rhs_fold_dg_commute[OF dg_list_commute_travsides[OF la]])
qed

lemma dg_tree_st_commute_routed_cmb_g_at:
  assumes Henter: "\<And>ci d. dg_tree_st_commute \<sigma>_st
        (sp_run_with (\<lambda>x. DG x bot) (dgs_enter S_st ci (mk_dg_man d (\<lambda>_. gk0))))
        (sp_run_with (\<lambda>x. DG x bot) (dgs_enter S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0))))"
    and Hcomb: "\<And>ci d de. dg_tree_st_commute \<sigma>_st
        (sp_run_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st ci (mk_dg_man d (\<lambda>_. gk0)) de))
        (sp_run_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)) (Floc de)))"
    and Hroute: "\<And>u c' d ca'. route_st u c' d ca' = route_abs u c' (Floc d) ca'"
  shows "dg_tree_st_commute \<sigma>_st
           (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc caller p)
           (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc (Floc caller) p)"
proof -
  let ?ci = "call_info_of ca p"
  let ?et_st = "sp_run_with (\<lambda>x. DG x bot) (dgs_enter S_st ?ci (mk_dg_man caller (\<lambda>_. gk0)))"
  let ?et_abs = "sp_run_with (\<lambda>x. DG x bot)
                   (dgs_enter S_abs ?ci (mk_dg_man (Floc caller) (\<lambda>_. gk0)))"
  let ?\<sigma>_abs = "fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st"
  have ent: "Floc (locals (traverse_rhs ?et_st \<sigma>_st)) = locals (traverse_rhs ?et_abs ?\<sigma>_abs)"
    using dg_tree_st_commute_trav[OF Henter] by (metis fun_of_dg_st_gen_simps(1))
  have ctx_eq: "route_abs cc ctx (locals (traverse_rhs ?et_abs ?\<sigma>_abs)) ca
              = route_st cc ctx (locals (traverse_rhs ?et_st \<sigma>_st)) ca"
    unfolding ent[symmetric] by (rule Hroute[symmetric])
  have tail: "\<And>es_st es_abs. Floc (locals es_st) = locals es_abs \<Longrightarrow>
      dg_tree_st_commute \<sigma>_st
        (side_effect (seed_key (FunctionEntry p) (route_st cc ctx (locals es_st) ca))
           (DG (locals es_st) bot)
           (answer (DG bot bot))
         \<bind> (\<lambda>_. read_local (FunctionResult p, route_st cc ctx (locals es_st) ca)
           \<bind> (\<lambda>cs. sp_run_with (\<lambda>x. DG x bot)
                 (dg_spec_combine_transfer S_st ?ci (mk_dg_man caller (\<lambda>_. gk0)) (locals cs)))))
        (side_effect (seed_key (FunctionEntry p) (route_abs cc ctx (locals es_abs) ca))
           (DG (locals es_abs) bot)
           (answer (DG bot bot))
         \<bind> (\<lambda>_. read_local (FunctionResult p, route_abs cc ctx (locals es_abs) ca)
           \<bind> (\<lambda>cs. sp_run_with (\<lambda>x. DG x bot)
                 (dg_spec_combine_transfer S_abs ?ci (mk_dg_man (Floc caller) (\<lambda>_. gk0)) (locals cs)))))"
  proof -
    fix es_st es_abs
    assume e: "Floc (locals es_st) = locals es_abs"
    have r: "route_abs cc ctx (locals es_abs) ca = route_st cc ctx (locals es_st) ca"
      unfolding e[symmetric] by (rule Hroute[symmetric])
    show "dg_tree_st_commute \<sigma>_st
        (side_effect (seed_key (FunctionEntry p) (route_st cc ctx (locals es_st) ca))
           (DG (locals es_st) bot) (answer (DG bot bot))
         \<bind> (\<lambda>_. read_local (FunctionResult p, route_st cc ctx (locals es_st) ca)
           \<bind> (\<lambda>cs. sp_run_with (\<lambda>x. DG x bot)
                 (dg_spec_combine_transfer S_st ?ci (mk_dg_man caller (\<lambda>_. gk0)) (locals cs)))))
        (side_effect (seed_key (FunctionEntry p) (route_abs cc ctx (locals es_abs) ca))
           (DG (locals es_abs) bot) (answer (DG bot bot))
         \<bind> (\<lambda>_. read_local (FunctionResult p, route_abs cc ctx (locals es_abs) ca)
           \<bind> (\<lambda>cs. sp_run_with (\<lambda>x. DG x bot)
                 (dg_spec_combine_transfer S_abs ?ci (mk_dg_man (Floc caller) (\<lambda>_. gk0)) (locals cs)))))"
      unfolding r
      apply (simp only: seqcomp_tree.simps)
      apply (rule dg_tree_st_commute_side_effect[where d = "DG (locals es_st) bot",
              simplified fun_of_dg_st_gen_simps e Fglob_bot])
      apply (rule dg_tree_st_commute_QueryL)
      apply (simp only: fun_of_dg_st_gen_simps)
      apply (rule Hcomb)
      done
  qed
  show ?thesis
    unfolding routed_cmb_g_at_def Let_def
    by (rule dg_tree_st_commute_seqcomp[OF Henter]) (rule tail[OF ent])
qed

text \<open>The call site itself: the resolver must answer the same targets on both
  carriers, which is the resolution-level twin of \<open>Hroute\<close>. At
  \<^const>\<open>static_resolve\<close> that premise is free, since the answer never reads the
  state.\<close>

lemma dg_tree_st_commute_routed_cmb_g:
  assumes Henter: "\<And>ci d. dg_tree_st_commute \<sigma>_st
        (sp_run_with (\<lambda>x. DG x bot) (dgs_enter S_st ci (mk_dg_man d (\<lambda>_. gk0))))
        (sp_run_with (\<lambda>x. DG x bot) (dgs_enter S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0))))"
    and Hcomb: "\<And>ci d de. dg_tree_st_commute \<sigma>_st
        (sp_run_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st ci (mk_dg_man d (\<lambda>_. gk0)) de))
        (sp_run_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)) (Floc de)))"
    and Hroute: "\<And>u c' d ca'. route_st u c' d ca' = route_abs u c' (Floc d) ca'"
    and Hresolve: "\<And>w cc' ca' d. resolve_st w cc' ca' d = resolve_abs w cc' ca' (Floc d)"
  shows "dg_tree_st_commute \<sigma>_st
           (routed_cmb_g S_st gk0 seed_key resolve_st route_st ctx ca cc v)
           (routed_cmb_g S_abs gk0 seed_key resolve_abs route_abs ctx ca cc v)"
proof -
  let ?caller = "locals (\<sigma>_st (Inl (cc, ctx)))"
  have at: "\<And>p. dg_tree_st_commute \<sigma>_st
      (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller p)
      (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc (Floc ?caller) p)"
    using Henter Hcomb Hroute by (rule dg_tree_st_commute_routed_cmb_g_at)
  have la: "list_all2 (dg_tree_st_commute \<sigma>_st)
      (map (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller)
        (resolve_st v cc ca ?caller))
      (map (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc (Floc ?caller))
        (resolve_st v cc ca ?caller))"
    by (simp add: list_all2_conv_all_nth at)
  have body: "dg_tree_st_commute \<sigma>_st
      (side_rhs_fold_dg bot
        (map (routed_cmb_g_at S_st gk0 seed_key route_st ctx ca cc ?caller)
          (resolve_st v cc ca ?caller)))
      (side_rhs_fold_dg bot
        (map (routed_cmb_g_at S_abs gk0 seed_key route_abs ctx ca cc (Floc ?caller))
          (resolve_st v cc ca ?caller)))"
    using dg_tree_st_commute_side_rhs_fold_dg[OF la, where acc_st = bot]
    by (simp add: Floc_bot)
  show ?thesis
    unfolding routed_cmb_g_def
    using body by (simp add: dg_tree_st_commute_def Hresolve[symmetric] comp_def)
qed

lemma dg_tree_st_commute_routed_extra_g:
  shows "list_all2 (dg_tree_st_commute \<sigma>_st)
           (routed_extra_g seed_key gk0 route_st ctx v)
           (routed_extra_g seed_key gk0 route_abs ctx v)"
  by (cases v) (simp_all add: routed_extra_g_def dg_tree_st_commute_def Fglob_bot)

end

section \<open>Reading the executable generator as the generic hook generator\<close>

text \<open>
  Two generators build the same equation system by different enumerations.
  \<^const>\<open>dg_gen_of\<close> walks call sites and, at each, folds over that site's static
  targets; the generic hook generator walks return edges and emits one tree per
  edge. A call site with several targets is therefore listed once per target and
  each listing folds over all of them, so the two produce genuinely different
  strategy trees --- not merely reordered ones.

  What they agree on is everything a solver or a soundness proof looks at. The
  duplicated contributions collapse because the fold accumulates with \<open>(\<squnion>)\<close>, so
  the answer, the published sides and the dependency set all match. These are
  observational theorems for that reason, and deliberately not an equality.
\<close>

lemma set_concat_static_targets:
  "set (concat (map (\<lambda>(cc, ca). map (h cc ca) (static_targets g v cc ca))
                    (call_site_list g v)))
     = set (map (\<lambda>(c, ca, p). h c ca p) (call_target_list g v))"
proof -
  have "set (static_targets g v c ca) = {p. (c, ca, p) \<in> set (call_target_list g v)}"
    for c ca
    unfolding static_targets_def call_target_list_def by force
  then show ?thesis
    unfolding call_site_list_def by force
qed

context sound_dg_spec_ltr_for
begin

text \<open>The two per-target combine trees are the same tree: both compose the
  specification's combine at the call site and the callee's result node.\<close>

text \<open>Oriented so the rewrite is usable: the call-site node the generic hook
  carries determines everything, whereas \<^const>\<open>dg_cmb_at_of\<close> does not mention
  it.\<close>

lemma ltr_combine_tree_eq_dg_cmb_at_of:
  "ltr_combine_tree cc ca (FunctionResult p) v = dg_cmb_at_of S () ca cc p"
  by (simp add: dg_cmb_at_of_def ltr_combine_tree_def)

text \<open>
  Away from a procedure-entry node the two enter legs name the callee
  differently -- one by \<^const>\<open>entry_proc\<close>, one by an \<open>undefined\<close> branch -- so
  they agree only where that node really is an entry. \<^const>\<open>wf_cfg\<close> is what
  rules the other case out: a call edge never points anywhere else, so the
  enumeration is empty there and neither spelling is reached.
\<close>

lemma entry_call_list_empty_if_not_entry:
  assumes wf: "wf_cfg g" and fin: "finite (calls g)"
    and ne: "\<And>p. v \<noteq> FunctionEntry p"
  shows "entry_call_list g v = []"
proof (rule ccontr)
  assume "entry_call_list g v \<noteq> []"
  then obtain c ca where "(c, ca) \<in> set (entry_call_list g v)"
    by (cases "entry_call_list g v") auto
  then have "(c, ca) \<in> entry_calls g v" by (simp add: fin)
  then obtain after where "(c, ca, v, after) \<in> calls g"
    by (auto simp: entry_calls_def)
  with wf have "\<exists>p. v = FunctionEntry p" unfolding wf_cfg_def by blast
  with ne show False by blast
qed

lemma dg_extra_of_eq_ltr_enter_trees:
  assumes wf: "wf_cfg g" and fin: "finite (calls g)"
  shows "dg_extra_of S g route () v
           = map (\<lambda>(cl, ca). ltr_enter_tree cl ca v) (entry_call_list g v)"
  by (cases v)
     (simp_all add: dg_extra_of_def ltr_enter_tree_def transfer_tree_def
        entry_call_list_empty_if_not_entry[OF wf fin])

text \<open>
  The three observations the solver and the soundness proof take of one node's
  equation. The intra leg is the same list by definition of
  \<^const>\<open>intra_predecessor_addr_list\<close>, the enter leg by the lemma above, and the
  combine leg only up to the duplication described at the head of this section
  --- which \<open>side_rhs_fold_dg_flat_cong\<close> absorbs, since it asks for set equality
  of the flattened contributions rather than list equality.
\<close>

lemma dg_gen_of_obs_hook_gen:
  assumes wf: "wf_cfg g" and fin: "finite (calls g)"
  shows
    "traverse_rhs (dg_gen_of S g bot0 s0d s0g vc) \<tau>
       = traverse_rhs (hooks.hook_gen g bot0 s0d s0g vc) \<tau>"
    "sides_of_rhs (dg_gen_of S g bot0 s0d s0g vc) \<tau> z
       = sides_of_rhs (hooks.hook_gen g bot0 s0d s0g vc) \<tau> z"
    "dep_aux \<tau> (dg_gen_of S g bot0 s0d s0g vc)
       = dep_aux \<tau> (hooks.hook_gen g bot0 s0d s0g vc)"
proof -
  obtain v c where vc: "vc = (v, c)" by (cases vc)
  have c: "c = ()" by simp
  define I where
    "I = map (\<lambda>(u, a). transfer_tree (dg_spec_step S a) (Inl (u, ())) (\<lambda>_. ()))
           (intra_predecessor_list g v)"
  define TSS where
    "TSS = map (\<lambda>(cc, ca). map (dg_cmb_at_of S () ca cc) (static_targets g v cc ca))
             (call_site_list g v)"
  define U where
    "U = map (\<lambda>(cl, ca, ex). ltr_combine_tree cl ca ex v) (return_call_action_list g v)"
  define Z where
    "Z = map (\<lambda>(cl, ca). ltr_enter_tree cl ca v) (entry_call_list g v)"

  have flat: "set (concat TSS) = set U"
  proof -
    have "set U = set (map (\<lambda>(cc, ca, p). dg_cmb_at_of S () ca cc p) (call_target_list g v))"
      unfolding U_def return_call_action_list_eq_call_target_list
      by (simp add: ltr_combine_tree_eq_dg_cmb_at_of case_prod_beta)
    then show ?thesis
      unfolding TSS_def
        set_concat_static_targets[where h = "\<lambda>cc ca. dg_cmb_at_of S () ca cc"]
      by simp
  qed

  have key:
    "traverse_rhs (side_rhs_fold_dg acc (I @ map (side_rhs_fold_dg bot) TSS @ Z)) \<tau>
       = traverse_rhs (side_rhs_fold_dg acc (I @ U @ Z)) \<tau>"
    "sides_of_rhs (side_rhs_fold_dg acc (I @ map (side_rhs_fold_dg bot) TSS @ Z)) \<tau> w
       = sides_of_rhs (side_rhs_fold_dg acc (I @ U @ Z)) \<tau> w"
    "dep_aux \<tau> (side_rhs_fold_dg acc (I @ map (side_rhs_fold_dg bot) TSS @ Z))
       = dep_aux \<tau> (side_rhs_fold_dg acc (I @ U @ Z))"
    for acc w
    by (rule side_rhs_fold_dg_flat_cong[OF flat])+

  have gen: "dg_gen_of S g bot0 s0d s0g (v, ())
               = (let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
                      t = side_rhs_fold_dg acc0 (I @ map (side_rhs_fold_dg bot) TSS @ Z)
                  in if v = cfg_entry g then side_effect () (DG bot s0g) t else t)"
    unfolding dg_gen_of_def side_cfg_T_eff_keyed_seed_dg_def
      intra_predecessor_addr_list_def dg_cmb_of_def dg_spec_edge_tree_def
    by (simp add: Let_def split_def o_def I_def TSS_def Z_def
        dg_extra_of_eq_ltr_enter_trees[OF wf fin])

  have hgen: "hooks.hook_gen g bot0 s0d s0g (v, ())
                = (let acc0 = (if v = cfg_entry g then bot0 \<squnion> s0d else bot0);
                       t = side_rhs_fold_dg acc0 (I @ U @ Z)
                   in if v = cfg_entry g then side_effect () (DG bot s0g) t else t)"
    unfolding hooks.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
      ltr_edge_tree_def dg_spec_edge_tree_def
    by (simp add: Let_def split_def I_def U_def Z_def)

  show
    "traverse_rhs (dg_gen_of S g bot0 s0d s0g vc) \<tau>
       = traverse_rhs (hooks.hook_gen g bot0 s0d s0g vc) \<tau>"
    "sides_of_rhs (dg_gen_of S g bot0 s0d s0g vc) \<tau> z
       = sides_of_rhs (hooks.hook_gen g bot0 s0d s0g vc) \<tau> z"
    "dep_aux \<tau> (dg_gen_of S g bot0 s0d s0g vc)

       = dep_aux \<tau> (hooks.hook_gen g bot0 s0d s0g vc)"
    unfolding vc c gen hgen by (simp_all add: Let_def key)
qed

text \<open>
  The form the solver's contract is stated in. \<^const>\<open>part_post_solution\<close> reads a
  system only through those three observations, so a post-solution of one
  generator is a post-solution of the other.
\<close>

lemma part_post_solution_dg_gen_of_iff:
  assumes wf: "wf_cfg g" and fin: "finite (calls g)"
  shows "part_post_solution (dg_gen_of S g bot0 s0d s0g) x sigma vars
           \<longleftrightarrow> part_post_solution (hooks.hook_gen g bot0 s0d s0g) x sigma vars"
proof -
  have "sides_of_rhs (dg_gen_of S g bot0 s0d s0g u) sigma
          = sides_of_rhs (hooks.hook_gen g bot0 s0d s0g u) sigma" for u
    by (rule ext) (rule dg_gen_of_obs_hook_gen(2)[OF wf fin])
  then show ?thesis
    by (simp add: dep\<^sub>L_def dep_def dg_gen_of_obs_hook_gen[OF wf fin])
qed

end

end

