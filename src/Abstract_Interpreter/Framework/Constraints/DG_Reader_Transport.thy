theory DG_Reader_Transport
  imports Routed_Context_Unit
begin

section \<open>Reading a whole equation system through a pair of readers\<close>

text \<open>
  A \<open>reader\<close> here maps one carrier to another --- typically an implementation
  value to the mathematical value it stands for. This theory proves, once, that
  reading commutes with everything an equation is built from: a node's value,
  the side effects it emits, and the unknowns it queries. The only properties
  any proof in the chain uses are that a reader preserves \<open>bot\<close> and \<open>(\<squnion>)\<close>, so
  they are the locale's two assumptions and the development is generic in both
  carriers. A concrete readback becomes a one-line interpretation.
\<close>

subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

lemma dep_aux_Side: "dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t"
  by (simp add: dep_aux_def)

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
     fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) =
       traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) \<and>
     (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) =
       sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k) \<and>
     dep_aux \<sigma>_st t_st =
       dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"

lemma dg_tree_st_commute_trav:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
   \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (traverse_rhs t_st \<sigma>_st) =
       traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_sides:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
   \<Longrightarrow> fun_of_dg_st_gen Floc Fglob (sides_of_rhs t_st \<sigma>_st k) =
       sides_of_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_dep:
  "dg_tree_st_commute \<sigma>_st t_st t_abs
   \<Longrightarrow> dep_aux \<sigma>_st t_st =
       dep_aux (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) t_abs"
  by (simp add: dg_tree_st_commute_def)

text \<open>
  The same relation between two \<^emph>\<open>programs\<close>, bundled with the
  well-formedness each side needs for the fold's observations to be well posed.
  Carrying \<^const>\<open>sp_wf\<close> inside the relation is what lets a list induction
  over two contribution lists keep it: a \<open>list_all2\<close> of this relation says every
  pair transports and every element runs its continuation once.
\<close>

definition dg_prog_st_commute ::
  "('u + 'k \<Rightarrow> ('a,'b) dg_state)
   \<Rightarrow> ('u, 'k, ('a,'b) dg_state, ('a,'b) dg_state) strategy_program
   \<Rightarrow> ('u, 'k, ('a2,'b2) dg_state, ('a2,'b2) dg_state) strategy_program \<Rightarrow> bool"
where
  "dg_prog_st_commute \<sigma>_st p_st p_abs \<longleftrightarrow>
     sp_wf p_st \<and> sp_wf p_abs
     \<and> dg_tree_st_commute \<sigma>_st (sp_compile p_st) (sp_compile p_abs)"

lemma dg_prog_st_commuteI:
  "\<lbrakk>sp_wf p_st; sp_wf p_abs;
    dg_tree_st_commute \<sigma>_st (sp_compile p_st) (sp_compile p_abs)\<rbrakk>
   \<Longrightarrow> dg_prog_st_commute \<sigma>_st p_st p_abs"
  by (simp add: dg_prog_st_commute_def)

lemma dg_prog_st_commute_wf_st: "dg_prog_st_commute \<sigma>_st p_st p_abs \<Longrightarrow> sp_wf p_st"
  by (simp add: dg_prog_st_commute_def)

lemma dg_prog_st_commute_wf_abs: "dg_prog_st_commute \<sigma>_st p_st p_abs \<Longrightarrow> sp_wf p_abs"
  by (simp add: dg_prog_st_commute_def)

lemma dg_prog_st_commute_tree:
  "dg_prog_st_commute \<sigma>_st p_st p_abs
   \<Longrightarrow> dg_tree_st_commute \<sigma>_st (sp_compile p_st) (sp_compile p_abs)"
  by (simp add: dg_prog_st_commute_def)

lemma dg_prog_list_wf_st:
  "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs
   \<Longrightarrow> \<forall>p \<in> set ps_st. sp_wf p"
  by (induction rule: list_all2_induct) (auto simp: dg_prog_st_commute_def)

lemma dg_prog_list_wf_abs:
  "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs
   \<Longrightarrow> \<forall>p \<in> set ps_abs. sp_wf p"
  by (induction rule: list_all2_induct) (auto simp: dg_prog_st_commute_def)

lemma dg_list_commute_trav:
  "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs
   \<Longrightarrow> list_all2
       (\<lambda>p_st p_abs. fun_of_dg_st_gen Floc Fglob (traverse_program p_st \<sigma>_st) =
         traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))
       ps_st ps_abs"
  by (erule list_all2_mono) (simp add: dg_prog_st_commute_def dg_tree_st_commute_def)

lemma dg_list_commute_travsides:
  "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs
   \<Longrightarrow> list_all2
       (\<lambda>p_st p_abs.
         sp_wf p_st \<and> sp_wf p_abs \<and>
         fun_of_dg_st_gen Floc Fglob (traverse_program p_st \<sigma>_st) =
           traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) \<and>
         (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_program p_st \<sigma>_st k) =
           sides_of_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k))
       ps_st ps_abs"
  by (erule list_all2_mono) (simp add: dg_prog_st_commute_def dg_tree_st_commute_def)

lemma dg_list_commute_dep:
  "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs
     \<Longrightarrow> list_all2 (\<lambda>p_st p_abs. dep_program \<sigma>_st p_st
                    = dep_program (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) p_abs) ps_st ps_abs"
  by (erule list_all2_mono) (simp add: dg_prog_st_commute_def dg_tree_st_commute_def)


subsubsection \<open>Classifier-parametric fold transport\<close>

lemma side_acc_dg_commute:
  assumes
    "list_all2
       (\<lambda>p_st p_abs.
         fun_of_dg_st_gen Floc Fglob (traverse_program p_st \<sigma>_st) =
           traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))
       ps_st ps_abs"
  shows
    "Floc (side_acc_dg acc_st \<sigma>_st ps_st) =
     side_acc_dg (Floc acc_st)
       (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) ps_abs"
  using assms
proof (induction ps_st ps_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons p_st ps_st p_abs ps_abs)
  have hl: "Floc (locals (traverse_program p_st \<sigma>_st))
              = locals (traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_gen_simps(1))
  have h: "Floc (acc_st \<squnion> locals (traverse_program p_st \<sigma>_st))
           = Floc acc_st \<squnion> locals (traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st))"
    by (simp add: Floc_sup hl)
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg_simps(2))
qed

lemma sides_side_rhs_fold_dg_commute:
  assumes
    "list_all2
       (\<lambda>p_st p_abs.
         sp_wf p_st \<and> sp_wf p_abs \<and>
         fun_of_dg_st_gen Floc Fglob (traverse_program p_st \<sigma>_st) =
           traverse_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) \<and>
         (\<forall>k. fun_of_dg_st_gen Floc Fglob (sides_of_program p_st \<sigma>_st k) =
           sides_of_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k))
       ps_st ps_abs"
  shows
    "fun_of_dg_st_gen Floc Fglob
       (sides_of_program (side_rhs_fold_dg acc_st ps_st) \<sigma>_st k) =
     sides_of_program (side_rhs_fold_dg acc_abs ps_abs)
       (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  using assms
proof (induction ps_st ps_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: bot_fun_def)
next
  case (Cons p_st ps_st p_abs ps_abs)
  have sd:
    "fun_of_dg_st_gen Floc Fglob (sides_of_program p_st \<sigma>_st k) =
     sides_of_program p_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih:
    "fun_of_dg_st_gen Floc Fglob
       (sides_of_program
           (side_rhs_fold_dg
             (acc_st \<squnion> locals (traverse_program p_st \<sigma>_st)) ps_st)
         \<sigma>_st k)
     = sides_of_program
           (side_rhs_fold_dg
             (acc_abs \<squnion>
               locals (traverse_program p_abs
                 (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)))
             ps_abs)
         (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  have wf: "sp_wf p_st" "sp_wf p_abs" using Cons.hyps(1) by simp_all
  show ?case
    by (simp add: sp_compile_bind sp_wfD[OF wf(1)] sp_wfD[OF wf(2)]
          fun_of_dg_st_gen_sup sd ih comp_def)
qed


subsubsection \<open>Routed heterogeneous CALL/COMB transport\<close>

text \<open>
  \<^const>\<open>routed_call_program\<close>/\<^const>\<open>routed_entry_seed_programs\<close>
  (\<^theory>\<open>Voblint_Framework.Routed_Call_Programs\<close>) are the canonical
  heterogeneous routing shape: parametric only in a routing
  function \<open>route\<close> and a seed-key injection \<open>seed_key\<close>, with the seed payload
  carried on the \<open>locals\<close> half so \<open>'D\<close>/\<open>'G\<close> stay independent. The two lemmas
  below feed this generic engine's \<open>Hcmb\<close>/\<open>Hextra\<close> obligations directly, so any
  context-sensitive analysis instantiating \<open>cmb\<close>/\<open>extra\<close> at those constants
  discharges CALL/COMB transport once here rather than re-deriving its own
  tree-commute reasoning.

  The specification's own enter and combine appear inside the routed tree as
  compiled sub-trees, so their transport hypotheses are themselves tree commutes
  -- and
  \<open>caller_cont\<close> needs no hypothesis at all, since
  \<^const>\<open>dg_spec_combine_transfer\<close> already runs it inside the combine sub-tree.
  Sequencing them is what \<open>dg_tree_st_commute_seqcomp\<close> does: a bind commutes when
  its head commutes and its continuation commutes at the head's answer.
\<close>

lemma dg_tree_st_commute_seqcomp:
  assumes head: "dg_tree_st_commute \<sigma>_st t_st t_abs"
    and tail: "dg_tree_st_commute \<sigma>_st (k_st (traverse_rhs t_st \<sigma>_st))
                 (k_abs (traverse_rhs t_abs (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st)))"
  shows "dg_tree_st_commute \<sigma>_st (sp_lift_tree t_st k_st) (sp_lift_tree t_abs k_abs)"
  using head tail
  unfolding dg_tree_st_commute_def
  by (simp add: fun_of_dg_st_gen_sup)

lemma dg_tree_st_commute_answer:
  "dg_tree_st_commute \<sigma>_st (Answer d) (Answer (fun_of_dg_st_gen Floc Fglob d))"
  by (simp add: dg_tree_st_commute_def)

lemma dg_tree_st_commute_read_local:
  "dg_tree_st_commute \<sigma>_st (QueryL x Answer) (QueryL x Answer)"
  by (simp add: dg_tree_st_commute_def)

text \<open>A local-only transfer compiles to a single answer, so its commute is the
  readback equation on the pure function alone -- no tree reasoning, and no
  hypothesis about the global half beyond the reader's own \<open>bot\<close> law.\<close>

lemma dg_tree_st_commute_local_transfer:
  assumes "Floc (f d) = F (Floc d)"
  shows "dg_tree_st_commute \<sigma>_st
           (sp_compile_with (\<lambda>x. DG x bot) (local_transfer f (mk_dg_man d gk)))
           (sp_compile_with (\<lambda>x. DG x bot) (local_transfer F (mk_dg_man (Floc d) gk)))"
  by (simp add: dg_tree_st_commute_def local_transfer_def mk_dg_man_def
      fun_of_dg_st_gen_def bot_dg_state_def assms Floc_bot Fglob_bot)

lemma dg_tree_st_commute_local_combine_transfer:
  assumes "Floc (f d de) = F (Floc d) (Floc de)"
  shows "dg_tree_st_commute \<sigma>_st
           (sp_compile_with (\<lambda>x. DG x bot) (local_combine_transfer f (mk_dg_man d gk) de))
           (sp_compile_with (\<lambda>x. DG x bot)
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
  shows "dg_tree_st_commute \<sigma>_st (Side y d t_st)
           (Side y (fun_of_dg_st_gen Floc Fglob d) t_abs)"
proof -
  have sides: "\<And>k. fun_of_dg_st_gen Floc Fglob (sides_of_rhs (Side y d t_st) \<sigma>_st k)
      = sides_of_rhs (Side y (fun_of_dg_st_gen Floc Fglob d) t_abs)
          (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
  proof -
    fix k
    show "fun_of_dg_st_gen Floc Fglob (sides_of_rhs (Side y d t_st) \<sigma>_st k)
        = sides_of_rhs (Side y (fun_of_dg_st_gen Floc Fglob d) t_abs)
            (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) k"
      using dg_tree_st_commute_sides[OF cont]
      by (cases "k = Inr y") (simp_all add: Let_def fun_of_dg_st_gen_sup)
  qed
  show ?thesis
    using cont sides unfolding dg_tree_st_commute_def
    by (simp add: dep_aux_Side)
qed

lemma dg_prog_st_commute_side_rhs_fold_dg:
  assumes la: "list_all2 (dg_prog_st_commute \<sigma>_st) ps_st ps_abs"
  shows "dg_prog_st_commute \<sigma>_st
           (side_rhs_fold_dg acc_st ps_st)
           (side_rhs_fold_dg (Floc acc_st) ps_abs)"
proof -
  have dep: "(\<Union>p\<in>set ps_st. dep_program \<sigma>_st p)
      = (\<Union>p\<in>set ps_abs. dep_program (fun_of_dg_st_gen Floc Fglob \<circ> \<sigma>_st) p)"
    using dg_list_commute_dep[OF la]
    by (induction rule: list_all2_induct) (auto simp: comp_def)
  show ?thesis
    unfolding dg_prog_st_commute_def dg_tree_st_commute_def
    by (simp add: sp_wf_side_rhs_fold_dg dg_prog_list_wf_st[OF la] dg_prog_list_wf_abs[OF la]
          traverse_side_rhs_fold_dg[OF dg_prog_list_wf_st[OF la]]
          traverse_side_rhs_fold_dg[OF dg_prog_list_wf_abs[OF la]] Fglob_bot
          dep_program_side_rhs_fold_dg_char[OF dg_prog_list_wf_st[OF la]]
          dep_program_side_rhs_fold_dg_char[OF dg_prog_list_wf_abs[OF la]] dep
          side_acc_dg_commute[OF dg_list_commute_trav[OF la]]
          sides_side_rhs_fold_dg_commute[OF dg_list_commute_travsides[OF la]])
qed

text \<open>
  What a compiled entry must satisfy to transport. Entry answers a list of
  caller-continuation/callee-entry pairs, which is not the solver's carrier, so the
  readback cannot be stated on the answer of a compiled tree the way the edge and
  combine transports are. It is stated on the program instead: run both entries
  against continuations that already agree on pairs read back componentwise, and the
  two trees agree. This observes the entry program exactly as \<^const>\<open>enter_runs\<close>
  does, and for the same reason.
\<close>

definition dg_enter_st_commute ::
  "('u + 'k \<Rightarrow> ('a,'b) dg_state)
   \<Rightarrow> ('u,'k,('a,'b) dg_state,'a enter_result list) strategy_program
   \<Rightarrow> ('u,'k,('a2,'b2) dg_state,'a2 enter_result list) strategy_program \<Rightarrow> bool"
where
  "dg_enter_st_commute \<sigma>_st T_st T_abs \<longleftrightarrow>
     (\<forall>K_st K_abs.
        (\<forall>ps. dg_tree_st_commute \<sigma>_st (K_st ps) (K_abs (map (map_prod Floc Floc) ps)))
          \<longrightarrow> dg_tree_st_commute \<sigma>_st (T_st K_st) (T_abs K_abs))"

lemma dg_enter_st_commuteD:
  assumes "dg_enter_st_commute \<sigma>_st T_st T_abs"
    and "\<And>ps. dg_tree_st_commute \<sigma>_st (K_st ps) (K_abs (map (map_prod Floc Floc) ps))"
  shows "dg_tree_st_commute \<sigma>_st (T_st K_st) (T_abs K_abs)"
  using assms unfolding dg_enter_st_commute_def by blast

text \<open>A Base-style entry answers its list outright, so its transport is the readback
  equation on that list alone.\<close>

lemma dg_enter_st_commute_local_enter_transfer:
  assumes "map (map_prod Floc Floc) (f d) = F (Floc d)"
  shows "dg_enter_st_commute \<sigma>_st
           (local_enter_transfer f (mk_dg_man d gk))
           (local_enter_transfer F (mk_dg_man (Floc d) gk))"
  unfolding dg_enter_st_commute_def local_enter_transfer_def sp_return_def
proof (intro allI impI)
  fix K_st K_abs
  assume K: "\<forall>ps. dg_tree_st_commute \<sigma>_st (K_st ps) (K_abs (map (map_prod Floc Floc) ps))"
  show "dg_tree_st_commute \<sigma>_st (K_st (f (man_local (mk_dg_man d gk))))
          (K_abs (F (man_local (mk_dg_man (Floc d) gk))))"
    using K[rule_format, of "f d"] assms by simp
qed

text \<open>
  One call alternative. The bottom branch is a plain combine against \<^const>\<open>bot\<close>, so
  it needs nothing beyond \<open>Hcomb\<close>; the other publishes the seed and reads the callee
  exit back, which is where \<open>Hroute\<close> is used. \<open>Hbot\<close> is what keeps the two carriers
  on the \<^emph>\<open>same\<close> branch: without it one could take the seed and the other not.
\<close>

lemma dg_prog_st_commute_routed_call_alternative_program:
  assumes wf_st: "dg_spec_wf S_st"
    and wf_abs: "dg_spec_wf S_abs"
    and Hcomb: "\<And>ci d de. dg_tree_st_commute \<sigma>_st
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st ci (mk_dg_man d (\<lambda>_. gk0)) de))
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)) (Floc de)))"
    and Hroute: "\<And>u c' d ca'. route_st u c' d ca' = route_abs u c' (Floc d) ca'"
    and Hbot: "\<And>d. is_bot_abs (Floc d) = is_bot_st d"
  shows "dg_prog_st_commute \<sigma>_st
           (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st ctx ca cc p alt)
           (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc p
              (map_prod Floc Floc alt))"
proof (rule dg_prog_st_commuteI)
  show "sp_wf (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st
                 ctx ca cc p alt)"
    by (rule sp_wf_routed_call_alternative_program[OF wf_st])
  show "sp_wf (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc p
                (map_prod Floc Floc alt))"
    by (rule sp_wf_routed_call_alternative_program[OF wf_abs])
  show "dg_tree_st_commute \<sigma>_st
          (sp_compile (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st
             ctx ca cc p alt))
          (sp_compile (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs
             ctx ca cc p (map_prod Floc Floc alt)))"
  proof (cases alt)
  case (Pair cont entry)
  show ?thesis
  proof (cases "is_bot_st entry")
    case True
    then have abs: "is_bot_abs (Floc entry)" by (simp add: Hbot)
    have cb: "dg_tree_st_commute \<sigma>_st
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st (call_info_of ca p) (mk_dg_man cont (\<lambda>_. gk0)) bot))
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs (call_info_of ca p)
              (mk_dg_man (Floc cont) (\<lambda>_. gk0)) bot))"
      using Hcomb[of "call_info_of ca p" cont bot] by (simp add: Floc_bot)
    show ?thesis
      unfolding Pair using cb by (simp add: True abs sp_compile_def)
  next
    case False
    then have abs: "\<not> is_bot_abs (Floc entry)" by (simp add: Hbot)
    have r: "route_abs cc ctx (Floc entry) ca = route_st cc ctx entry ca"
      by (rule Hroute[symmetric])
    have eq_st: "sp_compile (routed_call_alternative_program
        S_st gk0 seed_key route_st is_bot_st ctx ca cc p (cont, entry))
        = Side (seed_key (FunctionEntry p) (route_st cc ctx entry ca)) (DG entry bot)
            (QueryL (FunctionResult p, route_st cc ctx entry ca)
               (\<lambda>cs. sp_compile_with (\<lambda>x. DG x bot)
                  (dg_spec_combine_transfer S_st (call_info_of ca p)
                     (mk_dg_man cont (\<lambda>_. gk0)) (locals cs))))"
      using False by (simp add: sp_compile_def)
    have eq_abs: "sp_compile (routed_call_alternative_program S_abs gk0 seed_key route_abs
            is_bot_abs ctx ca cc p (Floc cont, Floc entry))
        = Side (seed_key (FunctionEntry p) (route_st cc ctx entry ca)) (DG (Floc entry) bot)
            (QueryL (FunctionResult p, route_st cc ctx entry ca)
               (\<lambda>cs. sp_compile_with (\<lambda>x. DG x bot)
                  (dg_spec_combine_transfer S_abs (call_info_of ca p)
                     (mk_dg_man (Floc cont) (\<lambda>_. gk0)) (locals cs))))"
      using abs by (simp add: r sp_compile_def)
    show ?thesis
      unfolding Pair map_prod_simp fst_conv snd_conv eq_st eq_abs
      by (rule dg_tree_st_commute_side_effect
            [where d = "DG entry bot", simplified fun_of_dg_st_gen_simps Fglob_bot],
          rule dg_tree_st_commute_QueryL,
          simp only: fun_of_dg_st_gen_simps,
          rule Hcomb)
  qed
  qed
qed

lemma dg_prog_st_commute_routed_callee_call_program:
  assumes wf_st: "dg_spec_wf S_st"
    and wf_abs: "dg_spec_wf S_abs"
    and Henter: "\<And>ci d. dg_enter_st_commute \<sigma>_st
        (enter\<^sup># S_st ci (mk_dg_man d (\<lambda>_. gk0)))
        (enter\<^sup># S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)))"
    and Hcomb: "\<And>ci d de. dg_tree_st_commute \<sigma>_st
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st ci (mk_dg_man d (\<lambda>_. gk0)) de))
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)) (Floc de)))"
    and Hroute: "\<And>u c' d ca'. route_st u c' d ca' = route_abs u c' (Floc d) ca'"
    and Hbot: "\<And>d. is_bot_abs (Floc d) = is_bot_st d"
  shows "dg_prog_st_commute \<sigma>_st
           (routed_callee_call_program S_st gk0 seed_key route_st is_bot_st ctx ca cc caller p)
           (routed_callee_call_program S_abs gk0 seed_key route_abs is_bot_abs
             ctx ca cc (Floc caller) p)"
  unfolding dg_prog_st_commute_def
proof (intro conjI sp_wf_routed_callee_call_program wf_st wf_abs)
  have alt: "\<And>x. dg_prog_st_commute \<sigma>_st
      (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st ctx ca cc p x)
      (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc p
         (map_prod Floc Floc x))"
    using wf_st wf_abs Hcomb Hroute Hbot
    by (rule dg_prog_st_commute_routed_call_alternative_program)
  show "dg_tree_st_commute \<sigma>_st
      (sp_compile (routed_callee_call_program S_st gk0 seed_key route_st is_bot_st
         ctx ca cc caller p))
      (sp_compile (routed_callee_call_program S_abs gk0 seed_key route_abs is_bot_abs
         ctx ca cc (Floc caller) p))"
    unfolding routed_callee_call_program_def sp_compile_bind
  proof (rule dg_enter_st_commuteD[OF Henter])
    fix ps :: "'a enter_result list"
    have la: "list_all2 (dg_prog_st_commute \<sigma>_st)
        (map (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st ctx ca cc p) ps)
        (map (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc p)
          (map (map_prod Floc Floc) ps))"
      by (simp add: list_all2_conv_all_nth alt)
    show "dg_tree_st_commute \<sigma>_st
        (sp_compile (side_rhs_fold_dg bot
          (map (routed_call_alternative_program S_st gk0 seed_key route_st is_bot_st ctx ca cc p)
            ps)))
        (sp_compile (side_rhs_fold_dg bot
          (map (routed_call_alternative_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc p)
            (map (map_prod Floc Floc) ps))))"
      using dg_prog_st_commute_side_rhs_fold_dg[OF la, where acc_st = bot]
      by (simp add: Floc_bot dg_prog_st_commute_def)
  qed
qed

text \<open>The call site itself: the resolver must answer the same targets on both
  carriers, which is the resolution-level twin of \<open>Hroute\<close>. At
  \<^const>\<open>static_resolve\<close> that premise is free, since the answer never reads the
  state.\<close>

lemma dg_prog_st_commute_routed_call_program:
  assumes wf_st: "dg_spec_wf S_st"
    and wf_abs: "dg_spec_wf S_abs"
    and Henter: "\<And>ci d. dg_enter_st_commute \<sigma>_st
        (enter\<^sup># S_st ci (mk_dg_man d (\<lambda>_. gk0)))
        (enter\<^sup># S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)))"
    and Hcomb: "\<And>ci d de. dg_tree_st_commute \<sigma>_st
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_st ci (mk_dg_man d (\<lambda>_. gk0)) de))
        (sp_compile_with (\<lambda>x. DG x bot)
           (dg_spec_combine_transfer S_abs ci (mk_dg_man (Floc d) (\<lambda>_. gk0)) (Floc de)))"
    and Hroute: "\<And>u c' d ca'. route_st u c' d ca' = route_abs u c' (Floc d) ca'"
    and Hbot: "\<And>d. is_bot_abs (Floc d) = is_bot_st d"
    and Hresolve: "\<And>w cc' ca' d. resolve_st w cc' ca' d = resolve_abs w cc' ca' (Floc d)"
  shows "dg_prog_st_commute \<sigma>_st
           (routed_call_program S_st gk0 seed_key resolve_st is_bot_st route_st ctx ca cc v)
           (routed_call_program S_abs gk0 seed_key resolve_abs is_bot_abs route_abs ctx ca cc v)"
  unfolding dg_prog_st_commute_def
proof (intro conjI sp_wf_routed_call_program wf_st wf_abs)
  let ?caller = "locals (\<sigma>_st (Inl (cc, ctx)))"
  have at: "\<And>p. dg_prog_st_commute \<sigma>_st
      (routed_callee_call_program S_st gk0 seed_key route_st is_bot_st ctx ca cc ?caller p)
      (routed_callee_call_program S_abs gk0 seed_key route_abs is_bot_abs ctx ca cc
         (Floc ?caller) p)"
    using wf_st wf_abs Henter Hcomb Hroute Hbot
    by (rule dg_prog_st_commute_routed_callee_call_program)
  have la: "list_all2 (dg_prog_st_commute \<sigma>_st)
      (map (routed_callee_call_program S_st gk0 seed_key route_st is_bot_st ctx ca cc ?caller)
        (resolve_st v cc ca ?caller))
      (map
        (routed_callee_call_program S_abs gk0 seed_key route_abs is_bot_abs
          ctx ca cc (Floc ?caller))
        (resolve_st v cc ca ?caller))"
    by (simp add: list_all2_conv_all_nth at)
  have body: "dg_tree_st_commute \<sigma>_st
      (sp_compile (side_rhs_fold_dg bot
        (map (routed_callee_call_program S_st gk0 seed_key route_st is_bot_st ctx ca cc ?caller)
          (resolve_st v cc ca ?caller))))
      (sp_compile (side_rhs_fold_dg bot
        (map
          (routed_callee_call_program S_abs gk0 seed_key route_abs is_bot_abs
            ctx ca cc (Floc ?caller))
          (resolve_st v cc ca ?caller))))"
    using dg_prog_st_commute_side_rhs_fold_dg[OF la, where acc_st = bot]
    by (simp add: Floc_bot dg_prog_st_commute_def)
  show "dg_tree_st_commute \<sigma>_st
      (sp_compile (routed_call_program S_st gk0 seed_key resolve_st is_bot_st route_st ctx ca cc v))
      (sp_compile (routed_call_program S_abs gk0 seed_key resolve_abs is_bot_abs route_abs
         ctx ca cc v))"
    unfolding routed_call_program_def sp_compile_bind
    using body
    by (simp add: dg_tree_st_commute_def sp_wf_observes Hresolve[symmetric] comp_def)
qed

lemma dg_prog_st_commute_routed_entry_seed_programs:
  shows "list_all2 (dg_prog_st_commute \<sigma>_st)
           (routed_entry_seed_programs seed_key route_st ctx v)
           (routed_entry_seed_programs seed_key route_abs ctx v)"
  by (cases v)
     (auto simp: routed_entry_seed_programs_def dg_prog_st_commute_def
        dg_tree_st_commute_def sp_compile_def Fglob_bot)

end
end

