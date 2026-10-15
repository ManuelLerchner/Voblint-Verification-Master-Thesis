theory DG_Reader_Transport
  imports Routed_Context
begin

section \<open>Reading a whole equation system through a pair of readers\<close>

text \<open>
  A \<open>reader\<close> here maps one carrier to another --- typically an implementation
  value to the mathematical value it stands for. This theory proves, once, that
  reading commutes with everything an equation is built from: a node's value,
  the side effects it emits, and the unknowns it queries. The only properties
  any proof in the chain uses are that a reader preserves \<open>bot\<close> and \<open>(\<squnion>)\<close>, so
  they are the locale's two assumptions and the development is generic in both
  carriers. A concrete reader becomes a one-line interpretation.
\<close>

subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

subsection \<open>Carrier-generic whole-CFG commute\<close>

text \<open>
  The commute facts below only ever use that a reader preserves \<open>bot\<close> and \<open>(\<squnion>)\<close>; no
  proof in the chain inspects \<open>default_st_to_fun\<close> or \<open>gabs_state\<close> itself.
  \<open>dg_reader_commute_gen\<close> factors that out: a pair of local/global readers \<open>Floc\<close>/\<open>Fglob\<close>
  satisfying those two laws, from which every whole-tree and whole-equation-system commute
  fact in this chain is proved once.
\<close>

text \<open>
  Reading a pair componentwise is the datatype's own map,
  \<^const>\<open>map_dg_state\<close>; its selector equations join the simplifier.
\<close>

declare dg_state.map_sel [simp]

text \<open>
  The locale assumes only that both readers preserve \<open>bot\<close> and joins;
  monotonicity and the commutation with \<open>map_dg_state\<close> follow.
\<close>

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

lemma map_dg_state_bot [simp]:
  "map_dg_state Floc Fglob (bot :: ('a,'b) dg_state) = bot"
  by (simp add: bot_dg_state_def Floc_bot Fglob_bot)

lemma map_dg_state_sup:
  "map_dg_state Floc Fglob (a \<squnion> b :: ('a,'b) dg_state)
     = map_dg_state Floc Fglob a \<squnion> map_dg_state Floc Fglob b"
  by (simp add: sup_dg_state_def Floc_sup Fglob_sup)

subsubsection \<open>Bundled per-tree transport relation\<close>

text \<open>
  \<open>dg_tree_st_commute\<close> bundles the three facts one strategy tree must
  transport: its value, its side effects per key, and its dependencies.
\<close>

definition dg_tree_st_commute ::
  "('u + 'k \<Rightarrow> ('a,'b) dg_state) \<Rightarrow> ('u, 'k, ('a,'b) dg_state) strategy_tree
    \<Rightarrow> ('u, 'k, ('a2,'b2) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute \<sigma>_st t_st t_abs \<longleftrightarrow>
     map_dg_state Floc Fglob (traverse_rhs t_st \<sigma>_st) =
       traverse_rhs t_abs (map_dg_state Floc Fglob \<circ> \<sigma>_st) \<and>
     (\<forall>k. map_dg_state Floc Fglob (sides_of_rhs t_st \<sigma>_st k) =
       sides_of_rhs t_abs (map_dg_state Floc Fglob \<circ> \<sigma>_st) k) \<and>
     dep_aux \<sigma>_st t_st =
       dep_aux (map_dg_state Floc Fglob \<circ> \<sigma>_st) t_abs"

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

subsubsection \<open>Routed heterogeneous CALL/COMB transport\<close>

text \<open>
  \<^const>\<open>routed_call_program\<close>/\<^const>\<open>routed_entry_seed_programs\<close>
  (\<^theory>\<open>Voblint_Framework.Routed_Call_Programs\<close>) are the canonical
  heterogeneous routing shape: parametric only in a routing
  function \<open>route\<close> and a seed-key injection \<open>seed\<close>, with the seed payload
  carried on the \<open>dg_local\<close> half so \<open>'D\<close>/\<open>'G\<close> stay independent. The lemmas
  below transport \<^const>\<open>routed_call_program\<close>, so any context-sensitive analysis
  instantiating \<open>cmb\<close> at that constant discharges CALL/COMB transport once here
  rather than re-deriving its own tree-commute reasoning.

  The specification's own enter and combine appear inside the routed tree as
  compiled sub-trees, so their transport hypotheses are themselves tree commutes.
  Sequencing them is what \<open>dg_tree_st_commute_seqcomp\<close> does: a bind commutes when
  its head commutes and its continuation commutes at the head's answer.
\<close>

lemma dg_tree_st_commute_seqcomp:
  assumes head: "dg_tree_st_commute \<sigma>_st t_st t_abs"
    and tail: "dg_tree_st_commute \<sigma>_st (k_st (traverse_rhs t_st \<sigma>_st))
                 (k_abs (traverse_rhs t_abs (map_dg_state Floc Fglob \<circ> \<sigma>_st)))"
  shows "dg_tree_st_commute \<sigma>_st (sp_lift_tree t_st k_st) (sp_lift_tree t_abs k_abs)"
  using head tail
  unfolding dg_tree_st_commute_def
  by (simp add: map_dg_state_sup)

lemma dg_tree_st_commute_answer:
  "dg_tree_st_commute \<sigma>_st (Answer d) (Answer (map_dg_state Floc Fglob d))"
  by (simp add: dg_tree_st_commute_def)

text \<open>A local-only transfer compiles to a single answer, so its commute is the
  reader equation on the pure function alone -- no tree reasoning, and no
  hypothesis about the global half beyond the reader's own \<open>bot\<close> law.\<close>

lemma dg_tree_st_commute_local_transfer:
  assumes "Floc (f d) = F (Floc d)"
  shows "dg_tree_st_commute \<sigma>_st
           (sp_compile_with (\<lambda>x. DG x bot) (local_transfer f (mk_dg_man d gk)))
           (sp_compile_with (\<lambda>x. DG x bot) (local_transfer F (mk_dg_man (Floc d) gk)))"
  by (simp add: dg_tree_st_commute_def local_transfer_def mk_dg_man_def
      dg_state.map_sel bot_dg_state_def assms Floc_bot Fglob_bot)

text \<open>
  What a compiled entry must satisfy to transport. Entry answers a list of
  caller-continuation/callee-entry pairs, which is not the solver's carrier, so the
  reader equation cannot be stated on the answer of a compiled tree the way the edge and
  combine transports are. It is stated on the program instead: run both entries
  against continuations that already agree on pairs mapped componentwise by the readers, and the
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

end
end
