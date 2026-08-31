theory DG_Soundness
  imports DG_Unit_Spec DG_Keyed_Generator
begin

section \<open>Native heterogeneous soundness\<close>

text \<open>
  Collecting soundness stated directly over an analysis's two domains \<open>D\<close> and
  \<open>G\<close>.  The analysis supplies \<open>gammaDG\<close>, the joint meaning of a per-point
  Answer and the shared Side fact.  Independent analyses use the intersection
  \<open>gamma_dg d g = [[d]] Int [[g]]\<close>; the homogeneous unit analysis uses
  \<open>gamma_unit d g = [[d Sup g]]\<close> because its transfer merges the slots.

  The locale \<open>sound_dg_spec\<close> assumes only monotonicity of \<open>gammaDG\<close> and
  semantic soundness of the analysis's edge and combine operations.  It derives
  the structural post-fixpoint from the heterogeneous generator, then applies
  the collecting-semantics post-fixpoint theorem directly.  No homogeneous
  equation system or representation transport appears in this proof.
\<close>

subsection \<open>Fold bounds\<close>

text \<open>
  Order bounds for \<open>side_rhs_fold_dg\<close>/\<open>side_acc_dg\<close>: the accumulator and every
  folded Answer are below the folded result, and every tree's side
  contribution is below the fold's.
\<close>

lemma side_acc_dg_ge_acc:
  "acc \<le> side_acc_dg acc sigma ts"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> locals (traverse_rhs t sigma)" by simp
  also have "... \<le> side_acc_dg
      (acc \<squnion> locals (traverse_rhs t sigma)) sigma ts"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma locals_traverse_le_side_acc_dg:
  assumes "t \<in> set ts"
  shows "locals (traverse_rhs t sigma) \<le> side_acc_dg acc sigma ts"
using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    have "locals (traverse_rhs t sigma)
        \<le> acc \<squnion> locals (traverse_rhs t' sigma)"
      using True by simp
    also have "... \<le> side_acc_dg
        (acc \<squnion> locals (traverse_rhs t' sigma)) sigma ts"
      by (rule side_acc_dg_ge_acc)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma sides_le_side_rhs_fold_dg:
  assumes "t \<in> set ts"
  shows "sides_of_rhs t sigma k
    \<le> sides_of_rhs (side_rhs_fold_dg acc ts) sigma k"
using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    then show ?thesis
      by (simp add: sides_of_rhs_seqcomp_at)
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "sides_of_rhs t sigma k
        \<le> sides_of_rhs
          (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts) sigma k"
      by (rule Cons.IH)
    also have "... \<le> sides_of_rhs t' sigma k \<squnion>
        sides_of_rhs
          (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts) sigma k"
      by simp
    also have "... =
        sides_of_rhs (side_rhs_fold_dg acc (t' # ts)) sigma k"
      by (simp add: sides_of_rhs_seqcomp_at)
    finally show ?thesis .
  qed
qed

subsection \<open>The intersection concretization\<close>

definition gamma_dg ::
  "'d::sound_domain abs_state \<Rightarrow> 'g::sound_domain abs_state \<Rightarrow> store set"
where
  "gamma_dg d g = \<lbrakk>d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"

lemma gamma_dg_le_D: "gamma_dg d g \<subseteq> \<lbrakk>d\<rbrakk>"
  unfolding gamma_dg_def by blast

lemma gamma_dg_le_G: "gamma_dg d g \<subseteq> \<lbrakk>g\<rbrakk>"
  unfolding gamma_dg_def by blast

lemma gamma_dg_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_dg d g \<subseteq> gamma_dg d' g'"
  using gamma_state_mono[OF assms(1)] gamma_state_mono[OF assms(2)]
  unfolding gamma_dg_def by blast

(* Pointwise duals of gamma_dg_le_D / gamma_dg_le_G, for call sites that need
   the per-element fact rather than the set inclusion. *)
lemma gamma_dgD1 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>"
  using gamma_dg_le_D by blast

lemma gamma_dgD2 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>g\<rbrakk>"
  using gamma_dg_le_G by blast



text \<open>
  \<open>vars_cover g vars\<close> bundles the one recurring obligation every
  post-solution soundness theorem in this development needs: \<open>vars\<close> contains
  the CFG entry, every \<open>intra\<close> edge's target, and every call's callee entry
  and continuation. The four components are one semantic fact -- ``\<open>vars\<close> is
  a cover of \<open>g\<close>'s reachable nodes'' -- not four independent assumptions, so
  callers state and discharge it as a single premise instead of four
  positional ones. Global (not locale-local): every analysis instance and
  the executable pipeline cite it under the same name.
\<close>
definition vars_cover :: "cfg \<Rightarrow> (cfg_node \<times> unit) set \<Rightarrow> bool" where
  "vars_cover g vars \<longleftrightarrow>
     (cfg_entry g, ()) \<in> vars
   \<and> (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow> (v, ()) \<in> vars)
   \<and> (\<forall>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
        \<longrightarrow> (FunctionEntry q, ()) \<in> vars)
   \<and> (\<forall>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
        \<longrightarrow> (k, ()) \<in> vars)"

lemma vars_coverI [intro]:
  assumes "(cfg_entry g, ()) \<in> vars"
    and "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (k, ()) \<in> vars"
  shows "vars_cover g vars"
  unfolding vars_cover_def using assms by blast

lemma vars_cover_entryD [dest]: "vars_cover g vars \<Longrightarrow> (cfg_entry g, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_edgeD [dest]:
  "vars_cover g vars \<Longrightarrow> (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_enterD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

lemma vars_cover_combineD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (k, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

subsection \<open>Analysis-parametric heterogeneous soundness\<close>

locale sound_dg_spec =
  fixes S :: "('D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG d g) \<subseteq>
        (case dg_spec_step S a d g of
           (g', d') \<Rightarrow> gammaDG d' g')"
    and caller_cont_sound:
      "s \<in> gammaDG dc g \<Longrightarrow> s \<in> gammaDG (dgs_caller_cont S ci dc g) g"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dcont g; t \<in> gammaDG de g\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t \<in>
          (case dgs_combine S ci dcont de g of
             (g', d') \<Rightarrow> gammaDG d' g')"
    and enter_sound:
      "s \<in> gammaDG dc g \<Longrightarrow>
        call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
          (case dgs_enter S ci dc g of
             (g', d') \<Rightarrow> gammaDG d' g')"
begin

text \<open>Fst/snd-shaped restatements of the three per-step soundness assumptions,
  so a caller comparing against dg_D/dg_G (which are always applied via fst/snd)
  does not need to obtain the case-split pair and its equation just to unpack a
  case-of-tuple result each time.\<close>
lemma step_sound_fs:
  "edge_collect a (gammaDG d g)
     \<subseteq> gammaDG (snd (dg_spec_step S a d g)) (fst (dg_spec_step S a d g))"
  using step_sound by (simp add: case_prod_beta)

text \<open>
  The bridge between the two halves of the call protocol.  \<^const>\<open>dgs_combine\<close> is
  stated against the caller \<^emph>\<open>continuation\<close>, which conceptually comes out of
  \<open>enter\<close>; a right-hand side that reads the caller unknown again at return
  reconstructs it by applying \<^const>\<open>dgs_caller_cont\<close> there.  This lemma is what
  licenses that reconstruction, and it is the only place the two are composed --
  \<open>combine_sound\<close> itself never mentions the raw pre-call caller state.

  \<open>caller_cont_sound\<close> says the continuation may forget information, but may not
  exclude any concrete caller state represented before the call.  That is an
  inclusion between concretizations, not a claim about the abstract order: it does
  not force \<open>dc \<le> dgs_caller_cont S ci dc g\<close> unless \<open>gammaDG\<close> happens to reflect
  that order, and two incomparable abstract elements can satisfy it.

  The two global arguments are deliberately separate.  \<open>caller_cont\<close> is applied to
  the global state \<open>enter\<close> would have seen, \<open>combine\<close> to the one in scope at
  return, and \<open>g1 \<le> g2\<close> is what relates them.  On the routed path both come from
  the same \<open>read_global\<close> key within one traversal, so equality holds there and
  \<open>order_refl\<close> discharges the side condition; stating the ordered form keeps the
  lemma usable if a caller ever reads the two at genuinely different points.
\<close>
lemma combine_sound_at_call:
  assumes sv: "s \<in> gammaDG dc g1" and tv: "t \<in> gammaDG de g2"
    and gg: "g1 \<le> g2"
  shows "combine_collect gs (ci_dst ci) s t \<in>
           (case dgs_combine S ci (dgs_caller_cont S ci dc g1) de g2 of
              (g', d') \<Rightarrow> gammaDG d' g')"
proof -
  have "s \<in> gammaDG (dgs_caller_cont S ci dc g1) g1"
    by (rule caller_cont_sound[OF sv])
  then have "s \<in> gammaDG (dgs_caller_cont S ci dc g1) g2"
    using gammaDG_mono[OF order_refl gg] by blast
  from combine_sound[OF this tv] show ?thesis .
qed

lemma combine_sound_at_call_fs:
  assumes sv: "s \<in> gammaDG dc g1" and tv: "t \<in> gammaDG de g2"
    and gg: "g1 \<le> g2"
  shows "combine_collect gs (ci_dst ci) s t
           \<in> gammaDG (snd (dgs_combine S ci (dgs_caller_cont S ci dc g1) de g2))
                      (fst (dgs_combine S ci (dgs_caller_cont S ci dc g1) de g2))"
  using combine_sound_at_call[OF sv tv gg] by (simp add: case_prod_beta)

lemma enter_sound_fs:
  assumes "s \<in> gammaDG dc g"
  shows "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
           gammaDG (snd (dgs_enter S ci dc g)) (fst (dgs_enter S ci dc g))"
  using enter_sound[OF assms] by (simp add: case_prod_beta)

lemma combine_sound_fs:
  assumes "s \<in> gammaDG dcont g" and "t \<in> gammaDG de g"
  shows "combine_collect gs (ci_dst ci) s t \<in>
           gammaDG (snd (dgs_combine S ci dcont de g)) (fst (dgs_combine S ci dcont de g))"
  using combine_sound[OF assms] by (simp add: case_prod_beta)

text \<open>The cross-validating pull family's own combine, at the resolved shape: the call
  site is handed the continuation node and folds one tree per procedure the resolver
  answers with. \<^const>\<open>static_targets\<close> answers from the CFG, so this family keeps
  exactly the trees it had.\<close>

definition dg_cmb_at ::
  "unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pname
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_cmb_at ctx ca cc p =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree S (call_info_of ca p) cc (FunctionResult p)))"

definition dg_cmb ::
  "cfg \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
        ('D, 'G) dg_state) strategy_tree"
where
  "dg_cmb g route ctx ca cc v =
     side_rhs_fold_dg bot (map (dg_cmb_at ctx ca cc) (static_targets g v cc ca))"

text \<open>The callee name is not otherwise available at an entry-indexed enumeration
  site, and \<^const>\<open>dgs_enter\<close> never reads \<open>ci_callee\<close> (only \<open>ci_formals\<close>/\<open>ci_args\<close>),
  so \<open>v\<close>'s own procedure -- when \<open>v\<close> is the \<open>FunctionEntry\<close> \<^const>\<open>entry_call_list\<close>
  indexes by -- is as good a witness as any; the \<open>undefined\<close> branch is unreachable
  since \<^const>\<open>entry_call_list\<close> is only ever nonempty at a \<open>FunctionEntry\<close> node.\<close>

definition dg_enter ::
  "unit \<Rightarrow> call_info \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_enter ctx ci cl =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_edge_tree (dgs_enter S ci) cl))"

definition dg_extra ::
  "cfg \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree list"
where
  "dg_extra g route ctx v =
     map (\<lambda>(cl, ca). dg_enter ctx
            (call_info_of ca (case v of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined)) cl)
         (entry_call_list g v)"

definition dg_gen ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit, unit,
        ('D, 'G) dg_state) eqsT"
where
  "dg_gen g bot0 s0d s0g =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. ())
       (\<lambda>_ _ _ _. ()) (dg_cmb g) (dg_extra g) g S bot0 s0d s0g"

definition dg_D ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> 'D"
where
  "dg_D sigma v = locals (sigma (Inl (v, ())))"

definition dg_G ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> 'G"
where
  "dg_G sigma = globs (sigma (Inr ()))"

definition dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_gamma sigma v = gammaDG (dg_D sigma v) (dg_G sigma)"

(* Dest/intro pair for the dg_gamma/gammaDG bridge, cited at the postfix
   soundness call sites below instead of re-unfolding dg_gamma_def at each. *)
lemma dg_gammaD [dest]: "s \<in> dg_gamma sigma v \<Longrightarrow> s \<in> gammaDG (dg_D sigma v) (dg_G sigma)"
  unfolding dg_gamma_def by simp

lemma dg_gammaI [intro]: "s \<in> gammaDG (dg_D sigma v) (dg_G sigma) \<Longrightarrow> s \<in> dg_gamma sigma v"
  unfolding dg_gamma_def by simp

definition dg_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit,
      ('D, 'G) dg_state) strategy_tree list"
where
  "dg_trees g v =
     map (\<lambda>(src, a). apply_dg_spec_at S a src ())
       (intra_predecessor_addr_list g v ())
     @ map (\<lambda>(cc, ca). dg_cmb g (\<lambda>_ _ _ _. ()) () ca cc v)
       (call_site_list g v)
     @ dg_extra g (\<lambda>_ _ _ _. ()) () v"

definition dg_acc ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> pp
   \<Rightarrow> 'D"
where
  "dg_acc g bot0 s0d v =
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_dg_gen:
  "eq (dg_gen g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (dg_acc g bot0 s0d v)
     sigma (dg_trees g v)) bot"
  unfolding dg_gen_def dg_trees_def dg_acc_def
  by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)

lemma sides_fold_le_dg_gen:
  "sides_of_rhs
      (side_rhs_fold_dg (dg_acc g bot0 s0d v)
        (dg_trees g v)) sigma k
   \<le> sides_of_rhs (dg_gen g bot0 s0d s0g (v, ())) sigma k"
  unfolding dg_gen_def dg_trees_def dg_acc_def
    side_cfg_T_eff_keyed_seed_dg_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

text \<open>
  \<open>dg_postfix\<close> is the DG-specific instance of a semantic post-fixpoint:
  \<open>sigma\<close> dominates the seed on both projections, and every specification
  transfer --- \<open>dg_spec_step\<close> on an intra edge, \<open>dgs_enter\<close> on a call entry,
  \<open>dgs_combine\<close> on a call return --- is bounded on both projections by
  \<open>sigma\<close> at its target. The eight conjuncts are the two seed bounds plus a
  D/G pair for each of the three transfer kinds; each has its own named
  projection lemma below (\<open>dg_postfix_entryD\<close>, \<open>dg_postfix_edgeD\<close>, ...) so
  callers never navigate the conjunction positionally.
\<close>
definition dg_postfix ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        ('D, 'G) dg_state)
   \<Rightarrow> bool"
where
  "dg_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_D sigma (cfg_entry g) \<and>
     s0g \<le> dg_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
        snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_D sigma v) \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
        fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_G sigma) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        snd (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
          \<le> dg_D sigma (FunctionEntry p)) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        fst (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
          \<le> dg_G sigma) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        snd (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
          (dg_G sigma)) \<le> dg_D sigma k) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        fst (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
          (dg_G sigma)) \<le> dg_G sigma)"

(* Stable, order-independent projections out of dg_postfix's 8-way conjunction; each
   pays the conjunct-navigation cost once here instead of at every call site via a
   positional [THEN conjunct2, THEN conjunct2, ...] chain that would silently misdirect
   if a conjunct were ever inserted or reordered. *)
lemma dg_postfix_entryD [dest]:
  assumes pf: "dg_postfix g s0d s0g sigma"
  shows "s0d \<le> dg_D sigma (cfg_entry g)"
  using pf unfolding dg_postfix_def by blast

lemma dg_postfix_entryG:
  assumes pf: "dg_postfix g s0d s0g sigma"
  shows "s0g \<le> dg_G sigma"
  using pf unfolding dg_postfix_def by blast

lemma dg_postfix_edgeD [dest]:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
  shows "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_D sigma w"
  using pf edge unfolding dg_postfix_def by auto

lemma dg_postfix_edgeG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
  shows "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
  using dg_postfix_def edge pf by fastforce

lemma dg_postfix_enterD [dest]:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "snd (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma))
           \<le> dg_D sigma (FunctionEntry p)"
  using pf ce unfolding dg_postfix_def by fastforce

lemma dg_postfix_enterG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "fst (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma))
           \<le> dg_G sigma"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_postfix_combineD [dest]:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "snd (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma))
           \<le> dg_D sigma k"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_postfix_combineG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "fst (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma))
           \<le> dg_G sigma"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_edge_tree_local:
  "locals (traverse_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma)
   = snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (subst traverse_intra_keyed)
    (simp add: traverse_dg_edge_tree)

lemma dg_edge_tree_global:
  "globs (sides_of_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma (Inr ()))
   = fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_edge_tree_Inr
      sum.map_comp o_def)

lemma dg_combine_tree_local:
  "locals (traverse_rhs (dg_cmb_at () (CallEdge dst fs as) cc p) sigma)
   = snd (dgs_combine S (call_info_of (CallEdge dst fs as) p)
            (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma))
            (dg_D sigma (FunctionResult p)) (dg_G sigma))"
  unfolding dg_cmb_at_def dg_spec_combine_tree_def dg_D_def dg_G_def
  apply (subst traverse_intra_keyed)
  apply (simp add: traverse_dg_combine_tree)
  done

lemma dg_combine_tree_global:
  "globs (sides_of_rhs (dg_cmb_at () (CallEdge dst fs as) cc p) sigma (Inr ()))
   = fst (dgs_combine S (call_info_of (CallEdge dst fs as) p)
            (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma cc) (dg_G sigma))
            (dg_D sigma (FunctionResult p)) (dg_G sigma))"
  unfolding dg_cmb_at_def dg_spec_combine_tree_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_combine_tree_Inr
      sum.map_comp o_def)

lemma dg_enter_tree_local:
  "locals (traverse_rhs (dg_enter () ci cl) sigma)
   = snd (dgs_enter S ci (dg_D sigma cl) (dg_G sigma))"
  unfolding dg_enter_def dg_D_def dg_G_def
  by (subst traverse_intra_keyed)
    (simp add: traverse_dg_edge_tree)

lemma dg_enter_tree_global:
  "globs (sides_of_rhs (dg_enter () ci cl) sigma (Inr ()))
   = fst (dgs_enter S ci (dg_D sigma cl) (dg_G sigma))"
  unfolding dg_enter_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_edge_tree_Inr
      sum.map_comp o_def)

theorem dg_post_solution_postfix:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g)
        x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
  shows "dg_postfix g s0d s0g sigma"
proof -
  note cover_entry = vars_cover_entryD[OF cover]
    and cover_edge = vars_cover_edgeD[OF cover]
    and cover_enter = vars_cover_enterD[OF cover]
    and cover_combine = vars_cover_combineD[OF cover]
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (dg_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using se_constraint_holds_local[OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (dg_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using se_constraint_holds_sides[OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast

  have entryD: "s0d \<le> dg_D sigma (cfg_entry g)"
  proof -
    have "s0d \<le> dg_acc g bot0 s0d (cfg_entry g)"
      by (simp add: dg_acc_def)
    also have "... \<le> side_acc_dg
        (dg_acc g bot0 s0d (cfg_entry g)) sigma
        (dg_trees g (cfg_entry g))"
      by (rule side_acc_dg_ge_acc)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g)
          (cfg_entry g, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma (cfg_entry g)"
      using eq_le[OF cover_entry]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show ?thesis .
  qed

  have entryG: "s0g \<le> dg_G sigma"
  proof -
    have "DG bot s0g \<le>
       sides_of_rhs
         (dg_gen g bot0 s0d s0g (cfg_entry g, ()))
         sigma (Inr ())"
      unfolding dg_gen_def side_cfg_T_eff_keyed_seed_dg_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: dg_G_def less_eq_dg_state_def)
  qed

  have edge_tree_mem:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
    have "(u, a) \<in> set (intra_predecessor_list g v)"
      using edge
      by (simp add: set_intra_predecessor_list[OF finI] intra_predecessors_def)
    then show "map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
      by (force simp: dg_trees_def intra_predecessor_addr_list_def
          apply_dg_spec_relabel_as_at image_iff)
  qed

  have edgeD:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma v"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
    have "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d v)
          sigma (dg_trees g v)"
      using locals_traverse_le_side_acc_dg[OF edge_tree_mem[OF edge]]
      by (simp add: dg_edge_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (v, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma v"
      using eq_le[OF cover_edge[OF edge]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma v" .
  qed

  have edgeG:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
    have "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d v)
            (dg_trees g v)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF edge_tree_mem[OF edge], where k = "Inr ()"]
      by (simp add: dg_edge_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (v, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_edge[OF edge], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma" .
  qed

  have enter_tree_mem:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      dg_enter () (call_info_of (CallEdge dst fs as) p) c \<in> set (dg_trees g (FunctionEntry p))"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "(c, CallEdge dst fs as) \<in> set (entry_call_list g (FunctionEntry p))"
      using ce by (auto simp: set_entry_call_list[OF finC] entry_calls_iff)
    then show "dg_enter () (call_info_of (CallEdge dst fs as) p) c
        \<in> set (dg_trees g (FunctionEntry p))"
      by (force simp: dg_trees_def dg_extra_def image_iff)
  qed

  have enterD:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      snd (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> dg_D sigma (FunctionEntry p)"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "snd (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d (FunctionEntry p))
          sigma (dg_trees g (FunctionEntry p))"
      using locals_traverse_le_side_acc_dg[OF enter_tree_mem[OF ce]]
      by (simp add: dg_enter_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (FunctionEntry p, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma (FunctionEntry p)"
      using eq_le[OF cover_enter[OF ce]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> dg_D sigma (FunctionEntry p)" .
  qed

  have enterG:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      fst (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> dg_G sigma"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "fst (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d (FunctionEntry p))
            (dg_trees g (FunctionEntry p))) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF enter_tree_mem[OF ce], where k = "Inr ()"]
      by (simp add: dg_enter_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (FunctionEntry p, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_enter[OF ce], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dgs_enter S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma))
        \<le> dg_G sigma" .
  qed

  have combine_tree_mem:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      dg_cmb g (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c k \<in> set (dg_trees g k)"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "(c, CallEdge dst fs as) \<in> set (call_site_list g k)"
      using ce by (auto simp: set_call_site_list[OF finC])
    then show "dg_cmb g (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c k
        \<in> set (dg_trees g k)"
      by (force simp: dg_trees_def)
  qed

  text \<open>Each resolved callee contributes one tree to the call site's own fold,
    so a call edge reaches the generated equation in two hops: into the site's
    target fold, then into the node's tree list.\<close>

  have combine_at_mem:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      dg_cmb_at () (CallEdge dst fs as) c p
        \<in> set (map (dg_cmb_at () (CallEdge dst fs as) c)
                 (static_targets g k c (CallEdge dst fs as)))"
    by (simp add: static_targets_iff[OF finC])

  have combineD:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      snd (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_D sigma k"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "snd (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
          (dg_G sigma))
        = locals (traverse_rhs (dg_cmb_at () (CallEdge dst fs as) c p) sigma)"
      by (simp add: dg_combine_tree_local)
    also have "... \<le> locals (traverse_rhs
        (dg_cmb g (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c k) sigma)"
      using locals_traverse_le_side_acc_dg[OF combine_at_mem[OF ce], where acc = bot]
      by (simp add: dg_cmb_def traverse_side_rhs_fold_dg)
    also have "... \<le> side_acc_dg (dg_acc g bot0 s0d k)
          sigma (dg_trees g k)"
      by (rule locals_traverse_le_side_acc_dg[OF combine_tree_mem[OF ce]])
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (k, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma k"
      using eq_le[OF cover_combine[OF ce]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_D sigma k" .
  qed

  have combineG:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      fst (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_G sigma"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "fst (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
          (dg_G sigma))
        = globs (sides_of_rhs (dg_cmb_at () (CallEdge dst fs as) c p) sigma (Inr ()))"
      by (simp add: dg_combine_tree_global)
    also have "... \<le> globs (sides_of_rhs
        (dg_cmb g (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c k) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF combine_at_mem[OF ce], where acc = bot and k = "Inr ()"]
      by (simp add: dg_cmb_def less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d k)
            (dg_trees g k)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF combine_tree_mem[OF ce], where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (k, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_combine[OF ce], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dgs_combine S (call_info_of (CallEdge dst fs as) p) (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p) (dg_D sigma c) (dg_G sigma)) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_G sigma" .
  qed

  show ?thesis
    unfolding dg_postfix_def
    using entryD entryG edgeD edgeG enterD enterG combineD combineG by blast
qed

text \<open>The three set-valued closure obligations of a \<^const>\<open>dg_postfix\<close> against
  \<^const>\<open>dg_gamma\<close> discharge the trace-native collecting endpoint.\<close>

lemma dg_postfix_gamma_entry:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
proof -
  have d_le: "s0d \<le> dg_D sigma (cfg_entry g)"
    and g_le: "s0g \<le> dg_G sigma"
    using dg_postfix_entryD[OF pf] dg_postfix_entryG[OF pf] .
  have "gammaDG s0d s0g \<subseteq>
      gammaDG (dg_D sigma (cfg_entry g)) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show ?thesis
    using sound0 dg_gammaI by blast
qed

lemma dg_postfix_gamma_edge:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
    and sin: "s \<in> edge_collect a (dg_gamma sigma u)"
  shows "s \<in> dg_gamma sigma w"
proof -
  have sin':
      "s \<in> edge_collect a (gammaDG (dg_D sigma u) (dg_G sigma))"
    using sin unfolding dg_gamma_def .
  have out: "s \<in> gammaDG (snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
                         (fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))"
    using step_sound_fs sin' by blast
  have d_le: "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_D sigma w"
    using dg_postfix_edgeD[OF pf edge] .
  have g_le: "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_edgeG[OF pf edge] .
  have "gammaDG (snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
                (fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma w) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "s \<in> dg_gamma sigma w"
    using out dg_gammaI by blast
qed

lemma dg_postfix_gamma_call:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_gamma sigma u"
  shows "call_enter gs (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
proof -
  have sin': "s \<in> gammaDG (dg_D sigma u) (dg_G sigma)"
    using dg_gammaD[OF sin] .
  have out: "call_enter gs (CallEdge dst pars args) s \<in>
               gammaDG (snd (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma)))
                       (fst (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma)))"
    using enter_sound_fs[where ci = "call_info_of (CallEdge dst pars args) p", OF sin'] by simp
  have d_le: "snd (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma))
                \<le> dg_D sigma (FunctionEntry p)"
    using dg_postfix_enterD[OF pf ce] .
  have g_le: "fst (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_enterG[OF pf ce] .
  have "gammaDG (snd (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma)))
                (fst (dgs_enter S (call_info_of (CallEdge dst pars args) p) (dg_D sigma u) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma (FunctionEntry p)) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "call_enter gs (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
    using out dg_gammaI by blast
qed

lemma dg_postfix_gamma_combine:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and comb: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_gamma sigma cl"
    and tin: "t \<in> dg_gamma sigma (FunctionResult p)"
  shows "combine_collect gs dst s t \<in> dg_gamma sigma cont"
proof -
  have sin': "s \<in> gammaDG (dg_D sigma cl) (dg_G sigma)"
    using dg_gammaD[OF sin] .
  have tin': "t \<in> gammaDG (dg_D sigma (FunctionResult p)) (dg_G sigma)"
    using dg_gammaD[OF tin] .
  have out: "combine_collect gs dst s t \<in>
      gammaDG (snd (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
              (fst (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma)))"
    using combine_sound_at_call_fs[where ci = "call_info_of (CallEdge dst pars args) p",
                                   OF sin' tin' order_refl]
    by simp

  have d_le: "snd (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p))
                (dg_G sigma)) \<le> dg_D sigma cont"
    using dg_postfix_combineD[OF pf comb] .
  have g_le: "fst (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p))
                (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_combineG[OF pf comb] .
  have "gammaDG (snd (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
                (fst (dgs_combine S (call_info_of (CallEdge dst pars args) p) (dgs_caller_cont S (call_info_of (CallEdge dst pars args) p) (dg_D sigma cl) (dg_G sigma)) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma cont) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "combine_collect gs dst s t \<in> dg_gamma sigma cont"
    using out dg_gammaI by blast
qed

subsection \<open>Reduction to the hook-parametric shape\<close>

text \<open>
  \<open>dg_trees\<close>'s three tree constructors, restated as functions of exactly the
  shape the hook-parametric generator below fixes (\<open>edge_tree\<close>/\<open>combine_tree\<close>/
  \<open>enter_tree\<close>, each ignoring the destination/continuation position the same
  way \<open>dg_trees\<close> already does). \<open>dg_edge_tree_local\<close>/\<open>dg_combine_tree_local\<close>/
  \<open>dg_enter_tree_local\<close> (and their \<open>_global\<close> siblings) above already compute
  exactly what that generator's three soundness assumptions need, so this
  spec-record route is an instance of the hook route rather than a second,
  independent proof of the same per-step obligation.
\<close>

definition dg_edge_tree_hook ::
  "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_edge_tree_hook u a v =
     map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))"

definition dg_combine_tree_hook ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_combine_tree_hook cc ca ex k = dg_cmb_at () ca cc (result_proc ex)"

definition dg_enter_tree_hook ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_enter_tree_hook cc ca p =
     dg_enter () (call_info_of ca (case p of FunctionEntry proc \<Rightarrow> proc | _ \<Rightarrow> undefined)) cc"

lemma dg_edge_tree_hook_local:
  "locals (traverse_rhs (dg_edge_tree_hook u a v) sigma)
     = snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding dg_edge_tree_hook_def by (rule dg_edge_tree_local)

lemma dg_edge_tree_hook_global:
  "globs (sides_of_rhs (dg_edge_tree_hook u a v) sigma (Inr ()))
     = fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding dg_edge_tree_hook_def by (rule dg_edge_tree_global)

lemma dg_combine_tree_hook_local:
  "locals (traverse_rhs (dg_combine_tree_hook cc (CallEdge dst fs as) (FunctionResult p) k) sigma)
     = snd (dgs_combine S (call_info_of (CallEdge dst fs as) p)
              (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p)
                 (dg_D sigma cc) (dg_G sigma))
              (dg_D sigma (FunctionResult p)) (dg_G sigma))"
  unfolding dg_combine_tree_hook_def by (simp add: dg_combine_tree_local)

lemma dg_combine_tree_hook_global:
  "globs (sides_of_rhs (dg_combine_tree_hook cc (CallEdge dst fs as) (FunctionResult p) k) sigma (Inr ()))
     = fst (dgs_combine S (call_info_of (CallEdge dst fs as) p)
              (dgs_caller_cont S (call_info_of (CallEdge dst fs as) p)
                 (dg_D sigma cc) (dg_G sigma))
              (dg_D sigma (FunctionResult p)) (dg_G sigma))"
  unfolding dg_combine_tree_hook_def by (simp add: dg_combine_tree_global)

lemma dg_enter_tree_hook_local:
  "locals (traverse_rhs (dg_enter_tree_hook cc ca p) sigma)
     = snd (dgs_enter S (call_info_of ca (case p of FunctionEntry proc \<Rightarrow> proc | _ \<Rightarrow> undefined))
              (dg_D sigma cc) (dg_G sigma))"
  unfolding dg_enter_tree_hook_def by (simp add: dg_enter_tree_local)

lemma dg_enter_tree_hook_global:
  "globs (sides_of_rhs (dg_enter_tree_hook cc ca p) sigma (Inr ()))
     = fst (dgs_enter S (call_info_of ca (case p of FunctionEntry proc \<Rightarrow> proc | _ \<Rightarrow> undefined))
              (dg_D sigma cc) (dg_G sigma))"
  unfolding dg_enter_tree_hook_def by (simp add: dg_enter_tree_global)

end


subsection \<open>Hook-parametric D/G soundness\<close>

definition dg_hook_D ::
  "((pp \<times> unit + unit) \<Rightarrow> ('D::bounded_semilattice_sup_bot,
    'G::bounded_semilattice_sup_bot) dg_state) \<Rightarrow> pp \<Rightarrow> 'D"
where
  "dg_hook_D sigma v = locals (sigma (Inl (v, ())))"
definition dg_hook_G ::
  "((pp \<times> unit + unit) \<Rightarrow> ('D::bounded_semilattice_sup_bot,
    'G::bounded_semilattice_sup_bot) dg_state) \<Rightarrow> 'G"
where
  "dg_hook_G sigma = globs (sigma (Inr ()))"

definition dg_hook_gamma ::
  "('D::bounded_semilattice_sup_bot \<Rightarrow>
     'G::bounded_semilattice_sup_bot \<Rightarrow> store set)
   \<Rightarrow> ((pp \<times> unit + unit) \<Rightarrow> ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_hook_gamma gammaDG sigma v =
    gammaDG (dg_hook_D sigma v) (dg_hook_G sigma)"

locale sound_dg_hooks =
  fixes gammaDG :: "'D::bounded_semilattice_sup_bot \<Rightarrow>
      'G::bounded_semilattice_sup_bot \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and edge_tree :: "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and combine_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and enter_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
  assumes gammaDG_mono:
      "\<And>d d' g g'. \<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and edge_hook_sound:
      "\<And>sigma source action destination.
        edge_collect action (dg_hook_gamma gammaDG sigma source) \<subseteq>
          gammaDG
            (locals (traverse_rhs
              (edge_tree source action destination) sigma))
            (globs (sides_of_rhs
              (edge_tree source action destination) sigma (Inr ())))"
    and enter_hook_sound:
      "\<And>sigma caller dst fs args callee s.
        s \<in> dg_hook_gamma gammaDG sigma caller \<Longrightarrow>
        call_enter gs (CallEdge dst fs args) s \<in>
          gammaDG
            (locals (traverse_rhs
              (enter_tree caller (CallEdge dst fs args)
                (FunctionEntry callee)) sigma))
            (globs (sides_of_rhs
              (enter_tree caller (CallEdge dst fs args)
                (FunctionEntry callee)) sigma (Inr ())))"
    and combine_hook_sound:
      "\<And>sigma caller dst fs args callee continuation s t.
        \<lbrakk>s \<in> dg_hook_gamma gammaDG sigma caller;
          t \<in> dg_hook_gamma gammaDG sigma (FunctionResult callee)\<rbrakk>
        \<Longrightarrow> combine_collect gs dst s t \<in>
          gammaDG
            (locals (traverse_rhs
              (combine_tree caller (CallEdge dst fs args)
                (FunctionResult callee) continuation) sigma))
            (globs (sides_of_rhs
              (combine_tree caller (CallEdge dst fs args)
                (FunctionResult callee) continuation) sigma (Inr ())))"
begin

definition hook_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree list"
where
  "hook_trees g v =
     map (\<lambda>(u, a). edge_tree u a v) (intra_predecessor_list g v)
     @ map (\<lambda>(c, ca, ex). combine_tree c ca ex v)
       (return_call_action_list g v)
     @ map (\<lambda>(c, ca). enter_tree c ca v)
       (entry_call_list g v)"

definition hook_gen ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G \<Rightarrow>
   (pp \<times> unit, unit, ('D, 'G) dg_state) eqsT"
where
  "hook_gen g bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_trees intra_predecessor_list (\<lambda>_. ())
      (\<lambda>_ u a v. edge_tree u a v)
      (\<lambda>_ c ca ex v. combine_tree c ca ex v)
      (\<lambda>_ c ca v. enter_tree c ca v)
      g bot0 s0d s0g"

definition hook_acc ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> pp \<Rightarrow> 'D"
where
  "hook_acc g bot0 s0d v =
    (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_hook_gen:
  "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (hook_acc g bot0 s0d v)
     sigma (hook_trees g v)) bot"
  unfolding hook_gen_def hook_trees_def hook_acc_def
  by (simp add: eq_side_cfg_T_eff_keyed_seed_trees)

lemma sides_fold_le_hook_gen:
  "sides_of_rhs
      (side_rhs_fold_dg (hook_acc g bot0 s0d v)
        (hook_trees g v)) sigma k
   \<le> sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma k"
  unfolding hook_gen_def hook_trees_def hook_acc_def
    side_cfg_T_eff_keyed_seed_trees_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

text \<open>
  \<open>hook_gen\<close> is one instantiation of the representation-neutral
  \<^const>\<open>side_cfg_T_eff_keyed_seed_trees\<close>, so its single-tree degeneracy at a
  node with exactly one incoming edge, call return, or call entry is the
  generic reduction proved once for that generator. An analysis instance
  cites the named tree constructor (\<open>edge_tree\<close>, \<open>enter_tree\<close>, or
  \<open>combine_tree\<close>) directly instead of re-unfolding \<open>hook_gen_def\<close> and the
  fold's single-element case at every node.
\<close>

lemma hook_gen_single_edge:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "intra_predecessor_list g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (edge_tree u a v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (edge_tree u a v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_edge[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry pred no_combine no_enter bot0])

lemma hook_gen_single_enter:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "intra_predecessor_list g v = []"
    and no_combine: "return_call_action_list g v = []"
    and pred: "entry_call_list g v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (enter_tree caller action v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (enter_tree caller action v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_enter[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry no_edge no_combine pred bot0])

lemma hook_gen_single_combine:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "intra_predecessor_list g v = []"
    and pred: "return_call_action_list g v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (combine_tree caller action callee_exit v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (combine_tree caller action callee_exit v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_combine[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry no_edge pred no_enter bot0])

lemma hook_gen_entry:
  fixes bot0 :: 'D
  assumes no_edge: "intra_predecessor_list g (cfg_entry g) = []"
    and no_combine: "return_call_action_list g (cfg_entry g) = []"
    and no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (cfg_entry g, ()) sigma = DG s0d bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma (Inr ()) = DG bot s0g"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_entry[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF no_edge no_combine no_enter bot0])

definition hook_postfix ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state)
   \<Rightarrow> bool"
where
  "hook_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_hook_D sigma (cfg_entry g) \<and>
     s0g \<le> dg_hook_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
       edge_collect a (dg_hook_gamma gammaDG sigma u)
         \<subseteq> dg_hook_gamma gammaDG sigma v) \<and>
     (\<forall>c dst fs args p k s.
       (c, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g \<longrightarrow>
       s \<in> dg_hook_gamma gammaDG sigma c \<longrightarrow>
       call_enter gs (CallEdge dst fs args) s \<in>
         dg_hook_gamma gammaDG sigma (FunctionEntry p)) \<and>
     (\<forall>c dst fs args p k s t.
       (c, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g \<longrightarrow>
       s \<in> dg_hook_gamma gammaDG sigma c \<longrightarrow>
       t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p) \<longrightarrow>
       combine_collect gs dst s t \<in> dg_hook_gamma gammaDG sigma k)"



lemma hook_tree_local_le:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
    and cover: "(v, ()) \<in> vars"
    and tree: "t \<in> set (hook_trees g v)"
  shows "locals (traverse_rhs t sigma) \<le> dg_hook_D sigma v"
proof -
  have eq_le:
      "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using se_constraint_holds_local
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
      cover
    by blast
  have "locals (traverse_rhs t sigma)
      \<le> side_acc_dg (hook_acc g bot0 s0d v)
        sigma (hook_trees g v)"
    by (rule locals_traverse_le_side_acc_dg[OF tree])
  also have "... = locals
      (eq (hook_gen g bot0 s0d s0g) (v, ()) sigma)"
    by (simp add: eq_hook_gen)
  also have "... \<le> dg_hook_D sigma v"
    using eq_le
    by (simp add: dg_hook_D_def less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma hook_tree_side_le:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
    and cover: "(v, ()) \<in> vars"
    and tree: "t \<in> set (hook_trees g v)"
  shows "globs (sides_of_rhs t sigma (Inr ())) \<le> dg_hook_G sigma"
proof -
  have sides_le:
      "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma
        \<le> sigma"
    using se_constraint_holds_sides
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
      cover
    by blast
  have "globs (sides_of_rhs t sigma (Inr ()))
      \<le> globs (sides_of_rhs
        (side_rhs_fold_dg (hook_acc g bot0 s0d v)
          (hook_trees g v)) sigma (Inr ()))"
    using sides_le_side_rhs_fold_dg[OF tree, where k = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  also have "... \<le> globs (sides_of_rhs
      (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()))"
    using sides_fold_le_hook_gen[where k = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  also have "... \<le> dg_hook_G sigma"
    using sides_le[THEN le_funD, of "Inr ()"]
    by (simp add: dg_hook_G_def less_eq_dg_state_def)
  finally show ?thesis .
qed



lemma hook_edge_tree_mem:
  assumes finI: "finite (intra g)"
    and edge: "(u, a, v) \<in> intra g"
  shows "edge_tree u a v \<in> set (hook_trees g v)"
proof -
  have "(u, a) \<in> set (intra_predecessor_list g v)"
    using edge
    by (simp add: set_intra_predecessor_list[OF finI] intra_predecessors_def)
  then show ?thesis
    by (auto simp: hook_trees_def)
qed

lemma hook_enter_tree_mem:
  assumes finC: "finite (calls g)"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
  shows "enter_tree caller (CallEdge dst fs args) (FunctionEntry p)
      \<in> set (hook_trees g (FunctionEntry p))"
proof -
  have "(caller, CallEdge dst fs args) \<in>
      set (entry_call_list g (FunctionEntry p))"
    using call
    by (auto simp: set_entry_call_list[OF finC] entry_calls_iff)
  then show ?thesis
    by (force simp: hook_trees_def image_iff)
qed

lemma hook_combine_tree_mem:
  assumes finC: "finite (calls g)"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
  shows "combine_tree caller (CallEdge dst fs args) (FunctionResult p) k
      \<in> set (hook_trees g k)"
proof -
  have "(caller, CallEdge dst fs args, FunctionResult p) \<in>
      set (return_call_action_list g k)"
    using call
    by (auto simp: set_return_call_action_list[OF finC]
      return_call_actions_iff)
  then show ?thesis
    by (force simp: hook_trees_def)
qed



theorem hook_post_solution_postfix:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_enter:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
  shows "hook_postfix g s0d s0g sigma"
proof -
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (hook_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using se_constraint_holds_local
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (hook_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using se_constraint_holds_sides
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast

  have entryD: "s0d \<le> dg_hook_D sigma (cfg_entry g)"
  proof -
    have "s0d \<le> hook_acc g bot0 s0d (cfg_entry g)"
      by (simp add: hook_acc_def)
    also have "... \<le> side_acc_dg
        (hook_acc g bot0 s0d (cfg_entry g))
        sigma (hook_trees g (cfg_entry g))"
      by (rule side_acc_dg_ge_acc)
    also have "... = locals
        (eq (hook_gen g bot0 s0d s0g)
          (cfg_entry g, ()) sigma)"
      by (simp add: eq_hook_gen)
    also have "... \<le> dg_hook_D sigma (cfg_entry g)"
      using eq_le[OF cover_entry]
      by (simp add: dg_hook_D_def less_eq_dg_state_def)
    finally show ?thesis .
  qed

  have entryG: "s0g \<le> dg_hook_G sigma"
  proof -
    have "DG bot s0g \<le>
       sides_of_rhs
         (hook_gen g bot0 s0d s0g (cfg_entry g, ()))
         sigma (Inr ())"
      unfolding hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: dg_hook_G_def less_eq_dg_state_def)
  qed

  have edge:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      edge_collect a (dg_hook_gamma gammaDG sigma u)
        \<subseteq> dg_hook_gamma gammaDG sigma v"
  proof -
    fix u a v
    assume intra: "(u, a, v) \<in> intra g"
    have d_le:
      "locals (traverse_rhs (edge_tree u a v) sigma)
        \<le> dg_hook_D sigma v"
      by (rule hook_tree_local_le
        [OF pp cover_edge[OF intra] hook_edge_tree_mem[OF finI intra]])
    have g_le:
      "globs (sides_of_rhs (edge_tree u a v) sigma (Inr ()))
        \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_edge[OF intra] hook_edge_tree_mem[OF finI intra]])
    have "gammaDG
        (locals (traverse_rhs (edge_tree u a v) sigma))
        (globs (sides_of_rhs (edge_tree u a v) sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma v"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "edge_collect a (dg_hook_gamma gammaDG sigma u)
        \<subseteq> dg_hook_gamma gammaDG sigma v"
      using edge_hook_sound by blast
  qed

  have enter:
    "\<And>caller dst fs args p k s.
      (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
      \<Longrightarrow> s \<in> dg_hook_gamma gammaDG sigma caller
      \<Longrightarrow> call_enter gs (CallEdge dst fs args) s \<in>
        dg_hook_gamma gammaDG sigma (FunctionEntry p)"
  proof -
    fix caller dst fs args p k s
    assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
      and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    have d_le:
      "locals (traverse_rhs
        (enter_tree caller (CallEdge dst fs args) (FunctionEntry p)) sigma)
        \<le> dg_hook_D sigma (FunctionEntry p)"
      by (rule hook_tree_local_le
        [OF pp cover_enter[OF call] hook_enter_tree_mem[OF finC call]])
    have g_le:
      "globs (sides_of_rhs
        (enter_tree caller (CallEdge dst fs args) (FunctionEntry p))
        sigma (Inr ())) \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_enter[OF call] hook_enter_tree_mem[OF finC call]])
    have "gammaDG
        (locals (traverse_rhs
          (enter_tree caller (CallEdge dst fs args) (FunctionEntry p)) sigma))
        (globs (sides_of_rhs
          (enter_tree caller (CallEdge dst fs args) (FunctionEntry p))
          sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma (FunctionEntry p)"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "call_enter gs (CallEdge dst fs args) s \<in>
        dg_hook_gamma gammaDG sigma (FunctionEntry p)"
      using enter_hook_sound[OF sin] by blast
  qed

  have combine:
    "\<And>caller dst fs args p k s t.
      (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
      \<Longrightarrow> s \<in> dg_hook_gamma gammaDG sigma caller
      \<Longrightarrow> t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)
      \<Longrightarrow> combine_collect gs dst s t \<in>
        dg_hook_gamma gammaDG sigma k"
  proof -
    fix caller dst fs args p k s t
    assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
      and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
      and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
    have d_le:
      "locals (traverse_rhs
        (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
        sigma) \<le> dg_hook_D sigma k"
      by (rule hook_tree_local_le
        [OF pp cover_combine[OF call] hook_combine_tree_mem[OF finC call]])
    have g_le:
      "globs (sides_of_rhs
        (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
        sigma (Inr ())) \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_combine[OF call] hook_combine_tree_mem[OF finC call]])
    have "gammaDG
        (locals (traverse_rhs
          (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
          sigma))
        (globs (sides_of_rhs
          (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
          sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma k"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "combine_collect gs dst s t \<in>
        dg_hook_gamma gammaDG sigma k"
      using combine_hook_sound[OF sin tin] by blast
  qed

  show ?thesis
    unfolding hook_postfix_def
    using entryD entryG edge enter combine by blast
qed


lemma hook_postfix_entryD [dest]:
  assumes pf: "hook_postfix g s0d s0g sigma"
  shows "s0d \<le> dg_hook_D sigma (cfg_entry g)"
  using pf unfolding hook_postfix_def by blast

lemma hook_postfix_entryG:
  assumes pf: "hook_postfix g s0d s0g sigma"
  shows "s0g \<le> dg_hook_G sigma"
  using pf unfolding hook_postfix_def by blast

lemma hook_postfix_edge:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and edge: "(u, a, v) \<in> intra g"
  shows "edge_collect a (dg_hook_gamma gammaDG sigma u)
    \<subseteq> dg_hook_gamma gammaDG sigma v"
  using pf edge unfolding hook_postfix_def by blast

lemma hook_postfix_enter:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
  shows "call_enter gs (CallEdge dst fs args) s \<in>
    dg_hook_gamma gammaDG sigma (FunctionEntry p)"
  using pf call sin unfolding hook_postfix_def by blast

lemma hook_postfix_combine:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
  shows "combine_collect gs dst s t \<in>
    dg_hook_gamma gammaDG sigma k"
  using pf call sin tin unfolding hook_postfix_def by blast

subsection \<open>Generic post-solution assembly\<close>

text \<open>
  Turning a per-node dependency-closure fact (a @{const dep\<^sub>L} equation,
  obtained by unfolding @{const hook_gen} against the node's own CFG shape)
  and a per-node @{const se_constraint_holds} fact into the single conjunct
  @{const part_post_solution} needs at that node -- and combining every
  node's conjunct with exit membership into @{const part_post_solution}
  itself -- is the same argument regardless of which CFG or domain
  instantiates this locale: only the node's own predecessor count (zero at
  entry, one at an ordinary edge, two at a join) and its concrete
  dependency/effect facts vary per call site. These lemmas fix that argument
  once, so an instance's own post-solution assembly reduces to a case split
  whose branches each cite one dependency fact, one membership fact, and one
  @{const se_constraint_holds} fact.
\<close>

lemma hook_gen_dep_and_se_entry:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) = {}"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma
      (cfg_entry g, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma (cfg_entry g, ())"
  using dep_eq se by auto

lemma hook_gen_dep_and_se_single:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u, ())}"
    and mem: "(u, ()) \<in> vars"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem se by auto

lemma hook_gen_dep_and_se_pair:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u1, ()), (u2, ())}"
    and mem1: "(u1, ()) \<in> vars"
    and mem2: "(u2, ()) \<in> vars"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem1 mem2 se by auto

text \<open>
  Assembling the whole node-indexed ball into @{const part_post_solution}
  itself needs only exit membership, via
  @{thm part_post_solution_iff_se_constraint_holds}.
\<close>

lemma part_post_solution_of_ball:
  assumes exit_mem: "x \<in> vars"
    and ball: "\<forall>u \<in> vars. dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma u \<subseteq> vars \<and>
      se_constraint_holds (hook_gen g bot0 s0d s0g u) sigma u"
  shows "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
  unfolding part_post_solution_iff_se_constraint_holds using exit_mem ball by blast

end

subsection \<open>The spec-record route as a hook instance\<close>

text \<open>
  \<open>sound_dg_spec\<close>'s per-step obligations (\<open>step_sound\<close>, \<open>combine_sound\<close>,
  \<open>enter_sound\<close>) are exactly \<open>sound_dg_hooks\<close>'s three hook obligations
  specialized at the tree instantiation \<open>dg_edge_tree_hook\<close>/
  \<open>dg_combine_tree_hook\<close>/\<open>dg_enter_tree_hook\<close>: \<open>dg_D\<close>/\<open>dg_G\<close> and
  \<open>dg_hook_D\<close>/\<open>dg_hook_G\<close> unfold to the same term, so \<open>dg_gamma\<close> and
  \<open>dg_hook_gamma\<close> agree pointwise, and each hook tree's local/global answer is
  the corresponding \<open>dg_spec_step\<close>/\<open>dgs_enter\<close>/\<open>dgs_combine\<close> component by
  \<open>dg_edge_tree_hook_local\<close>/\<open>_global\<close> and its combine/enter siblings. This
  makes every \<open>sound_dg_spec\<close> interpretation a \<open>sound_dg_hooks\<close> interpretation
  for free, with no change to any existing \<open>sound_dg_spec\<close> interpretation.
\<close>

text \<open>The target is interpreted under the \<open>hooks\<close> qualifier: both locales
  fix an assumption named \<open>gammaDG_mono\<close>, so an unqualified sublocale would
  make every concrete \<open>sound_dg_spec\<close> interpretation (\<open>sign_dg\<close>, \<open>ivl_dg\<close>,
  ...) export two facts under the same flattened name and fail to build.\<close>

sublocale sound_dg_spec \<subseteq> hooks: sound_dg_hooks gammaDG gs
  dg_edge_tree_hook dg_combine_tree_hook dg_enter_tree_hook
proof unfold_locales
  fix d d' g g' :: 'G and e e' :: 'D
  show "\<lbrakk>e \<le> e'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG e g \<subseteq> gammaDG e' g'"
    by (rule gammaDG_mono)
next
  fix sigma source action destination
  have dD: "dg_hook_D sigma source = dg_D sigma source"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  show "edge_collect action (dg_hook_gamma gammaDG sigma source) \<subseteq>
      gammaDG
        (locals (traverse_rhs (dg_edge_tree_hook source action destination) sigma))
        (globs (sides_of_rhs (dg_edge_tree_hook source action destination) sigma (Inr ())))"
    unfolding dg_hook_gamma_def dD dG
      dg_edge_tree_hook_local dg_edge_tree_hook_global
    by (rule step_sound_fs)
next
  fix sigma caller dst fs args callee s
  assume sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
  have dD: "dg_hook_D sigma caller = dg_D sigma caller"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  have sin': "s \<in> gammaDG (dg_D sigma caller) (dg_G sigma)"
    using sin unfolding dg_hook_gamma_def dD dG .
  show "call_enter gs (CallEdge dst fs args) s \<in>
      gammaDG
        (locals (traverse_rhs
          (dg_enter_tree_hook caller (CallEdge dst fs args) (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (dg_enter_tree_hook caller (CallEdge dst fs args) (FunctionEntry callee)) sigma (Inr ())))"
    unfolding dg_enter_tree_hook_local dg_enter_tree_hook_global
    using enter_sound_fs[where ci = "call_info_of (CallEdge dst fs args) callee", OF sin']
    by simp
next
  fix sigma caller dst fs args callee continuation s t
  assume sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult callee)"
  have dDc: "dg_hook_D sigma caller = dg_D sigma caller"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dDe: "dg_hook_D sigma (FunctionResult callee) = dg_D sigma (FunctionResult callee)"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  have sin': "s \<in> gammaDG (dg_D sigma caller) (dg_G sigma)"
    using sin unfolding dg_hook_gamma_def dDc dG .
  have tin': "t \<in> gammaDG (dg_D sigma (FunctionResult callee)) (dg_G sigma)"
    using tin unfolding dg_hook_gamma_def dDe dG .
  show "combine_collect gs dst s t \<in>
      gammaDG
        (locals (traverse_rhs
          (dg_combine_tree_hook caller (CallEdge dst fs args) (FunctionResult callee) continuation)
          sigma))
        (globs (sides_of_rhs
          (dg_combine_tree_hook caller (CallEdge dst fs args) (FunctionResult callee) continuation)
          sigma (Inr ())))"
    unfolding dg_combine_tree_hook_local dg_combine_tree_hook_global
    using combine_sound_at_call_fs[where ci = "call_info_of (CallEdge dst fs args) callee",
                                   OF sin' tin' order_refl]
    by simp
qed

context sound_dg_spec
begin

text \<open>
  The two equation systems --- \<open>dg_gen\<close>, built directly off the spec-record, and
  \<open>hook_gen\<close>, inherited from the hook-route sublocale interpretation above ---
  denote the same function, not merely a sound approximation of each other. They
  are not the same term: \<open>dg_gen\<close> folds one tree per call \<^emph>\<open>site\<close>, which resolves
  its callees and folds their contributions, while \<open>hook_gen\<close> folds one flat tree
  per call-site/callee pair. Both foldings range over the same contributions, so
  every observable of the generated right-hand side --- its answer, its side
  contribution at any key, and its dependency set --- agrees.
\<close>

lemma dg_trees_as_hook_shape:
  "dg_trees g v
     = map (\<lambda>(u, a). dg_edge_tree_hook u a v) (intra_predecessor_list g v)
       @ map (side_rhs_fold_dg bot)
           (map (\<lambda>(cc, ca). map (dg_cmb_at () ca cc) (static_targets g v cc ca))
                (call_site_list g v))
       @ map (\<lambda>(c, ca). dg_enter_tree_hook c ca v) (entry_call_list g v)"
  unfolding dg_trees_def dg_extra_def dg_edge_tree_hook_def dg_enter_tree_hook_def
    dg_cmb_def
  by (auto simp: intra_predecessor_addr_list_def apply_dg_spec_relabel_as_at
        o_def case_prod_unfold)

lemma set_dg_cmb_targets_eq_hook:
  "set (concat (map (\<lambda>(cc, ca). map (dg_cmb_at () ca cc) (static_targets g v cc ca))
                    (call_site_list g v)))
     = set (map (\<lambda>(c, ca, ex). dg_combine_tree_hook c ca ex v)
                (return_call_action_list g v))"
proof -
  have "set (concat (map (\<lambda>(cc, ca). map (dg_cmb_at () ca cc) (static_targets g v cc ca))
                         (call_site_list g v)))
          = set (map (\<lambda>(c, ca, p). dg_cmb_at () ca c p) (call_target_list g v))"
    by (rule set_concat_call_site_static_targets)
  also have "... = set (map (\<lambda>(c, ca, ex). dg_combine_tree_hook c ca ex v)
                            (return_call_action_list g v))"
    unfolding dg_combine_tree_hook_def call_target_list_eq_return_call_action_list
    by (simp add: case_prod_unfold)
  finally show ?thesis .
qed

lemma dg_trees_agrees_hook_trees:
  "side_acc_dg acc sigma (dg_trees g v) = side_acc_dg acc sigma (hooks.hook_trees g v)"
  "sides_of_rhs (side_rhs_fold_dg acc (dg_trees g v)) sigma z
     = sides_of_rhs (side_rhs_fold_dg acc (hooks.hook_trees g v)) sigma z"
  "dep_aux sigma (side_rhs_fold_dg acc (dg_trees g v))
     = dep_aux sigma (side_rhs_fold_dg acc (hooks.hook_trees g v))"
proof -
  show "side_acc_dg acc sigma (dg_trees g v) = side_acc_dg acc sigma (hooks.hook_trees g v)"
    using side_rhs_fold_dg_flat_cong(1)[OF set_dg_cmb_targets_eq_hook,
            where acc = acc and \<tau> = sigma]
    unfolding dg_trees_as_hook_shape hooks.hook_trees_def
    by (simp add: traverse_side_rhs_fold_dg)
next
  show "sides_of_rhs (side_rhs_fold_dg acc (dg_trees g v)) sigma z
          = sides_of_rhs (side_rhs_fold_dg acc (hooks.hook_trees g v)) sigma z"
    unfolding dg_trees_as_hook_shape hooks.hook_trees_def
    by (rule side_rhs_fold_dg_flat_cong(2)[OF set_dg_cmb_targets_eq_hook])
next
  show "dep_aux sigma (side_rhs_fold_dg acc (dg_trees g v))
          = dep_aux sigma (side_rhs_fold_dg acc (hooks.hook_trees g v))"
    unfolding dg_trees_as_hook_shape hooks.hook_trees_def
    by (rule side_rhs_fold_dg_flat_cong(3)[OF set_dg_cmb_targets_eq_hook])
qed

lemma dg_gen_unfold:
  "dg_gen g bot0 s0d s0g (v, ())
     = (if v = cfg_entry g
        then depend_on () (DG bot s0g) (side_rhs_fold_dg (dg_acc g bot0 s0d v) (dg_trees g v))
        else side_rhs_fold_dg (dg_acc g bot0 s0d v) (dg_trees g v))"
  unfolding dg_gen_def dg_trees_def dg_acc_def side_cfg_T_eff_keyed_seed_dg_def
  by (simp add: Let_def)

lemma hook_gen_unfold:
  "hooks.hook_gen g bot0 s0d s0g (v, ())
     = (if v = cfg_entry g
        then depend_on () (DG bot s0g)
               (side_rhs_fold_dg (dg_acc g bot0 s0d v) (hooks.hook_trees g v))
        else side_rhs_fold_dg (dg_acc g bot0 s0d v) (hooks.hook_trees g v))"
  unfolding hooks.hook_gen_def hooks.hook_trees_def dg_acc_def
    side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: Let_def)

lemma dg_gen_agrees_hook_gen:
  "eq (dg_gen g bot0 s0d s0g) (v, ()) sigma
     = eq (hooks.hook_gen g bot0 s0d s0g) (v, ()) sigma"
  "sides_of_rhs (dg_gen g bot0 s0d s0g (v, ())) sigma z
     = sides_of_rhs (hooks.hook_gen g bot0 s0d s0g (v, ())) sigma z"
  "dep_aux sigma (dg_gen g bot0 s0d s0g (v, ()))
     = dep_aux sigma (hooks.hook_gen g bot0 s0d s0g (v, ()))"
    apply (simp add: eq_dg_gen hooks.eq_hook_gen dg_acc_def hooks.hook_acc_def
             dg_trees_agrees_hook_trees(1))
   apply (simp add: dg_gen_unfold hook_gen_unfold dg_trees_agrees_hook_trees(2) Let_def)
  apply (simp add: dg_gen_unfold hook_gen_unfold dg_trees_agrees_hook_trees(3))
  done

end

subsection \<open>The canonical independent-transfer spec\<close>

text \<open>
  The record an independent-transfer analysis denotes: every edge action
  advances each slot by its own transfer, the combine is structural in each
  slot.  Any two sound transfers yield a \<open>sound_dg_spec\<close> instance; at
  \<open>tfD = tfG\<close> this is the homogeneous single-domain analysis as the diagonal.
\<close>

definition indep_dg_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> 'd::sound_domain domain_transfer
   \<Rightarrow> 'g::sound_domain domain_transfer
   \<Rightarrow> ('d abs_state, 'g abs_state) dg_spec"
where
  "indep_dg_spec gs tfD tfG = \<lparr>
    dgs_skip       = (\<lambda>d g. (apply_tf tfG EA_Nop g, apply_tf tfD EA_Nop d)),
    dgs_assign     = (\<lambda>x e d g. (apply_tf tfG (EA_Assign x e) g,
                                 apply_tf tfD (EA_Assign x e) d)),
    dgs_special    = (\<lambda>sc x d g. (apply_tf tfG (EA_Special sc x) g,
                                  apply_tf tfD (EA_Special sc x) d)),
    dgs_branch     = (\<lambda>b pol d g. (branch\<^sup># tfG b pol g,
                                   branch\<^sup># tfD b pol d)),
    dgs_body       = (\<lambda>p d g. (body\<^sup># tfG p g, body\<^sup># tfD p d)),
    dgs_return     = (\<lambda>e p d g. (return\<^sup># tfG e p g, return\<^sup># tfD e p d)),
    dgs_enter      = (\<lambda>ci d g. (snd (enter\<^sup># tfG ci g),
                                snd (enter\<^sup># tfD ci d))),
    dgs_event      = (\<lambda>ev d g. (event\<^sup># tfG ev g, event\<^sup># tfD ev d)),
    dgs_caller_cont    = (\<lambda>_ d _. d),
    dgs_combine_env    = (\<lambda>_ dc de g. (combine_env gs g g, combine_env gs dc de)),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (combine_assign (ci_dst ci) (g ret_var) (fst merged),
       combine_assign (ci_dst ci) (de ret_var) (snd merged)))
  \<rparr>"

text \<open>Uniform in \<open>apply_tf tfG a\<close>/\<open>apply_tf tfD a\<close> for every case, including
  \<open>EA_Check\<close>: \<^const>\<open>dgs_event\<close> is an independent field of both products, exactly
  like \<^const>\<open>dgs_body\<close>/\<^const>\<open>dgs_return\<close> above.\<close>
lemma dg_spec_step_indep [simp]:
  "dg_spec_step (indep_dg_spec gs tfD tfG) a d g
   = (apply_tf tfG a g, apply_tf tfD a d)"
  unfolding indep_dg_spec_def
  by (cases a) simp_all

lemma dgs_combine_indep [simp]:
  "dgs_combine (indep_dg_spec gs tfD tfG) dst dc de g
   = (combine\<^sup># gs (ci_dst dst) g g, combine\<^sup># gs (ci_dst dst) dc de)"
  unfolding dgs_combine_def indep_dg_spec_def combine_collect_abs_def by simp

text \<open>The combine obligation of @{locale sound_dg_spec} for the independent
  product, as a named corollary: applied by @{method rule} at the interpretation
  boundary instead of positional \<open>for\<close> binders.\<close>
lemma gamma_dg_combine_sound:
  assumes sc: "s \<in> gamma_dg dc g" and tc: "t \<in> gamma_dg de g"
  shows "combine_collect gs (ci_dst dst) s t \<in>
           (case dgs_combine (indep_dg_spec gs tfD tfG) dst dc de g of (g', d') \<Rightarrow> gamma_dg d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc\<rbrakk>" using gamma_dgD1[OF sc] .
  have tc': "t \<in> \<lbrakk>de\<rbrakk>" using gamma_dgD1[OF tc] .
  have sg: "s \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF sc] .
  have tg: "t \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF tc] .
  have d_sound: "combine_collect gs (ci_dst dst) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst dst) dc de\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  have g_sound: "combine_collect gs (ci_dst dst) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst dst) g g\<rbrakk>"
    by (rule combine_collect_sound[OF sg tg])
  show ?thesis
    using d_sound g_sound unfolding gamma_dg_def by simp
qed

text \<open>The enter obligation of @{locale sound_dg_spec} for the independent product:
  each slot's callee-entry store lands in its own \<^const>\<open>tf_enter\<close> image.\<close>
lemma gamma_dg_enter_sound:
  assumes soundD: "sound_transfer_for gs tfD" and soundG: "sound_transfer_for gs tfG"
    and sc: "s \<in> gamma_dg dc g"
  shows "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
           (case dgs_enter (indep_dg_spec gs tfD tfG) ci dc g of (g', d') \<Rightarrow> gamma_dg d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc\<rbrakk>" using gamma_dgD1[OF sc] .
  have sg: "s \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF sc] .
  have d_sound: "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> \<lbrakk>snd (enter\<^sup># tfD ci dc)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_entry_for[OF soundD sc']
    by (simp add: call_enter_CallEdge)
  have g_sound: "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> \<lbrakk>snd (enter\<^sup># tfG ci g)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_entry_for[OF soundG sg]
    by (simp add: call_enter_CallEdge)
  show ?thesis
    unfolding indep_dg_spec_def gamma_dg_def by (simp add: d_sound g_sound)
qed

lemma sound_dg_spec_indep:
  assumes soundD: "sound_transfer_for gs tfD"
    and soundG: "sound_transfer_for gs tfG"
  shows "sound_dg_spec (indep_dg_spec gs tfD tfG) gamma_dg gs"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_dg_mono)
  subgoal for a d g
  proof -
    have d_input:
        "edge_collect a (gamma_dg d g) \<subseteq> edge_collect a \<lbrakk>d\<rbrakk>"
      by (rule edge_collect_mono[OF gamma_dg_le_D])
    have d_transfer:
        "edge_collect a \<lbrakk>d\<rbrakk> \<subseteq> \<lbrakk>apply_tf tfD a d\<rbrakk>"
      by (rule sound_transfer_for.edge_collect_apply_tf_sound_for[OF soundD])
    have d_sound:
        "edge_collect a (gamma_dg d g) \<subseteq> \<lbrakk>apply_tf tfD a d\<rbrakk>"
      using d_input d_transfer by blast
    have g_input:
        "edge_collect a (gamma_dg d g) \<subseteq> edge_collect a \<lbrakk>g\<rbrakk>"
      by (rule edge_collect_mono[OF gamma_dg_le_G])
    have g_transfer:
        "edge_collect a \<lbrakk>g\<rbrakk> \<subseteq> \<lbrakk>apply_tf tfG a g\<rbrakk>"
      by (rule sound_transfer_for.edge_collect_apply_tf_sound_for[OF soundG])
    show ?thesis
      using d_sound g_input g_transfer
      unfolding gamma_dg_def by auto
  qed
  subgoal premises prems using prems by (simp add: indep_dg_spec_def)
  subgoal premises prems by (rule gamma_dg_combine_sound[OF prems])
  subgoal premises prems by (rule gamma_dg_enter_sound[OF soundD soundG prems])
  done

subsection \<open>The homogeneous analysis as a diagonal interpretation\<close>

text \<open>
  \<open>gamma_unit gs d g\<close> is the meaning \<^const>\<open>unit_step_for\<close> actually assumes of a
  point's \<open>D\<close>/\<open>G\<close> pair: \<^const>\<open>combine_env\<close> routes each name to the one component
  that owns it (\<open>D\<close> for locals, \<open>G\<close> for globals), never the raw lattice join, so an
  untouched name's precision in its owning component is not destroyed by the other
  component's unrelated default.
\<close>
definition gamma_unit ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_unit gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"

lemma gamma_unit_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_unit gs d g \<subseteq> gamma_unit gs d' g'"
  unfolding gamma_unit_def
  by (rule gamma_state_mono) (use assms in \<open>auto simp: combine_env_def le_fun_def\<close>)

lemma gamma_unitD [dest]: "s \<in> gamma_unit gs d g \<Longrightarrow> s \<in> \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_unit_def by simp

text \<open>
  The defining equation as a citable lemma: client theories that need the
  full equality (not just the membership direction \<open>gamma_unitD\<close> gives) can
  cite this instead of reaching for \<open>gamma_unit_def\<close> directly.
\<close>
lemma gamma_unit_eq: "gamma_unit gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_unit_def ..


text \<open>
  Every call site owns \<open>ret_var\<close> as its own compiler-internal name, never a
  user-declared global (\<^const>\<open>reserved_ret_var\<close>); that is what lets the
  combine step read the return value straight out of \<open>de\<close> instead of routing
  it through \<^const>\<open>combine_env\<close> a second time.
\<close>
lemma combine_env_combine_env_left [simp]:
  "combine_env gs (combine_env gs dc g) (combine_env gs de g) = combine_env gs dc g"
  by (auto simp: combine_env_def)

lemma combine_env_local_eq [simp]:
  "\<not> gs x \<Longrightarrow> combine_env gs sc se x = sc x"
  by (simp add: combine_env_def)

text \<open>The \<^const>\<open>combine_env\<close> analogue of \<open>restrict_local_for_global_join\<close>:
  splitting a state into its local/global halves and routing them back through
  \<^const>\<open>combine_env\<close> recovers the original state exactly, since each half is
  already zero outside the location it owns.\<close>
lemma combine_env_restrict_id [simp]:
  "combine_env gs (restrict_local_for gs sigma) (restrict_global_for gs sigma) = sigma"
  by (simp add: combine_env_for_eq_restrictions restrict_local_for_global_join)

text \<open>
  The soundness argument for a homogeneous specification does not depend on
  how the merge and the split are chosen: every step merges \<open>D\<close> and \<open>G\<close>,
  applies the raw transfer, and splits the result back, and the target
  concretization is the re-merged pair. \<open>merge_split_spec\<close> captures exactly
  that shape -- a merge \<open>M\<close>, a split pair \<open>sg\<close>/\<open>sd\<close> whose re-merge is the
  identity, and the record equations -- and proves \<open>sound_dg_spec\<close> once for
  its \<open>gammaM d g = \<lbrakk>M d g\<rbrakk>\<close>. \<^const>\<open>unit_dg_spec_for\<close> is the exclusive
  instance (\<^const>\<open>combine_env\<close> routing, split by
  \<^const>\<open>restrict_local_for\<close>/\<^const>\<open>restrict_global_for\<close>); a non-exclusive
  covering split over the raw lattice join is a second one. The locale
  characterizes the record by its equations rather than rebuilding it, so an
  instance keeps its own optimized definition and only shows it equal to the
  generic shape.
\<close>

locale merge_split_spec =
  fixes S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and M :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sg :: "'a abs_state \<Rightarrow> 'a abs_state"
    and sd :: "'a abs_state \<Rightarrow> 'a abs_state"
    and tf :: "'a domain_transfer"
  assumes tf_sound: "sound_transfer_for gs tf"
    and M_mono: "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> M d g \<le> M d' g'"
    and reassemble [simp]: "M (sd res) (sg res) = res"
    and step_eq: "dg_spec_step S a d g =
      (let res = apply_tf tf a (M d g) in (sg res, sd res))"
    and enter_eq: "dgs_enter S ci d g =
      (let res = snd (enter\<^sup># tf ci (M d g)) in (sg res, sd res))"
    and cont_eq: "dgs_caller_cont S ci dc g = dc"
    and combine_eq: "dgs_combine S ci dc de g =
      (let res = combine\<^sup># gs (ci_dst ci) (M dc g) (M de g)
       in (sg res, sd res))"
begin

definition gammaM :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set" where
  "gammaM d g = \<lbrakk>M d g\<rbrakk>"

theorem merge_split_sound: "sound_dg_spec S gammaM gs"
proof unfold_locales
  fix d d' g g' :: "'a abs_state"
  assume "d \<le> d'" "g \<le> g'"
  then show "gammaM d g \<subseteq> gammaM d' g'"
    unfolding gammaM_def by (intro gamma_state_mono M_mono)
next
  fix a and d g :: "'a abs_state"
  have "edge_collect a \<lbrakk>M d g\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a (M d g)\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for[OF tf_sound])
  then show "edge_collect a (gammaM d g)
      \<subseteq> (case dg_spec_step S a d g of (g', d') \<Rightarrow> gammaM d' g')"
    unfolding gammaM_def step_eq by (simp add: Let_def)
next
  fix s and dc g :: "'a abs_state" and ci :: call_info
  assume "s \<in> gammaM dc g"
  then show "s \<in> gammaM (dgs_caller_cont S ci dc g) g"
    by (simp add: cont_eq)
next
  fix s t and dcont de g :: "'a abs_state" and ci :: call_info
  assume s: "s \<in> gammaM dcont g" and t: "t \<in> gammaM de g"
  have "combine_collect gs (ci_dst ci) s t
          \<in> \<lbrakk>combine\<^sup># gs (ci_dst ci) (M dcont g) (M de g)\<rbrakk>"
    by (rule combine_collect_sound[OF s[unfolded gammaM_def] t[unfolded gammaM_def]])
  then show "combine_collect gs (ci_dst ci) s t
      \<in> (case dgs_combine S ci dcont de g of (g', d') \<Rightarrow> gammaM d' g')"
    unfolding gammaM_def combine_eq by (simp add: Let_def)
next
  fix s and dc g :: "'a abs_state" and ci :: call_info
  assume "s \<in> gammaM dc g"
  then have sc': "s \<in> \<lbrakk>M dc g\<rbrakk>" unfolding gammaM_def .
  have "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
          \<in> \<lbrakk>snd (enter\<^sup># tf ci (M dc g))\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound sc']
    by (simp add: call_enter_CallEdge)
  then show "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> (case dgs_enter S ci dc g of (g', d') \<Rightarrow> gammaM d' g')"
    unfolding gammaM_def enter_eq by (simp add: Let_def)
qed

end

lemma merge_split_spec_unit_for:
  assumes sound: "sound_transfer_for gs tf"
    and reserved: "reserved_ret_var gs"
  shows "merge_split_spec (unit_dg_spec_for gs tf) gs (combine_env gs)
           (restrict_global_for gs) (restrict_local_for gs) tf"
proof (rule merge_split_spec.intro)
  show "sound_transfer_for gs tf" by (rule sound)
next
  fix d d' g g' :: "'a abs_state"
  assume "d \<le> d'" "g \<le> g'"
  then show "combine_env gs d g \<le> combine_env gs d' g'"
    by (rule combine_env_mono)
next
  show "\<And>res :: 'a abs_state.
      combine_env gs (restrict_local_for gs res) (restrict_global_for gs res) = res"
    by (rule combine_env_restrict_id)
next
  show "\<And>a d g. dg_spec_step (unit_dg_spec_for gs tf) a d g =
      (let res = apply_tf tf a (combine_env gs d g)
       in (restrict_global_for gs res, restrict_local_for gs res))"
    by (simp add: dg_spec_step_unit_for unit_step_for_def)
next
  show "\<And>ci d g. dgs_enter (unit_dg_spec_for gs tf) ci d g =
      (let res = snd (enter\<^sup># tf ci (combine_env gs d g))
       in (restrict_global_for gs res, restrict_local_for gs res))"
    by (simp add: dgs_enter_unit_dg_spec_for unit_step_for_def)
next
  show "\<And>ci dc g. dgs_caller_cont (unit_dg_spec_for gs tf) ci dc g = dc"
    by (simp add: unit_dg_spec_for_def)
next
  show "\<And>ci dc de g. dgs_combine (unit_dg_spec_for gs tf) ci dc de g =
      (let res = combine\<^sup># gs (ci_dst ci) (combine_env gs dc g) (combine_env gs de g)
       in (restrict_global_for gs res, restrict_local_for gs res))"
    using reserved
    unfolding dgs_combine_unit_dg_spec_for combine_collect_abs_def reserved_ret_var_def
    by (simp add: Let_def)
qed

lemma sound_dg_spec_unit_for:
  assumes sound: "sound_transfer_for gs tf"
    and reserved: "reserved_ret_var gs"
  shows "sound_dg_spec (unit_dg_spec_for gs tf) (gamma_unit gs) gs"
proof -
  interpret merge_split_spec "unit_dg_spec_for gs tf" gs "combine_env gs"
    "restrict_global_for gs" "restrict_local_for gs" tf
    by (rule merge_split_spec_unit_for[OF sound reserved])
  have "gamma_unit gs = gammaM"
    by (simp add: fun_eq_iff gamma_unit_def gammaM_def)
  then show ?thesis using merge_split_sound by simp
qed

text \<open>The combine half of the unit argument, kept standalone: the lifted
  diagonal section below reuses it verbatim through
  \<open>gamma_unit_combine_sound_for_lifted\<close>, where only the live/live case
  reaches an actual combine.\<close>
lemma gamma_unit_combine_sound_for:
  assumes reserved: "reserved_ret_var gs"
    and sc: "s \<in> gamma_unit gs dc g" and tc: "t \<in> gamma_unit gs de g"
  shows "combine_collect gs (ci_dst dst) s t \<in>
           (case dgs_combine (unit_dg_spec_for gs tf) dst dc de g of (g', d') \<Rightarrow> gamma_unit gs d' g')"
proof -
  have sc': "s \<in> \<lbrakk>combine_env gs dc g\<rbrakk>" using gamma_unitD[OF sc] .
  have tc': "t \<in> \<lbrakk>combine_env gs de g\<rbrakk>" using gamma_unitD[OF tc] .
  have "combine_collect gs (ci_dst dst) s t \<in>
          \<lbrakk>combine\<^sup># gs (ci_dst dst) (combine_env gs dc g) (combine_env gs de g)\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  then show ?thesis
    using reserved
    unfolding dgs_combine_unit_dg_spec_for gamma_unit_def combine_collect_abs_def
      reserved_ret_var_def
    by (simp add: Let_def)
qed

subsection \<open>The homogeneous analysis as a lifted diagonal interpretation, generic over the
  transfer\<close>

text \<open>
  \<open>gamma_unit_lifted\<close> concretizes the reachability-aware pair exactly as
  \<open>unit_step_for_lifted\<close> reconstructs it: \<open>assemble_env_abs\<close> routes payloads
  through \<^const>\<open>combine_env\<close> rather than joining them. The construction is
  generic in \<open>tf\<close> and uses only \<^locale>\<open>sound_transfer_for\<close> plus an exact
  \<open>empty_pred\<close>.
\<close>

text \<open>
  The g=Bot case concretizes through \<^const>\<open>combine_env\<close> at \<open>bot\<close>, not as \<open>\<lbrakk>d0\<rbrakk>\<close>
  unchanged: coarser than what \<^const>\<open>unit_step_for_lifted\<close> actually preserves (sound,
  since \<open>\<lbrakk>combine_env gs d0 bot\<rbrakk> \<subseteq> \<lbrakk>d0\<rbrakk>\<close> whenever \<open>bot\<close> is more precise than an unrelated
  live value), but this is what lets every obligation below reduce directly to the existing
  \<open>gamma_unit\<close>-based lemmas at a literal \<open>g := bot\<close>, with no purity side-condition on \<open>d0\<close>.
\<close>

definition gamma_unit_lifted ::
  "(vname => bool) => 'a::sound_domain abs_state lifted => 'a abs_state lifted => store set"
where
  "gamma_unit_lifted gs d g =
     (case d of Bot \<Rightarrow> {} | Lifted d0 \<Rightarrow> gamma_unit gs d0 (case g of Bot \<Rightarrow> bot | Lifted g0 \<Rightarrow> g0))"

lemma gamma_unit_lifted_Bot [simp]: "gamma_unit_lifted gs Bot g = {}"
  unfolding gamma_unit_lifted_def by simp

lemma gamma_unit_lifted_Lifted_Bot [simp]:
  "gamma_unit_lifted gs (Lifted d0) Bot = gamma_unit gs d0 bot"
  unfolding gamma_unit_lifted_def by simp

lemma gamma_unit_lifted_Lifted_Lifted [simp]:
  "gamma_unit_lifted gs (Lifted d0) (Lifted g0) = gamma_unit gs d0 g0"
  unfolding gamma_unit_lifted_def by simp

lemma gamma_unit_lifted_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_unit_lifted gs d g \<subseteq> gamma_unit_lifted gs d' g'"
proof (cases d)
  case Bot
  then show ?thesis by simp
next
  case (Lifted d0)
  with assms obtain d0' where d0': "d' = Lifted d0'" "d0 \<le> d0'" by (cases d') auto
  have gle: "(case g of Bot \<Rightarrow> bot | Lifted g0 \<Rightarrow> g0) \<le> (case g' of Bot \<Rightarrow> bot | Lifted g0 \<Rightarrow> g0)"
    using assms(2) by (cases g; cases g') (auto simp: bot.extremum)
  show ?thesis
    unfolding Lifted d0'
    unfolding gamma_unit_lifted_def
    using gamma_unit_mono[OF d0'(2) gle]
    by simp
qed

text \<open>The exact predicate that lets a lifted-reachable transfer result normalize correctly:
  \<open>empty_pred\<close> agrees with \<^const>\<open>is_empty_state\<close> everywhere.\<close>

lemma gamma_unit_step_sound_for_lifted:
  assumes sound: "sound_transfer_for gs tf"
    and exact: "\<And>s. empty_pred s = is_empty_state s"
  shows "edge_collect a (gamma_unit_lifted gs d g) \<subseteq>
           (case dg_spec_step (unit_dg_spec_for_lifted gs empty_pred tf) a d g of (g', d') \<Rightarrow>
              gamma_unit_lifted gs d' g')"
proof (cases d)
  case Bot
  then show ?thesis by simp
next
  case (Lifted d0)
  obtain m where m_def: "assemble_env_abs gs d g = Lifted m"
    unfolding Lifted by simp
  have gamma_eq: "gamma_unit_lifted gs d g = \<lbrakk>m\<rbrakk>"
    using m_def unfolding Lifted gamma_unit_lifted_def gamma_unit_def
    by (cases g) auto
  have base: "edge_collect a \<lbrakk>m\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a m\<rbrakk>"
    using sound_transfer_for.edge_collect_apply_tf_sound_for[OF sound, where a = a] .
  have step: "dg_spec_step (unit_dg_spec_for_lifted gs empty_pred tf) a d g
                = (map_lift (restrict_global_for gs) (normalize_lift empty_pred (apply_tf tf a m)),
                   map_lift (restrict_local_for gs) (normalize_lift empty_pred (apply_tf tf a m)))"
    unfolding dg_spec_step_unit_for_lifted unit_step_for_lifted_def
    by (simp add: m_def Let_def transfer_lift_def)
  show ?thesis
    unfolding gamma_eq step
  proof (cases "empty_pred (apply_tf tf a m)")
    case True
    with exact have "\<lbrakk>apply_tf tf a m\<rbrakk> = {}"
      using is_empty_state_iff_gamma_state_empty by blast
    with base have "edge_collect a \<lbrakk>m\<rbrakk> = {}" by blast
    then show "edge_collect a \<lbrakk>m\<rbrakk> \<subseteq>
        (case (map_lift (restrict_global_for gs) (normalize_lift empty_pred (apply_tf tf a m)),
               map_lift (restrict_local_for gs) (normalize_lift empty_pred (apply_tf tf a m)))
          of (g', d') \<Rightarrow> gamma_unit_lifted gs d' g')"
      by (simp add: True)
  next
    case False
    then show "edge_collect a \<lbrakk>m\<rbrakk> \<subseteq>
        (case (map_lift (restrict_global_for gs) (normalize_lift empty_pred (apply_tf tf a m)),
               map_lift (restrict_local_for gs) (normalize_lift empty_pred (apply_tf tf a m)))
          of (g', d') \<Rightarrow> gamma_unit_lifted gs d' g')"
      using base
      by (simp add: gamma_unit_def combine_env_restrict_id)
  qed
qed

lemma gamma_unit_combine_sound_for_lifted:
  assumes reserved: "reserved_ret_var gs"
    and exact: "\<And>s. empty_pred s = is_empty_state s"
    and sc: "s \<in> gamma_unit_lifted gs dc g" and tc: "t \<in> gamma_unit_lifted gs de g"
  shows "combine_collect gs (ci_dst dst) s t \<in>
           (case dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) dst dc de g of (g', d') \<Rightarrow>
              gamma_unit_lifted gs d' g')"
proof -
  obtain dc0 where dc0: "dc = Lifted dc0" using sc by (cases dc) auto
  obtain de0 where de0: "de = Lifted de0" using tc by (cases de) auto
  define g0 where "g0 = (case g of Bot \<Rightarrow> bot | Lifted x \<Rightarrow> x)"
  have sc': "s \<in> gamma_unit gs dc0 g0"
    using sc unfolding dc0 g0_def gamma_unit_lifted_def by (cases g) auto
  have tc': "t \<in> gamma_unit gs de0 g0"
    using tc unfolding de0 g0_def gamma_unit_lifted_def by (cases g) auto
  have raw: "combine_collect gs (ci_dst dst) s t \<in>
               (case dgs_combine (unit_dg_spec_for gs tf) dst dc0 de0 g0 of (g', d') \<Rightarrow> gamma_unit gs d' g')"
    by (rule gamma_unit_combine_sound_for[OF reserved sc' tc'])
  have raw_eq: "dgs_combine (unit_dg_spec_for gs tf) dst dc0 de0 g0
                  = (let res = combine_assign (ci_dst dst) (de0 ret_var) (combine_env gs dc0 g0)
                     in (restrict_global_for gs res, restrict_local_for gs res))"
    unfolding dgs_combine_unit_dg_spec_for by simp
  have target: "dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) dst dc de g
                  = (let res = combine_assign (ci_dst dst) (de0 ret_var) (combine_env gs dc0 g0)
                     in (map_lift (restrict_global_for gs) (normalize_lift empty_pred res),
                         map_lift (restrict_local_for gs) (normalize_lift empty_pred res)))"
    unfolding dgs_combine_unit_dg_spec_for_lifted
    unfolding unit_combine_step_assign_for_lifted_def unit_combine_step_env_for_lifted_def
    by (simp add: dc0 de0 g0_def Let_def transfer_lift2_def restrict_global_for_local_join)
  show ?thesis
  proof (cases "empty_pred (combine_assign (ci_dst dst) (de0 ret_var) (combine_env gs dc0 g0))")
    case True
    have empty: "\<lbrakk>combine_assign (ci_dst dst) (de0 ret_var) (combine_env gs dc0 g0)\<rbrakk> = {}"
      using exact True is_empty_state_iff_gamma_state_empty by blast
    with raw raw_eq have "combine_collect gs (ci_dst dst) s t \<in> {}"
      by (simp add: Let_def gamma_unit_def combine_env_restrict_id)
    then show ?thesis
      using target True by simp
  next
    case False
    with raw raw_eq have "combine_collect gs (ci_dst dst) s t \<in>
        \<lbrakk>combine_assign (ci_dst dst) (de0 ret_var) (combine_env gs dc0 g0)\<rbrakk>"
      by (simp add: Let_def gamma_unit_def combine_env_restrict_id)
    with target False show ?thesis
      by (simp add: Let_def gamma_unit_def normalize_lift_def combine_env_restrict_id)
  qed
qed

lemma gamma_unit_enter_sound_for_lifted:
  assumes sound: "sound_transfer_for gs tf"
    and exact: "\<And>s. empty_pred s = is_empty_state s"
    and sc: "s \<in> gamma_unit_lifted gs dc g"
  shows "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
           (case dgs_enter (unit_dg_spec_for_lifted gs empty_pred tf) ci dc g of (g', d') \<Rightarrow>
              gamma_unit_lifted gs d' g')"
proof -
  obtain dc0 where dc0: "dc = Lifted dc0" using sc by (cases dc) auto
  define g0 where "g0 = (case g of Bot \<Rightarrow> bot | Lifted x \<Rightarrow> x)"
  have sc': "s \<in> \<lbrakk>combine_env gs dc0 g0\<rbrakk>"
    using sc unfolding dc0 g0_def gamma_unit_lifted_def gamma_unit_def by (cases g) auto
  have base: "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> \<lbrakk>snd (enter\<^sup># tf ci (combine_env gs dc0 g0))\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_entry_for[OF sound sc']
    by (simp add: call_enter_CallEdge)
  have enter: "dgs_enter (unit_dg_spec_for_lifted gs empty_pred tf) ci dc g
                 = (map_lift (restrict_global_for gs) (normalize_lift empty_pred (snd (enter\<^sup># tf ci (combine_env gs dc0 g0)))),
                    map_lift (restrict_local_for gs) (normalize_lift empty_pred (snd (enter\<^sup># tf ci (combine_env gs dc0 g0)))))"
    unfolding dgs_enter_unit_dg_spec_for_lifted unit_step_for_lifted_def
    by (simp add: dc0 g0_def Let_def transfer_lift_def)
  show ?thesis
  proof (cases "empty_pred (snd (enter\<^sup># tf ci (combine_env gs dc0 g0)))")
    case True
    with exact base have "\<lbrakk>snd (enter\<^sup># tf ci (combine_env gs dc0 g0))\<rbrakk> = {}"
      using is_empty_state_iff_gamma_state_empty by blast
    with base show ?thesis using enter True by simp
  next
    case False
    with enter show ?thesis
      using base
      by (simp add: gamma_unit_def normalize_lift_def combine_env_restrict_id)
  qed
qed


theorem sound_dg_spec_unit_for_lifted:
  assumes sound: "sound_transfer_for gs tf"
    and reserved: "reserved_ret_var gs"
    and exact: "\<And>s. empty_pred s = is_empty_state s"
  shows "sound_dg_spec (unit_dg_spec_for_lifted gs empty_pred tf) (gamma_unit_lifted gs) gs"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_unit_lifted_mono)
  subgoal for a d g
    by (rule gamma_unit_step_sound_for_lifted[OF sound exact])
  subgoal premises prems using prems by (simp add: unit_dg_spec_for_lifted_def)
  subgoal premises prems
    by (rule gamma_unit_combine_sound_for_lifted[OF reserved exact prems])
  subgoal premises prems
    by (rule gamma_unit_enter_sound_for_lifted[OF sound exact prems])
  done
end
