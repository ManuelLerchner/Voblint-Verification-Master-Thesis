theory TD_Side_CFG
  imports State_Restriction "Voblint_VIMP.VIMP_Globals" "TD.TD_side"
    Strategy_Tree_Combinators
begin

(* TD_side defines a record field \<sigma> for its internal state; hide the short
   name so our \<sigma> variables (abstract state maps) are unambiguous. *)
hide_const (open) \<sigma>

section \<open>Side IP solver: generic base\<close>

text \<open>
  Generic base for the side-effecting interprocedural solver.

  \<open>side_env\<close> combines the local unknown at a program point with the
  join of the named global unknowns, over the locals/globals restriction
  algebra of @{theory Voblint_Core.State_Restriction}.

  The interprocedural strategy tree and transfer functions live in TD_Side_Tree;
  monotonicity and solver preconditions live in TD_Side_Eff_Bounds and TD_Side_Eff_Cone_Lemmas.
\<close>



(* The abstract state combined from the local unknown at v and the join of all
   named-global unknowns (glob_env).  At 'g = unit this is the single global
   unknown \<sigma> (Inr ()) (glob_env_unit). *)
definition side_env ::
  "(pp + 'g::finite => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> glob_env \<sigma>"

(* The base unfold: 23 call sites across the solver core reach past this
   definition via unfolding side_env_def. Left untagged: a locale
   abbreviation (ltr_gamma.gamma_ltr) is itself stated in terms of side_env,
   and eagerly expanding side_env elsewhere breaks the term-shape matching
   that abbreviation's own unfold relies on -- cite explicitly instead. *)
lemma side_env_apply:
  "side_env \<sigma> v = \<sigma> (Inl v) \<squnion> glob_env \<sigma>"
  unfolding side_env_def by (rule refl)

text \<open>
  Lifted counterpart of \<^const>\<open>side_env\<close>: the same reconstruction, cross-role
  (local slot against the accumulated global), so \<^const>\<open>assemble_local_global\<close>
  replaces \<open>\<squnion>\<close> for exactly the reason \<open>unit_edge_tree\<close>'s reconstruction does
  (AD-52) -- a \<open>Bot\<close> local unknown must dominate rather than be resurrected by
  a live global.
\<close>
definition side_env_lift ::
  "(pp + 'g::finite => 'a::bounded_semilattice_sup_bot abs_state lifted) => pp => 'a abs_state lifted" where
  "side_env_lift \<sigma> v = assemble_local_global (\<sigma> (Inl v)) (glob_env \<sigma>)"

(* Reading a single named global g combined with the locals at v. *)
definition side_env_g ::
  "(pp + 'g => 'a::bounded_semilattice_sup_bot abs_state) => 'g => pp => 'a abs_state"
where
  "side_env_g \<sigma> g v = \<sigma> (Inl v) \<squnion> \<sigma> (Inr g)"

lemma side_env_eq_side_env_g:
  "side_env \<sigma> v = side_env_g \<sigma> () v"
  unfolding side_env_def side_env_g_def by (simp add: glob_env_unit)

(* Reading a single named global is a tighter view than the joined global
   environment: side_env_g picks one slot, side_env joins all of them. *)
lemma side_env_g_le_side_env:
  fixes \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "side_env_g \<sigma> g v \<le> side_env \<sigma> v"
  unfolding side_env_g_def side_env_def
  by (rule sup_mono[OF order_refl glob_env_upper])


subsection \<open>Unit-global effectful trees\<close>

text \<open>
  Unit-global effectful trees query the local program point and the unit global
  slot, compute one abstract post-state, then split that result between the local
  Answer and the global Side contribution consumed by TD_side.
\<close>

text \<open>
  Both trees reconstruct one local input (or two, for combine) from the queried
  unknown and the current global.  With the solver payload lifted (AD-52), that
  reconstruction is cross-role -- the queried local unknown against the accumulated
  global -- so it goes through \<^const>\<open>assemble_local_global\<close> rather than plain
  \<open>\<squnion>\<close>: a \<open>Bot\<close> local unknown (this control-flow point is unreachable) dominates
  regardless of what the global side holds, while a \<open>Bot\<close> global (no side
  contribution published yet) is neutral. The domain transfer \<open>f\<close> / \<open>combine\<^sup>#\<close> only
  ever runs on an actually reconstructed \<open>Lifted\<close> input -- \<^const>\<open>transfer_lift\<close>
  short-circuits \<open>Bot\<close> in without calling \<open>f\<close> at all, and additionally re-collapses
  a live input whose own transfer result lands on witness-bottom, exactly as the
  raw pipeline's \<open>is_bot_state\<close> check did, but now recorded structurally in the
  result rather than erased back to a raw value indistinguishable from a live
  bottom-valued state (AD-52's core finding). A reachable input's split reuses
  \<^const>\<open>map_lift\<close>: \<open>Bot\<close> in gives \<open>Bot\<close> Answer and \<open>Bot\<close> Side (no local result, no
  side contribution -- a dead edge publishes nothing), \<open>Lifted r\<close> gives the ordinary
  local/global restriction of \<open>r\<close>, lifted.
\<close>

definition unit_edge_tree ::
  "(vname => bool)
   => ('a::sound_domain abs_state => 'a abs_state)
   => (unit, 'a) edge_tf_tree"
where
  "unit_edge_tree gs f u = do {
     su <- read_local u;
     g <- read_global ();
     let res = transfer_lift is_bot_state f (assemble_local_global su g);
     depend_on () (map_lift (restrict_global_for gs) res)
       (answer (map_lift (restrict_local_for gs) res))
   }"

(* Procedure-return combine: query the caller local cc, the callee-exit local
   ex, and the global; reassemble both operands and split the result of the
   supplied combine operation cmb into a local Answer and a global Side.  cmb is
   a parameter rather than the structural locals-from-caller/globals-from-callee
   formula: an analysis provides its own sound over-approximation of the concrete
   return combination, and one builder then serves both roles of Goblint's
   combine interface -- the destination-free environment merge (combine_env\<^sup>#)
   and the destination-aware whole combine (combine_env\<^sup># followed by
   combine_assign\<^sup>#).  Either reconstructed operand being Bot means no concrete
   predecessor reaches the combine (an unreachable call site, or a callee exit
   reached only from dead code), so the combine as a whole is dead too --
   assemble_local_global's Bot dominance on both operands, threaded through
   transfer_lift2, gives this for free without a separate is_bot_state test. *)
definition unit_combine_tree ::
  "(vname => bool)
   => ('a::sound_domain abs_state => 'a abs_state => 'a abs_state)
   => pp => pp
   => (pp, unit, 'a abs_state lifted) strategy_tree"
where
  "unit_combine_tree gs cmb cc ex = do {
     sc <- read_local cc;
     se <- read_local ex;
     g <- read_global ();
     let res = transfer_lift2 is_bot_state cmb
                 (assemble_local_global sc g) (assemble_local_global se g);
     depend_on () (map_lift (restrict_global_for gs) res)
       (answer (map_lift (restrict_local_for gs) res))
   }"


lemma traverse_unit_edge_tree:
  "traverse_rhs (unit_edge_tree gs f u) \<sigma> = map_lift (restrict_local_for gs) (res_edge f u \<sigma>)"
  unfolding unit_edge_tree_def res_edge_def
  by (simp add: Let_def)

(* The tree's single Side contribution to the global slot is the global
   restriction of the result. *)
lemma sides_unit_edge_tree_Inr:
  "sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inr ()) =
   map_lift (restrict_global_for gs) (res_edge f u \<sigma>)"
  unfolding unit_edge_tree_def res_edge_def
  by (simp add: Let_def)

text \<open>
  \<open>unit_edge_contribution\<close> is \<^const>\<open>unit_edge_tree\<close>'s body without the
  \<open>depend_on\<close>/\<open>answer\<close> split: it reads the same predecessor local and global,
  computes the same unsplit \<open>res_edge\<close> value, and answers it directly,
  publishing no \<^const>\<open>Side\<close> at all (\<open>issue #121\<close>). A CFG merge node with
  several such contribution trees can therefore be folded via the existing
  \<open>fold_rhs_trees\<close> combinator and split \<^emph>\<open>once\<close>, instead of each predecessor
  edge publishing (and each sibling observing) its own intermediate \<open>Side\<close>
  -- see \<open>publish_split_lifted\<close> in the RHS-tree theory that already imports
  this one.\<close>

definition unit_edge_contribution ::
  "(vname => bool)
   => ('a::sound_domain abs_state => 'a abs_state)
   => (unit, 'a) edge_tf_tree"
where
  "unit_edge_contribution gs f u = do {
     su <- read_local u;
     g <- read_global ();
     answer (transfer_lift is_bot_state f (assemble_local_global su g))
   }"

lemma traverse_unit_edge_contribution:
  "traverse_rhs (unit_edge_contribution gs f u) \<sigma> = res_edge f u \<sigma>"
  unfolding unit_edge_contribution_def res_edge_def by simp

lemma sides_of_rhs_unit_edge_contribution [simp]:
  "sides_of_rhs (unit_edge_contribution gs f u) \<sigma> = \<bottom>"
  unfolding unit_edge_contribution_def by (simp add: bot_fun_def)

text \<open>\<open>unit_edge_contribution\<close> queries exactly the same keys as
  \<^const>\<open>unit_edge_tree\<close> -- \<^const>\<open>dep_aux\<close> only accumulates at
  \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> nodes and passes straight through a
  \<^const>\<open>Side\<close> (\<open>dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t\<close>; its payload \<open>d\<close> is a
  plain value, not a tree, so it hides no further dependency), and the two
  trees share the identical \<open>QueryL\<close>/\<open>QueryG\<close> prefix, differing only in
  whether that prefix ends in \<open>depend_on ... (answer ...)\<close> or plain \<open>answer\<close>.
  So this is an equality, not merely the subset the buffered publication
  needs.\<close>

lemma dep_aux_unit_edge_contribution_eq_unit_edge_tree:
  "dep_aux \<sigma> (unit_edge_contribution gs f u) = dep_aux \<sigma> (unit_edge_tree gs f u)"
  unfolding unit_edge_contribution_def unit_edge_tree_def by (simp add: Let_def)

(* Reassembling the tree's local Answer and global Side recovers the full result:
   map_lift distributes over assemble_local_global's Lifted/Lifted case exactly as
   restrict_local_for_global_join does for the unlifted join, and both sides are
   Bot together when res_edge is Bot. *)
lemma etf_full_unit_edge_tree:
  "etf_full (unit_edge_tree gs f u) \<sigma> = res_edge f u \<sigma>"
  unfolding etf_full_def
  apply (simp add: all_sides_eq_sides_Inr_unit traverse_unit_edge_tree sides_unit_edge_tree_Inr)
  apply (cases "res_edge f u \<sigma>")
   apply simp
  apply (simp add: restrict_local_for_global_join)
  done

(* Both traverse_rhs and its single Side are map_lift of the same res_edge, and
   map_lift only ever produces Bot from a Bot input, so the two collapse together. *)
lemma reachability_coherent_unit_edge_tree:
  "reachability_coherent_tree (unit_edge_tree gs f u) \<sigma>"
  unfolding reachability_coherent_tree_def
  by (cases "res_edge f u \<sigma>")
     (simp_all add: traverse_unit_edge_tree all_sides_eq_sides_Inr_unit sides_unit_edge_tree_Inr)



(* The unit-global combine tree returns the combined locals as its Answer; with a
   destination-aware cmb these include the destination the call assigns to. *)
lemma traverse_unit_combine_tree:
  "traverse_rhs (unit_combine_tree gs cmb cc ex) \<sigma>
     = map_lift (restrict_local_for gs) (res_combine cmb cc ex \<sigma>)"
  unfolding unit_combine_tree_def res_combine_def
  by (simp add: Let_def)

(* The unit-global combine tree contributes the combined globals to the global slot. *)
lemma sides_unit_combine_tree_Inr:
  "sides_of_rhs (unit_combine_tree gs cmb cc ex) \<sigma> (Inr ()) =
   map_lift (restrict_global_for gs) (res_combine cmb cc ex \<sigma>)"
  unfolding unit_combine_tree_def res_combine_def
  by (simp add: Let_def)

(* The unit-global combine tree reassembles to the supplied combine's result. *)
lemma etf_full_unit_combine_tree:
  "etf_full (unit_combine_tree gs cmb cc ex) \<sigma> = res_combine cmb cc ex \<sigma>"
  unfolding etf_full_def
  apply (simp add: all_sides_eq_sides_Inr_unit traverse_unit_combine_tree sides_unit_combine_tree_Inr)
  apply (cases "res_combine cmb cc ex \<sigma>")
   apply simp
  apply (simp add: restrict_local_for_global_join)
  done

(* Both traverse_rhs and its single Side are map_lift of the same res_combine,
   so they collapse together exactly as in the unit_edge_tree case. *)
lemma reachability_coherent_unit_combine_tree:
  "reachability_coherent_tree (unit_combine_tree gs cmb cc ex) \<sigma>"
  unfolding reachability_coherent_tree_def
  by (cases "res_combine cmb cc ex \<sigma>")
     (simp_all add: traverse_unit_combine_tree all_sides_eq_sides_Inr_unit
       sides_unit_combine_tree_Inr)

text \<open>Side-free counterpart of \<^const>\<open>unit_combine_tree\<close>, mirroring
  \<^const>\<open>unit_edge_contribution\<close> (\<open>issue #121\<close>).\<close>

definition unit_combine_contribution ::
  "('a::sound_domain abs_state => 'a abs_state => 'a abs_state) => pp => pp
   => (pp, unit, 'a abs_state lifted) strategy_tree"
where
  "unit_combine_contribution cmb cc ex = do {
     sc <- read_local cc;
     se <- read_local ex;
     g <- read_global ();
     answer (transfer_lift2 is_bot_state cmb
               (assemble_local_global sc g) (assemble_local_global se g))
   }"

lemma traverse_unit_combine_contribution:
  "traverse_rhs (unit_combine_contribution cmb cc ex) \<sigma> = res_combine cmb cc ex \<sigma>"
  unfolding unit_combine_contribution_def res_combine_def by simp

lemma sides_of_rhs_unit_combine_contribution [simp]:
  "sides_of_rhs (unit_combine_contribution cmb cc ex) \<sigma> = \<bottom>"
  unfolding unit_combine_contribution_def by (simp add: bot_fun_def)

lemma dep_aux_unit_combine_contribution_eq_unit_combine_tree:
  "dep_aux \<sigma> (unit_combine_contribution cmb cc ex) = dep_aux \<sigma> (unit_combine_tree gs cmb cc ex)"
  unfolding unit_combine_contribution_def unit_combine_tree_def by (simp add: Let_def)


subsection \<open>Local-only effectful edge trees\<close>

text \<open>
  When an edge transfer preserves globals and only reads locals, the tree can
  query the source local unknown without @{term QueryG}.  Soundness and
  post-fixpoint bounds use @{const etf_full} joined with @{const glob_env}.
\<close>

definition local_bot_on_locals ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> bool"
where
  "local_bot_on_locals gs g \<longleftrightarrow> (\<forall>x. \<not> gs x \<longrightarrow> g x = bot)"

lemma local_bot_join:
  assumes "local_bot_on_locals gs (a :: 'a::bounded_semilattice_sup_bot abs_state)"
    and "local_bot_on_locals gs b"
  shows "local_bot_on_locals gs (a \<squnion> b)"
  using assms unfolding local_bot_on_locals_def by (auto simp: sup_fun_def)

lemma glob_env_local_bot:
  fixes \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  assumes inr: "\<And>g. local_bot_on_locals gs (\<sigma> (Inr g))"
  shows "local_bot_on_locals gs (glob_env \<sigma>)"
  unfolding local_bot_on_locals_def glob_env_def abs_join_set_def
proof (clarify)
  fix x
  assume ng: "\<not> gs x"
  have elem_bot: "\<And>a. a \<in> range (\<lambda>g. \<sigma> (Inr g)) \<Longrightarrow> a x = bot"
    using inr ng unfolding local_bot_on_locals_def by auto
  have fold_bot:
    "\<And>A. finite A \<Longrightarrow> A \<subseteq> range (\<lambda>g. \<sigma> (Inr g)) \<Longrightarrow>
      Finite_Set.fold (\<squnion>) bot A x = bot"
  proof -
    fix A
    assume finA: "finite A"
      and subA: "A \<subseteq> range (\<lambda>g. \<sigma> (Inr g))"
    from finA subA show "Finite_Set.fold (\<squnion>) bot A x = bot"
    proof (induction A rule: finite_induct)
      case empty
      then show ?case by simp
    next
      case (insert a A)
      have subA: "A \<subseteq> range (\<lambda>g. \<sigma> (Inr g))"
        using insert.prems by auto
      have ax: "a x = bot"
        using insert.prems elem_bot by auto
      have ih: "Finite_Set.fold (\<squnion>) bot A x = bot"
        using insert.IH[OF subA] .
      have fold_insert:
        "Finite_Set.fold (\<squnion>) bot (insert a A) =
         a \<squnion> Finite_Set.fold (\<squnion>) bot A"
        using insert.hyps by (simp)
      have "Finite_Set.fold (\<squnion>) bot (insert a A) x =
            (a \<squnion> Finite_Set.fold (\<squnion>) bot A) x"
        using fold_insert by simp
      also have "... = bot"
        using ax ih by (simp add: sup_fun_def)
      finally show ?case .
    qed
  qed
  show "Finite_Set.fold (\<squnion>) bot (range (\<lambda>g. \<sigma> (Inr g))) x = bot"
    using fold_bot by simp
qed

definition local_edge_invariant ::
  "(vname => bool) => ('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> bool"
where
  "local_edge_invariant gs f \<longleftrightarrow>
     (\<forall>su g. local_bot_on_locals gs g \<longrightarrow>
        f (restrict_local_for gs su \<squnion> g) =
        restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g)"

(* The direct instantiation of local_edge_invariant's definition, cited by
   domain instances instead of re-unfolding the quantified definition at
   every call site. *)
lemma local_edge_invariantD:
  "local_edge_invariant gs f \<Longrightarrow> local_bot_on_locals gs g \<Longrightarrow>
   f (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g"
  unfolding local_edge_invariant_def by blast

lemma local_edge_invariant_local_result:
  assumes inv: "local_edge_invariant gs f"
  shows "restrict_local_for gs (f (restrict_local_for gs su)) = f (restrict_local_for gs su)"
proof -
  have "f (restrict_local_for gs su \<squnion> bot) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> bot"
    using inv unfolding local_edge_invariant_def local_bot_on_locals_def
    by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
  then show ?thesis by simp
qed

lemma local_edge_invariant_comp:
  assumes f: "local_edge_invariant gs f"
    and h: "local_edge_invariant gs h"
  shows "local_edge_invariant gs (\<lambda>su. f (h su))"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals gs g"
  have h_step: "h (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (h (restrict_local_for gs su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  have h_local: "restrict_local_for gs (h (restrict_local_for gs su)) = h (restrict_local_for gs su)"
    using local_edge_invariant_local_result[OF h, of su] .
  show "f (h (restrict_local_for gs su \<squnion> g)) = restrict_local_for gs (f (h (restrict_local_for gs su))) \<squnion> g"
    using f lb h_step h_local unfolding local_edge_invariant_def by metis
qed

lemma local_edge_invariant_sup:
  assumes f: "local_edge_invariant gs f"
    and h: "local_edge_invariant gs h"
  shows "local_edge_invariant gs (\<lambda>su. f su \<squnion> h su)"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "'a abs_state"
  fix g :: "'a abs_state"
  assume lb: "local_bot_on_locals gs g"
  have f_step: "f (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (f (restrict_local_for gs su)) \<squnion> g"
    using f lb unfolding local_edge_invariant_def by blast
  have h_step: "h (restrict_local_for gs su \<squnion> g) = restrict_local_for gs (h (restrict_local_for gs su)) \<squnion> g"
    using h lb unfolding local_edge_invariant_def by blast
  show "f (restrict_local_for gs su \<squnion> g) \<squnion> h (restrict_local_for gs su \<squnion> g) =
        restrict_local_for gs (f (restrict_local_for gs su) \<squnion> h (restrict_local_for gs su)) \<squnion> g"
    using f_step h_step
    by (simp add: restrict_local_for_sup sup_assoc sup_left_commute sup_commute)
qed

text \<open>
  local_edge_tree never queries the global -- \<open>local_edge_action\<close> edges neither
  read nor write globals -- so unlike unit_edge_tree/unit_combine_tree there is no
  cross-role reconstruction here: the only source of \<open>Bot\<close> is the queried local
  unknown itself, propagated by \<^const>\<open>map_lift\<close>. Unlike unit_edge_tree, this
  cannot use \<^const>\<open>transfer_lift\<close>'s extra witness-bottom re-check on the
  reconstruction's own output: that output is always a \<^const>\<open>restrict_local_for\<close>-shaped
  value (\<open>bot\<close> at every global-role position by construction, from both
  \<open>restrict_local_for\<close> itself and \<open>restrict_global_for gs su\<close> being \<open>bot\<close> since
  \<open>su\<close> is already restrict_local'd), so \<^const>\<open>is_bot_state\<close> on it is vacuously
  true the moment the program has any global variable at all -- exactly AD-52's
  vacuity trap, applied to a reconstruction rather than a stored value. Plain
  structural propagation avoids it: only the queried unknown's own \<open>Bot\<close>-ness
  (a genuine reachability fact carried through the solver, not a syntactic
  artifact of restriction) can make this tree dead.
\<close>
definition local_edge_tree ::
  "(vname => bool) => ('a::sound_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "local_edge_tree gs f u = do {
     su <- read_local u;
     answer (map_lift
               (\<lambda>s. restrict_local_for gs (f (restrict_local_for gs s)) \<squnion> restrict_global_for gs s) su)
   }"

(* res_local names local_edge_tree's reconstructed result, mirroring res_edge. *)
definition res_local ::
  "(vname => bool) \<Rightarrow> ('a::sound_domain abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state lifted) \<Rightarrow> 'a abs_state lifted" where
  "res_local gs f u \<sigma> =
     map_lift
       (\<lambda>s. restrict_local_for gs (f (restrict_local_for gs s)) \<squnion> restrict_global_for gs s) (\<sigma> (Inl u))"

lemma traverse_local_edge_tree:
  "traverse_rhs (local_edge_tree gs f u) \<sigma> = res_local gs f u \<sigma>"
  unfolding local_edge_tree_def res_local_def by (simp add: seqcomp_tree.simps Let_def)

text \<open>
  res_local is monotone whenever f is, mirroring res_edge_mono: the reconstructed
  local/global split composes restrict_local_for/restrict_global_for/f under
  map_lift, all of which are monotone.
\<close>
lemma res_local_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes f_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> f s1 \<le> f s2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_local gs f u \<sigma>1 \<le> res_local gs f u \<sigma>2"
  unfolding res_local_def
proof (rule map_lift_mono[OF _ le_funD[OF le]])
  fix a b :: "'a abs_state"
  assume ab: "a \<le> b"
  show "restrict_local_for gs (f (restrict_local_for gs a)) \<squnion> restrict_global_for gs a
          \<le> restrict_local_for gs (f (restrict_local_for gs b)) \<squnion> restrict_global_for gs b"
    by (rule sup_mono[OF restrict_local_for_mono[OF f_mono[OF restrict_local_for_mono[OF ab]]]
          restrict_global_for_mono[OF ab]])
qed

lemma sides_local_edge_tree_Inr:
  "sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inr ()) = Bot"
  unfolding local_edge_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma local_bot_on_locals_restrict_global [intro]:
  "local_bot_on_locals gs (restrict_global_for gs \<sigma>)"
  unfolding restrict_global_for_def local_bot_on_locals_def by simp

text \<open>
  Role-aware lift of \<^const>\<open>local_bot_on_locals\<close> for a solver-facing global
  slot: \<open>Bot\<close> (no side contribution published) trivially satisfies "carries bot
  in its local components", since there is no reconstructed value to check;
  \<open>Lifted g\<close> constrains \<open>g\<close> pointwise exactly as before.
\<close>
definition local_bot_on_locals_lift ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state lifted \<Rightarrow> bool"
where
  "local_bot_on_locals_lift gs x = (case x of Bot \<Rightarrow> True | Lifted g \<Rightarrow> local_bot_on_locals gs g)"

lemma local_bot_on_locals_lift_Bot [simp]: "local_bot_on_locals_lift gs Bot"
  unfolding local_bot_on_locals_lift_def by simp

lemma local_bot_on_locals_lift_Lifted [simp]:
  "local_bot_on_locals_lift gs (Lifted g) = local_bot_on_locals gs g"
  unfolding local_bot_on_locals_lift_def by simp

lemma local_bot_on_locals_lift_join:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  assumes "local_bot_on_locals_lift gs a" and "local_bot_on_locals_lift gs b"
  shows "local_bot_on_locals_lift gs (a \<squnion> b)"
  using assms by (cases a; cases b) (auto intro: local_bot_join)

lemma local_bot_on_locals_lift_map_restrict_global [intro]:
  "local_bot_on_locals_lift gs (map_lift (restrict_global_for gs) x)"
  by (cases x) (simp_all add: local_bot_on_locals_restrict_global)

lemma le_restrict_global_for_when_local_bot:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes lb: "local_bot_on_locals gs a"
  assumes le: "a \<le> b"
  shows "a \<le> restrict_global_for gs b"
  unfolding restrict_global_for_def le_fun_def
proof (intro allI impI)
  fix x
  have ax: "a x \<le> b x"
    using le by (simp add: le_funD)
  show "a x \<le> (if gs x then b x else bot)"
    using ax lb unfolding local_bot_on_locals_def by (cases "gs x") auto

qed

lemma le_map_lift_restrict_global_for_when_local_bot_lift:
  fixes a b :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  assumes lb: "local_bot_on_locals_lift gs a"
  assumes le: "a \<le> b"
  shows "a \<le> map_lift (restrict_global_for gs) b"
proof (cases a)
  case Bot
  then show ?thesis by simp
next
  case (Lifted a')
  then obtain b' where b_eq: "b = Lifted b'" and le': "a' \<le> b'"
    using le by (cases b) auto
  have lb': "local_bot_on_locals gs a'"
    using lb Lifted by simp
  show ?thesis
    unfolding Lifted b_eq
    by (simp add: le_restrict_global_for_when_local_bot[OF lb' le'])
qed


lemma sides_inr_local_bot_unit_edge_tree:
  "local_bot_on_locals_lift gs (sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_edge_tree_Inr
    by (rule local_bot_on_locals_lift_map_restrict_global)
next
  case False
  then show ?thesis by simp
qed

lemma sides_inr_local_bot_local_edge_tree:
  "local_bot_on_locals_lift gs (sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inr g))"
  unfolding local_edge_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma sides_inr_local_bot_unit_combine_tree:
  "local_bot_on_locals_lift gs (sides_of_rhs (unit_combine_tree gs cmb cc ex) \<sigma> (Inr g))"
proof (cases "g = ()")
  case True
  show ?thesis unfolding True sides_unit_combine_tree_Inr
    by (rule local_bot_on_locals_lift_map_restrict_global)
next
  case False
  then show ?thesis by simp
qed

lemma all_sides_local_edge_tree:
  "all_sides (local_edge_tree gs f u) \<sigma> = Bot"
  unfolding local_edge_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma sides_local_edge_tree_Inl:
  "sides_of_rhs (local_edge_tree gs f u) \<sigma> (Inl u') = Bot"
  unfolding local_edge_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma etf_full_local_edge_tree:
  "etf_full (local_edge_tree gs f u) \<sigma> = res_local gs f u \<sigma>"
  unfolding etf_full_def traverse_local_edge_tree all_sides_local_edge_tree
  by (cases "res_local gs f u \<sigma>") simp_all

(* all_sides is unconditionally Bot for local_edge_tree, so coherence holds
   independently of what traverse_rhs is. *)
lemma reachability_coherent_local_edge_tree:
  "reachability_coherent_tree (local_edge_tree gs f u) \<sigma>"
  unfolding reachability_coherent_tree_def by (simp add: all_sides_local_edge_tree)

lemma etf_collecting_full_local_edge_tree:
  "etf_collecting_full_lift (local_edge_tree gs f u) \<sigma> =
   assemble_local_global (res_local gs f u \<sigma>) (glob_env \<sigma>)"
  unfolding etf_collecting_full_lift_def etf_collecting_full_with_def etf_full_local_edge_tree
  by (rule refl)

lemma dep_aux_local_edge_tree:
  "dep_aux \<sigma>1 (local_edge_tree gs f u) = dep_aux \<sigma>2 (local_edge_tree gs f u)"
  unfolding local_edge_tree_def by simp

lemma etf_collecting_full_le_side_env:
  fixes t :: "(pp, 'g::finite, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
    and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state" and w :: pp
  assumes le: "etf_full t \<sigma> \<le> side_env \<sigma> w"
  shows "etf_collecting_full t \<sigma> \<le> side_env \<sigma> w"
proof -
  have "etf_collecting_full t \<sigma> = etf_full t \<sigma> \<squnion> glob_env \<sigma>"
    unfolding etf_collecting_full_def etf_collecting_full_with_def ..
  also have "\<dots> \<le> side_env \<sigma> w \<squnion> glob_env \<sigma>"
    using le by (rule sup_mono[OF _ order_refl])
  also have "\<dots> = side_env \<sigma> w"
    unfolding side_env_def by (simp add: sup_assoc sup_commute sup_left_commute)
  finally show ?thesis .
qed

text \<open>
  Lifted counterpart: cross-role reconstruction throughout, so \<^const>\<open>side_env_lift\<close>
  bounds \<^const>\<open>etf_collecting_full_lift\<close> via \<open>assemble_local_global_mono\<close>
  rather than plain \<open>sup_mono\<close> -- a \<open>Bot\<close> local answer under a \<open>Bot\<close> bound at \<open>w\<close>
  stays \<open>Bot\<close> on both sides regardless of \<open>glob_env\<close>.
\<close>
lemma etf_collecting_full_le_side_env_lift:
  fixes t :: "(pp, 'g::finite, 'a::sound_domain abs_state lifted) strategy_tree"
    and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state lifted" and w :: pp
  assumes le: "etf_full t \<sigma> \<le> side_env_lift \<sigma> w"
  shows "etf_collecting_full_lift t \<sigma> \<le> side_env_lift \<sigma> w"
proof -
  have "etf_collecting_full_lift t \<sigma> = assemble_local_global (etf_full t \<sigma>) (glob_env \<sigma>)"
    unfolding etf_collecting_full_lift_def etf_collecting_full_with_def ..
  also have "\<dots> \<le> assemble_local_global (side_env_lift \<sigma> w) (glob_env \<sigma>)"
    by (rule assemble_local_global_mono[OF le order_refl])
  also have "\<dots> = side_env_lift \<sigma> w"
    unfolding side_env_lift_def
    by (cases "\<sigma> (Inl w)"; cases "glob_env \<sigma>") (simp_all add: sup_assoc sup_left_idem)
  finally show ?thesis .
qed

lemma id_local_edge_invariant: "local_edge_invariant gs (\<lambda>env. env)"
  unfolding local_edge_invariant_def by (simp add: restrict_local_for_idem)


text \<open>
  Lifted callers only ever have a raw local witness \<open>su\<close> (from case-splitting
  \<open>\<sigma> (Inl u)\<close> against a concrete membership witness) together with the raw
  global contribution \<open>g'\<close> reconstructed from \<open>\<sigma> (Inr ())\<close> -- \<open>bot\<close> when it is
  itself \<open>Bot\<close>, its payload when \<open>Lifted\<close>, exactly \<open>gamma_state_lift_assemble_local_global\<close>'s
  \<open>g'\<close>. Stated directly over \<open>su\<close>/\<open>g'\<close> rather than \<open>\<sigma>\<close>, this is the same algebraic
  fact the pre-lift version proved, letting every call site below reuse it unchanged.
\<close>
lemma local_edge_invariant_side_env_eq:
  fixes f :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and su g' :: "'a abs_state"
  assumes inv: "local_edge_invariant gs f"
  assumes lb: "local_bot_on_locals gs g'"
  shows "f (su \<squnion> g') =
    restrict_local_for gs (f (restrict_local_for gs su)) \<squnion>
    restrict_global_for gs su \<squnion> g'"
proof -
  have rg: "local_bot_on_locals gs (restrict_global_for gs su)"
    by (rule local_bot_on_locals_restrict_global)
  have g: "local_bot_on_locals gs (restrict_global_for gs su \<squnion> g')"
    by (rule local_bot_join[OF rg lb])
  have env: "su \<squnion> g' = restrict_local_for gs su \<squnion> (restrict_global_for gs su \<squnion> g')"
    using restrict_local_for_global_join[of gs su] by (simp add: sup_commute sup_left_commute)
  have step: "f (restrict_local_for gs su \<squnion> (restrict_global_for gs su \<squnion> g')) =
              restrict_local_for gs (f (restrict_local_for gs su)) \<squnion>
              (restrict_global_for gs su \<squnion> g')"
    using local_edge_invariantD[OF inv g] .
  show ?thesis
    by (simp only: env step sup_assoc)
qed

lemma Inl_dep_aux_local_edge_tree:
  "Inl u \<in> dep_aux \<sigma> (local_edge_tree gs f u)"
  unfolding local_edge_tree_def by simp

subsection \<open>Local branch tree: forward-feasibility branch for local-only guards\<close>

text \<open>
  \<open>local_branch_tree\<close> is \<open>local_edge_tree\<close>'s counterpart for a branch edge
  whose guard is \<^const>\<open>local_edge_action\<close>-classified (no global mention).
  Generic over any lifted local transfer \<open>h\<close> -- \<open>branch_lifted\<close> for a
  domain's own interpreted \<open>backward_domain_refined\<close> locale, at the call
  site that wires this in -- it runs \<open>h\<close> through \<^const>\<open>bind_lift\<close> instead
  of \<^const>\<open>map_lift\<close>: a genuinely infeasible \<open>h\<close> (\<^const>\<open>Bot\<close>) collapses the
  whole tree to \<^const>\<open>Bot\<close> structurally, matching Goblint's \<open>Deadcode\<close> as an
  outer control-flow fact, rather than producing a \<^const>\<open>Lifted\<close> answer whose
  coordinates happen to be pointwise \<^const>\<open>bot\<close>. A reachable branch
  (\<^const>\<open>Lifted\<close> \<open>r\<close>) is reassembled exactly as \<open>local_edge_tree\<close> reassembles
  an ordinary local transfer: \<open>r\<close>'s own local part, joined with the pre-edge
  globals of the queried unknown -- never with anything \<open>h\<close> itself might have
  produced at global-role positions.
\<close>

definition local_branch_tree ::
  "(vname => bool) => ('a::sound_domain abs_state => 'a abs_state lifted)
   => (unit, 'a) edge_tf_tree"
where
  "local_branch_tree gs h u = do {
     su <- read_local u;
     answer (bind_lift su (%s.
       map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                 (h (restrict_local_for gs s))))
   }"

(* res_local_branch names local_branch_tree's reconstructed result, mirroring res_local. *)
definition res_local_branch ::
  "(vname => bool) => ('a::sound_domain abs_state => 'a abs_state lifted) => pp
   => (pp + unit => 'a abs_state lifted) => 'a abs_state lifted" where
  "res_local_branch gs h u \<sigma> =
     bind_lift (\<sigma> (Inl u)) (%s.
       map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                 (h (restrict_local_for gs s)))"

lemma traverse_local_branch_tree:
  "traverse_rhs (local_branch_tree gs h u) \<sigma> = res_local_branch gs h u \<sigma>"
  unfolding local_branch_tree_def res_local_branch_def by (simp add: seqcomp_tree.simps Let_def)

text \<open>
  Monotone whenever \<open>h\<close> is -- unlike \<^const>\<open>res_local\<close>, no side condition on
  an arbitrary raw \<open>f\<close> is needed here since \<open>h\<close>'s own \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close>
  split is already threaded structurally through \<^const>\<open>bind_lift\<close>.
\<close>
lemma res_local_branch_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit => 'a::sound_domain abs_state lifted"
  assumes h_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> h s1 \<le> h s2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_local_branch gs h u \<sigma>1 \<le> res_local_branch gs h u \<sigma>2"
  unfolding res_local_branch_def
proof (cases "\<sigma>1 (Inl u)")
  case Bot
  then show "bind_lift (\<sigma>1 (Inl u)) (%s. map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                (h (restrict_local_for gs s)))
      \<le> bind_lift (\<sigma>2 (Inl u)) (%s. map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                (h (restrict_local_for gs s)))"
    by simp
next
  case (Lifted a)
  from le_funD[OF le, of "Inl u"] Lifted obtain b where b_eq: "\<sigma>2 (Inl u) = Lifted b" and ab: "a \<le> b"
    by (cases "\<sigma>2 (Inl u)") auto
  have hb: "h (restrict_local_for gs a) \<le> h (restrict_local_for gs b)"
    by (rule h_mono[OF restrict_local_for_mono[OF ab]])
  have "map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs a) (h (restrict_local_for gs a))
      \<le> map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs b) (h (restrict_local_for gs b))"
    using hb
  proof (cases "h (restrict_local_for gs a)")
    case Bot
    then show ?thesis by simp
  next
    case (Lifted ra)
    with hb obtain rb where hb_eq: "h (restrict_local_for gs b) = Lifted rb" and rab: "ra \<le> rb"
      by (cases "h (restrict_local_for gs b)") auto
    show ?thesis
      unfolding Lifted hb_eq
      by (simp only: map_lift_Lifted less_eq_lifted.simps(3))
         (rule sup_mono[OF restrict_local_for_mono[OF rab] restrict_global_for_mono[OF ab]])
  qed
  then show "bind_lift (\<sigma>1 (Inl u)) (%s. map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                (h (restrict_local_for gs s)))
      \<le> bind_lift (\<sigma>2 (Inl u)) (%s. map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs s)
                (h (restrict_local_for gs s)))"
    unfolding Lifted b_eq by simp
qed

lemma sides_local_branch_tree_Inr:
  "sides_of_rhs (local_branch_tree gs h u) \<sigma> (Inr ()) = Bot"
  unfolding local_branch_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma sides_local_branch_tree_Inl:
  "sides_of_rhs (local_branch_tree gs h u) \<sigma> (Inl u') = Bot"
  unfolding local_branch_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma all_sides_local_branch_tree:
  "all_sides (local_branch_tree gs h u) \<sigma> = Bot"
  unfolding local_branch_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

lemma etf_full_local_branch_tree:
  "etf_full (local_branch_tree gs h u) \<sigma> = res_local_branch gs h u \<sigma>"
  unfolding etf_full_def traverse_local_branch_tree all_sides_local_branch_tree
  by (cases "res_local_branch gs h u \<sigma>") simp_all

lemma reachability_coherent_local_branch_tree:
  "reachability_coherent_tree (local_branch_tree gs h u) \<sigma>"
  unfolding reachability_coherent_tree_def by (simp add: all_sides_local_branch_tree)

lemma etf_collecting_full_local_branch_tree:
  "etf_collecting_full_lift (local_branch_tree gs h u) \<sigma> =
   assemble_local_global (res_local_branch gs h u \<sigma>) (glob_env \<sigma>)"
  unfolding etf_collecting_full_lift_def etf_collecting_full_with_def etf_full_local_branch_tree
  by (rule refl)

lemma dep_aux_local_branch_tree:
  "dep_aux \<sigma>1 (local_branch_tree gs h u) = dep_aux \<sigma>2 (local_branch_tree gs h u)"
  unfolding local_branch_tree_def by simp

lemma Inl_dep_aux_local_branch_tree:
  "Inl u \<in> dep_aux \<sigma> (local_branch_tree gs h u)"
  unfolding local_branch_tree_def by simp

lemma sides_inr_local_bot_local_branch_tree:
  "local_bot_on_locals_lift gs (sides_of_rhs (local_branch_tree gs h u) \<sigma> (Inr g))"
  unfolding local_branch_tree_def by (simp add: seqcomp_tree.simps split: lifted.splits)

text \<open>
  Explicit witnesses for \<^const>\<open>local_branch_tree\<close>'s two branch outcomes.
  \<open>local_branch_tree_dead\<close>: a genuinely infeasible \<open>h\<close> on the restricted
  local input collapses the whole tree to \<^const>\<open>Bot\<close> regardless of what
  \<open>\<sigma>\<close> carries at the global slot -- live globals cannot resurrect a dead
  local branch, matching \<open>assemble_local_global\<close>'s own \<open>Bot\<close>-dominates
  clause one layer up. \<open>local_branch_tree_reach\<close>: a feasible \<open>h\<close>
  reassembles exactly as \<^const>\<open>local_edge_tree\<close> would -- the narrowed
  local result joined with the pre-edge globals of the queried unknown.
\<close>

lemma local_branch_tree_dead:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
    and h :: "'a abs_state \<Rightarrow> 'a abs_state lifted"
  assumes hu: "\<sigma> (Inl u) = Lifted su"
  assumes dead: "h (restrict_local_for gs su) = Bot"
  shows "etf_collecting_full_lift (local_branch_tree gs h u) \<sigma> = Bot"
  unfolding etf_collecting_full_local_branch_tree res_local_branch_def hu
  by (simp add: dead)

lemma local_branch_tree_reach:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
    and h :: "'a abs_state \<Rightarrow> 'a abs_state lifted"
  assumes hu: "\<sigma> (Inl u) = Lifted su"
  assumes reach: "h (restrict_local_for gs su) = Lifted r"
  shows "etf_collecting_full_lift (local_branch_tree gs h u) \<sigma> =
    assemble_local_global (Lifted (restrict_local_for gs r \<squnion> restrict_global_for gs su)) (glob_env \<sigma>)"
  unfolding etf_collecting_full_local_branch_tree res_local_branch_def hu
  by (simp add: reach)

subsection \<open>Lifted local-edge frame property\<close>

text \<open>
  The lifted analogue of \<^const>\<open>local_edge_invariant\<close>: instead of requiring a
  reconstructed full-state input and a reconstructed restricted-then-reattached
  output to agree as plain \<open>abs_state\<close> values -- which forced \<open>branch\<close>'s old
  whole-state-\<^const>\<open>bot\<close> collapse to falsely claim a live global got
  overwritten -- this states the same restrict/reattach discipline over \<open>h\<close>'s
  own \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> split. A \<^const>\<open>Bot\<close> decision on the restricted
  input propagates to \<^const>\<open>Bot\<close> on the full input regardless of \<open>g\<close> (via
  \<^const>\<open>map_lift\<close>'s own \<open>map_lift f Bot = Bot\<close>), matching Goblint's \<open>Deadcode\<close>
  dominating any live global; a \<^const>\<open>Lifted\<close> decision reattaches \<open>g\<close>
  unchanged, so a reachable branch never has to compare against \<open>g\<close> at all.
\<close>

definition local_edge_invariant_lifted ::
  "(vname => bool) => ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state lifted) => bool"
where
  "local_edge_invariant_lifted gs h \<longleftrightarrow>
     (\<forall>su g. local_bot_on_locals gs g \<longrightarrow>
        h (restrict_local_for gs su \<squnion> g) =
        map_lift (%r. restrict_local_for gs r \<squnion> g) (h (restrict_local_for gs su)))"

lemma local_edge_invariant_liftedD:
  "local_edge_invariant_lifted gs h \<Longrightarrow> local_bot_on_locals gs g \<Longrightarrow>
   h (restrict_local_for gs su \<squnion> g) =
   map_lift (%r. restrict_local_for gs r \<squnion> g) (h (restrict_local_for gs su))"
  unfolding local_edge_invariant_lifted_def by blast

text \<open>
  Lifted counterpart of \<open>local_edge_invariant_side_env_eq\<close>: the same
  reduction from a fully-assembled input (\<open>su \<squnion> g'\<close>, an arbitrary local witness
  joined with the accumulated global) to the restrict/reattach recipe
  \<^const>\<open>res_local_branch\<close> actually computes, now carried through \<open>h\<close>'s lifted
  result instead of a plain \<open>abs_state\<close> value.
\<close>
lemma local_edge_invariant_lifted_side_env_eq:
  fixes h :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state lifted"
    and su g' :: "'a abs_state"
  assumes inv: "local_edge_invariant_lifted gs h"
  assumes lb: "local_bot_on_locals gs g'"
  shows "h (su \<squnion> g') =
    map_lift (%r. restrict_local_for gs r \<squnion> restrict_global_for gs su \<squnion> g')
      (h (restrict_local_for gs su))"
proof -
  have rg: "local_bot_on_locals gs (restrict_global_for gs su)"
    by (rule local_bot_on_locals_restrict_global)
  have g: "local_bot_on_locals gs (restrict_global_for gs su \<squnion> g')"
    by (rule local_bot_join[OF rg lb])
  have env: "su \<squnion> g' = restrict_local_for gs su \<squnion> (restrict_global_for gs su \<squnion> g')"
    using restrict_local_for_global_join[of gs su] by (simp add: sup_commute sup_left_commute)
  have step: "h (restrict_local_for gs su \<squnion> (restrict_global_for gs su \<squnion> g')) =
              map_lift (%r. restrict_local_for gs r \<squnion> (restrict_global_for gs su \<squnion> g'))
                (h (restrict_local_for gs su))"
    using local_edge_invariant_liftedD[OF inv g] .
  show ?thesis
    by (simp only: env step sup_assoc)
qed


subsection \<open>Effectful transfer record factories\<close>

definition unit_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "unit_etf_of_transfer gs tf = \<lparr>
    etf_skip       = (\<lambda>u. unit_edge_tree gs (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. unit_edge_tree gs (apply_tf tf (EA_Assign x e)) u),
    etf_special    = (\<lambda>sc x u. unit_edge_tree gs (apply_tf tf (EA_Special sc x)) u),
    etf_branch     = (\<lambda>b pol u. unit_edge_tree gs (branch\<^sup># tf b pol) u),
    etf_body       = (\<lambda>p u. unit_edge_tree gs (body\<^sup># tf p) u),
    etf_return     = (\<lambda>e p u. unit_edge_tree gs (return\<^sup># tf e p) u),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (enter\<^sup># tf xs es) u),
    etf_event      = (\<lambda>ev u. unit_edge_tree gs (event\<^sup># tf ev) u),
    etf_combine_env     =
      (\<lambda>ci. unit_combine_tree gs (\<lambda>\<sigma>c. combine_env\<^sup># tf ci (caller_cont\<^sup># tf ci \<sigma>c))),
    etf_combine_collect =
      (\<lambda>ci. unit_combine_tree gs (\<lambda>\<sigma>c. tf_combine_collect_abs tf ci (caller_cont\<^sup># tf ci \<sigma>c)))
  \<rparr>"

definition mixed_etf_edge_tree ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> edge_action \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "mixed_etf_edge_tree gs tf a u =
    (if local_edge_action gs a then local_edge_tree gs (apply_tf tf a) u
     else unit_edge_tree gs (apply_tf tf a) u)"

text \<open>
  \<open>mixed_etf_of_transfer\<close>'s branch case is parametric in an explicit lifted
  branch operation \<open>bl\<close> (a domain's own \<open>branch_lifted\<close> at the call
  site, e.g. Sign's -- see \<^const>\<open>local_branch_tree\<close>'s own docstring),
  rather than hardcoding any domain-specific constant here: this Core theory
  stays domain-agnostic, and the caller instantiates \<open>bl\<close>. A local guard
  routes through \<^const>\<open>local_branch_tree\<close>, preserving \<^const>\<open>Bot\<close> through
  a genuine infeasibility; a non-local guard is unchanged, still driven by
  the domain's plain \<open>branch\<close> field through \<^const>\<open>unit_edge_tree\<close> (M3
  establishes that route already collapses a whole-state-\<^const>\<open>bot\<close> result
  to outer \<^const>\<open>Bot\<close> correctly, so it needs no lifted counterpart).
\<close>

definition mixed_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer
   => (exp => bool => 'a abs_state => 'a abs_state lifted)
   => (unit, 'a) effectful_domain_transfer"
where
  "mixed_etf_of_transfer gs tf bl = \<lparr>
    etf_skip       = mixed_etf_edge_tree gs tf EA_Nop,
    etf_assign     = (\<lambda>x e. mixed_etf_edge_tree gs tf (EA_Assign x e)),
    etf_special    = (\<lambda>sc x. mixed_etf_edge_tree gs tf (EA_Special sc x)),
    etf_branch     = (\<lambda>b pol u.
        if local_edge_action gs (if pol then EA_Assume b else EA_AssumeNot b)
        then local_branch_tree gs (bl b pol) u
        else unit_edge_tree gs (branch\<^sup># tf b pol) u),
    etf_body       = (\<lambda>p u. unit_edge_tree gs (body\<^sup># tf p) u),
    etf_return     = (\<lambda>e p. mixed_etf_edge_tree gs tf (EA_Ret e p)),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (enter\<^sup># tf xs es) u),
    etf_event      = (\<lambda>ev u. local_edge_tree gs (event\<^sup># tf ev) u),
    etf_combine_env     =
      (\<lambda>ci. unit_combine_tree gs (\<lambda>\<sigma>c. combine_env\<^sup># tf ci (caller_cont\<^sup># tf ci \<sigma>c))),
    etf_combine_collect =
      (\<lambda>ci. unit_combine_tree gs (\<lambda>\<sigma>c. tf_combine_collect_abs tf ci (caller_cont\<^sup># tf ci \<sigma>c)))
  \<rparr>"

lemma apply_etf_unit_of_transfer:
  "apply_etf (unit_etf_of_transfer gs tf) a u = unit_edge_tree gs (apply_tf tf a) u"
  unfolding unit_etf_of_transfer_def
  by (cases a) simp_all

text \<open>Both builders hand the combine tree the \<^emph>\<open>continuation\<close>: the tree reconstructs the
  raw call-site state, so \<open>caller_cont\<^sup>#\<close> is applied here, at the boundary that stands in for
  \<open>enter\<close>.  The combine operations themselves never reapply it.\<close>

lemma etf_combine_env_unit_of_transfer:
  "etf_combine_env (unit_etf_of_transfer gs tf) ci cc ex
     = unit_combine_tree gs (\<lambda>\<sigma>c. combine_env\<^sup># tf ci (caller_cont\<^sup># tf ci \<sigma>c)) cc ex"
  unfolding unit_etf_of_transfer_def by simp

lemma etf_combine_collect_unit_of_transfer:
  "etf_combine_collect (unit_etf_of_transfer gs tf) ci cc ex
     = unit_combine_tree gs
         (\<lambda>\<sigma>c. tf_combine_collect_abs tf ci (caller_cont\<^sup># tf ci \<sigma>c)) cc ex"
  unfolding unit_etf_of_transfer_def by simp

text \<open>\<open>EA_Check\<close> routes through \<^const>\<open>local_edge_tree\<close> here, not
  \<^const>\<open>mixed_etf_edge_tree\<close>: \<^const>\<open>local_edge_action\<close> classifies \<open>EA_Check\<close>
  as unconditionally local (matching \<open>EA_Nop\<close>'s own classification), so this is
  the same routing \<open>mixed_etf_edge_tree gs tf EA_Nop\<close> would have picked, stated
  directly instead of through an edge-action-shaped detour.\<close>
text \<open>
  \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close> no longer fall under the \<open>_ \<Rightarrow> mixed_etf_edge_tree ...\<close>
  wildcard: their transfer is \<open>etf_branch\<close>'s own \<open>bl\<close>-parametric local/non-local
  split (\<^const>\<open>mixed_etf_of_transfer\<close>'s docstring), not \<^const>\<open>mixed_etf_edge_tree\<close>'s.
\<close>
lemma apply_etf_mixed_of_transfer:
  "apply_etf (mixed_etf_of_transfer gs tf bl) a u =
     (case a of
        EA_Check bc \<Rightarrow> local_edge_tree gs (apply_tf tf a) u
      | EA_Assume b \<Rightarrow>
          (if local_edge_action gs (EA_Assume b) then local_branch_tree gs (bl b True) u
           else unit_edge_tree gs (branch\<^sup># tf b True) u)
      | EA_AssumeNot b \<Rightarrow>
          (if local_edge_action gs (EA_AssumeNot b) then local_branch_tree gs (bl b False) u
           else unit_edge_tree gs (branch\<^sup># tf b False) u)
      | _ \<Rightarrow> mixed_etf_edge_tree gs tf a u)"
  unfolding mixed_etf_of_transfer_def mixed_etf_edge_tree_def
  by (cases a) simp_all

lemma etf_combine_env_mixed_of_transfer:
  "etf_combine_env (mixed_etf_of_transfer gs tf bl) ci cc ex
     = unit_combine_tree gs (\<lambda>\<sigma>c. combine_env\<^sup># tf ci (caller_cont\<^sup># tf ci \<sigma>c)) cc ex"
  unfolding mixed_etf_of_transfer_def by simp

lemma etf_combine_collect_mixed_of_transfer:
  "etf_combine_collect (mixed_etf_of_transfer gs tf bl) ci cc ex
     = unit_combine_tree gs
         (\<lambda>\<sigma>c. tf_combine_collect_abs tf ci (caller_cont\<^sup># tf ci \<sigma>c)) cc ex"
  unfolding mixed_etf_of_transfer_def by simp

lemma mixed_etf_edge_tree_local:
  assumes "local_edge_action gs a"
  shows "mixed_etf_edge_tree gs tf a u = local_edge_tree gs (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

lemma mixed_etf_edge_tree_unit:
  assumes "\<not> local_edge_action gs a"
  shows "mixed_etf_edge_tree gs tf a u = unit_edge_tree gs (apply_tf tf a) u"
  using assms unfolding mixed_etf_edge_tree_def by simp

text \<open>
  Every witness-based tree-soundness lemma below needs exactly this: a concrete
  membership witness in the reconstructed input's concretization rules out
  \<open>Bot\<close> in the local slot (the lifted counterpart of \<open>is_bot_state_witnessI\<close>'s
  pre-lift role), extracting the local slot's raw payload \<open>su\<close> and reducing the
  premise to the ordinary raw-join membership the underlying \<open>tf_sound_*_forD\<close>
  facts are stated against.
\<close>
lemma local_input_witness:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s :: store
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  obtains su where "\<sigma> (Inl u) = Lifted su"
    and "s \<in> \<lbrakk>su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
proof (cases "\<sigma> (Inl u)")
  case Bot
  then have False using s unfolding gamma_state_lift_assemble_local_global by simp
  then show ?thesis ..
next
  case (Lifted su)
  have "s \<in> \<lbrakk>su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using s unfolding Lifted gamma_state_lift_assemble_local_global by simp
  with Lifted show ?thesis using that by blast
qed

lemma local_bot_on_locals_inr:
  fixes \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes "inr_slot_locals_bot gs \<sigma>"
  shows "local_bot_on_locals gs (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)"
  using assms unfolding inr_slot_locals_bot_def local_bot_on_locals_def
  by (cases "\<sigma> (Inr ())") auto

subsection \<open>Generic collecting soundness for tree shapes\<close>

text \<open>
  Every \<open>in_gamma_unit_edge_tree_*\<close> obligation below has the same shape: given a
  concrete witness \<open>s\<close> in the reconstructed input and a semantic soundness step
  \<open>sound\<close> for the concrete successor \<open>s'\<close>, \<open>unit_edge_tree\<close>'s \<open>res_edge\<close> collapses to
  \<open>Bot\<close> only if the \<^emph>\<open>output\<close> \<open>f a\<close> is witness-bottom -- which \<open>sound\<close> itself rules
  out, since \<open>s' \<in> \<lbrakk>f a\<rbrakk>\<close> is a concrete witness for the output, not the input. Proving
  this once generically (parametric in \<open>f\<close>/\<open>s'\<close>/\<open>sound\<close>) avoids repeating the same
  five-step derivation once per action.
\<close>
lemma in_gamma_unit_edge_tree:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s s' :: store
    and f :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  assumes sound: "\<And>a. s \<in> \<lbrakk>a\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>f a\<rbrakk>"
  shows "s' \<in> gamma_state_lift (etf_collecting_full_lift (unit_edge_tree gs f u) \<sigma>)"
proof -
  obtain su where hu: "\<sigma> (Inl u) = Lifted su"
    and hs: "s \<in> \<lbrakk>su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF s] .
  have hf: "s' \<in> \<lbrakk>f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))\<rbrakk>"
    using sound[OF hs] .
  have not_bot: "\<not> is_bot_state (f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    using hf is_bot_state_witnessI by blast
  have eq: "etf_full (unit_edge_tree gs f u) \<sigma> =
            Lifted (f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    unfolding etf_full_unit_edge_tree res_edge_def hu assemble_local_global_Lifted transfer_lift_Lifted
    using not_bot by simp
  have st: "s' \<in> gamma_state_lift (etf_full (unit_edge_tree gs f u) \<sigma>)"
    using hf unfolding eq by simp
  show ?thesis
    by (rule in_gamma_etf_collecting_full_lift) (rule st)
qed

text \<open>
  \<open>unit_edge_tree\<close> is not modified for branch: a domain's own \<open>branch\<close>
  (M1's plain, unchanged \<open>abs_state \<Rightarrow> abs_state\<close> projection of
  \<open>branch_lifted\<close>) still drives it directly for a non-local guard. This is
  sound: unlike \<^const>\<open>local_edge_tree\<close>, \<^const>\<open>res_edge\<close>'s reconstruction
  \<^const>\<open>assemble_local_global\<close>s the queried unknown against the LIVE
  accumulated global before calling \<open>f\<close>, so \<open>f\<close> sees the fully assembled
  input, not a locally-restricted one -- the AD-52 vacuity trap that forces
  \<^const>\<open>local_edge_tree\<close> to use plain structural \<^const>\<open>map_lift\<close> (see its
  own docstring) does not apply here: an \<open>is_bot_state\<close> output really is a
  genuine reachability fact, not an artifact of restriction, so
  \<^const>\<open>transfer_lift\<close>'s own witness-bottom recheck already turns a
  whole-state-\<^const>\<open>bot\<close> branch decision into outer \<^const>\<open>Bot\<close> correctly.
  No parallel \<open>unit_branch_tree\<close> is needed for the non-local branch case.
\<close>

lemma res_edge_bot_of_is_bot_state:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
    and f :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes hu: "\<sigma> (Inl u) = Lifted su"
  assumes bot_result: "is_bot_state (f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
  shows "res_edge f u \<sigma> = Bot"
  unfolding res_edge_def hu assemble_local_global_Lifted transfer_lift_Lifted normalize_lift_def
  using bot_result by simp

lemma etf_collecting_full_unit_edge_tree_bot_of_is_bot_state:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
    and f :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes hu: "\<sigma> (Inl u) = Lifted su"
  assumes bot_result: "is_bot_state (f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
  shows "etf_collecting_full_lift (unit_edge_tree gs f u) \<sigma> = Bot"
proof -
  have re: "res_edge f u \<sigma> = Bot"
    unfolding res_edge_def hu assemble_local_global_Lifted transfer_lift_Lifted normalize_lift_def
    using bot_result by simp
  show ?thesis
    unfolding etf_collecting_full_lift_def etf_collecting_full_with_def etf_full_unit_edge_tree re
    by simp
qed

text \<open>
  Instantiated at a whole-state-\<^const>\<open>bot\<close>-producing \<open>branch\<close>: a definite
  contradiction on a non-local branch guard routes through
  \<^const>\<open>unit_edge_tree\<close> exactly as \<open>EA_Assign\<close>/\<open>EA_Special\<close>/... already do
  via \<open>mixed_etf_edge_tree_unit\<close>, with no rewiring needed: the
  fully-assembled input's whole-state \<^const>\<open>bot\<close> result is genuinely
  \<^const>\<open>is_bot_state\<close>, so it collapses to outer \<^const>\<open>Bot\<close> without a
  separate lifted branch mechanism for this case.
\<close>

lemma unit_edge_tree_branch_dead:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
    and branch :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes hu: "\<sigma> (Inl u) = Lifted su"
  assumes dead: "branch (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)) = bot"
  shows "etf_collecting_full_lift (unit_edge_tree gs branch u) \<sigma> = Bot"
proof (rule etf_collecting_full_unit_edge_tree_bot_of_is_bot_state)
  show "\<sigma> (Inl u) = Lifted su" by (rule hu)
next
  show "is_bot_state (branch (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    unfolding dead by simp
qed

context sound_transfer_for
begin


text \<open>
  local_edge_tree never checks witness-bottom at all (res_local uses map_lift, not
  transfer_lift -- see local_edge_tree's own docstring), so this reconstructed-input
  step has no not_bot side condition, unlike \<open>in_gamma_unit_edge_tree\<close>: the
  reconstructed input reduces unconditionally once the local slot is known Lifted.
  One generic lemma, parametric in \<open>f\<close>/\<open>s'\<close>/\<open>sound\<close>, covers every action; \<open>EA_Nop\<close>'s
  case is the instance \<open>f = (\<lambda>env. env)\<close> via @{thm id_local_edge_invariant}.
\<close>
lemma in_gamma_local_edge_tree:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s s' :: store
    and f :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes inv: "local_edge_invariant gs f"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  assumes sound: "\<And>a. s \<in> \<lbrakk>a\<rbrakk> \<Longrightarrow> s' \<in> \<lbrakk>f a\<rbrakk>"
  shows "s' \<in> gamma_state_lift (etf_collecting_full_lift (local_edge_tree gs f u) \<sigma>)"
proof -
  obtain su where hu: "\<sigma> (Inl u) = Lifted su"
    and hs: "s \<in> \<lbrakk>su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF s] .
  have lb: "local_bot_on_locals gs (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)"
    using local_bot_on_locals_inr[OF inr] .
  have hf: "s' \<in> \<lbrakk>f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))\<rbrakk>"
    using sound[OF hs] .
  have eq: "etf_collecting_full_lift (local_edge_tree gs f u) \<sigma> =
            Lifted (f (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    unfolding etf_collecting_full_local_edge_tree res_local_def hu
    by (simp add: assemble_local_global_Lifted glob_env_unit local_edge_invariant_side_env_eq[OF inv lb])
  show ?thesis using hf unfolding eq by simp
qed

end


text \<open>
  Soundness for \<^const>\<open>local_branch_tree\<close>: parametric in \<open>h\<close>'s own soundness
  (\<open>sound\<close>, matching \<open>branch_lifted_sound\<close>'s shape at the call site) and in
  \<^const>\<open>local_edge_invariant_lifted\<close> (\<open>inv\<close>, discharged per domain once branch
  is rewired through this tree). No \<open>s'\<close> is needed -- unlike an ordinary local
  edge transfer, branch never produces a different concrete witness.
\<close>
lemma in_gamma_local_branch_tree:
  fixes u :: pp and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s :: store
    and h :: "'a abs_state \<Rightarrow> 'a abs_state lifted"
  assumes inv: "local_edge_invariant_lifted gs h"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
  assumes sound: "\<And>a. s \<in> \<lbrakk>a\<rbrakk> \<Longrightarrow> s \<in> gamma_state_lift (h a)"
  shows "s \<in> gamma_state_lift (etf_collecting_full_lift (local_branch_tree gs h u) \<sigma>)"
proof -
  obtain su where hu: "\<sigma> (Inl u) = Lifted su"
    and hs: "s \<in> \<lbrakk>su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF s] .
  have lb: "local_bot_on_locals gs (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)"
    using local_bot_on_locals_inr[OF inr] .
  have hf: "s \<in> gamma_state_lift (h (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    using sound[OF hs] .
  have eq: "etf_collecting_full_lift (local_branch_tree gs h u) \<sigma> =
            h (su \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))"
    unfolding etf_collecting_full_local_branch_tree res_local_branch_def hu
    by (cases "h (restrict_local_for gs su)")
       (simp_all add: assemble_local_global_Lifted glob_env_unit
          local_edge_invariant_lifted_side_env_eq[OF inv lb])
  show ?thesis using hf unfolding eq .
qed

subsection \<open>Generic effectful soundness from domain transfer\<close>

text \<open>
  Both @{const unit_etf_of_transfer} and @{const mixed_etf_of_transfer} route
  \<open>etf_combine_env\<close>/\<open>etf_combine_collect\<close> through @{const unit_combine_tree}
  (calls never take the local-restriction branch), differing only in which
  combine operation they hand it, so the combine obligation is proved once here
  against an arbitrary sound operation and reused by both instance proofs below.
\<close>

text \<open>
  Tree-level soundness of an arbitrary combine operation: whenever \<open>cmb\<close>
  over-approximates the concrete two-input operation \<open>r\<close>, the tree built from it
  is sound at the reassembled inputs.  Both roles of Goblint's combine interface
  instantiate this -- \<open>r\<close> is @{const combine_env} against \<open>combine_env\<^sup>#\<close>, or
  @{const combine_collect} against @{const tf_combine_collect_abs} -- so neither
  needs its own witness argument.
\<close>
lemma in_gamma_unit_combine_tree:
  fixes cc ex :: pp
    and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s t :: store
    and cmb :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes cmb_sound: "\<And>\<sigma>c \<sigma>e. s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow> r \<in> \<lbrakk>cmb \<sigma>c \<sigma>e\<rbrakk>"
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ())))"
  assumes t: "t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ())))"
  shows "r \<in> gamma_state_lift (etf_full (unit_combine_tree gs cmb cc ex) \<sigma>)"
proof -
  obtain sc where hc: "\<sigma> (Inl cc) = Lifted sc"
    and hsc: "s \<in> \<lbrakk>sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF s] .
  obtain se where he: "\<sigma> (Inl ex) = Lifted se"
    and hse: "t \<in> \<lbrakk>se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF t] .
  have res: "r \<in> \<lbrakk>cmb (sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))
                     (se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))\<rbrakk>"
    by (rule cmb_sound[OF hsc hse])
  have not_bot: "\<not> is_bot_state (sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))"
    and not_bot_e: "\<not> is_bot_state (se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))"
    using is_bot_state_witnessI[OF hsc] is_bot_state_witnessI[OF hse] by simp_all
  have eq: "etf_full (unit_combine_tree gs cmb cc ex) \<sigma> =
            Lifted (cmb (sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))
                        (se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    unfolding etf_full_unit_combine_tree res_combine_def hc he
    using not_bot not_bot_e is_bot_state_witnessI[OF res]
    by (simp add: assemble_local_global_Lifted transfer_lift2_Lifted normalize_lift_not_bot)
  show ?thesis using res unfolding eq by simp
qed


lemma sound_effectful_transfer_unit_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer_for gs tf"
  shows "sound_effectful_transfer gs (unit_etf_of_transfer gs tf)"
proof -
  interpret sound_transfer_for gs tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift (etf_skip (unit_etf_of_transfer gs tf) u) \<sigma>))"
      by (auto simp add: unit_etf_of_transfer_def intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(x := aval e s) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_assign (unit_etf_of_transfer gs tf) x e u) \<sigma>))"
      unfolding unit_etf_of_transfer_def apply_tf.simps by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>sc x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). \<forall>v.
              special_result sc s v \<longrightarrow>
              s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_special (unit_etf_of_transfer gs tf) sc x u) \<sigma>))"
      unfolding unit_etf_of_transfer_def apply_tf.simps by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(b::exp) (pol::bool) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). truthy (aval b s) = pol
            \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift
                  (etf_branch (unit_etf_of_transfer gs tf) b pol u) \<sigma>))"
      unfolding unit_etf_of_transfer_def
      by (fastforce intro: in_gamma_unit_edge_tree tf_sound_branch_forD)
  next
    show "\<forall>p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_body (unit_etf_of_transfer gs tf) p u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(e::exp option) p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
                \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_return (unit_etf_of_transfer gs tf) e p u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>xs (es::exp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
                \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_enter (unit_etf_of_transfer gs tf) xs es u) \<sigma>))"
      by (auto simp add: unit_etf_of_transfer_def intro: in_gamma_unit_edge_tree)

  next
    show "\<forall>ev u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_event (unit_etf_of_transfer gs tf) ev u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>ci cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_env gs s t
                \<in> gamma_state_lift (etf_full (etf_combine_env (unit_etf_of_transfer gs tf) ci cc ex) \<sigma>))"
      by (auto simp add: etf_combine_env_unit_of_transfer
               intro: in_gamma_unit_combine_tree tf_sound_combine_env_at_call_forD)
  next
    show "\<forall>ci cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_collect gs (ci_dst ci) s t
                \<in> gamma_state_lift (etf_full (etf_combine_collect (unit_etf_of_transfer gs tf) ci cc ex) \<sigma>))"
      by (auto simp add: etf_combine_collect_unit_of_transfer
               intro: in_gamma_unit_combine_tree tf_sound_combine_collect_at_call_forD)
  qed
qed


text \<open>
  The branch case's obligation is parametric in \<open>bl\<close>, the lifted branch
  operation \<^const>\<open>mixed_etf_of_transfer\<close> threads into \<^const>\<open>local_branch_tree\<close>.
  \<open>bl_sound\<close> mirrors \<open>tf_sound_branch_for\<close>'s shape at the lifted return type
  (\<open>branch_lifted_sound\<close>'s shape at a domain's own call site); \<open>bl_inv\<close> mirrors
  \<open>loc_inv\<close> for \<open>bl\<close> specifically, since \<open>bl\<close> is not \<^const>\<open>apply_tf\<close>-shaped and
  so cannot be discharged as an instance of \<open>loc_inv\<close> itself.
\<close>
lemma sound_effectful_transfer_mixed_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
    and bl :: "exp => bool => 'a abs_state => 'a abs_state lifted"
  assumes st: "sound_transfer_for gs tf"
  assumes loc_inv: "\<And>a. local_edge_action gs a \<Longrightarrow> \<not> is_branch_action a \<Longrightarrow>
      local_edge_invariant gs (apply_tf tf a)"
  assumes bl_sound: "\<And>b pol \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow> s \<in> gamma_state_lift (bl b pol \<sigma>)"
  assumes bl_inv: "\<And>b pol. local_edge_action gs (if pol then EA_Assume b else EA_AssumeNot b) \<Longrightarrow>
      local_edge_invariant_lifted gs (bl b pol)"
  shows "sound_effectful_transfer gs (mixed_etf_of_transfer gs tf bl)"
proof -
  interpret sound_transfer_for gs tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift (etf_skip (mixed_etf_of_transfer gs tf bl) u) \<sigma>))"
    proof -
      have inv': "local_edge_invariant gs (skip\<^sup># tf)"
        using loc_inv[of EA_Nop] by (simp add: apply_tf.simps)
      show ?thesis
        unfolding mixed_etf_of_transfer_def mixed_etf_edge_tree_def apply_tf.simps
        using inv' by (auto intro: in_gamma_local_edge_tree in_gamma_unit_edge_tree)
    qed
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(x := aval e s) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_assign (mixed_etf_of_transfer gs tf bl) x e u) \<sigma>))"
    proof (intro allI impI ballI)
      fix x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      show "s(x := aval e s) \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_assign (mixed_etf_of_transfer gs tf bl) x e u) \<sigma>)"
      proof (cases "local_edge_action gs (EA_Assign x e)")
        case True
        have inv': "local_edge_invariant gs (assign\<^sup># tf x e)"
          using loc_inv[OF True]
          by (simp add: local_edge_invariant_def)
        have "s(x := aval e s) \<in> gamma_state_lift
                (etf_collecting_full_lift (local_edge_tree gs (assign\<^sup># tf x e) u) \<sigma>)"
          by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_assign_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF True] apply_tf.simps)
      next
        case False
        have "s(x := aval e s) \<in> gamma_state_lift
                (etf_collecting_full_lift (unit_edge_tree gs (assign\<^sup># tf x e) u) \<sigma>)"
          by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_assign_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF False] apply_tf.simps)
      qed
    qed
  next
    show "\<forall>sc x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). \<forall>v.
              special_result sc s v \<longrightarrow>
              s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_special (mixed_etf_of_transfer gs tf bl) sc x u) \<sigma>))"
    proof (intro allI impI ballI)
      fix sc x u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store and v
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
        and sr: "special_result sc s v"
      show "s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_special (mixed_etf_of_transfer gs tf bl) sc x u) \<sigma>)"
      proof (cases "local_edge_action gs (EA_Special sc x)")
        case True
        have inv': "local_edge_invariant gs (special\<^sup># tf sc x)"
          using loc_inv[OF True] by (simp add: apply_tf.simps)
        have "s(x := v) \<in> gamma_state_lift
                (etf_collecting_full_lift (local_edge_tree gs (special\<^sup># tf sc x) u) \<sigma>)"
          by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_special_forD[OF _ sr])
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF True] apply_tf.simps)
      next
        case False
        have "s(x := v) \<in> gamma_state_lift
                (etf_collecting_full_lift (unit_edge_tree gs (special\<^sup># tf sc x) u) \<sigma>)"
          by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_special_forD[OF _ sr])
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF False] apply_tf.simps)
      qed
    qed
  next
    show "\<forall>(b::exp) (pol::bool) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). truthy (aval b s) = pol
            \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift
                  (etf_branch (mixed_etf_of_transfer gs tf bl) b pol u) \<sigma>))"
    proof (intro allI impI ballI)
      fix b pol u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
        and hb: "truthy (aval b s) = pol"
      show "s \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_branch (mixed_etf_of_transfer gs tf bl) b pol u) \<sigma>)"
      proof (cases "local_edge_action gs (if pol then EA_Assume b else EA_AssumeNot b)")
        case True
        have inv': "local_edge_invariant_lifted gs (bl b pol)"
          using bl_inv[OF True] .
        have "s \<in> gamma_state_lift
                (etf_collecting_full_lift (local_branch_tree gs (bl b pol) u) \<sigma>)"
          by (rule in_gamma_local_branch_tree[OF inv' inr s]) (rule bl_sound[OF _ hb])
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def True)
      next
        case False
        have "s \<in> gamma_state_lift
                (etf_collecting_full_lift (unit_edge_tree gs (branch\<^sup># tf b pol) u) \<sigma>)"
          by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_branch_forD[OF _ hb])
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def False)
      qed
    qed

  next
    show "\<forall>p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_body (mixed_etf_of_transfer gs tf bl) p u) \<sigma>))"
      unfolding mixed_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(e::exp option) p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
                \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_return (mixed_etf_of_transfer gs tf bl) e p u) \<sigma>))"
    proof (intro allI impI ballI)
      fix e p u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      show "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in>
              gamma_state_lift (etf_collecting_full_lift
                (etf_return (mixed_etf_of_transfer gs tf bl) e p u) \<sigma>)"
      proof (cases "local_edge_action gs (EA_Ret e p)")
        case True
        have inv': "local_edge_invariant gs (return\<^sup># tf e p)"
          using loc_inv[OF True]
          by (simp add: apply_tf.simps)
        have "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in>
                gamma_state_lift
                  (etf_collecting_full_lift (local_edge_tree gs (return\<^sup># tf e p) u) \<sigma>)"
          by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_return_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF True] apply_tf.simps)
      next
        case False
        have "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in>
                gamma_state_lift
                  (etf_collecting_full_lift (unit_edge_tree gs (return\<^sup># tf e p) u) \<sigma>)"
          by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_return_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF False] apply_tf.simps)
      qed
    qed
  next
    show "\<forall>xs (es::exp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
                \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_enter (mixed_etf_of_transfer gs tf bl) xs es u) \<sigma>))"
      unfolding mixed_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>ev u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_event (mixed_etf_of_transfer gs tf bl) ev u) \<sigma>))"
    proof (intro allI impI ballI)
      fix ev u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      obtain bc where ev_eq: "ev = Check_Event bc" by (cases ev) simp
      have inv': "local_edge_invariant gs (event\<^sup># tf ev)"
        using loc_inv[of "EA_Check bc"] by (simp add: ev_eq apply_tf.simps)
      have "s \<in> gamma_state_lift (etf_collecting_full_lift (local_edge_tree gs (event\<^sup># tf ev) u) \<sigma>)"
        by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_event_forD)
      then show "s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_event (mixed_etf_of_transfer gs tf bl) ev u) \<sigma>)"
        by (simp add: mixed_etf_of_transfer_def)
    qed
  next
    show "\<forall>ci cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_env gs s t
                \<in> gamma_state_lift (etf_full (etf_combine_env (mixed_etf_of_transfer gs tf bl) ci cc ex) \<sigma>))"
      by (auto simp add: etf_combine_env_mixed_of_transfer
               intro: in_gamma_unit_combine_tree tf_sound_combine_env_at_call_forD)
  next
    show "\<forall>ci cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_collect gs (ci_dst ci) s t
                \<in> gamma_state_lift (etf_full (etf_combine_collect (mixed_etf_of_transfer gs tf bl) ci cc ex) \<sigma>))"
      by (auto simp add: etf_combine_collect_mixed_of_transfer
               intro: in_gamma_unit_combine_tree tf_sound_combine_collect_at_call_forD)
  qed
qed

(* Generic reachability over the solver's local dependency relation: a single
   dependency step lands in the transitive closure, which is itself transitive. *)
lemma trans_dep\<^sub>L_step_in:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> dep\<^sub>L T \<sigma> x"
  shows "y \<in> trans_dep\<^sub>L T \<sigma> x"
  using assms by blast

lemma trans_dep\<^sub>L_trans:
  fixes T :: "(pp, unit, 'd::order_bot) eqsT"
  assumes "y \<in> trans_dep\<^sub>L T \<sigma> x"
    and "z \<in> dep\<^sub>L T \<sigma> y"
  shows "z \<in> trans_dep\<^sub>L T \<sigma> x"
  by (metis Nitpick.tranclp_unfold assms(1,2) mem_Collect_eq tranclp.trancl_into_trancl)


end
