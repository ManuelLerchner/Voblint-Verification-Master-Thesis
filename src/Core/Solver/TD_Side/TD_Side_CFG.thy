theory TD_Side_CFG
  imports Constraint_System_Sound Split_State "Voblint_VIMP.VIMP_Globals" "TD.TD_side"
    Strategy_Tree_Combinators
begin

(* TD_side defines a record field \<sigma> for its internal state; hide the short
   name so our \<sigma> variables (abstract state maps) are unambiguous. *)
hide_const (open) \<sigma>

section \<open>Side IP solver: generic base\<close>

text \<open>
  Generic base for the side-effecting interprocedural solver.

  A locals/globals split on abstract states: restrict_local / restrict_global
  keep one component (the other set to bot), so their join recovers the
  original state.  side_env combines the local unknown at a program point with
  the single global unknown.

  The interprocedural strategy tree and transfer functions live in TD_Side_Tree;
  monotonicity and solver preconditions live in TD_Side_Eff_Bounds and TD_Side_Eff_Cone_Lemmas.
\<close>

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local_for gs \<sigma> = (%x. if gs x then bot else \<sigma> x)"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for gs \<sigma> = (%x. if gs x then \<sigma> x else bot)"

lemma restrict_local_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_local_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_local_for gs sigma2"
  unfolding restrict_local_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_global_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_global_for gs sigma2"
  unfolding restrict_global_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_le:
  "restrict_global_for gs (sigma :: 'a::bounded_semilattice_sup_bot abs_state) \<le> sigma"
  unfolding restrict_global_for_def le_fun_def by (auto simp: bot_least)

lemma map_lift_restrict_global_for_le:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) x \<le> x"
  by (cases x) (simp_all add: restrict_global_for_le)

lemma restrict_local_for_join [simp]:
  "restrict_local_for gs (A \<squnion> B) = restrict_local_for gs A \<squnion> restrict_local_for gs B"
  unfolding restrict_local_for_def sup_fun_def by (rule ext) simp

lemma restrict_global_for_join [simp]:
  "restrict_global_for gs (A \<squnion> B) = restrict_global_for gs A \<squnion> restrict_global_for gs B"
  unfolding restrict_global_for_def sup_fun_def by (rule ext) simp

lemma restrict_local_for_idem [simp]:
  "restrict_local_for gs (restrict_local_for gs A) = restrict_local_for gs A"
  unfolding restrict_local_for_def by (rule ext) simp

lemma restrict_global_for_idem [simp]:
  "restrict_global_for gs (restrict_global_for gs A) = restrict_global_for gs A"
  unfolding restrict_global_for_def by (rule ext) simp

lemma map_lift_restrict_global_for_idem [simp]:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) (map_lift (restrict_global_for gs) x)
           = map_lift (restrict_global_for gs) x"
  by (cases x) simp_all

lemma restrict_local_for_restrict_global_for_bot [simp]:
  "restrict_local_for gs (restrict_global_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_global_for_restrict_local_for_bot [simp]:
  "restrict_global_for gs (restrict_local_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_global_join:
  "restrict_local_for gs \<sigma> \<squnion> restrict_global_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_global_for_local_join:
  "restrict_global_for gs \<sigma> \<squnion> restrict_local_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp
lemma restrict_global_for_sup [simp]:
  "restrict_global_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_global_for gs B"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_local_for_sup [simp]:
  "restrict_local_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_local_for gs A"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp



(* Monotonicity in the queried assignment (join = \<squnion>). *)

lemma join_abs_state_left_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and acc1 acc2 s :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join acc1 s \<le> join acc2 s"
  by (rule join_mono[OF acc_le order_refl])

lemma join_abs_state_right_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and s acc1 acc2 :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join s acc1 \<le> join s acc2"
  by (rule join_mono[OF order_refl acc_le])


(* restrict_local / restrict_global are join-homomorphisms, idempotent, and
   annihilate each other; together these make the algebra confluent, so a
   split-state combine such as restrict_local (restrict_local A \<squnion> restrict_global B)
   = restrict_local A closes by plain simp without a dedicated lemma. *)
(* combine_env\<^sup>#'s primitive definition is a single if-then-else lambda; this
   reduces it to the confluent restrict_local_for/restrict_global_for algebra so
   proofs never need to unfold combine_env_abs_def and re-derive the split by
   hand. *)
lemma combine_env_abs_for_eq_restrict:
  "combine_env\<^sup># gs sc se =
     restrict_local_for gs sc \<squnion> restrict_global_for gs se"
  unfolding combine_env_abs_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp


subsection \<open>Split-state bridge\<close>

text \<open>
  The split representation of \<open>Split_State\<close> packages exactly this
  \<^const>\<open>restrict_local_for\<close> / \<^const>\<open>restrict_global_for\<close> decomposition:
  \<^const>\<open>split_state\<close> is the pair of the two restrictions, restriction pairs
  are well-formed split states, and \<^const>\<open>merge_state\<close> of two restrictions
  is their join.
\<close>

lemma split_state_eq_restrict:
  "split_state gs \<sigma> = (restrict_local_for gs \<sigma>, restrict_global_for gs \<sigma>)"
  unfolding split_state_def restrict_local_for_def restrict_global_for_def by simp

lemma wf_split_restrict:
  "wf_split gs (restrict_local_for gs A, restrict_global_for gs B)"
  unfolding wf_split_def restrict_local_for_def restrict_global_for_def by simp

lemma merge_state_restrict:
  "merge_state gs (restrict_local_for gs A, restrict_global_for gs B)
   = restrict_local_for gs A \<squnion> restrict_global_for gs B"
  unfolding merge_state_def restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp


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
   ex, and the global; reassemble locals-from-caller + globals-from-callee
   (= combine_env\<^sup>#) and split into a local Answer and a global Side.  Either
   reconstructed operand being Bot means no concrete predecessor reaches the
   combine (an unreachable call site, or a callee exit reached only from dead
   code), so the combine as a whole is dead too -- assemble_local_global's Bot
   dominance on both operands, threaded through transfer_lift2, gives this for
   free without a separate is_bot_state test. *)
definition unit_combine_tree ::
  "(vname => bool) => vname option => pp => pp
   => (pp, unit, 'a::sound_domain abs_state lifted) strategy_tree"
where
  "unit_combine_tree gs dst cc ex = do {
     sc <- read_local cc;
     se <- read_local ex;
     g <- read_global ();
     let res = transfer_lift2 is_bot_state (combine\<^sup># gs dst)
                 (assemble_local_global sc g) (assemble_local_global se g);
     depend_on () (map_lift (restrict_global_for gs) res)
       (answer (map_lift (restrict_local_for gs) res))
   }"


(* res_edge names the reconstructed input's transfer result -- Bot when either the
   reconstructed input or f's own result is witness-bottom, Lifted f's result
   otherwise -- so the three reassembly lemmas below state the same value instead
   of repeating it. *)
definition res_edge ::
  "('a::sound_domain abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state lifted) \<Rightarrow> 'a abs_state lifted" where
  "res_edge f u \<sigma> =
     transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"

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



text \<open>
  res_edge is monotone whenever \<open>f\<close> is: witness-bottom is downward closed
  (\<^const>\<open>is_bot_state\<close>'s own monotonicity lemma), so a smaller input can only make the
  short-circuit fire \<^emph>\<open>more\<close> often, and \<^term>\<open>bot\<close> is below every other case.
\<close>
lemma res_edge_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes f_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> f s1 \<le> f s2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_edge f u \<sigma>1 \<le> res_edge f u \<sigma>2"
proof -
  have inp_le: "assemble_local_global (\<sigma>1 (Inl u)) (\<sigma>1 (Inr ()))
                  \<le> assemble_local_global (\<sigma>2 (Inl u)) (\<sigma>2 (Inr ()))"
    by (rule assemble_local_global_mono; rule le_funD[OF le])
  show ?thesis
    unfolding res_edge_def by (rule transfer_lift_mono[OF f_mono is_bot_state_mono inp_le])
qed

(* res_combine mirrors res_edge for the two-input combine tree: Bot when either
   reconstructed operand is Bot or the combine itself lands on witness-bottom,
   the fixed abstract combine otherwise -- via transfer_lift2 rather than a
   separate is_bot_state test, same as res_edge. *)
definition res_combine ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> ('a::sound_domain) abs_state lifted) \<Rightarrow> 'a abs_state lifted" where
  "res_combine gs dst cc ex \<sigma> =
     transfer_lift2 is_bot_state (combine\<^sup># gs dst)
       (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ())))
       (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ())))"

text \<open>
  res_combine's monotonicity mirrors res_edge_mono, over two reconstructed operands
  instead of one.
\<close>
lemma res_combine_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes combine_mono: "\<And>t1 t2 u1 u2. t1 \<le> t2 \<Longrightarrow> u1 \<le> u2 \<Longrightarrow>
             combine\<^sup># gs dst t1 u1 \<le> combine\<^sup># gs dst t2 u2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_combine gs dst cc ex \<sigma>1 \<le> res_combine gs dst cc ex \<sigma>2"
proof -
  have cc_le: "assemble_local_global (\<sigma>1 (Inl cc)) (\<sigma>1 (Inr ()))
                 \<le> assemble_local_global (\<sigma>2 (Inl cc)) (\<sigma>2 (Inr ()))"
    and ex_le: "assemble_local_global (\<sigma>1 (Inl ex)) (\<sigma>1 (Inr ()))
                 \<le> assemble_local_global (\<sigma>2 (Inl ex)) (\<sigma>2 (Inr ()))"
    by (rule assemble_local_global_mono; rule le_funD[OF le])+
  show ?thesis
    unfolding res_combine_def
  proof (rule transfer_lift2_mono)
    fix t1 t2 u1 u2 :: "'a abs_state"
    assume "t1 \<le> t2" "u1 \<le> u2"
    then show "combine\<^sup># gs dst t1 u1 \<le> combine\<^sup># gs dst t2 u2" using combine_mono
      by (simp add: combine_collect_abs_mono)
  next
    fix a b :: "'a abs_state"
    assume "a \<le> b" "is_bot_state b"
    then show "is_bot_state a" by (rule is_bot_state_mono)
  next
    show "assemble_local_global (\<sigma>1 (Inl cc)) (\<sigma>1 (Inr ()))
            \<le> assemble_local_global (\<sigma>2 (Inl cc)) (\<sigma>2 (Inr ()))" by (rule cc_le)
  next
    show "assemble_local_global (\<sigma>1 (Inl ex)) (\<sigma>1 (Inr ()))
            \<le> assemble_local_global (\<sigma>2 (Inl ex)) (\<sigma>2 (Inr ()))" by (rule ex_le)
  qed
qed

(* The unit-global combine tree returns the combined locals as its Answer; unlike
   a plain combine_env these include the destination when the call assigns one. *)
lemma traverse_unit_combine_tree:
  "traverse_rhs (unit_combine_tree gs dst cc ex) \<sigma>
     = map_lift (restrict_local_for gs) (res_combine gs dst cc ex \<sigma>)"
  unfolding unit_combine_tree_def res_combine_def
  by (simp add: Let_def)

(* The unit-global combine tree contributes the combined globals to the global slot. *)
lemma sides_unit_combine_tree_Inr:
  "sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inr ()) =
   map_lift (restrict_global_for gs) (res_combine gs dst cc ex \<sigma>)"
  unfolding unit_combine_tree_def res_combine_def
  by (simp add: Let_def)

(* The unit-global combine tree reassembles to the fixed abstract combine. *)
lemma etf_full_unit_combine_tree:
  "etf_full (unit_combine_tree gs dst cc ex) \<sigma> = res_combine gs dst cc ex \<sigma>"
  unfolding etf_full_def
  apply (simp add: all_sides_eq_sides_Inr_unit traverse_unit_combine_tree sides_unit_combine_tree_Inr)
  apply (cases "res_combine gs dst cc ex \<sigma>")
   apply simp
  apply (simp add: restrict_local_for_global_join)
  done

(* Both traverse_rhs and its single Side are map_lift of the same res_combine,
   so they collapse together exactly as in the unit_edge_tree case. *)
lemma reachability_coherent_unit_combine_tree:
  "reachability_coherent_tree (unit_combine_tree gs dst cc ex) \<sigma>"
  unfolding reachability_coherent_tree_def
  by (cases "res_combine gs dst cc ex \<sigma>")
     (simp_all add: traverse_unit_combine_tree all_sides_eq_sides_Inr_unit
       sides_unit_combine_tree_Inr)

text \<open>Side-free counterpart of \<^const>\<open>unit_combine_tree\<close>, mirroring
  \<^const>\<open>unit_edge_contribution\<close> (\<open>issue #121\<close>).\<close>

definition unit_combine_contribution ::
  "(vname => bool) => vname option => pp => pp
   => (pp, unit, 'a::sound_domain abs_state lifted) strategy_tree"
where
  "unit_combine_contribution gs dst cc ex = do {
     sc <- read_local cc;
     se <- read_local ex;
     g <- read_global ();
     answer (transfer_lift2 is_bot_state (combine\<^sup># gs dst)
               (assemble_local_global sc g) (assemble_local_global se g))
   }"

lemma traverse_unit_combine_contribution:
  "traverse_rhs (unit_combine_contribution gs dst cc ex) \<sigma> = res_combine gs dst cc ex \<sigma>"
  unfolding unit_combine_contribution_def res_combine_def by simp

lemma sides_of_rhs_unit_combine_contribution [simp]:
  "sides_of_rhs (unit_combine_contribution gs dst cc ex) \<sigma> = \<bottom>"
  unfolding unit_combine_contribution_def by (simp add: bot_fun_def)

lemma dep_aux_unit_combine_contribution_eq_unit_combine_tree:
  "dep_aux \<sigma> (unit_combine_contribution gs dst cc ex) = dep_aux \<sigma> (unit_combine_tree gs dst cc ex)"
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
  "local_bot_on_locals_lift gs (sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inr g))"
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

subsection \<open>Effectful transfer record factories\<close>

definition unit_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "unit_etf_of_transfer gs tf = \<lparr>
    etf_skip       = (\<lambda>u. unit_edge_tree gs (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. unit_edge_tree gs (apply_tf tf (EA_Assign x e)) u),
    etf_random     = (\<lambda>x u. unit_edge_tree gs (apply_tf tf (EA_Random x)) u),
    etf_branch     = (\<lambda>b pol u. unit_edge_tree gs (branch\<^sup># tf b pol) u),
    etf_body       = (\<lambda>p u. unit_edge_tree gs (body\<^sup># tf p) u),
    etf_return     = (\<lambda>e p u. unit_edge_tree gs (return\<^sup># tf e p) u),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (enter\<^sup># tf xs es) u),
    etf_event      = (\<lambda>ev u. unit_edge_tree gs (event\<^sup># tf ev) u),
    etf_combine    = unit_combine_tree gs
  \<rparr>"

definition mixed_etf_edge_tree ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> edge_action \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "mixed_etf_edge_tree gs tf a u =
    (if local_edge_action gs a then local_edge_tree gs (apply_tf tf a) u
     else unit_edge_tree gs (apply_tf tf a) u)"

definition mixed_etf_of_transfer ::
  "(vname => bool) => 'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "mixed_etf_of_transfer gs tf = \<lparr>
    etf_skip       = mixed_etf_edge_tree gs tf EA_Nop,
    etf_assign     = (\<lambda>x e. mixed_etf_edge_tree gs tf (EA_Assign x e)),
    etf_random     = (\<lambda>x. mixed_etf_edge_tree gs tf (EA_Random x)),
    etf_branch     = (\<lambda>b pol. mixed_etf_edge_tree gs tf (if pol then EA_Assume b else EA_AssumeNot b)),
    etf_body       = (\<lambda>p u. unit_edge_tree gs (body\<^sup># tf p) u),
    etf_return     = (\<lambda>e p. mixed_etf_edge_tree gs tf (EA_Ret e p)),
    etf_enter      = (\<lambda>xs es u. unit_edge_tree gs (enter\<^sup># tf xs es) u),
    etf_event      = (\<lambda>ev u. local_edge_tree gs (event\<^sup># tf ev) u),
    etf_combine    = unit_combine_tree gs
  \<rparr>"

lemma apply_etf_unit_of_transfer:
  "apply_etf (unit_etf_of_transfer gs tf) a u = unit_edge_tree gs (apply_tf tf a) u"
  unfolding unit_etf_of_transfer_def
  by (cases a) simp_all

lemma etf_combine_unit_of_transfer:
  "etf_combine (unit_etf_of_transfer gs tf) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding unit_etf_of_transfer_def by simp

text \<open>\<open>EA_Check\<close> routes through \<^const>\<open>local_edge_tree\<close> here, not
  \<^const>\<open>mixed_etf_edge_tree\<close>: \<^const>\<open>local_edge_action\<close> classifies \<open>EA_Check\<close>
  as unconditionally local (matching \<open>EA_Nop\<close>'s own classification), so this is
  the same routing \<open>mixed_etf_edge_tree gs tf EA_Nop\<close> would have picked, stated
  directly instead of through an edge-action-shaped detour.\<close>
lemma apply_etf_mixed_of_transfer:
  "apply_etf (mixed_etf_of_transfer gs tf) a u =
     (case a of EA_Check bc \<Rightarrow> local_edge_tree gs (apply_tf tf a) u
      | _ \<Rightarrow> mixed_etf_edge_tree gs tf a u)"
  unfolding mixed_etf_of_transfer_def mixed_etf_edge_tree_def
  by (cases a) simp_all

lemma etf_combine_mixed_of_transfer:
  "etf_combine (mixed_etf_of_transfer gs tf) dst cc ex = unit_combine_tree gs dst cc ex"
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

subsection \<open>Generic effectful soundness from domain transfer\<close>

text \<open>
  Both @{const unit_etf_of_transfer} and @{const mixed_etf_of_transfer} route
  \<open>etf_combine\<close> through the same @{const unit_combine_tree} (calls never take
  the local-restriction branch), so the combine obligation is proved once here,
  independent of \<open>tf\<close>, and reused by both instance proofs below.
\<close>
lemma in_gamma_unit_combine_tree:
  fixes dst :: "vname option" and cc ex :: pp
    and \<sigma> :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted" and s t :: store
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ())))"
  assumes t: "t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ())))"
  shows "combine_collect gs dst s t \<in> gamma_state_lift (etf_full (unit_combine_tree gs dst cc ex) \<sigma>)"
proof -
  obtain sc where hc: "\<sigma> (Inl cc) = Lifted sc"
    and hsc: "s \<in> \<lbrakk>sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF s] .
  obtain se where he: "\<sigma> (Inl ex) = Lifted se"
    and hse: "t \<in> \<lbrakk>se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)\<rbrakk>"
    using local_input_witness[OF t] .
  have not_bot: "\<not> is_bot_state (sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))
                   \<and> \<not> is_bot_state (se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))"
    using is_bot_state_witnessI[OF hsc] is_bot_state_witnessI[OF hse] by simp
  have eq: "etf_full (unit_combine_tree gs dst cc ex) \<sigma> =
            Lifted (combine\<^sup># gs dst (sc \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg))
                                     (se \<squnion> (case \<sigma> (Inr ()) of Bot \<Rightarrow> bot | Lifted sg \<Rightarrow> sg)))"
    unfolding etf_full_unit_combine_tree res_combine_def hc he
    using not_bot
    by (smt (verit) assemble_local_global_Lifted combine_collect_sound hsc
        hse is_bot_state_witnessI normalize_lift_not_bot
        transfer_lift2_Lifted)
  show ?thesis
    using combine_collect_sound[OF hsc hse] unfolding eq by simp
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
    show "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). \<forall>v.
              s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_random (unit_etf_of_transfer gs tf) x u) \<sigma>))"
      unfolding unit_etf_of_transfer_def apply_tf.simps by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(b::bexp) (pol::bool) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). bval b s = pol
            \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift
                  (etf_branch (unit_etf_of_transfer gs tf) b pol u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_body (unit_etf_of_transfer gs tf) p u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(e::aexp option) p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
                \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_return (unit_etf_of_transfer gs tf) e p u) \<sigma>))"
      unfolding unit_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>xs (es::aexp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
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
    show "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_collect gs dst s t
                \<in> gamma_state_lift (etf_full (etf_combine (unit_etf_of_transfer gs tf) dst cc ex) \<sigma>))"
      by (auto simp add: etf_combine_unit_of_transfer intro: in_gamma_unit_combine_tree)
  qed
qed


lemma sound_effectful_transfer_mixed_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer_for gs tf"
  assumes loc_inv: "\<And>a. local_edge_action gs a \<Longrightarrow>
      local_edge_invariant gs (apply_tf tf a)"
  shows "sound_effectful_transfer gs (mixed_etf_of_transfer gs tf)"
proof -
  interpret sound_transfer_for gs tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift (etf_skip (mixed_etf_of_transfer gs tf) u) \<sigma>))"
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
                (etf_assign (mixed_etf_of_transfer gs tf) x e u) \<sigma>))"
    proof (intro allI impI ballI)
      fix x e u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      show "s(x := aval e s) \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_assign (mixed_etf_of_transfer gs tf) x e u) \<sigma>)"
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
    show "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). \<forall>v.
              s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_random (mixed_etf_of_transfer gs tf) x u) \<sigma>))"
    proof (intro allI impI ballI)
      fix x u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store and v
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      show "s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_random (mixed_etf_of_transfer gs tf) x u) \<sigma>)"
      proof (cases "local_edge_action gs (EA_Random x)")
        case True
        have inv': "local_edge_invariant gs (tf_random tf x)"
          using loc_inv[OF True] by (simp add: apply_tf.simps)
        have "s(x := v) \<in> gamma_state_lift
                (etf_collecting_full_lift (local_edge_tree gs (tf_random tf x) u) \<sigma>)"
          by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_random_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF True] apply_tf.simps)
      next
        case False
        have "s(x := v) \<in> gamma_state_lift
                (etf_collecting_full_lift (unit_edge_tree gs (tf_random tf x) u) \<sigma>)"
          by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_random_forD)
        then show ?thesis
          by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF False] apply_tf.simps)
      qed
    qed
  next
    show "\<forall>(b::bexp) (pol::bool) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))). bval b s = pol
            \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift
                  (etf_branch (mixed_etf_of_transfer gs tf) b pol u) \<sigma>))"
    proof (intro allI impI ballI)
      fix b pol u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
        and hb: "bval b s = pol"
      show "s \<in> gamma_state_lift (etf_collecting_full_lift
              (etf_branch (mixed_etf_of_transfer gs tf) b pol u) \<sigma>)"
      proof (cases pol)
        case True
        then have hbT: "bval b s = True" using hb by simp
        show ?thesis
        proof (cases "local_edge_action gs (EA_Assume b)")
          case local_True: True
          have inv': "local_edge_invariant gs (branch\<^sup># tf b True)"
            using loc_inv[OF local_True] by (simp add: apply_tf.simps)
          have "s \<in> gamma_state_lift
                  (etf_collecting_full_lift (local_edge_tree gs (branch\<^sup># tf b True) u) \<sigma>)"
            by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_branch_forD[OF _ hbT])
          then show ?thesis
            using True
            by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF local_True] apply_tf.simps)
        next
          case local_False: False
          have "s \<in> gamma_state_lift
                  (etf_collecting_full_lift (unit_edge_tree gs (branch\<^sup># tf b True) u) \<sigma>)"
            by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_branch_forD[OF _ hbT])
          then show ?thesis
            using True
            by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF local_False] apply_tf.simps)
        qed
      next
        case False
        then have hbF: "bval b s = False" using hb by simp
        show ?thesis
        proof (cases "local_edge_action gs (EA_AssumeNot b)")
          case local_True: True
          have inv': "local_edge_invariant gs (branch\<^sup># tf b False)"
            using loc_inv[OF local_True] by (simp add: apply_tf.simps)
          have "s \<in> gamma_state_lift
                  (etf_collecting_full_lift (local_edge_tree gs (branch\<^sup># tf b False) u) \<sigma>)"
            by (rule in_gamma_local_edge_tree[OF inv' inr s]) (rule tf_sound_branch_forD[OF _ hbF])
          then show ?thesis
            using False
            by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_local[OF local_True] apply_tf.simps)
        next
          case local_False: False
          have "s \<in> gamma_state_lift
                  (etf_collecting_full_lift (unit_edge_tree gs (branch\<^sup># tf b False) u) \<sigma>)"
            by (rule in_gamma_unit_edge_tree[OF inr s]) (rule tf_sound_branch_forD[OF _ hbF])
          then show ?thesis
            using False
            by (simp add: mixed_etf_of_transfer_def mixed_etf_edge_tree_unit[OF local_False] apply_tf.simps)
        qed
      qed
    qed

  next
    show "\<forall>p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_body (mixed_etf_of_transfer gs tf) p u) \<sigma>))"
      unfolding mixed_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>(e::aexp option) p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
                \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_return (mixed_etf_of_transfer gs tf) e p u) \<sigma>))"
    proof (intro allI impI ballI)
      fix e p u :: _ and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state lifted" and s :: store
      assume inr: "inr_slot_locals_bot gs \<sigma>"
        and s: "s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"
      show "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in>
              gamma_state_lift (etf_collecting_full_lift
                (etf_return (mixed_etf_of_transfer gs tf) e p u) \<sigma>)"
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
    show "\<forall>xs (es::aexp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
                \<in> gamma_state_lift (etf_collecting_full_lift
                (etf_enter (mixed_etf_of_transfer gs tf) xs es u) \<sigma>))"
      unfolding mixed_etf_of_transfer_def by (auto intro: in_gamma_unit_edge_tree)
  next
    show "\<forall>ev u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ()))).
              s \<in> gamma_state_lift (etf_collecting_full_lift
                    (etf_event (mixed_etf_of_transfer gs tf) ev u) \<sigma>))"
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
                    (etf_event (mixed_etf_of_transfer gs tf) ev u) \<sigma>)"
        by (simp add: mixed_etf_of_transfer_def)
    qed
  next
    show "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
            (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ()))).
            \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ()))).
              combine_collect gs dst s t
                \<in> gamma_state_lift (etf_full (etf_combine (mixed_etf_of_transfer gs tf) dst cc ex) \<sigma>))"
      by (auto simp add: etf_combine_mixed_of_transfer intro: in_gamma_unit_combine_tree)
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
