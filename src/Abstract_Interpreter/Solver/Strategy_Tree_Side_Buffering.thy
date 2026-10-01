theory Strategy_Tree_Side_Buffering
  imports "TD.Basics_side"
begin

section \<open>Per-key buffering of one right-hand side's side effects\<close>

text \<open>
  One right-hand side may emit several \<^const>\<open>Side\<close> writes to the same key.
  Declaratively that is already a join --- \<^const>\<open>sides_of_rhs\<close>'s own
  \<^const>\<open>Side\<close> equation joins into the key it writes --- but a solver applies
  its update rule once per \<^const>\<open>Side\<close>, on the accumulate reached so far. An
  update rule that keeps one slot per write origin therefore records a partial
  accumulate, and the global it feeds can fall below a value that same origin
  has already established; the drop destabilizes that global's readers, whose
  re-evaluation restores it, and the two alternate without converging.

  \<open>buffer_sides\<close> removes the cause rather than the symptom: it accumulates
  every write per key and flushes each key exactly once, so an update rule only
  ever sees a completed contribution. Nothing here is specific to procedure
  calls, contexts, or the D/G layer --- the property being repaired is that a
  right-hand side may name one key twice, which any equation generator can do.
\<close>

subsection \<open>The per-key accumulator\<close>

text \<open>
  An association list rather than a map: the flush below emits one
  \<^const>\<open>Side\<close> per entry in list order, and \<open>acc_add\<close> appends an
  unseen key at the end, so that order is first occurrence in the traversal.
  A map would leave the flush order to the key type's own arrangement, which
  is exactly the scheduling detail a narrowing update rule is sensitive to.
\<close>

fun acc_add ::
  "'g \<Rightarrow> 'd::bounded_semilattice_sup_bot \<Rightarrow> ('g \<times> 'd) list \<Rightarrow> ('g \<times> 'd) list"
where
  "acc_add k d [] = [(k, d)]"
| "acc_add k d ((k', d') # kvs) =
     (if k' = k then (k', d' \<squnion> d) # kvs else (k', d') # acc_add k d kvs)"

fun acc_at :: "'g \<Rightarrow> ('g \<times> 'd::bounded_semilattice_sup_bot) list \<Rightarrow> 'd" where
  "acc_at k [] = bot"
| "acc_at k ((k', d') # kvs) = (if k' = k then d' else bot) \<squnion> acc_at k kvs"

definition acc_val ::
  "('g \<times> 'd::bounded_semilattice_sup_bot) list \<Rightarrow> 'x + 'g \<Rightarrow> 'd" where
  "acc_val acc z = (case z of Inl _ \<Rightarrow> bot | Inr k \<Rightarrow> acc_at k acc)"

lemma acc_val_Inl [simp]: "acc_val acc (Inl u) = bot"
  by (simp add: acc_val_def)

lemma acc_val_Inr [simp]: "acc_val acc (Inr k) = acc_at k acc"
  by (simp add: acc_val_def)

lemma acc_val_Nil [simp]: "acc_val [] z = bot"
  by (cases z) simp_all

lemma acc_at_add:
  "acc_at k' (acc_add k d acc) = acc_at k' acc \<squnion> (if k' = k then d else bot)"
  by (induction acc) (auto simp: ac_simps)

lemma acc_val_add:
  "acc_val (acc_add k d acc) z = acc_val acc z \<squnion> (if z = Inr k then d else bot)"
  by (cases z) (simp_all add: acc_at_add)

lemma acc_val_Cons:
  "acc_val ((k, d) # kvs) z = acc_val kvs z \<squnion> (if z = Inr k then d else bot)"
  by (cases z) (auto simp: ac_simps)

subsubsection \<open>Key order and distinctness\<close>

text \<open>What the flush order rests on: an unseen key is appended, a seen one is joined in
  place, so the key list only ever grows at the end and stays distinct.\<close>
lemma acc_keys_add:
  "map fst (acc_add k d acc)
     = (if k \<in> set (map fst acc) then map fst acc else map fst acc @ [k])"
  by (induction acc) (auto simp add: rev_image_eqI)

lemma acc_add_append:
  "k \<notin> set (map fst acc) \<Longrightarrow> acc_add k d acc = acc @ [(k, d)]"
  by (induction acc) (auto simp add: rev_image_eqI)

lemma distinct_acc_add:
  "distinct (map fst acc) \<Longrightarrow> distinct (map fst (acc_add k d acc))"
  by (cases "k \<in> set (map fst acc)") (simp_all add: acc_keys_add)

subsection \<open>Buffering a right-hand side\<close>

text \<open>The traversal that does the buffering: writes are collected into the accumulator on
  the way down and emitted at the next flush point, so a query branch cannot lose the writes
  made before it.

  A flush point is every answer, and every local read \<open>QueryL y\<close> with
  \<open>publish_before y\<close>. Flushing only at answers gives the strongest guarantee: no key is
  written twice on any path, whatever the tree. But it also holds back a write past the
  local reads that follow it, and a local read is what makes the solver evaluate the
  unknown read. A call site publishes the callee's entry state and then reads the
  callee's exit; held back to the answer, the publication reaches the solver only after
  the callee has been solved from an entry it has not yet received. Goblint's
  normal-call transfer issues \<open>sidel\<close> before \<open>getl\<close>, and its solver applies a
  side effect when it is issued, so there the callee starts from the published entry. A
  flush before such a read costs the at-most-once guarantee for keys written again after
  it, so \<open>distinct_side_path_buffer_sides\<close> below states when it still holds, and the
  caller chooses \<open>publish_before\<close> where it can tell that it does.\<close>
text \<open>
  A key whose completed contribution is \<^const>\<open>bot\<close> is not flushed. Publishing
  it would be a no-op for every consumer --- \<open>sides_of_rhs\<close> joins it in, and a
  join with \<^const>\<open>bot\<close> changes nothing --- while still costing the solver an
  update-rule application and a destabilization of that global's readers. The
  generator appends the publication to every answer path without asking whether
  the transfer wrote anything, so on a node that touches no global this is the
  only place the emptiness is known.
\<close>
primrec flush_sides ::
  "('g \<times> 'd::bounded_semilattice_sup_bot) list \<Rightarrow> ('x, 'g, 'd) strategy_tree
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "flush_sides [] t = t"
| "flush_sides (kv # kvs) t =
     (if snd kv \<le> bot then flush_sides kvs t
      else Side (fst kv) (snd kv) (flush_sides kvs t))"

abbreviation flushed :: "('g \<times> 'd::bounded_semilattice_sup_bot) list \<Rightarrow> ('g \<times> 'd) list"
  where "flushed acc \<equiv> filter (\<lambda>kv. \<not> snd kv \<le> bot) acc"

primrec buffer_aux ::
  "('x \<Rightarrow> bool) \<Rightarrow> ('g \<times> 'd) list
   \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "buffer_aux publish_before acc (Answer d) = flush_sides acc (Answer d)"
| "buffer_aux publish_before acc (QueryL y g) =
     (if publish_before y
      then flush_sides acc (QueryL y (\<lambda>v. buffer_aux publish_before [] (g v)))
      else QueryL y (\<lambda>v. buffer_aux publish_before acc (g v)))"
| "buffer_aux publish_before acc (QueryG y g) =
     QueryG y (\<lambda>v. buffer_aux publish_before acc (g v))"
| "buffer_aux publish_before acc (Side y d t) = buffer_aux publish_before (acc_add y d acc) t"

definition buffer_sides ::
  "('x \<Rightarrow> bool) \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "buffer_sides publish_before t = buffer_aux publish_before [] t"

definition buffer_eqs ::
  "('x \<Rightarrow> 'x \<Rightarrow> bool) \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT
   \<Rightarrow> ('x, 'g, 'd) eqsT" where
  "buffer_eqs publish_before T = (\<lambda>x. buffer_sides (publish_before x) (T x))"

lemma buffer_eqs_apply [simp]:
  "buffer_eqs publish_before T x = buffer_sides (publish_before x) (T x)"
  by (simp add: buffer_eqs_def)

subsection \<open>The declarative reading is unchanged\<close>

text \<open>Buffering is invisible to the declarative reading: the local value is untouched, and
  the side contribution at each key is the same join as before, only emitted at a flush
  point. That is what makes this a scheduling change and not a semantic one, wherever the
  flush points are.\<close>
lemma traverse_rhs_flush_sides [simp]:
  "traverse_rhs (flush_sides acc t) \<sigma> = traverse_rhs t \<sigma>"
  by (induction acc) simp_all

lemma traverse_rhs_buffer_aux [simp]:
  "traverse_rhs (buffer_aux publish_before acc t) \<sigma> = traverse_rhs t \<sigma>"
  by (induction t arbitrary: acc) simp_all

lemma traverse_rhs_buffer_sides [simp]:
  "traverse_rhs (buffer_sides publish_before t) \<sigma> = traverse_rhs t \<sigma>"
  by (simp add: buffer_sides_def)

lemma sides_of_rhs_flush_sides [simp]:
  "sides_of_rhs (flush_sides acc t) \<sigma> z = sides_of_rhs t \<sigma> z \<squnion> acc_val acc z"
  by (induction acc arbitrary: z)
     (auto simp add: Let_def acc_val_Cons ac_simps dest!: le_bot)

lemma sides_of_rhs_buffer_aux [simp]:
  "sides_of_rhs (buffer_aux publish_before acc t) \<sigma> z = sides_of_rhs t \<sigma> z \<squnion> acc_val acc z"
  by (induction t arbitrary: acc z) (auto simp add: acc_val_add Let_def ac_simps)

lemma sides_of_rhs_buffer_sides [simp]:
  "sides_of_rhs (buffer_sides publish_before t) \<sigma> = sides_of_rhs t \<sigma>"
  by (rule ext) (simp add: buffer_sides_def)

lemma dep_aux_flush_sides [simp]:
  "dep_aux \<sigma> (flush_sides acc t) = dep_aux \<sigma> t"
  by (induction acc) simp_all

lemma dep_aux_buffer_aux [simp]:
  "dep_aux \<sigma> (buffer_aux publish_before acc t) = dep_aux \<sigma> t"
  by (induction t arbitrary: acc) simp_all

lemma dep_aux_buffer_sides [simp]:
  "dep_aux \<sigma> (buffer_sides publish_before t) = dep_aux \<sigma> t"
  by (simp add: buffer_sides_def)

subsection \<open>The operational property the update rules rely on\<close>

text \<open>
  Semantic preservation alone does not say a solver sees fewer writes; it says
  the writes sum to the same thing. \<open>side_path\<close> names the keys one
  evaluation actually writes, in the order it writes them --- the continuations
  are functions, so which \<^const>\<open>Side\<close> nodes an evaluation meets depends on
  \<open>\<sigma>\<close>, and the statement has to be relative to it.
\<close>

primrec side_path ::
  "('x + 'g \<Rightarrow> 'd) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> 'g list" where
  "side_path \<sigma> (Answer d) = []"
| "side_path \<sigma> (QueryL y g) = side_path \<sigma> (g (\<sigma> (Inl y)))"
| "side_path \<sigma> (QueryG y g) = side_path \<sigma> (g (\<sigma> (Inr y)))"
| "side_path \<sigma> (Side y d t) = y # side_path \<sigma> t"

lemma side_path_flush_sides [simp]:
  "side_path \<sigma> (flush_sides acc t) = map fst (flushed acc) @ side_path \<sigma> t"
  by (induction acc) simp_all

text \<open>
  The flush points split one evaluation of the original tree into segments, and
  the buffer writes a key once for each segment in which the key receives a value
  other than \<^const>\<open>bot\<close>. The buffered evaluation therefore writes each key at
  most once exactly when no key receives such a value in two segments.
  \<open>settled_writes C P\<close> walks the evaluation and checks this: \<open>C\<close> holds the
  keys an earlier flush point has already written, and \<open>P\<close> the keys the current
  segment will write at the next one.
\<close>

primrec settled_writes ::
  "('x \<Rightarrow> bool) \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'g set \<Rightarrow> 'g set
   \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> bool"
where
  "settled_writes publish_before \<sigma> C P (Answer d) = True"
| "settled_writes publish_before \<sigma> C P (QueryL y g) =
     (if publish_before y
      then settled_writes publish_before \<sigma> (C \<union> P) {} (g (\<sigma> (Inl y)))
      else settled_writes publish_before \<sigma> C P (g (\<sigma> (Inl y))))"
| "settled_writes publish_before \<sigma> C P (QueryG y g) =
     settled_writes publish_before \<sigma> C P (g (\<sigma> (Inr y)))"
| "settled_writes publish_before \<sigma> C P (Side y d t) =
     ((d \<le> bot \<or> y \<notin> C)
      \<and> settled_writes publish_before \<sigma> C (if d \<le> bot then P else insert y P) t)"

lemma flushed_keys_acc_add:
  "fst ` set (flushed (acc_add k d acc))
     = fst ` set (flushed acc) \<union> (if d \<le> bot then {} else {k})"
proof (induction acc)
  case Nil
  then show ?case by simp
next
  case (Cons kv acc)
  obtain k' d' where kv: "kv = (k', d')" by (cases kv)
  show ?case
  proof (cases "k' = k")
    case True
    then show ?thesis
      by (cases "d' \<le> bot"; cases "d \<le> bot") (auto simp add: kv)
  next
    case False
    then show ?thesis
      using Cons.IH by (cases "d' \<le> bot") (auto simp add: kv)
  qed
qed

lemma distinct_side_path_buffer_aux:
  assumes "distinct (map fst acc)"
    and "fst ` set (flushed acc) \<inter> C = {}"
    and "settled_writes publish_before \<sigma> C (fst ` set (flushed acc)) t"
  shows "distinct (side_path \<sigma> (buffer_aux publish_before acc t))
           \<and> set (side_path \<sigma> (buffer_aux publish_before acc t)) \<inter> C = {}"
  using assms
proof (induction t arbitrary: acc C)
  case (Answer d)
  then show ?case by (auto simp add: distinct_map_filter)
next
  case (QueryL y g)
  show ?case
  proof (cases "publish_before y")
    case True
    have "distinct (side_path \<sigma> (buffer_aux publish_before [] (g (\<sigma> (Inl y)))))
        \<and> set (side_path \<sigma> (buffer_aux publish_before [] (g (\<sigma> (Inl y)))))
            \<inter> (C \<union> fst ` set (flushed acc)) = {}"
      by (rule QueryL.IH) (use QueryL.prems(3) True in simp_all)
    then show ?thesis
      using QueryL.prems(1,2) True by (auto simp add: distinct_map_filter)
  next
    case False
    then show ?thesis using QueryL.prems by (simp add: QueryL.IH)
  qed
next
  case (QueryG y g)
  then show ?case by simp
next
  case (Side y d t)
  have "distinct (map fst (acc_add y d acc))"
    using Side.prems(1) by (rule distinct_acc_add)
  moreover have "fst ` set (flushed (acc_add y d acc)) \<inter> C = {}"
    unfolding flushed_keys_acc_add using Side.prems(2,3) by auto
  moreover have "settled_writes publish_before \<sigma> C (fst ` set (flushed (acc_add y d acc))) t"
    unfolding flushed_keys_acc_add using Side.prems(3) by (cases "d \<le> bot") simp_all
  ultimately have "distinct (side_path \<sigma> (buffer_aux publish_before (acc_add y d acc) t))
      \<and> set (side_path \<sigma> (buffer_aux publish_before (acc_add y d acc) t)) \<inter> C = {}"
    by (rule Side.IH)
  then show ?case by simp
qed

theorem distinct_side_path_buffer_sides:
  assumes "settled_writes publish_before \<sigma> {} {} t"
  shows "distinct (side_path \<sigma> (buffer_sides publish_before t))"
  using distinct_side_path_buffer_aux[where acc = "[]" and C = "{}"] assms
  by (simp add: buffer_sides_def)

text \<open>With no flush point before a local read nothing is ever closed, so the
  condition holds for every tree and every evaluation: flushing at answers only
  writes each key at most once unconditionally.\<close>

lemma settled_writes_answers_only:
  "settled_writes (\<lambda>_. False) \<sigma> {} P t"
  by (induction t arbitrary: P) simp_all

corollary distinct_side_path_buffer_sides_answers_only:
  "distinct (side_path \<sigma> (buffer_sides (\<lambda>_. False) t))"
  by (rule distinct_side_path_buffer_sides) (rule settled_writes_answers_only)

text \<open>The elision, pinned at both polarities: a completed contribution of
  \<^const>\<open>bot\<close> costs the evaluation no write, and one carrying a value still
  costs exactly one. Stated over \<open>side_path\<close> because the writes an evaluation
  performs are what the elision is for.\<close>

lemma side_path_flush_sides_bot [simp]:
  "side_path \<sigma> (flush_sides [(k, bot)] t) = side_path \<sigma> t"
  by simp

lemma side_path_flush_sides_value:
  assumes "\<not> d \<le> bot"
  shows "side_path \<sigma> (flush_sides [(k, d)] t) = k # side_path \<sigma> t"
  using assms by simp

text \<open>
  So a buffered system writes each key at most once per evaluation whenever its
  writes settle: every key an evaluation contributes to is flushed exactly once,
  with its completed contribution, and a key the evaluation never touches is not
  written at all. Flushing at answers only replaces the generator-level
  assumption that no two contributions of one right-hand side can name the same
  key --- an assumption about how equations happen to be built, which a shared
  resume node refutes --- with a property of the equations handed to the solver.
  A caller that also flushes before local reads takes that assumption back for
  the keys written on both sides of such a read, and must know there are none.
\<close>

subsection \<open>Buffering is idempotent\<close>

text \<open>The entries a flush drops are exactly the ones it would have skipped, so
  flushing the filtered accumulator is the same tree.\<close>
lemma flush_sides_flushed [simp]: "flush_sides (flushed acc) t = flush_sides acc t"
  by (induction acc) simp_all

lemma acc_add_fold_append:
  "distinct (map fst (acc0 @ acc))
     \<Longrightarrow> foldl (\<lambda>a kv. acc_add (fst kv) (snd kv) a) acc0 acc = acc0 @ acc"
  by (induction acc arbitrary: acc0) (auto simp add: acc_add_append)

lemma buffer_aux_flush_sides:
  "buffer_aux publish_before acc0 (flush_sides acc t)
     = buffer_aux publish_before
         (foldl (\<lambda>a kv. acc_add (fst kv) (snd kv) a) acc0 (flushed acc)) t"
  by (induction acc arbitrary: acc0) simp_all

lemma buffer_sides_idem [simp]:
  "buffer_sides publish_before (buffer_sides publish_before t) = buffer_sides publish_before t"
proof -
  have "\<And>acc. distinct (map fst acc)
      \<Longrightarrow> buffer_aux publish_before [] (buffer_aux publish_before acc t)
          = buffer_aux publish_before acc t"
    by (induction t)
       (auto simp add: buffer_aux_flush_sides acc_add_fold_append distinct_acc_add
             distinct_map_filter)
  then show ?thesis by (simp add: buffer_sides_def)
qed

subsection \<open>The one transfer every consumer needs\<close>

text \<open>
  \<^const>\<open>part_post_solution\<close> --- the solver interface the analyzer soundness
  spine consumes --- is stated over \<^const>\<open>dep\<^sub>L\<close>,
  \<^const>\<open>traverse_rhs\<close> and \<^const>\<open>sides_of_rhs\<close> alone. All three are
  invariant under buffering, wherever the flush points are, so a solution of the
  buffered system is a solution of the original one. Buffering preserves this
  declarative right-hand-side semantics and the post-solution obligation the
  soundness proof consumes; it does not claim the buffered and unbuffered systems
  drive the solver through the same operational iteration, or, under widening, to
  the same computed post-solution.
\<close>

lemma dep_buffer_eqs [simp]: "dep (buffer_eqs publish_before T) \<sigma> x = dep T \<sigma> x"
  by (simp add: dep_def)

lemma dep_L_buffer_eqs [simp]: "dep\<^sub>L (buffer_eqs publish_before T) \<sigma> x = dep\<^sub>L T \<sigma> x"
  by (simp add: dep\<^sub>L_def)

theorem part_post_solution_buffer_eqs [simp]:
  "part_post_solution (buffer_eqs publish_before T) x \<sigma> vars
     = part_post_solution T x \<sigma> vars"
  by simp

end
