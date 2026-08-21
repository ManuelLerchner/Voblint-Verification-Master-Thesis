theory Side_Buffering
  imports Strategy_Tree_Monad
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

lemma acc_keys_add:
  "map fst (acc_add k d acc)
     = (if k \<in> set (map fst acc) then map fst acc else map fst acc @ [k])"
proof (induction acc)
  case Nil
  show ?case by simp
next
  case (Cons kv kvs)
  obtain k' d' where kv: "kv = (k', d')" by (cases kv)
  show ?case
  proof (cases "k' = k")
    case True
    then show ?thesis by (simp add: kv)
  next
    case False
    then show ?thesis using Cons.IH by (simp add: kv)
  qed
qed

lemma acc_add_append:
  "k \<notin> set (map fst acc) \<Longrightarrow> acc_add k d acc = acc @ [(k, d)]"
proof (induction acc)
  case Nil
  show ?case by simp
next
  case (Cons kv kvs)
  obtain k' d' where kv: "kv = (k', d')" by (cases kv)
  have ne: "k' \<noteq> k" using Cons.prems by (auto simp: kv)
  have notin: "k \<notin> set (map fst kvs)" using Cons.prems by (simp add: kv)
  show ?case using Cons.IH[OF notin] ne by (simp add: kv)
qed

lemma distinct_acc_add:
  "distinct (map fst acc) \<Longrightarrow> distinct (map fst (acc_add k d acc))"
  by (cases "k \<in> set (map fst acc)") (simp_all add: acc_keys_add)

subsection \<open>Buffering a right-hand side\<close>

primrec flush_sides ::
  "('g \<times> 'd) list \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "flush_sides [] t = t"
| "flush_sides (kv # kvs) t = Side (fst kv) (snd kv) (flush_sides kvs t)"

primrec buffer_aux ::
  "('g \<times> 'd) list
   \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "buffer_aux acc (Answer d) = flush_sides acc (Answer d)"
| "buffer_aux acc (QueryL y g) = QueryL y (\<lambda>v. buffer_aux acc (g v))"
| "buffer_aux acc (QueryG y g) = QueryG y (\<lambda>v. buffer_aux acc (g v))"
| "buffer_aux acc (Side y d t) = buffer_aux (acc_add y d acc) t"

definition buffer_sides ::
  "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "buffer_sides t = buffer_aux [] t"

definition buffer_eqs ::
  "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT \<Rightarrow> ('x, 'g, 'd) eqsT" where
  "buffer_eqs T = (\<lambda>x. buffer_sides (T x))"

lemma buffer_eqs_apply [simp]: "buffer_eqs T x = buffer_sides (T x)"
  by (simp add: buffer_eqs_def)

subsection \<open>The declarative reading is unchanged\<close>

lemma traverse_flush_sides [simp]:
  "traverse_rhs (flush_sides acc t) \<sigma> = traverse_rhs t \<sigma>"
  by (induction acc) simp_all

lemma traverse_buffer_aux [simp]:
  "traverse_rhs (buffer_aux acc t) \<sigma> = traverse_rhs t \<sigma>"
  by (induction t arbitrary: acc) simp_all

lemma traverse_buffer_sides [simp]:
  "traverse_rhs (buffer_sides t) \<sigma> = traverse_rhs t \<sigma>"
  by (simp add: buffer_sides_def)

lemma sides_flush_sides:
  "sides_of_rhs (flush_sides acc t) \<sigma> z = sides_of_rhs t \<sigma> z \<squnion> acc_val acc z"
proof (induction acc arbitrary: z)
  case Nil
  show ?case by simp
next
  case (Cons kv kvs)
  obtain k d where kv: "kv = (k, d)" by (cases kv)
  show ?case
    by (simp add: kv Let_def Cons.IH acc_val_Cons ac_simps)
qed

lemma sides_buffer_aux:
  "sides_of_rhs (buffer_aux acc t) \<sigma> z = sides_of_rhs t \<sigma> z \<squnion> acc_val acc z"
proof (induction t arbitrary: acc z)
  case (Answer d)
  show ?case by (simp add: sides_flush_sides)
next
  case (Side y d t)
  show ?case
    by (simp add: Side.IH acc_val_add Let_def ac_simps)
qed simp_all

lemma sides_buffer_sides [simp]:
  "sides_of_rhs (buffer_sides t) \<sigma> = sides_of_rhs t \<sigma>"
  by (rule ext) (simp add: buffer_sides_def sides_buffer_aux)

lemma dep_aux_flush_sides [simp]:
  "dep_aux \<sigma> (flush_sides acc t) = dep_aux \<sigma> t"
  by (induction acc) simp_all

lemma dep_aux_buffer_aux [simp]:
  "dep_aux \<sigma> (buffer_aux acc t) = dep_aux \<sigma> t"
  by (induction t arbitrary: acc) simp_all

lemma dep_aux_buffer_sides [simp]:
  "dep_aux \<sigma> (buffer_sides t) = dep_aux \<sigma> t"
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
  "side_path \<sigma> (flush_sides acc t) = map fst acc @ side_path \<sigma> t"
  by (induction acc) simp_all

lemma distinct_side_path_buffer_aux:
  "distinct (map fst acc) \<Longrightarrow> distinct (side_path \<sigma> (buffer_aux acc t))"
proof (induction t arbitrary: acc)
  case (Side y d t)
  then show ?case by (simp add: distinct_acc_add)
qed simp_all

theorem distinct_side_path_buffer_sides:
  "distinct (side_path \<sigma> (buffer_sides t))"
  by (simp add: buffer_sides_def distinct_side_path_buffer_aux)

text \<open>
  So a buffered system writes each key at most once per evaluation, and the
  update rule's per-origin slot for that key is written exactly once, with the
  completed contribution. This replaces the generator-level assumption that no
  two contributions of one right-hand side can name the same key --- an
  assumption about how equations happen to be built, which a shared resume node
  refutes --- with a property of the equations handed to the solver.
\<close>

subsection \<open>Buffering is idempotent\<close>

lemma acc_add_fold_append:
  "distinct (map fst (acc0 @ acc))
     \<Longrightarrow> foldl (\<lambda>a kv. acc_add (fst kv) (snd kv) a) acc0 acc = acc0 @ acc"
proof (induction acc arbitrary: acc0)
  case (Cons kv kvs)
  obtain k d where kv: "kv = (k, d)" by (cases kv)
  have "k \<notin> set (map fst acc0)" using Cons.prems by (simp add: kv)
  then have "acc_add k d acc0 = acc0 @ [(k, d)]" by (rule acc_add_append)
  then show ?case using Cons.IH[of "acc0 @ [(k, d)]"] Cons.prems by (simp add: kv)
qed simp

lemma buffer_aux_flush_sides:
  "buffer_aux acc0 (flush_sides acc t)
     = buffer_aux (foldl (\<lambda>a kv. acc_add (fst kv) (snd kv) a) acc0 acc) t"
  by (induction acc arbitrary: acc0) simp_all

lemma buffer_sides_idem: "buffer_sides (buffer_sides t) = buffer_sides t"
proof -
  have "buffer_aux [] (buffer_aux acc t) = buffer_aux acc t"
    if "distinct (map fst acc)" for acc
    using that
  proof (induction t arbitrary: acc)
    case (Answer d)
    then show ?case
      by (simp add: buffer_aux_flush_sides acc_add_fold_append)
  next
    case (Side y d t)
    then show ?case by (simp add: distinct_acc_add)
  qed simp_all
  from this[of "[]"] show ?thesis by (simp add: buffer_sides_def)
qed

lemma buffer_eqs_idem: "buffer_eqs (buffer_eqs T) = buffer_eqs T"
  by (rule ext) (simp add: buffer_sides_idem)

subsection \<open>The one transfer every consumer needs\<close>

text \<open>
  \<^const>\<open>part_post_solution\<close> --- the solver interface the analyzer soundness
  spine consumes --- is stated over \<^const>\<open>dep\<^sub>L\<close>,
  \<^const>\<open>traverse_rhs\<close> and \<^const>\<open>sides_of_rhs\<close> alone. All three are
  invariant under buffering, so a solution of the buffered system is a solution
  of the original one and no result upstream of the solver changes.
\<close>

lemma dep_buffer_eqs [simp]: "dep (buffer_eqs T) \<sigma> x = dep T \<sigma> x"
  by (simp add: dep_def)

lemma dep_L_buffer_eqs [simp]: "dep\<^sub>L (buffer_eqs T) \<sigma> x = dep\<^sub>L T \<sigma> x"
  by (simp add: dep\<^sub>L_def)

theorem part_post_solution_buffer_eqs [simp]:
  "part_post_solution (buffer_eqs T) x \<sigma> vars = part_post_solution T x \<sigma> vars"
  by simp

end
