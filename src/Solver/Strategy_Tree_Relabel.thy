theory Strategy_Tree_Relabel
  imports Strategy_Tree_Sequencing
begin

section \<open>Relabelling the unknowns of a strategy tree\<close>

text \<open>
  A strategy tree's \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close> nodes name the unknowns it reads
  and writes: a local key (\<open>'x\<close>) and a global key (\<open>'g\<close>). \<open>relabel_ltree\<close> and
  \<open>relabel_gtree\<close> rewrite those keys in place, leaving every value and the
  tree's shape untouched -- the same computation, addressed differently. A
  generator built once against bare addressing reuses it at a context-sensitive
  one this way: \<open>relabel_ltree (\<lambda>w. (w, ctx))\<close> composed with \<open>relabel_gtree
  (\<lambda>_. gkey ctx)\<close> turns a context-insensitive tree into the keyed tree a
  caller would otherwise build and reprove sound from scratch per context. The
  win is definition and proof reuse, not runtime sharing -- each relabel
  produces a fresh tree value; nothing here is shared or memoized.
\<close>

subsection \<open>Relabelling local unknowns\<close>

primrec relabel_ltree ::
  "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('y, 'g, 'd) strategy_tree" where
  "relabel_ltree h (Answer d) = Answer d"
| "relabel_ltree h (QueryL y f) = QueryL (h y) (\<lambda>d. relabel_ltree h (f d))"
| "relabel_ltree h (QueryG y f) = QueryG y (\<lambda>d. relabel_ltree h (f d))"
| "relabel_ltree h (Side y d t) = Side y d (relabel_ltree h t)"

text \<open>
  Evaluating a relabelled tree at \<open>\<sigma>\<close> is the same as evaluating the original
  at the environment read back through \<open>h\<close>: a relabel only changes which slot
  of \<open>\<sigma>\<close> each \<open>QueryL\<close> reads, never what the read contributes to the answer.
\<close>

lemma traverse_rhs_relabel_ltree:
  "traverse_rhs (relabel_ltree h t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum h id z))"
  by (induction t) auto

lemma dep_aux_relabel_ltree:
  "dep_aux \<sigma> (relabel_ltree h t)
   = map_sum h id ` dep_aux (\<lambda>z. \<sigma> (map_sum h id z)) t"
  by (induction t arbitrary: \<sigma>) auto

subsection \<open>Relabelling global unknowns\<close>

primrec relabel_gtree ::
  "('g \<Rightarrow> 'h) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'h, 'd) strategy_tree" where
  "relabel_gtree r (Answer d) = Answer d"
| "relabel_gtree r (QueryL y f) = QueryL y (\<lambda>d. relabel_gtree r (f d))"
| "relabel_gtree r (QueryG y f) = QueryG (r y) (\<lambda>d. relabel_gtree r (f d))"
| "relabel_gtree r (Side y d t) = Side (r y) d (relabel_gtree r t)"

text \<open>
  Mirrors \<open>traverse_rhs_relabel_ltree\<close>: reading a globally-relabelled
  tree at \<open>\<sigma>\<close> is reading the original at the pullback of \<open>\<sigma>\<close> through \<open>r\<close>. \<open>r\<close>
  need not be injective -- two source globals can land on the same target key --
  so this pullback, not a plain \<open>\<sigma> \<circ> r\<close> substitution, is what stays correct
  in that case.
\<close>

lemma traverse_rhs_relabel_gtree:
  "traverse_rhs (relabel_gtree r t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum id r z))"
  by (induction t) auto

lemma dep_aux_relabel_gtree:
  "dep_aux \<sigma> (relabel_gtree r t)
   = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) auto

subsection \<open>Routing: composing both relabels for context-sensitive addressing\<close>

text \<open>
  Context-sensitivity uses both relabels at once: a per-edge tree built against
  a bare predecessor key \<open>u\<close> and an unkeyed global write is read against the
  context-keyed addressing by reindexing its local unknown \<open>u \<mapsto> (u, ctx)\<close> and
  rerouting its global write to \<open>gkey ctx\<close>. Composing the two relabels
  therefore denotes the original tree read against the composed pullback --
  this is the local half of routing correctness: it exhibits, as one
  \<^const>\<open>map_sum\<close> pullback, exactly which slots a keyed edge tree consults.
\<close>

lemma traverse_intra_keyed:
  "traverse_rhs (relabel_gtree (\<lambda>_. gkey ctx) (relabel_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
   = traverse_rhs t (\<lambda>z. \<sigma> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z))"
  by (simp add: traverse_rhs_relabel_gtree traverse_rhs_relabel_ltree sum.map_comp o_def)

subsection \<open>Side effects under a relabel\<close>

text \<open>
  \<^const>\<open>relabel_ltree\<close> never touches a \<open>QueryG\<close>/\<open>Side\<close> key, so its per-name
  side map is just the original read against the local pullback. For
  \<^const>\<open>relabel_gtree\<close>, a non-injective \<open>r\<close> can route two distinct source
  globals to the same target key, and the two contributions then join at that
  key -- so there is no general law for \<open>sides_of_rhs (relabel_gtree r t) \<sigma>
  (Inr (r g))\<close> in terms of \<open>sides_of_rhs t \<sigma> (Inr g)\<close> alone. The lemmas below
  cover the two shapes every routing site in this codebase needs: a
  \<^typ>\<open>unit\<close>-global tree collapsed onto one target key (where the collision
  question cannot arise, since there is only one source key to begin with),
  and a target key entirely outside \<open>r\<close>'s range.
\<close>

lemma sides_relabel_ltree_Inr:
  "sides_of_rhs (relabel_ltree h t) \<sigma> (Inr gg)
   = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum h id z)) (Inr gg)"
  by (induction t) (auto simp: Let_def)

lemma sides_relabel_gtree_unit:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (relabel_gtree r t) \<sigma> (Inr (r ()))
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id r z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_relabel_gtree_unit_gen:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (relabel_gtree (\<lambda>_. ()) t) \<sigma> (Inr ())
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id (\<lambda>_. ()) z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_relabel_gtree_off:
  "k \<notin> range r \<Longrightarrow> sides_of_rhs (relabel_gtree r t) \<sigma> (Inr k) = bot"
  by (induction t) (auto simp: Let_def)

end

