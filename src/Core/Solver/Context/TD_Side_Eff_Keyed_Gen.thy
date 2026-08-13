theory TD_Side_Eff_Keyed_Gen
  imports TD_Side_Eff_Sound
begin

section \<open>Global-key tree relabelling\<close>

text \<open>
  Global-key relabelling for strategy trees, the \<open>QueryG\<close> / \<open>Side\<close> analogue of
  \<^const>\<open>map_ltree\<close>.  The heterogeneous D/G generator relabels the local unknowns
  of a per-edge tree by context (\<^const>\<open>map_ltree\<close>) and routes its global writes to
  the context's keyed slot with \<open>map_gtree\<close>; \<open>traverse_rhs_map_gtree\<close> shows the
  latter commutes with the denotation under the matching \<^const>\<open>map_sum\<close>-pullback of
  the global slots, exactly as \<open>traverse_rhs_map_ltree\<close> does on the local side.
\<close>

subsection \<open>Relabelling global keys\<close>

primrec map_gtree ::
  "('g \<Rightarrow> 'h) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'h, 'd) strategy_tree" where
  "map_gtree r (Answer d) = Answer d"
| "map_gtree r (QueryL y f) = QueryL y (\<lambda>d. map_gtree r (f d))"
| "map_gtree r (QueryG y f) = QueryG (r y) (\<lambda>d. map_gtree r (f d))"
| "map_gtree r (Side y d t) = Side (r y) d (map_gtree r t)"

text \<open>
  The denotation of a global-relabelled tree is the original read against the
  \<^const>\<open>map_sum\<close>-pullback that reroutes the global slots by \<open>r\<close>; locals are
  untouched.  Global side (\<open>QueryG\<close>) reads at key \<open>r y\<close> exactly match reading the
  pulled-back environment at \<open>y\<close>.  Mirrors \<open>traverse_rhs_map_ltree\<close>.
\<close>

lemma traverse_rhs_map_gtree:
  "traverse_rhs (map_gtree r t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum id r z))"
  by (induction t) auto

lemma dep_aux_map_ltree:
  "dep_aux \<sigma> (map_ltree h t)
   = map_sum h id ` dep_aux (\<lambda>z. \<sigma> (map_sum h id z)) t"
  by (induction t arbitrary: \<sigma>) auto

lemma dep_aux_map_gtree:
  "dep_aux \<sigma> (map_gtree r t)
   = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) auto

subsection \<open>Routing: the keyed intra tree reads the context / keyed-slot pullback\<close>

text \<open>
  Composing the two relabels commutes: a keyed intra tree denotes \<^const>\<open>apply_etf\<close>
  read against the environment that reroutes locals to their context copy
  (\<open>w \<mapsto> (w, ctx)\<close>) and the transfer's global slot to the context key \<open>gkey ctx\<close>.
  This is the local half of routing correctness --- it exhibits, as a \<^const>\<open>map_sum\<close>
  pullback, precisely which slots a keyed edge tree consults.
\<close>

lemma traverse_intra_keyed:
  "traverse_rhs (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) t)) \<sigma>
   = traverse_rhs t (\<lambda>z. \<sigma> (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gkey ctx) z))"
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp o_def)

subsection \<open>Side commutes for the relabels\<close>

text \<open>
  \<^const>\<open>map_ltree\<close> leaves \<open>QueryG\<close> / \<open>Side\<close> keys fixed, so its per-name side map is
  the original read against the local pullback; \<^const>\<open>map_gtree\<close> with a constant
  relabel concentrates every \<^typ>\<open>unit\<close> \<open>Side\<close> at \<open>r ()\<close>, and reroutes off-range
  keys to \<open>bot\<close>.
\<close>

lemma sides_map_ltree_Inr:
  "sides_of_rhs (map_ltree h t) \<sigma> (Inr gg)
   = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum h id z)) (Inr gg)"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_unit:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (map_gtree r t) \<sigma> (Inr (r ()))
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id r z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_unit_gen:
  fixes t :: "('x, unit, 'b::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (map_gtree (\<lambda>_. ()) t) \<sigma> (Inr ())
         = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum id (\<lambda>_. ()) z)) (Inr ())"
  by (induction t) (auto simp: Let_def)

lemma sides_map_gtree_off:
  "k \<notin> range r \<Longrightarrow> sides_of_rhs (map_gtree r t) \<sigma> (Inr k) = bot"
  by (induction t) (auto simp: Let_def)

end

