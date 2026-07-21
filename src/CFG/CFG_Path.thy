theory CFG_Path
  imports CFG_Def
begin

section \<open>Edge-offset paths\<close>

text \<open>
  Offset shifting for edge-labelled step lists: compound CFGs compile sub-commands
  at a node offset k > 0, so offset_path renumbers a step list to match offset_edges.
  Consumed by the collecting transfer layer (CFG_Transfer).
\<close>

definition offset_path :: "nat => (edge_action * pp) list => (edge_action * pp) list" where
  "offset_path k es = map (\<lambda>(a, p). (a, p + k)) es"

lemma offset_path_Nil[simp]: "offset_path k [] = []"
  unfolding offset_path_def by simp

lemma offset_path_Cons[simp]:
  "offset_path k ((a, p) # es) = (a, p + k) # offset_path k es"
  unfolding offset_path_def by simp

lemma offset_path_append[simp]:
  "offset_path k (es1 @ es2) = offset_path k es1 @ offset_path k es2"
  unfolding offset_path_def by simp

end