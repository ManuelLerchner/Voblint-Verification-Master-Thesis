theory Compiled_Routed_Equations
  imports
    "Voblint_Framework.Routed_Context"
    "Voblint_Compile.Compile_Wellformed"
    "HOL-Library.RBT"
begin

section \<open>Executable routed equations for a compiled program\<close>

text \<open>
  A routed configuration chooses a global key, a seed-key constructor, a
  routing function, a D/G specification, an initial local state and an initial
  global state. The remaining equation-system wiring is fixed: predecessor
  enumeration, edge execution, static call resolution, seed publication, and
  bottom initialization of every other unknown.

  A context-insensitive analysis is this constructor at the unit context:
  \<open>Analysis_Global ()\<close> as the global key, \<open>Activation_Seed\<close> as the seed
  constructor and \<open>route_unit\<close> as the routing function. There is no second
  unit-context generator.

  Solver policy is deliberately outside this constructor. Always-join,
  per-origin, and warrowing instances can solve the same equations without
  hiding that choice here.

  The enumerations the equations read are stated over the edge relations and
  answer every query by re-enumerating a whole relation. The code equation at
  the end answers them from indexes built once per graph instead, so a solver
  step costs a lookup rather than a scan and sort of every edge.
\<close>

definition compiled_routed_eqs_for ::
    "'K
      \<Rightarrow> (pp \<Rightarrow> 'C \<Rightarrow> 'K)
      \<Rightarrow> (pp \<Rightarrow> 'C \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'C)
      \<Rightarrow> (pp \<times> 'C, 'K, unit,
           'D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec
      \<Rightarrow> cfg
      \<Rightarrow> 'D
      \<Rightarrow> 'G
      \<Rightarrow> (pp \<times> 'C, 'K, ('D, 'G) dg_state) eqsT"
where
  "compiled_routed_eqs_for global seed route S g initial initial_global =
     routed_node_rhs_buffered intra_predecessor_addr_list call_site_list
       (\<lambda>_. global) route
       (\<lambda>ctx' src a. dg_spec_edge_tree S a src (\<lambda>_. global))
       (routed_call_tree S global seed (static_resolve g) (\<lambda>d. d = bot))
       (routed_entry_seed_tree seed)
       g bot initial initial_global"

subsection \<open>Per-node edge indexes\<close>

text \<open>
  \<open>group_by_key key_of f xs\<close> files each element \<open>f\<close> accepts under its key,
  keeping list order within a key. A lookup is therefore the order-preserving
  filter of \<open>xs\<close> at that key, which is what lets it replace an enumeration
  inside a fold that observes order.
\<close>

definition group_lookup :: "('k::linorder, 'y list) rbt \<Rightarrow> 'k \<Rightarrow> 'y list" where
  "group_lookup m k = (case RBT.lookup m k of None \<Rightarrow> [] | Some ys \<Rightarrow> ys)"

definition group_by_key ::
    "('x \<Rightarrow> 'k::linorder) \<Rightarrow> ('x \<Rightarrow> 'y option) \<Rightarrow> 'x list \<Rightarrow> ('k, 'y list) rbt" where
  "group_by_key key_of f xs =
     foldr (\<lambda>x m. case f x of
                None \<Rightarrow> m
              | Some y \<Rightarrow> RBT.insert (key_of x) (y # group_lookup m (key_of x)) m)
       xs RBT.empty"

lemma group_lookup_group_by_key:
  "group_lookup (group_by_key key_of f xs) k
     = List.map_filter (\<lambda>x. if key_of x = k then f x else None) xs"
  by (induction xs) (auto simp: group_by_key_def group_lookup_def split: option.splits)

definition intra_predecessor_index ::
    "cfg \<Rightarrow> (cfg_node, (cfg_node \<times> edge_action) list) rbt" where
  "intra_predecessor_index g =
     group_by_key (\<lambda>(u, a, w). w) (\<lambda>(u, a, w). Some (u, a)) (cfg_intra_list g)"

lemma group_lookup_intra_predecessor_index:
  "group_lookup (intra_predecessor_index g) v = intra_predecessor_list g v"
proof -
  have "List.map_filter
          (\<lambda>x. if (\<lambda>(u, a, w). w) x = v then (\<lambda>(u, a, w). Some (u, a)) x else None) es
          = map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) es)"
    for es :: "(cfg_node \<times> edge_action \<times> cfg_node) list"
    by (induction es) auto
  then show ?thesis
    unfolding intra_predecessor_index_def intra_predecessor_list_def group_lookup_group_by_key
    by simp
qed

lemma map_group_lookup_intra_predecessor_index:
  "map (\<lambda>(u, a). (Inl (u, ctx), a)) (group_lookup (intra_predecessor_index g) v)
     = intra_predecessor_addr_list g v ctx"
  by (simp add: intra_predecessor_addr_list_def group_lookup_intra_predecessor_index)

definition call_target_index ::
    "cfg \<Rightarrow> (cfg_node, (cfg_node \<times> call_action \<times> pname) list) rbt" where
  "call_target_index g =
     group_by_key (\<lambda>(c, ca, ce, k). k) (\<lambda>(c, ca, ce, k). call_target_at k (c, ca, ce, k))
       (cfg_calls_list g)"

lemma group_lookup_call_target_index:
  "group_lookup (call_target_index g) v = call_target_list g v"
proof -
  have "(if (\<lambda>(c, ca, ce, k). k) e = v
         then (\<lambda>(c, ca, ce, k). call_target_at k (c, ca, ce, k)) e else None)
          = call_target_at v e" for e :: "cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node"
  proof -
    obtain c ca ce k where e: "e = (c, ca, ce, k)" by (cases e) auto
    show ?thesis by (cases ce) (auto simp: e)
  qed
  then show ?thesis
    unfolding call_target_index_def call_target_list_def group_lookup_group_by_key
    by simp
qed

text \<open>
  The indexes are let-bound outside the equation system, so a solver holding
  the system evaluates them once. The three selectors restate
  \<^const>\<open>intra_predecessor_addr_list\<close>, \<^const>\<open>call_site_list\<close> and
  \<^const>\<open>static_resolve\<close> over a lookup in place of the enumeration. They
  ignore their graph argument, which is sound only because the generator
  applies every selector at the one graph it is given.
\<close>

lemma compiled_routed_eqs_for_code [code]:
  "compiled_routed_eqs_for global seed route S g initial initial_global =
     (let preds = intra_predecessor_index g; targets = call_target_index g
      in routed_node_rhs_buffered
           (\<lambda>_ v ctx. map (\<lambda>(u, a). (Inl (u, ctx), a)) (group_lookup preds v))
           (\<lambda>_ v. remdups (map (\<lambda>(c, ca, p). (c, ca)) (group_lookup targets v)))
           (\<lambda>_. global) route
           (\<lambda>ctx' src a. dg_spec_edge_tree S a src (\<lambda>_. global))
           (routed_call_tree S global seed
              (\<lambda>v cc ca d. map (\<lambda>(c, a, p). p)
                 (filter (\<lambda>(c, a, p). c = cc \<and> a = ca) (group_lookup targets v)))
              (\<lambda>d. d = bot))
           (routed_entry_seed_tree seed)
           g bot initial initial_global)"
proof -
  note preds = map_group_lookup_intra_predecessor_index
  have sites: "remdups (map (\<lambda>(c, ca, p). (c, ca)) (group_lookup (call_target_index g) v))
      = call_site_list g v" for v
    by (simp add: call_site_list_def group_lookup_call_target_index)
  have resolve: "(\<lambda>v cc ca d. map (\<lambda>(c, a, p). p)
                   (filter (\<lambda>(c, a, p). c = cc \<and> a = ca) (group_lookup (call_target_index g) v)))
      = static_resolve g"
    by (intro ext) (simp add: static_resolve_def static_targets_def group_lookup_call_target_index)
  show ?thesis
    unfolding compiled_routed_eqs_for_def routed_node_rhs_buffered_def
      routed_contribution_trees_def Let_def
    by (simp only: preds sites resolve)
qed

end

