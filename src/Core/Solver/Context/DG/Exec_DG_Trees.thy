section \<open>Executable D/G strategy trees and their traversal\<close>

text \<open>
  The executable counterparts of the abstract per-edge, combine and enter trees, the support
  bound each one respects, and the commutation of a single tree's traversal, side-effect map
  and dependency set with the readback. Everything here is about one tree at a time; the fold
  over a whole node's tree list is the next layer up.
\<close>

theory Exec_DG_Trees
  imports
    Exec_DG_Refines
begin
subsection \<open>Owner-aware executable D/G trees\<close>

text \<open>
  \<open>placed_dg_edge_tree_with\<close> factors the query/answer/side skeleton out from
  the projection it materializes results through.  \<open>placed_dg_edge_tree\<close>
  keeps the original, defensive \<open>project_resolved_on\<close>; \<open>placed_dg_edge_tree_strict\<close>
  uses \<open>project_resolved_on_strict\<close>, whose output support is bounded by the
  write node's declared scope unconditionally (\<open>effective_support_rep_project_resolved_on_strict\<close>),
  with no fact about the raw transfer's own support needed.
\<close>

definition placed_dg_edge_tree_with ::
  "(pname => location list => (scoped_location => bool) =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   ('a exec_dg_st => 'a exec_dg_st) =>
   pp => pp => (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state)
     strategy_tree"
where
  "placed_dg_edge_tree_with proj owner_of locations_of keep_local publish_side
      transfer read_node write_node = do {
     local \<leftarrow> read_local read_node;
     side \<leftarrow> read_global ();
     let result = transfer (locals local \<squnion> globs side);
     depend_on () (DG bot
         (proj (owner_of write_node) (locations_of write_node)
           publish_side result))
       (answer (DG
         (proj (owner_of write_node) (locations_of write_node)
           keep_local result) bot))
   }"

text \<open>
  Dependency tracking is purely structural (\<open>dep_aux\<close>'s equations only look
  at the \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close>/\<open>Answer\<close> skeleton, never at what a leaf
  computes), so it transports for free regardless of which projection or
  transfer function a placed edge tree carries, and regardless of the
  valuation it is evaluated against.
\<close>

lemma dep_aux_placed_dg_edge_tree_with:
  "dep_aux sigma (placed_dg_edge_tree_with proj owner_of locations_of keep_local
      publish_side transfer read_node write_node) = {Inl read_node, Inr ()}"
  by (simp add: placed_dg_edge_tree_with_def dep_aux_def Let_def)

lemma dep_aux_placed_abs_dg_edge_tree:
  "dep_aux sigma (placed_abs_dg_edge_tree source_global owner_of keep_local
      publish_side transfer read_node write_node) = {Inl read_node, Inr ()}"
  by (simp add: placed_abs_dg_edge_tree_def dep_aux_def Let_def)

definition placed_dg_edge_tree ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   pp => pp => (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state)
     strategy_tree"
where
  "placed_dg_edge_tree = placed_dg_edge_tree_with project_resolved_on"

definition placed_dg_edge_tree_strict ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   pp => pp => (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state)
     strategy_tree"
where
  "placed_dg_edge_tree_strict = placed_dg_edge_tree_with project_resolved_on_strict"

lemma traverse_placed_dg_edge_tree:
  "traverse_rhs
    (placed_dg_edge_tree owner_of locations_of keep_local publish_side
      transfer read_node write_node) sigma =
    DG (project_resolved_on (owner_of write_node) (locations_of write_node)
          keep_local
          (transfer (locals (sigma (Inl read_node)) \<squnion>
             globs (sigma (Inr ())))))
      bot"
  unfolding placed_dg_edge_tree_def placed_dg_edge_tree_with_def
  by (simp add: Let_def)

lemma sides_placed_dg_edge_tree_Inr:
  "sides_of_rhs
    (placed_dg_edge_tree owner_of locations_of keep_local publish_side
      transfer read_node write_node) sigma (Inr ()) =
    DG bot
      (project_resolved_on (owner_of write_node) (locations_of write_node)
        publish_side
        (transfer (locals (sigma (Inl read_node)) \<squnion>
           globs (sigma (Inr ())))))"
  unfolding placed_dg_edge_tree_def placed_dg_edge_tree_with_def
  by (simp add: Let_def)

lemma traverse_placed_dg_edge_tree_strict:
  "traverse_rhs
    (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
      transfer read_node write_node) sigma =
    DG (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
          keep_local
          (transfer (locals (sigma (Inl read_node)) \<squnion>
             globs (sigma (Inr ())))))
      bot"
  unfolding placed_dg_edge_tree_strict_def placed_dg_edge_tree_with_def
  by (simp add: Let_def)

lemma sides_placed_dg_edge_tree_strict_Inr:
  "sides_of_rhs
    (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
      transfer read_node write_node) sigma (Inr ()) =
    DG bot
      (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
        publish_side
        (transfer (locals (sigma (Inl read_node)) \<squnion>
           globs (sigma (Inr ())))))"
  unfolding placed_dg_edge_tree_strict_def placed_dg_edge_tree_with_def
  by (simp add: Let_def)

lemma placed_dg_edge_tree_strict_local_support_bounded:
  "set (effective_support (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
        transfer read_node write_node) sigma)))) \<subseteq> set (locations_of write_node)"
  by (simp add: traverse_placed_dg_edge_tree_strict
    effective_support_rep_project_resolved_on_strict)

lemma placed_dg_edge_tree_strict_side_support_bounded:
  "set (effective_support (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
        transfer read_node write_node) sigma (Inr ()))))) \<subseteq> set (locations_of write_node)"
  by (simp add: sides_placed_dg_edge_tree_strict_Inr
    effective_support_rep_project_resolved_on_strict)

lemma placed_dg_edge_tree_strict_local_default_bot:
  "resolved_default (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
        transfer read_node write_node) sigma))) = (\<lambda>_. bot)"
  by (simp add: traverse_placed_dg_edge_tree_strict
    resolved_default_rep_project_resolved_on_strict)

lemma placed_dg_edge_tree_strict_side_default_bot:
  "resolved_default (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
        transfer read_node write_node) sigma (Inr ())))) = (\<lambda>_. bot)"
  by (simp add: sides_placed_dg_edge_tree_strict_Inr
    resolved_default_rep_project_resolved_on_strict)

lemma dg_refines_on_placed_edge:
  fixes executable_transfer ::
    "('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_transfer :: "'a abs_state => 'a abs_state"
    and executable_sigma ::
      "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and abstract_sigma ::
      "pp + unit => ('a abs_state, 'a abs_state) dg_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_transfer
          (locals (executable_sigma (Inl read_node)) \<squnion>
           globs (executable_sigma (Inr ())))) location =
      abstract_transfer
        (locals (abstract_sigma (Inl read_node)) \<squnion>
         globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of write_node))
      (DG
        (locals (traverse_rhs
          (placed_dg_edge_tree owner_of locations_of keep_local publish_side
            executable_transfer read_node write_node) executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_edge_tree owner_of locations_of keep_local publish_side
            executable_transfer read_node write_node) executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            abstract_transfer read_node write_node) abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            abstract_transfer read_node write_node) abstract_sigma (Inr ()))))"
  unfolding traverse_placed_dg_edge_tree sides_placed_dg_edge_tree_Inr
    traverse_placed_abs_dg_edge_tree sides_placed_abs_dg_edge_tree_Inr
  by (simp add: dg_refines_on_project[OF raw resolved])

lemma dg_refines_on_placed_edge_strict:
  fixes executable_transfer ::
    "('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_transfer :: "'a abs_state => 'a abs_state"
    and executable_sigma ::
      "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and abstract_sigma ::
      "pp + unit => ('a abs_state, 'a abs_state) dg_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_transfer
          (locals (executable_sigma (Inl read_node)) \<squnion>
           globs (executable_sigma (Inr ())))) location =
      abstract_transfer
        (locals (abstract_sigma (Inl read_node)) \<squnion>
         globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of write_node))
      (DG
        (locals (traverse_rhs
          (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
            executable_transfer read_node write_node) executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
            executable_transfer read_node write_node) executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            abstract_transfer read_node write_node) abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            abstract_transfer read_node write_node) abstract_sigma (Inr ()))))"
  unfolding traverse_placed_dg_edge_tree_strict sides_placed_dg_edge_tree_strict_Inr
    traverse_placed_abs_dg_edge_tree sides_placed_abs_dg_edge_tree_Inr
  by (simp add: dg_refines_on_project_strict[OF raw resolved])

definition placed_dg_enter_tree ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname list => exp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   vname list => exp list => pp => pp =>
   (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_enter_tree owner_of locations_of keep_local publish_side
      enter parameters arguments caller callee =
    placed_dg_edge_tree owner_of locations_of keep_local publish_side
      (enter parameters arguments) caller callee"

lemma placed_dg_enter_tree_eq:
  "placed_dg_enter_tree owner_of locations_of keep_local publish_side
      enter parameters arguments caller callee =
    placed_dg_edge_tree owner_of locations_of keep_local publish_side
      (enter parameters arguments) caller callee"
  unfolding placed_dg_enter_tree_def by rule

definition placed_dg_enter_tree_strict ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname list => exp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   vname list => exp list => pp => pp =>
   (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
      enter parameters arguments caller callee =
    placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
      (enter parameters arguments) caller callee"

lemma placed_dg_enter_tree_strict_eq:
  "placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
      enter parameters arguments caller callee =
    placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
      (enter parameters arguments) caller callee"
  unfolding placed_dg_enter_tree_strict_def by rule

lemma placed_dg_enter_tree_strict_local_support_bounded:
  "set (effective_support (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
        enter parameters arguments caller callee) sigma)))) \<subseteq>
    set (locations_of callee)"
  unfolding placed_dg_enter_tree_strict_eq
  by (rule placed_dg_edge_tree_strict_local_support_bounded)

lemma placed_dg_enter_tree_strict_side_support_bounded:
  "set (effective_support (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
        enter parameters arguments caller callee) sigma (Inr ()))))) \<subseteq>
    set (locations_of callee)"
  unfolding placed_dg_enter_tree_strict_eq
  by (rule placed_dg_edge_tree_strict_side_support_bounded)

lemma placed_dg_enter_tree_strict_local_default_bot:
  "resolved_default (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
        enter parameters arguments caller callee) sigma))) = (\<lambda>_. bot)"
  unfolding placed_dg_enter_tree_strict_eq
  by (rule placed_dg_edge_tree_strict_local_default_bot)

lemma placed_dg_enter_tree_strict_side_default_bot:
  "resolved_default (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
        enter parameters arguments caller callee) sigma (Inr ())))) = (\<lambda>_. bot)"
  unfolding placed_dg_enter_tree_strict_eq
  by (rule placed_dg_edge_tree_strict_side_default_bot)

lemma dep_aux_placed_dg_enter_tree_strict:
  "dep_aux sigma (placed_dg_enter_tree_strict owner_of locations_of keep_local
      publish_side enter parameters arguments caller callee) =
    {Inl caller, Inr ()}"
  unfolding placed_dg_enter_tree_strict_eq placed_dg_edge_tree_strict_def
  by (rule dep_aux_placed_dg_edge_tree_with)

lemma dep_aux_placed_abs_dg_enter_tree:
  "dep_aux sigma (placed_abs_dg_enter_tree source_global owner_of keep_local
      publish_side enter parameters arguments caller callee) =
    {Inl caller, Inr ()}"
  unfolding placed_abs_dg_enter_tree_def
  by (rule dep_aux_placed_abs_dg_edge_tree)

lemma dg_refines_on_placed_entry:
  fixes executable_enter ::
    "vname list => exp list =>
      ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_enter ::
      "vname list => exp list => 'a abs_state => 'a abs_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of callee) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_enter parameters arguments
          (locals (executable_sigma (Inl caller)) \<squnion>
           globs (executable_sigma (Inr ())))) location =
      abstract_enter parameters arguments
        (locals (abstract_sigma (Inl caller)) \<squnion>
         globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of callee) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of callee))
      (DG
        (locals (traverse_rhs
          (placed_dg_enter_tree owner_of locations_of keep_local publish_side
            executable_enter parameters arguments caller callee)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_enter_tree owner_of locations_of keep_local publish_side
            executable_enter parameters arguments caller callee)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_enter_tree source_global owner_of keep_local publish_side
            abstract_enter parameters arguments caller callee)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_enter_tree source_global owner_of keep_local publish_side
            abstract_enter parameters arguments caller callee)
          abstract_sigma (Inr ()))))"
proof -
  have bridge:
    "dg_refines_on (set (locations_of callee))
      (DG
        (locals (traverse_rhs
          (placed_dg_edge_tree owner_of locations_of keep_local publish_side
            (executable_enter parameters arguments) caller callee)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_edge_tree owner_of locations_of keep_local publish_side
            (executable_enter parameters arguments) caller callee)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            (abstract_enter parameters arguments) caller callee)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            (abstract_enter parameters arguments) caller callee)
          abstract_sigma (Inr ()))))"
    by (rule dg_refines_on_placed_edge[
      where executable_transfer = "executable_enter parameters arguments"
        and abstract_transfer = "abstract_enter parameters arguments"
        and executable_sigma = executable_sigma and abstract_sigma = abstract_sigma
        and read_node = caller and write_node = callee
        and source_global = source_global and owner_of = owner_of
        and locations_of = locations_of and keep_local = keep_local
        and publish_side = publish_side, OF raw resolved])
  show ?thesis
    unfolding placed_dg_enter_tree_def placed_abs_dg_enter_tree_def
    by (rule bridge)
qed

lemma dg_refines_on_placed_entry_strict:
  fixes executable_enter ::
    "vname list => exp list =>
      ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_enter ::
      "vname list => exp list => 'a abs_state => 'a abs_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of callee) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_enter parameters arguments
          (locals (executable_sigma (Inl caller)) \<squnion>
           globs (executable_sigma (Inr ())))) location =
      abstract_enter parameters arguments
        (locals (abstract_sigma (Inl caller)) \<squnion>
         globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of callee) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of callee))
      (DG
        (locals (traverse_rhs
          (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
            executable_enter parameters arguments caller callee)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
            executable_enter parameters arguments caller callee)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_enter_tree source_global owner_of keep_local publish_side
            abstract_enter parameters arguments caller callee)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_enter_tree source_global owner_of keep_local publish_side
            abstract_enter parameters arguments caller callee)
          abstract_sigma (Inr ()))))"
proof -
  have bridge:
    "dg_refines_on (set (locations_of callee))
      (DG
        (locals (traverse_rhs
          (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
            (executable_enter parameters arguments) caller callee)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
            (executable_enter parameters arguments) caller callee)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            (abstract_enter parameters arguments) caller callee)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
            (abstract_enter parameters arguments) caller callee)
          abstract_sigma (Inr ()))))"
    by (rule dg_refines_on_placed_edge_strict[
      where executable_transfer = "executable_enter parameters arguments"
        and abstract_transfer = "abstract_enter parameters arguments"
        and executable_sigma = executable_sigma and abstract_sigma = abstract_sigma
        and read_node = caller and write_node = callee
        and source_global = source_global and owner_of = owner_of
        and locations_of = locations_of and keep_local = keep_local
        and publish_side = publish_side, OF raw resolved])
  show ?thesis
    unfolding placed_dg_enter_tree_strict_def placed_abs_dg_enter_tree_def
    by (rule bridge)
qed

text \<open>Factored the same way as \<open>placed_dg_edge_tree_with\<close>: the skeleton is
  shared, the projection it materializes results through is a parameter.\<close>

definition placed_dg_combine_tree_with ::
  "(pname => location list => (scoped_location => bool) =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname option => 'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st) =>
   vname option => pp => pp => pp =>
   (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_combine_tree_with proj owner_of locations_of keep_local publish_side
      combine destination caller callee write_node = do {
     caller_state \<leftarrow> read_local caller;
     callee_state \<leftarrow> read_local callee;
     side \<leftarrow> read_global ();
     let result = combine destination (locals caller_state)
       (locals callee_state) (globs side);
     depend_on () (DG bot
         (proj (owner_of write_node)
           (locations_of write_node) publish_side result))
       (answer (DG
         (proj (owner_of write_node)
           (locations_of write_node) keep_local result) bot))
   }"

lemma dep_aux_placed_dg_combine_tree_with:
  "dep_aux sigma (placed_dg_combine_tree_with proj owner_of locations_of keep_local
      publish_side combine destination caller callee write_node) =
    {Inl caller, Inl callee, Inr ()}"
  by (simp add: placed_dg_combine_tree_with_def dep_aux_def Let_def)

lemma dep_aux_placed_abs_dg_combine_tree:
  "dep_aux sigma (placed_abs_dg_combine_tree source_global owner_of keep_local
      publish_side combine destination caller callee write_node) =
    {Inl caller, Inl callee, Inr ()}"
  by (simp add: placed_abs_dg_combine_tree_def dep_aux_def Let_def)

definition placed_dg_combine_tree ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname option =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st =>
     'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st) =>
   vname option => pp => pp => pp =>
   (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_combine_tree = placed_dg_combine_tree_with project_resolved_on"

definition placed_dg_combine_tree_strict ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname option =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st =>
     'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st) =>
   vname option => pp => pp => pp =>
   (pp, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_combine_tree_strict = placed_dg_combine_tree_with project_resolved_on_strict"

lemma traverse_placed_dg_combine_tree:
  "traverse_rhs
    (placed_dg_combine_tree owner_of locations_of keep_local publish_side
      combine destination caller callee write_node) sigma =
    DG (project_resolved_on (owner_of write_node) (locations_of write_node)
          keep_local
          (combine destination (locals (sigma (Inl caller)))
            (locals (sigma (Inl callee))) (globs (sigma (Inr ())))))
      bot"
  unfolding placed_dg_combine_tree_def placed_dg_combine_tree_with_def
  by (simp add: Let_def)

lemma sides_placed_dg_combine_tree_Inr:
  "sides_of_rhs
    (placed_dg_combine_tree owner_of locations_of keep_local publish_side
      combine destination caller callee write_node) sigma (Inr ()) =
    DG bot
      (project_resolved_on (owner_of write_node) (locations_of write_node)
        publish_side
        (combine destination (locals (sigma (Inl caller)))
          (locals (sigma (Inl callee))) (globs (sigma (Inr ())))))"
  unfolding placed_dg_combine_tree_def placed_dg_combine_tree_with_def
  by (simp add: Let_def)

lemma traverse_placed_dg_combine_tree_strict:
  "traverse_rhs
    (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
      combine destination caller callee write_node) sigma =
    DG (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
          keep_local
          (combine destination (locals (sigma (Inl caller)))
            (locals (sigma (Inl callee))) (globs (sigma (Inr ())))))
      bot"
  unfolding placed_dg_combine_tree_strict_def placed_dg_combine_tree_with_def
  by (simp add: Let_def)

lemma sides_placed_dg_combine_tree_strict_Inr:
  "sides_of_rhs
    (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
      combine destination caller callee write_node) sigma (Inr ()) =
    DG bot
      (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
        publish_side
        (combine destination (locals (sigma (Inl caller)))
          (locals (sigma (Inl callee))) (globs (sigma (Inr ())))))"
  unfolding placed_dg_combine_tree_strict_def placed_dg_combine_tree_with_def
  by (simp add: Let_def)

lemma placed_dg_combine_tree_strict_local_support_bounded:
  "set (effective_support (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
        combine destination caller callee write_node) sigma)))) \<subseteq>
    set (locations_of write_node)"
  by (simp add: traverse_placed_dg_combine_tree_strict
    effective_support_rep_project_resolved_on_strict)

lemma placed_dg_combine_tree_strict_side_support_bounded:
  "set (effective_support (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
        combine destination caller callee write_node) sigma (Inr ()))))) \<subseteq>
    set (locations_of write_node)"
  by (simp add: sides_placed_dg_combine_tree_strict_Inr
    effective_support_rep_project_resolved_on_strict)

lemma placed_dg_combine_tree_strict_local_default_bot:
  "resolved_default (rep_resolved_st
    (locals (traverse_rhs
      (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
        combine destination caller callee write_node) sigma))) = (\<lambda>_. bot)"
  by (simp add: traverse_placed_dg_combine_tree_strict
    resolved_default_rep_project_resolved_on_strict)

lemma placed_dg_combine_tree_strict_side_default_bot:
  "resolved_default (rep_resolved_st
    (globs (sides_of_rhs
      (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
        combine destination caller callee write_node) sigma (Inr ())))) = (\<lambda>_. bot)"
  by (simp add: sides_placed_dg_combine_tree_strict_Inr
    resolved_default_rep_project_resolved_on_strict)

lemma dg_refines_on_placed_combine:
  fixes executable_combine ::
    "vname option => ('a::bounded_semilattice_sup_bot) exec_dg_st =>
      'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st"
    and abstract_combine ::
      "vname option => 'a abs_state => 'a abs_state => 'a abs_state => 'a abs_state"
    and executable_sigma ::
      "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and abstract_sigma ::
      "pp + unit => ('a abs_state, 'a abs_state) dg_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_combine destination
          (locals (executable_sigma (Inl caller)))
          (locals (executable_sigma (Inl callee)))
          (globs (executable_sigma (Inr ())))) location =
      abstract_combine destination
        (locals (abstract_sigma (Inl caller)))
        (locals (abstract_sigma (Inl callee)))
        (globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of write_node))
      (DG
        (locals (traverse_rhs
          (placed_dg_combine_tree owner_of locations_of keep_local publish_side
            executable_combine destination caller callee write_node)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_combine_tree owner_of locations_of keep_local publish_side
            executable_combine destination caller callee write_node)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
            abstract_combine destination caller callee write_node)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
            abstract_combine destination caller callee write_node)
          abstract_sigma (Inr ()))))"
  unfolding traverse_placed_dg_combine_tree sides_placed_dg_combine_tree_Inr
    traverse_placed_abs_dg_combine_tree sides_placed_abs_dg_combine_tree_Inr
  by (simp add: dg_refines_on_project[OF raw resolved])

lemma dg_refines_on_placed_combine_strict:
  fixes executable_combine ::
    "vname option => ('a::bounded_semilattice_sup_bot) exec_dg_st =>
      'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st"
    and abstract_combine ::
      "vname option => 'a abs_state => 'a abs_state => 'a abs_state => 'a abs_state"
    and executable_sigma ::
      "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and abstract_sigma ::
      "pp + unit => ('a abs_state, 'a abs_state) dg_state"
  assumes raw:
    "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
      lookup_resolved_st_q
        (executable_combine destination
          (locals (executable_sigma (Inl caller)))
          (locals (executable_sigma (Inl callee)))
          (globs (executable_sigma (Inr ())))) location =
      abstract_combine destination
        (locals (abstract_sigma (Inl caller)))
        (locals (abstract_sigma (Inl callee)))
        (globs (abstract_sigma (Inr ())))
        (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set (locations_of write_node) \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set (locations_of write_node))
      (DG
        (locals (traverse_rhs
          (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
            executable_combine destination caller callee write_node)
          executable_sigma))
        (globs (sides_of_rhs
          (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
            executable_combine destination caller callee write_node)
          executable_sigma (Inr ()))))
      (DG
        (locals (traverse_rhs
          (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
            abstract_combine destination caller callee write_node)
          abstract_sigma))
        (globs (sides_of_rhs
          (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
            abstract_combine destination caller callee write_node)
          abstract_sigma (Inr ()))))"
  unfolding traverse_placed_dg_combine_tree_strict sides_placed_dg_combine_tree_strict_Inr
    traverse_placed_abs_dg_combine_tree sides_placed_abs_dg_combine_tree_Inr
  by (simp add: dg_refines_on_project_strict[OF raw resolved])

subsection \<open>Support-bounded hook transport\<close>

text \<open>
  \<^const>\<open>project_resolved_on\<close> already bounds the projected output by the
  declared scope together with whatever the raw transfer output carried
  (\<open>effective_support_rep_project_resolved_on\<close>).  A hook's raw transfer only
  grows that carried support by its own write footprint
  (\<open>support_growth_bounded\<close>); once the footprint and the read node's own
  scope both fall inside the write node's scope, the projected output stays
  inside it too.  This is the piece the classifier-parametric readback needs
  and the finite-scope escape hatch does not give for free: the write node's
  own scope must actually cover what the edge reads and writes, not merely
  agree with the abstract side on it.
\<close>

definition support_growth_bounded ::
  "(('a::bot) exec_dg_st => 'a exec_dg_st) => location set => bool"
where
  "support_growth_bounded transfer footprint \<longleftrightarrow>
    (\<forall>s. set (effective_support (rep_resolved_st (transfer s))) \<subseteq>
      set (effective_support (rep_resolved_st s)) \<union> footprint)"

lemma placed_dg_edge_tree_input_support_bounded:
  fixes sigma :: "pp + unit => ('a::bounded_semilattice_sup_bot exec_dg_st,
    'a exec_dg_st) dg_state"
  assumes read_local_bounded:
    "set (effective_support (rep_resolved_st (locals (sigma (Inl read_node)))))
      \<subseteq> read_scope"
    and read_side_bounded:
    "set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))
      \<subseteq> gscope"
    and covers: "read_scope \<union> gscope \<subseteq> write_scope"
  shows
    "set (effective_support (rep_resolved_st
      (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))) \<subseteq> write_scope"
proof -
  have "set (effective_support (rep_resolved_st
      (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))) \<subseteq>
    set (effective_support (rep_resolved_st (locals (sigma (Inl read_node))))) \<union>
    set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))"
    by (rule effective_support_rep_sup_resolved_st_q)
  also have "\<dots> \<subseteq> read_scope \<union> gscope"
    using read_local_bounded read_side_bounded by (rule Un_mono)
  also have "\<dots> \<subseteq> write_scope" by (rule covers)
  finally show ?thesis .
qed

lemma placed_dg_edge_tree_local_support_bounded:
  fixes transfer :: "('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and sigma :: "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  assumes growth: "support_growth_bounded transfer footprint"
    and footprint_scope: "footprint \<subseteq> set (locations_of write_node)"
    and input_bounded:
      "set (effective_support (rep_resolved_st
        (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ())))))
        \<subseteq> set (locations_of write_node)"
  shows
    "set (effective_support (rep_resolved_st
      (locals (traverse_rhs
        (placed_dg_edge_tree owner_of locations_of keep_local publish_side
          transfer read_node write_node) sigma)))) \<subseteq> set (locations_of write_node)"
proof -
  have transfer_bounded:
    "set (effective_support (rep_resolved_st
      (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))))
      \<subseteq> set (locations_of write_node)"
  proof -
    have "set (effective_support (rep_resolved_st
        (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ())))))) \<subseteq>
      set (effective_support (rep_resolved_st
        (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))) \<union> footprint"
      using growth unfolding support_growth_bounded_def by blast
    also have "\<dots> \<subseteq> set (locations_of write_node)"
      using input_bounded footprint_scope by blast
    finally show ?thesis .
  qed
  have "set (effective_support (rep_resolved_st
      (project_resolved_on (owner_of write_node) (locations_of write_node) keep_local
        (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))))) \<subseteq>
    set (locations_of write_node)"
    using transfer_bounded effective_support_rep_project_resolved_on by blast
  then show ?thesis
    by (simp add: traverse_placed_dg_edge_tree)
qed

lemma placed_dg_edge_tree_side_support_bounded:
  fixes transfer :: "('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and sigma :: "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  assumes growth: "support_growth_bounded transfer footprint"
    and footprint_scope: "footprint \<subseteq> set (locations_of write_node)"
    and input_bounded:
      "set (effective_support (rep_resolved_st
        (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ())))))
        \<subseteq> set (locations_of write_node)"
  shows
    "set (effective_support (rep_resolved_st
      (globs (sides_of_rhs
        (placed_dg_edge_tree owner_of locations_of keep_local publish_side
          transfer read_node write_node) sigma (Inr ()))))) \<subseteq>
      set (locations_of write_node)"
proof -
  have transfer_bounded:
    "set (effective_support (rep_resolved_st
      (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))))
      \<subseteq> set (locations_of write_node)"
  proof -
    have "set (effective_support (rep_resolved_st
        (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ())))))) \<subseteq>
      set (effective_support (rep_resolved_st
        (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))) \<union> footprint"
      using growth unfolding support_growth_bounded_def by blast
    also have "\<dots> \<subseteq> set (locations_of write_node)"
      using input_bounded footprint_scope by blast
    finally show ?thesis .
  qed
  have "set (effective_support (rep_resolved_st
      (project_resolved_on (owner_of write_node) (locations_of write_node) publish_side
        (transfer (locals (sigma (Inl read_node)) \<squnion> globs (sigma (Inr ()))))))) \<subseteq>
    set (locations_of write_node)"
    using transfer_bounded effective_support_rep_project_resolved_on by blast
  then show ?thesis
    by (simp add: sides_placed_dg_edge_tree_Inr)
qed

corollary placed_dg_enter_tree_local_support_bounded:
  fixes enter :: "vname list => exp list =>
    ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and sigma :: "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  assumes growth: "support_growth_bounded (enter parameters arguments) footprint"
    and footprint_scope: "footprint \<subseteq> set (locations_of callee)"
    and input_bounded:
      "set (effective_support (rep_resolved_st
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))))
        \<subseteq> set (locations_of callee)"
  shows
    "set (effective_support (rep_resolved_st
      (locals (traverse_rhs
        (placed_dg_enter_tree owner_of locations_of keep_local publish_side
          enter parameters arguments caller callee) sigma)))) \<subseteq>
      set (locations_of callee)"
  unfolding placed_dg_enter_tree_def
  by (rule placed_dg_edge_tree_local_support_bounded
    [where owner_of = owner_of and locations_of = locations_of
       and keep_local = keep_local and publish_side = publish_side
       and transfer = "enter parameters arguments" and read_node = caller
       and write_node = callee and sigma = sigma,
     OF growth footprint_scope input_bounded])

corollary placed_dg_enter_tree_side_support_bounded:
  fixes enter :: "vname list => exp list =>
    ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and sigma :: "pp + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  assumes growth: "support_growth_bounded (enter parameters arguments) footprint"
    and footprint_scope: "footprint \<subseteq> set (locations_of callee)"
    and input_bounded:
      "set (effective_support (rep_resolved_st
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))))
        \<subseteq> set (locations_of callee)"
  shows
    "set (effective_support (rep_resolved_st
      (globs (sides_of_rhs
        (placed_dg_enter_tree owner_of locations_of keep_local publish_side
          enter parameters arguments caller callee) sigma (Inr ()))))) \<subseteq>
      set (locations_of callee)"
  unfolding placed_dg_enter_tree_def
  by (rule placed_dg_edge_tree_side_support_bounded
    [where owner_of = owner_of and locations_of = locations_of
       and keep_local = keep_local and publish_side = publish_side
       and transfer = "enter parameters arguments" and read_node = caller
       and write_node = callee and sigma = sigma,
     OF growth footprint_scope input_bounded])

text \<open>
  \<^const>\<open>combine_collect_resolved_for_q\<close> keeps locals from its caller-side
  argument and globals from its callee-side argument
  (\<open>effective_support_rep_combine_collect_resolved_for_q\<close>), so the combine
  hook's support bound is asymmetric: it needs the caller's own scope and the
  side accumulator for its local half, and the callee's own scope and the
  side accumulator for its global half.  A callee-only local never enters the
  bound, matching what \<open>combine_collect_resolved_for_q\<close> itself discards.
\<close>

lemma placed_dg_combine_tree_transfer_support_bounded:
  fixes sigma :: "pp + unit => ('a::bounded_semilattice_sup_bot exec_dg_st,
    'a exec_dg_st) dg_state"
  assumes caller_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl caller)))))
        \<subseteq> caller_scope"
    and callee_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl callee)))))
        \<subseteq> callee_scope"
    and side_bounded:
      "set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))
        \<subseteq> gscope"
    and covers:
      "{loc \<in> caller_scope \<union> gscope. location_is_local loc} \<union>
       {loc \<in> callee_scope \<union> gscope. location_is_global loc} \<union>
       (case destination of None => {} | Some x => {location_of source_global x})
        \<subseteq> write_scope"
  shows
    "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q source_global destination
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))))
      \<subseteq> write_scope"
proof -
  have sc_bounded: "set (effective_support (rep_resolved_st
      (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ()))))) \<subseteq> caller_scope \<union> gscope"
  proof -
    have "set (effective_support (rep_resolved_st
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ()))))) \<subseteq>
      set (effective_support (rep_resolved_st (locals (sigma (Inl caller))))) \<union>
      set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))"
      by (rule effective_support_rep_sup_resolved_st_q)
    also have "\<dots> \<subseteq> caller_scope \<union> gscope"
      using caller_bounded side_bounded by blast
    finally show ?thesis .
  qed
  have se_bounded: "set (effective_support (rep_resolved_st
      (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))) \<subseteq> callee_scope \<union> gscope"
  proof -
    have "set (effective_support (rep_resolved_st
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))) \<subseteq>
      set (effective_support (rep_resolved_st (locals (sigma (Inl callee))))) \<union>
      set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))"
      by (rule effective_support_rep_sup_resolved_st_q)
    also have "\<dots> \<subseteq> callee_scope \<union> gscope"
      using callee_bounded side_bounded by blast
    finally show ?thesis .
  qed
  have "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q source_global destination
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ())))))) \<subseteq>
    {loc \<in> set (effective_support (rep_resolved_st
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ()))))). location_is_local loc} \<union>
    {loc \<in> set (effective_support (rep_resolved_st
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))). location_is_global loc} \<union>
    (case destination of None => {} | Some x => {location_of source_global x})"
    by (rule effective_support_rep_combine_collect_resolved_for_q)
  also have "\<dots> \<subseteq>
    {loc \<in> caller_scope \<union> gscope. location_is_local loc} \<union>
    {loc \<in> callee_scope \<union> gscope. location_is_global loc} \<union>
    (case destination of None => {} | Some x => {location_of source_global x})"
    using sc_bounded se_bounded by blast
  also have "\<dots> \<subseteq> write_scope" by (rule covers)
  finally show ?thesis .
qed

lemma placed_dg_combine_tree_local_support_bounded:
  fixes sigma :: "pp + unit => ('a::bounded_semilattice_sup_bot exec_dg_st,
    'a exec_dg_st) dg_state"
  assumes caller_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl caller)))))
        \<subseteq> caller_scope"
    and callee_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl callee)))))
        \<subseteq> callee_scope"
    and side_bounded:
      "set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))
        \<subseteq> gscope"
    and covers:
      "{loc \<in> caller_scope \<union> gscope. location_is_local loc} \<union>
       {loc \<in> callee_scope \<union> gscope. location_is_global loc} \<union>
       (case destination of None => {} | Some x => {location_of source_global x})
        \<subseteq> set (locations_of write_node)"
  shows
    "set (effective_support (rep_resolved_st
      (locals (traverse_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          (\<lambda>dst cs ce sd. combine_collect_resolved_for_q source_global dst (cs \<squnion> sd) (ce \<squnion> sd))
          destination caller callee write_node) sigma)))) \<subseteq>
      set (locations_of write_node)"
proof -
  have transfer_bounded: "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q source_global destination
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))))
      \<subseteq> set (locations_of write_node)"
    by (rule placed_dg_combine_tree_transfer_support_bounded
      [OF caller_bounded callee_bounded side_bounded covers])
  have "set (effective_support (rep_resolved_st
      (project_resolved_on (owner_of write_node) (locations_of write_node) keep_local
        (combine_collect_resolved_for_q source_global destination
          (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
          (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))))) \<subseteq>
    set (locations_of write_node)"
    using transfer_bounded effective_support_rep_project_resolved_on by blast
  then show ?thesis
    by (simp add: traverse_placed_dg_combine_tree)
qed

lemma placed_dg_combine_tree_side_support_bounded:
  fixes sigma :: "pp + unit => ('a::bounded_semilattice_sup_bot exec_dg_st,
    'a exec_dg_st) dg_state"
  assumes caller_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl caller)))))
        \<subseteq> caller_scope"
    and callee_bounded:
      "set (effective_support (rep_resolved_st (locals (sigma (Inl callee)))))
        \<subseteq> callee_scope"
    and side_bounded:
      "set (effective_support (rep_resolved_st (globs (sigma (Inr ())))))
        \<subseteq> gscope"
    and covers:
      "{loc \<in> caller_scope \<union> gscope. location_is_local loc} \<union>
       {loc \<in> callee_scope \<union> gscope. location_is_global loc} \<union>
       (case destination of None => {} | Some x => {location_of source_global x})
        \<subseteq> set (locations_of write_node)"
  shows
    "set (effective_support (rep_resolved_st
      (globs (sides_of_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          (\<lambda>dst cs ce sd. combine_collect_resolved_for_q source_global dst (cs \<squnion> sd) (ce \<squnion> sd))
          destination caller callee write_node) sigma (Inr ()))))) \<subseteq>
      set (locations_of write_node)"
proof -
  have transfer_bounded: "set (effective_support (rep_resolved_st
      (combine_collect_resolved_for_q source_global destination
        (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
        (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))))
      \<subseteq> set (locations_of write_node)"
    by (rule placed_dg_combine_tree_transfer_support_bounded
      [OF caller_bounded callee_bounded side_bounded covers])
  have "set (effective_support (rep_resolved_st
      (project_resolved_on (owner_of write_node) (locations_of write_node) publish_side
        (combine_collect_resolved_for_q source_global destination
          (locals (sigma (Inl caller)) \<squnion> globs (sigma (Inr ())))
          (locals (sigma (Inl callee)) \<squnion> globs (sigma (Inr ()))))))) \<subseteq>
    set (locations_of write_node)"
    using transfer_bounded effective_support_rep_project_resolved_on by blast
  then show ?thesis
    by (simp add: sides_placed_dg_combine_tree_Inr)
qed


lemma lookup_placed_dg_combine_tree_recombine:
  fixes sigma :: "pp + unit =>
    ('a::bounded_semilattice_sup_bot exec_dg_st, 'a exec_dg_st) dg_state"
  assumes relevant:
    "target \<in> set (locations_of write_node @
      effective_support
        (rep_resolved_st
          (combine destination (locals (sigma (Inl caller)))
            (locals (sigma (Inl callee))) (globs (sigma (Inr ()))))))"
    and covered:
      "keep_local (owner_of write_node, target) \<or>
       publish_side (owner_of write_node, target)"
  shows
    "lookup_resolved_st_q
      (locals (traverse_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          combine destination caller callee write_node) sigma) \<squnion>
       globs (sides_of_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          combine destination caller callee write_node) sigma (Inr ()))) target =
     lookup_resolved_st_q
      (combine destination (locals (sigma (Inl caller)))
        (locals (sigma (Inl callee))) (globs (sigma (Inr ())))) target"
proof -
  have result_eq:
    "locals (traverse_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          combine destination caller callee write_node) sigma) \<squnion>
       globs (sides_of_rhs
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          combine destination caller callee write_node) sigma (Inr ())) =
     project_resolved_on (owner_of write_node) (locations_of write_node)
       keep_local
       (combine destination (locals (sigma (Inl caller)))
         (locals (sigma (Inl callee))) (globs (sigma (Inr ())))) \<squnion>
     project_resolved_on (owner_of write_node) (locations_of write_node)
       publish_side
       (combine destination (locals (sigma (Inl caller)))
         (locals (sigma (Inl callee))) (globs (sigma (Inr ()))))"
    by (simp add: traverse_placed_dg_combine_tree
      sides_placed_dg_combine_tree_Inr)
  show ?thesis
    unfolding result_eq
    by (rule lookup_project_resolved_on_join[
      where owner = "owner_of write_node" and universe = "locations_of write_node"
        and keep_local = keep_local and publish_side = publish_side
        and s = "combine destination (locals (sigma (Inl caller)))
          (locals (sigma (Inl callee))) (globs (sigma (Inr ())))"
        and target = target, OF relevant covered])
qed


definition placed_dg_edge_of ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   unit => pp => edge_action => pp =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_edge_of owner_of locations_of keep_local publish_side transfer ctx
      read_node action write_node =
    map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
      (placed_dg_edge_tree owner_of locations_of keep_local publish_side
        (transfer action) read_node write_node))"

definition placed_dg_combine_of ::
  "(vname => bool) => (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   unit => pp => call_action => pp => pp =>
   (pp \<times> unit, unit, ('a::bounded_semilattice_sup_bot exec_dg_st,
     'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_combine_of source_global owner_of locations_of keep_local publish_side
      ctx caller action callee continuation =
    (case action of CallEdge destination parameters arguments =>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_dg_combine_tree owner_of locations_of keep_local publish_side
          (\<lambda>destination caller_state callee_state side_state.
            combine_collect_resolved_for_q source_global destination
              (caller_state \<squnion> side_state) (callee_state \<squnion> side_state))
          destination caller callee continuation)))"

definition placed_dg_enter_of ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname list => exp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   unit => pp => call_action => pp =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_enter_of owner_of locations_of keep_local publish_side enter ctx
      caller action callee =
    (case action of CallEdge destination parameters arguments =>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_dg_enter_tree owner_of locations_of keep_local publish_side
          enter parameters arguments caller callee)))"

definition placed_dg_gen_of ::
  "(vname => bool) => (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   (vname list => exp list => 'a exec_dg_st => 'a exec_dg_st) =>
   cfg => 'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT"
where
  "placed_dg_gen_of source_global owner_of locations_of keep_local publish_side
      transfer enter graph bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_trees intra_predecessor_list (\<lambda>_. ())
      (placed_dg_edge_of owner_of locations_of keep_local publish_side transfer)
      (placed_dg_combine_of source_global owner_of locations_of keep_local publish_side)
      (placed_dg_enter_of owner_of locations_of keep_local publish_side enter)
      graph bot0 s0d s0g"

text \<open>Strict counterparts, wired to \<open>placed_dg_*_tree_strict\<close> instead of the
  defensive \<open>placed_dg_*_tree\<close>: the equation system a placement instance
  actually solves should use these, so every generated value's support is
  bounded by construction.\<close>

definition placed_dg_edge_of_strict ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   unit => pp => edge_action => pp =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_edge_of_strict owner_of locations_of keep_local publish_side transfer ctx
      read_node action write_node =
    map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
      (placed_dg_edge_tree_strict owner_of locations_of keep_local publish_side
        (transfer action) read_node write_node))"

definition placed_dg_combine_of_strict ::
  "(vname => bool) => (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   unit => pp => call_action => pp => pp =>
   (pp \<times> unit, unit, ('a::bounded_semilattice_sup_bot exec_dg_st,
     'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_combine_of_strict source_global owner_of locations_of keep_local publish_side
      ctx caller action callee continuation =
    (case action of CallEdge destination parameters arguments =>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_dg_combine_tree_strict owner_of locations_of keep_local publish_side
          (\<lambda>destination caller_state callee_state side_state.
            combine_collect_resolved_for_q source_global destination
              (caller_state \<squnion> side_state) (callee_state \<squnion> side_state))
          destination caller callee continuation)))"

definition placed_dg_enter_of_strict ::
  "(pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname list => exp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   unit => pp => call_action => pp =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) strategy_tree"
where
  "placed_dg_enter_of_strict owner_of locations_of keep_local publish_side enter ctx
      caller action callee =
    (case action of CallEdge destination parameters arguments =>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_dg_enter_tree_strict owner_of locations_of keep_local publish_side
          enter parameters arguments caller callee)))"

text \<open>
  The executable hook-wrapper equations: \<open>placed_dg_edge_of_strict\<close>,
  \<open>placed_dg_combine_of_strict\<close>, and \<open>placed_dg_enter_of_strict\<close> each wrap
  their underlying tree constructor in \<open>map_gtree\<close>/\<open>map_ltree\<close> to fit the
  keyed generator's query shape. These lemmas push \<open>traverse_rhs\<close>/
  \<open>sides_of_rhs\<close> through that wrapping once, so an instance names the wrapped
  hook directly instead of re-unfolding \<open>map_gtree\<close>/\<open>map_ltree\<close> and the
  underlying tree definition at every call site.
\<close>

lemma traverse_rhs_placed_dg_edge_of_strict:
  "traverse_rhs
    (placed_dg_edge_of_strict owner_of locations_of keep_local publish_side
      transfer ctx read_node action write_node) sigma =
    DG (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
          keep_local
          (transfer action (locals (sigma (Inl (read_node, ctx))) \<squnion>
            globs (sigma (Inr ()))))) bot"
  unfolding placed_dg_edge_of_strict_def
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_dg_edge_tree_strict sum.map_comp o_def)

lemma sides_of_rhs_placed_dg_edge_of_strict:
  "sides_of_rhs
    (placed_dg_edge_of_strict owner_of locations_of keep_local publish_side
      transfer ctx read_node action write_node) sigma (Inr ()) =
    DG bot (project_resolved_on_strict (owner_of write_node) (locations_of write_node)
          publish_side
          (transfer action (locals (sigma (Inl (read_node, ctx))) \<squnion>
            globs (sigma (Inr ())))))"
  unfolding placed_dg_edge_of_strict_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_dg_edge_tree_strict_Inr sum.map_comp o_def)

lemma traverse_rhs_placed_dg_enter_of_strict:
  "traverse_rhs
    (placed_dg_enter_of_strict owner_of locations_of keep_local publish_side
      enter ctx caller (CallEdge destination parameters arguments) callee) sigma =
    DG (project_resolved_on_strict (owner_of callee) (locations_of callee)
          keep_local
          (enter parameters arguments (locals (sigma (Inl (caller, ctx))) \<squnion>
            globs (sigma (Inr ()))))) bot"
  unfolding placed_dg_enter_of_strict_def placed_dg_enter_tree_strict_eq
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_dg_edge_tree_strict sum.map_comp o_def)

lemma sides_of_rhs_placed_dg_enter_of_strict:
  "sides_of_rhs
    (placed_dg_enter_of_strict owner_of locations_of keep_local publish_side
      enter ctx caller (CallEdge destination parameters arguments) callee) sigma (Inr ()) =
    DG bot (project_resolved_on_strict (owner_of callee) (locations_of callee)
          publish_side
          (enter parameters arguments (locals (sigma (Inl (caller, ctx))) \<squnion>
            globs (sigma (Inr ())))))"
  unfolding placed_dg_enter_of_strict_def placed_dg_enter_tree_strict_eq
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_dg_edge_tree_strict_Inr sum.map_comp o_def)

lemma traverse_rhs_placed_dg_combine_of_strict:
  "traverse_rhs
    (placed_dg_combine_of_strict source_global owner_of locations_of keep_local publish_side
      ctx caller (CallEdge destination parameters arguments) callee continuation) sigma =
    DG (project_resolved_on_strict (owner_of continuation) (locations_of continuation)
          keep_local
          (combine_collect_resolved_for_q source_global destination
            (locals (sigma (Inl (caller, ctx))) \<squnion> globs (sigma (Inr ())))
            (locals (sigma (Inl (callee, ctx))) \<squnion> globs (sigma (Inr ()))))) bot"
  unfolding placed_dg_combine_of_strict_def
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_dg_combine_tree_strict sum.map_comp o_def)

lemma sides_of_rhs_placed_dg_combine_of_strict:
  "sides_of_rhs
    (placed_dg_combine_of_strict source_global owner_of locations_of keep_local publish_side
      ctx caller (CallEdge destination parameters arguments) callee continuation) sigma (Inr ()) =
    DG bot (project_resolved_on_strict (owner_of continuation) (locations_of continuation)
          publish_side
          (combine_collect_resolved_for_q source_global destination
            (locals (sigma (Inl (caller, ctx))) \<squnion> globs (sigma (Inr ())))
            (locals (sigma (Inl (callee, ctx))) \<squnion> globs (sigma (Inr ())))))"
  unfolding placed_dg_combine_of_strict_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_dg_combine_tree_strict_Inr sum.map_comp o_def)

definition placed_dg_gen_of_strict ::
  "(vname => bool) => (pp => pname) => (pp => location list) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   (vname list => exp list => 'a exec_dg_st => 'a exec_dg_st) =>
   cfg => 'a exec_dg_st => 'a exec_dg_st => 'a exec_dg_st =>
   (pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT"
where
  "placed_dg_gen_of_strict source_global owner_of locations_of keep_local publish_side
      transfer enter graph bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_trees intra_predecessor_list (\<lambda>_. ())
      (placed_dg_edge_of_strict owner_of locations_of keep_local publish_side transfer)
      (placed_dg_combine_of_strict source_global owner_of locations_of keep_local publish_side)
      (placed_dg_enter_of_strict owner_of locations_of keep_local publish_side enter)
      graph bot0 s0d s0g"


definition placed_abs_dg_edge_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow>
   (scoped_location \<Rightarrow> bool) \<Rightarrow> (scoped_location \<Rightarrow> bool) \<Rightarrow>
   (edge_action \<Rightarrow>
     ('a::bounded_semilattice_sup_bot) abs_state \<Rightarrow> 'a abs_state) \<Rightarrow>
   unit \<Rightarrow> pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "placed_abs_dg_edge_of source_global owner_of keep_local publish_side
      transfer ctx read_node action write_node =
    map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
      (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
        (transfer action) read_node write_node))"

definition placed_abs_dg_combine_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow>
   (scoped_location \<Rightarrow> bool) \<Rightarrow> (scoped_location \<Rightarrow> bool) \<Rightarrow>
   unit \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit,
     ('a::bounded_semilattice_sup_bot abs_state, 'a abs_state) dg_state)
       strategy_tree"
where
  "placed_abs_dg_combine_of source_global owner_of keep_local publish_side
      ctx caller action callee continuation =
    (case action of CallEdge destination parameters arguments \<Rightarrow>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_abs_dg_combine_tree source_global owner_of
          keep_local publish_side
          (\<lambda>destination caller_state callee_state side_state.
            combine\<^sup># source_global destination
              (caller_state \<squnion> side_state)
              (callee_state \<squnion> side_state))
          destination caller callee continuation)))"

definition placed_abs_dg_enter_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow>
   (scoped_location \<Rightarrow> bool) \<Rightarrow> (scoped_location \<Rightarrow> bool) \<Rightarrow>
   (vname list \<Rightarrow> exp list \<Rightarrow>
     ('a::bounded_semilattice_sup_bot) abs_state \<Rightarrow> 'a abs_state) \<Rightarrow>
   unit \<Rightarrow> pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "placed_abs_dg_enter_of source_global owner_of keep_local publish_side
      enter ctx caller action callee =
    (case action of CallEdge destination parameters arguments \<Rightarrow>
      map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>node. (node, ctx))
        (placed_abs_dg_enter_tree source_global owner_of
          keep_local publish_side enter parameters arguments caller callee)))"

text \<open>
  The abstract hook-wrapper equations, mirroring the executable ones above:
  \<open>placed_abs_dg_edge_of\<close>, \<open>placed_abs_dg_enter_of\<close>, and
  \<open>placed_abs_dg_combine_of\<close> each wrap \<^const>\<open>placed_abs_dg_edge_tree\<close>/
  \<^const>\<open>placed_abs_dg_combine_tree\<close> in \<open>map_gtree\<close>/\<open>map_ltree\<close>. An analysis
  instance's own hook-soundness proof (\<open>edge_hook_sound\<close>, \<open>enter_hook_sound\<close>,
  \<open>combine_hook_sound\<close> in the \<^locale>\<open>sound_dg_hooks\<close> locale) cites these
  named equations directly instead of unfolding \<open>map_gtree\<close>/\<open>map_ltree\<close> and
  the tree definition afresh for every domain.
\<close>

lemma traverse_rhs_placed_abs_dg_edge_of:
  "traverse_rhs
    (placed_abs_dg_edge_of source_global owner_of keep_local publish_side
      transfer ctx read_node action write_node) sigma =
    DG (project_abs_on (owner_of write_node) source_global keep_local
          (transfer action (locals (sigma (Inl (read_node, ctx))) \<squnion>
            globs (sigma (Inr ()))))) bot"
  unfolding placed_abs_dg_edge_of_def
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_abs_dg_edge_tree sum.map_comp o_def)

lemma sides_of_rhs_placed_abs_dg_edge_of:
  "sides_of_rhs
    (placed_abs_dg_edge_of source_global owner_of keep_local publish_side
      transfer ctx read_node action write_node) sigma (Inr ()) =
    DG bot (project_abs_on (owner_of write_node) source_global publish_side
          (transfer action (locals (sigma (Inl (read_node, ctx))) \<squnion>
            globs (sigma (Inr ())))))"
  unfolding placed_abs_dg_edge_of_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_abs_dg_edge_tree_Inr sum.map_comp o_def)

lemma traverse_rhs_placed_abs_dg_enter_of:
  "traverse_rhs
    (placed_abs_dg_enter_of source_global owner_of keep_local publish_side
      enter ctx caller (CallEdge destination parameters arguments) callee) sigma =
    DG (project_abs_on (owner_of callee) source_global keep_local
          (enter parameters arguments (locals (sigma (Inl (caller, ctx))) \<squnion>
            globs (sigma (Inr ()))))) bot"
  unfolding placed_abs_dg_enter_of_def placed_abs_dg_enter_tree_def
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_abs_dg_edge_tree sum.map_comp o_def)

lemma sides_of_rhs_placed_abs_dg_enter_of:
  "sides_of_rhs
    (placed_abs_dg_enter_of source_global owner_of keep_local publish_side
      enter ctx caller (CallEdge destination parameters arguments) callee) sigma (Inr ()) =
    DG bot (project_abs_on (owner_of callee) source_global publish_side
          (enter parameters arguments (locals (sigma (Inl (caller, ctx))) \<squnion>
            globs (sigma (Inr ())))))"
  unfolding placed_abs_dg_enter_of_def placed_abs_dg_enter_tree_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_abs_dg_edge_tree_Inr sum.map_comp o_def)

lemma traverse_rhs_placed_abs_dg_combine_of:
  "traverse_rhs
    (placed_abs_dg_combine_of source_global owner_of keep_local publish_side
      ctx caller (CallEdge destination parameters arguments) callee continuation) sigma =
    DG (project_abs_on (owner_of continuation) source_global keep_local
          (combine\<^sup># source_global destination
            (locals (sigma (Inl (caller, ctx))) \<squnion> globs (sigma (Inr ())))
            (locals (sigma (Inl (callee, ctx))) \<squnion> globs (sigma (Inr ()))))) bot"
  unfolding placed_abs_dg_combine_of_def
  by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
    traverse_placed_abs_dg_combine_tree sum.map_comp o_def)

lemma sides_of_rhs_placed_abs_dg_combine_of:
  "sides_of_rhs
    (placed_abs_dg_combine_of source_global owner_of keep_local publish_side
      ctx caller (CallEdge destination parameters arguments) callee continuation) sigma (Inr ()) =
    DG bot (project_abs_on (owner_of continuation) source_global publish_side
          (combine\<^sup># source_global destination
            (locals (sigma (Inl (caller, ctx))) \<squnion> globs (sigma (Inr ())))
            (locals (sigma (Inl (callee, ctx))) \<squnion> globs (sigma (Inr ())))))"
  unfolding placed_abs_dg_combine_of_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
    sides_placed_abs_dg_combine_tree_Inr sum.map_comp o_def)

definition placed_abs_dg_gen_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow>
   (scoped_location \<Rightarrow> bool) \<Rightarrow> (scoped_location \<Rightarrow> bool) \<Rightarrow>
   (edge_action \<Rightarrow>
     ('a::bounded_semilattice_sup_bot) abs_state \<Rightarrow> 'a abs_state) \<Rightarrow>
   (vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow>
   cfg \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow>
   (pp \<times> unit, unit, ('a abs_state, 'a abs_state) dg_state) eqsT"
where
  "placed_abs_dg_gen_of source_global owner_of keep_local publish_side
      transfer enter graph bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_trees intra_predecessor_list (\<lambda>_. ())
      (placed_abs_dg_edge_of source_global owner_of
        keep_local publish_side transfer)
      (placed_abs_dg_combine_of source_global owner_of
        keep_local publish_side)
      (placed_abs_dg_enter_of source_global owner_of
        keep_local publish_side enter)
      graph bot0 s0d s0g"





subsection \<open>Per-tree traversal commutation\<close>

text \<open>
  The D/G edge and combine trees have closed-form traversals
  (\<open>Voblint_Core.DG_Framework\<close>): the local Answer carries \<open>snd (step \<dots>)\<close>
  and no global, so \<open>fun_of_dg_st\<close> commutes with the traversal precisely when
  the analysis step commutes componentwise.
\<close>


lemma traverse_dg_edge_tree_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g)
                     = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (dg_edge_tree step_st u) \<sigma>_st)
           = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "snd (step_abs (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl u)))) (fun_of_exec_dg_st_for gs (globs (\<sigma>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (snd (step_st (locals (\<sigma>_st (Inl u))) (globs (\<sigma>_st (Inr ())))))"
    using H[of "locals (\<sigma>_st (Inl u))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_edge_tree fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_bot bot_fun_def)
qed

lemma traverse_wrapped_edge_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g)
                     = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_for gs (traverse_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_edge_tree_commute_for)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

subsection \<open>Wrapped-tree commutation and the accumulator fold\<close>

text \<open>
  The generator re-keys each tree with \<open>map_gtree\<close> / \<open>map_ltree\<close> to place
  local unknowns at \<open>(pp, c)\<close> and global unknowns at \<open>gkey c\<close>.  Those relabellings
  are transparent to \<open>fun_of_dg_st\<close>: it acts on values, they act on unknown
  keys, and the per-tree commutation is stated for an arbitrary valuation.
\<close>


text \<open>Generic mirror of \<open>traverse_wrapped_combine_commute\<close> over an arbitrary storage
  classifier \<open>gs\<close>, built on \<open>traverse_dg_combine_tree_commute_for\<close> below. (The
  \<open>side_acc_dg\<close> fold has its own generic mirror, \<open>side_acc_dg_commute_for\<close>, further
  down alongside \<open>sides_side_rhs_fold_dg_commute_for\<close>.)\<close>

lemma traverse_dg_combine_tree_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (dg_combine_tree comb_st dst cc ex) \<sigma>_st)
           = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "snd (comb_abs dst (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl cc)))) (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl ex))))
              (fun_of_exec_dg_st_for gs (globs (\<sigma>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (snd (comb_st dst (locals (\<sigma>_st (Inl cc))) (locals (\<sigma>_st (Inl ex)))
              (globs (\<sigma>_st (Inr ())))))"
    using H[of dst "locals (\<sigma>_st (Inl cc))" "locals (\<sigma>_st (Inl ex))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_combine_tree fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_bot bot_fun_def)
qed

lemma traverse_wrapped_combine_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_for gs (traverse_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_combine_tree_commute_for)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

end
