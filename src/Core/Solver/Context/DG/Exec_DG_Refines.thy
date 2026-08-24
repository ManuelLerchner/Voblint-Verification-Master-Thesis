section \<open>The executable carrier and its readback\<close>

text \<open>
  The verified solver uses the executable association-list carrier \<open>'a exec_dg_st\<close>, while
  soundness is stated over function-valued abstract states. This theory is the bottom of the
  bridge: the D/G product's lattice structure, the finite-scope representation the solver
  hands back, the readback \<open>fun_of_dg_st_for\<close> that lifts \<open>fun_of_exec_dg_st_for\<close> to that product,
  and the refinement relation between an executable table and an abstract one.

  D/G lattice operations are componentwise, so the product inherits the order, join, bottom,
  equality, and widening operations the solver requires.
\<close>

theory Exec_DG_Refines
  imports
    "Voblint_Core.DG_Soundness"
    "Voblint_Core.Exec_Refinement"
    "Voblint_Core.Routed_Context"
begin


type_synonym 'a exec_dg_st = "'a resolved_st_q"

subsection \<open>The combined warrowing arity for the executable state\<close>

text \<open>
  The D/G product requires each executable component to satisfy
  \<open>bounded_warrowing\<close>.  The association-list carrier already provides the required bottom,
  join, and warrowing operations, so the combined instance follows directly.
\<close>

text \<open>The quotient carrier inherits the executable lattice structure.\<close>

subsection \<open>Finite-scope D/G representation\<close>

text \<open>The executable local and side components represent their abstract counterparts pointwise on a finite set of executable locations.  Scope resolution is an explicit premise of transfer lemmas: this relation itself does not infer storage from a missing declaration.\<close>

definition dg_refines_on ::
  "location set =>
   (('a::bot) exec_dg_st, ('b::bot) exec_dg_st) dg_state =>
   ('a abs_state, 'b abs_state) dg_state => bool"
where
  "dg_refines_on universe executable abstract_state \<longleftrightarrow>
    (\<forall>location \<in> universe.
      lookup_resolved_st_q (locals executable) location =
        locals abstract_state (location_vname location)) \<and>
    (\<forall>location \<in> universe.
      lookup_resolved_st_q (globs executable) location =
        globs abstract_state (location_vname location))"

lemma dg_refines_onD_local:
  "\<lbrakk>dg_refines_on universe executable abstract_state; location \<in> universe\<rbrakk> \<Longrightarrow>
   lookup_resolved_st_q (locals executable) location =
     locals abstract_state (location_vname location)"
  by (simp add: dg_refines_on_def)

lemma dg_refines_onD_side:
  "\<lbrakk>dg_refines_on universe executable abstract_state; location \<in> universe\<rbrakk> \<Longrightarrow>
   lookup_resolved_st_q (globs executable) location =
     globs abstract_state (location_vname location)"
  by (simp add: dg_refines_on_def)

lemma dg_refines_onI:
  assumes "\<And>location. location \<in> universe \<Longrightarrow>
    lookup_resolved_st_q (locals executable) location =
      locals abstract_state (location_vname location)"
    and "\<And>location. location \<in> universe \<Longrightarrow>
    lookup_resolved_st_q (globs executable) location =
      globs abstract_state (location_vname location)"
  shows "dg_refines_on universe executable abstract_state"
  using assms by (simp add: dg_refines_on_def)

lemma dg_refines_on_recombine:
  fixes executable :: "('a::bounded_semilattice_sup_bot exec_dg_st,
    'a exec_dg_st) dg_state"
  assumes refines: "dg_refines_on universe executable abstract_state"
    and relevant: "location \<in> universe"
  shows
    "lookup_resolved_st_q (locals executable \<squnion> globs executable) location =
      (locals abstract_state \<squnion> globs abstract_state) (location_vname location)"
proof -
  have local:
    "lookup_resolved_st_q (locals executable) location =
      locals abstract_state (location_vname location)"
    by (rule dg_refines_onD_local[OF refines relevant])
  have side:
    "lookup_resolved_st_q (globs executable) location =
      globs abstract_state (location_vname location)"
    by (rule dg_refines_onD_side[OF refines relevant])
  show ?thesis by (simp add: local side)
qed

lemma dg_refines_on_sup:
  fixes exec1 exec2 :: "(('a::bounded_semilattice_sup_bot) exec_dg_st,
    ('b::bounded_semilattice_sup_bot) exec_dg_st) dg_state"
  assumes r1: "dg_refines_on universe exec1 abs1"
    and r2: "dg_refines_on universe exec2 abs2"
  shows "dg_refines_on universe (exec1 \<squnion> exec2) (abs1 \<squnion> abs2)"
proof (rule dg_refines_onI)
  fix location assume loc: "location \<in> universe"
  show "lookup_resolved_st_q (locals (exec1 \<squnion> exec2)) location =
      locals (abs1 \<squnion> abs2) (location_vname location)"
    by (simp add: sup_dg_state_def sup_fun_def
      dg_refines_onD_local[OF r1 loc] dg_refines_onD_local[OF r2 loc])
next
  fix location assume loc: "location \<in> universe"
  show "lookup_resolved_st_q (globs (exec1 \<squnion> exec2)) location =
      globs (abs1 \<squnion> abs2) (location_vname location)"
    by (simp add: sup_dg_state_def sup_fun_def
      dg_refines_onD_side[OF r1 loc] dg_refines_onD_side[OF r2 loc])
qed

lemma dg_refines_on_bot:
  "dg_refines_on universe (bot :: (('a::bounded_semilattice_sup_bot) exec_dg_st,
    ('b::bounded_semilattice_sup_bot) exec_dg_st) dg_state) bot"
  by (simp add: bot_dg_state_def dg_refines_onI)

definition project_abs_on ::
  "pname => (vname => bool) => (scoped_location => bool) =>
   'a::bot abs_state => 'a abs_state"
where
  "project_abs_on owner source_global placed state =
    project_component (\<lambda>x. placed (owner, location_of source_global x)) state"

lemma project_abs_on_lookup:
  assumes resolved: "location = location_of source_global (location_vname location)"
  shows
    "project_abs_on owner source_global placed state (location_vname location) =
      (if placed (owner, location) then state (location_vname location) else bot)"
  using resolved
  unfolding project_abs_on_def project_component_def by simp

subsection \<open>Owner-aware abstract D/G trees\<close>

text \<open>The abstract tree mirrors the executable placed tree.  It projects function states pointwise, while the executable tree materializes the same policy over a finite scope.\<close>

definition placed_abs_dg_edge_tree ::
  "(vname => bool) => (pp => pname) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state) =>
   pp => pp => (pp, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
      transfer read_node write_node = do {
     local \<leftarrow> read_local read_node;
     side \<leftarrow> read_global ();
     let result = transfer (locals local \<squnion> globs side);
     depend_on () (DG bot
         (project_abs_on (owner_of write_node) source_global publish_side result))
       (answer (DG
         (project_abs_on (owner_of write_node) source_global keep_local result)
         bot))
   }"

lemma traverse_placed_abs_dg_edge_tree:
  "traverse_rhs
    (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
      transfer read_node write_node) sigma =
    DG (project_abs_on (owner_of write_node) source_global keep_local
          (transfer (locals (sigma (Inl read_node)) \<squnion>
            globs (sigma (Inr ()))))) bot"
  unfolding placed_abs_dg_edge_tree_def by (simp add: Let_def)

lemma sides_placed_abs_dg_edge_tree_Inr:
  "sides_of_rhs
    (placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
      transfer read_node write_node) sigma (Inr ()) =
    DG bot
      (project_abs_on (owner_of write_node) source_global publish_side
        (transfer (locals (sigma (Inl read_node)) \<squnion>
          globs (sigma (Inr ())))))"
  unfolding placed_abs_dg_edge_tree_def by (simp add: Let_def)

definition placed_abs_dg_enter_tree ::
  "(vname => bool) => (pp => pname) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname list => exp list =>
     ('a::bounded_semilattice_sup_bot) abs_state => 'a abs_state) =>
   vname list => exp list => pp => pp =>
   (pp, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "placed_abs_dg_enter_tree source_global owner_of keep_local publish_side
      enter parameters arguments caller callee =
    placed_abs_dg_edge_tree source_global owner_of keep_local publish_side
      (enter parameters arguments) caller callee"

definition placed_abs_dg_combine_tree ::
  "(vname => bool) => (pp => pname) =>
   (scoped_location => bool) => (scoped_location => bool) =>
   (vname option => ('a::bounded_semilattice_sup_bot) abs_state =>
     'a abs_state => 'a abs_state => 'a abs_state) =>
   vname option => pp => pp => pp =>
   (pp, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
      combine destination caller callee write_node = do {
     caller_state \<leftarrow> read_local caller;
     callee_state \<leftarrow> read_local callee;
     side \<leftarrow> read_global ();
     let result = combine destination (locals caller_state)
       (locals callee_state) (globs side);
     depend_on () (DG bot
         (project_abs_on (owner_of write_node) source_global publish_side result))
       (answer (DG
         (project_abs_on (owner_of write_node) source_global keep_local result)
         bot))
   }"

lemma traverse_placed_abs_dg_combine_tree:
  "traverse_rhs
    (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
      combine destination caller callee write_node) sigma =
    DG (project_abs_on (owner_of write_node) source_global keep_local
      (combine destination (locals (sigma (Inl caller)))
        (locals (sigma (Inl callee))) (globs (sigma (Inr ()))))) bot"
  unfolding placed_abs_dg_combine_tree_def by (simp add: Let_def)

lemma sides_placed_abs_dg_combine_tree_Inr:
  "sides_of_rhs
    (placed_abs_dg_combine_tree source_global owner_of keep_local publish_side
      combine destination caller callee write_node) sigma (Inr ()) =
    DG bot
      (project_abs_on (owner_of write_node) source_global publish_side
        (combine destination (locals (sigma (Inl caller)))
          (locals (sigma (Inl callee))) (globs (sigma (Inr ())))))"
  unfolding placed_abs_dg_combine_tree_def by (simp add: Let_def)

lemma dg_refines_on_project:
  fixes executable_result :: "'a::bounded_semilattice_sup_bot exec_dg_st"
  assumes raw:
    "\<And>location. location \<in> set universe \<Longrightarrow>
      lookup_resolved_st_q executable_result location =
        abstract_result (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set universe \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set universe)
      (DG (project_resolved_on owner universe keep_local executable_result)
        (project_resolved_on owner universe publish_side executable_result))
      (DG (project_abs_on owner source_global keep_local abstract_result)
        (project_abs_on owner source_global publish_side abstract_result))"
proof (rule dg_refines_onI)
  fix location
  assume location: "location \<in> set universe"
  have raw_location:
    "lookup_resolved_st_q executable_result location =
      abstract_result (location_vname location)"
    by (rule raw[OF location])
  have resolved_location:
    "location = location_of source_global (location_vname location)"
    by (rule resolved[OF location])
  show
    "lookup_resolved_st_q
      (locals
        (DG (project_resolved_on owner universe keep_local executable_result)
          (project_resolved_on owner universe publish_side executable_result)))
      location =
      locals
        (DG (project_abs_on owner source_global keep_local abstract_result)
          (project_abs_on owner source_global publish_side abstract_result))
        (location_vname location)"
    by (simp add: lookup_project_resolved_on
      project_abs_on_lookup[OF resolved_location] raw_location location)
next
  fix location
  assume location: "location \<in> set universe"
  have raw_location:
    "lookup_resolved_st_q executable_result location =
      abstract_result (location_vname location)"
    by (rule raw[OF location])
  have resolved_location:
    "location = location_of source_global (location_vname location)"
    by (rule resolved[OF location])
  show
    "lookup_resolved_st_q
      (globs
        (DG (project_resolved_on owner universe keep_local executable_result)
          (project_resolved_on owner universe publish_side executable_result)))
      location =
      globs
        (DG (project_abs_on owner source_global keep_local abstract_result)
          (project_abs_on owner source_global publish_side abstract_result))
        (location_vname location)"
    by (simp add: lookup_project_resolved_on
      project_abs_on_lookup[OF resolved_location] raw_location location)
qed

lemma dg_refines_on_project_strict:
  fixes executable_result :: "'a::bounded_semilattice_sup_bot exec_dg_st"
  assumes raw:
    "\<And>location. location \<in> set universe \<Longrightarrow>
      lookup_resolved_st_q executable_result location =
        abstract_result (location_vname location)"
    and resolved:
      "\<And>location. location \<in> set universe \<Longrightarrow>
        location = location_of source_global (location_vname location)"
  shows
    "dg_refines_on (set universe)
      (DG (project_resolved_on_strict owner universe keep_local executable_result)
        (project_resolved_on_strict owner universe publish_side executable_result))
      (DG (project_abs_on owner source_global keep_local abstract_result)
        (project_abs_on owner source_global publish_side abstract_result))"
proof (rule dg_refines_onI)
  fix location
  assume location: "location \<in> set universe"
  have raw_location:
    "lookup_resolved_st_q executable_result location =
      abstract_result (location_vname location)"
    by (rule raw[OF location])
  have resolved_location:
    "location = location_of source_global (location_vname location)"
    by (rule resolved[OF location])
  show
    "lookup_resolved_st_q
      (locals
        (DG (project_resolved_on_strict owner universe keep_local executable_result)
          (project_resolved_on_strict owner universe publish_side executable_result)))
      location =
      locals
        (DG (project_abs_on owner source_global keep_local abstract_result)
          (project_abs_on owner source_global publish_side abstract_result))
        (location_vname location)"
    by (simp add: lookup_project_resolved_on_strict
      project_abs_on_lookup[OF resolved_location] raw_location location)
next
  fix location
  assume location: "location \<in> set universe"
  have raw_location:
    "lookup_resolved_st_q executable_result location =
      abstract_result (location_vname location)"
    by (rule raw[OF location])
  have resolved_location:
    "location = location_of source_global (location_vname location)"
    by (rule resolved[OF location])
  show
    "lookup_resolved_st_q
      (globs
        (DG (project_resolved_on_strict owner universe keep_local executable_result)
          (project_resolved_on_strict owner universe publish_side executable_result)))
      location =
      globs
        (DG (project_abs_on owner source_global keep_local abstract_result)
          (project_abs_on owner source_global publish_side abstract_result))
        (location_vname location)"
    by (simp add: lookup_project_resolved_on_strict
      project_abs_on_lookup[OF resolved_location] raw_location location)
qed



subsection \<open>Classifier-parametric readback\<close>

text \<open>
  The executable local/side readback, generic in the classifier: a placed
  executable state is written with a declaration-driven classifier, so
  reading it back needs the same classifier or the readback consults the
  wrong slot.
\<close>

definition fun_of_exec_dg_st_for ::
  "(vname => bool) => ('a::bot) exec_dg_st => 'a abs_state" where
  "fun_of_exec_dg_st_for gs = fun_of_resolved_st_q_for gs"

lemma fun_of_exec_dg_st_for_bot [simp]:
  "fun_of_exec_dg_st_for gs (bot :: ('a::order_bot) exec_dg_st) = bot"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_bot)

lemma fun_of_exec_dg_st_for_sup [simp]:
  "fun_of_exec_dg_st_for gs ((s :: ('a::bounded_semilattice_sup_bot) exec_dg_st) \<squnion> t)
     = fun_of_exec_dg_st_for gs s \<squnion> fun_of_exec_dg_st_for gs t"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_sup)

definition fun_of_dg_st_for ::
  "(vname => bool) =>
   (('a::bot) exec_dg_st, ('b::bot) exec_dg_st) dg_state => ('a abs_state, 'b abs_state) dg_state"
where
  "fun_of_dg_st_for gs d =
    DG (fun_of_exec_dg_st_for gs (locals d)) (fun_of_exec_dg_st_for gs (globs d))"

lemma fun_of_dg_st_for_simps [simp]:
  "locals (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (locals d)"
  "globs (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (globs d)"
  "fun_of_dg_st_for gs (DG a b) = DG (fun_of_exec_dg_st_for gs a) (fun_of_exec_dg_st_for gs b)"
  by (simp_all add: fun_of_dg_st_for_def)

lemma fun_of_dg_st_for_bot [simp]:
  "fun_of_dg_st_for gs (bot :: ('a::bounded_semilattice_sup_bot exec_dg_st,
                         'b::bounded_semilattice_sup_bot exec_dg_st) dg_state) = bot"
  by (simp add: bot_dg_state_def)

lemma fun_of_dg_st_for_sup:
  "fun_of_dg_st_for gs ((a::('c::bounded_semilattice_sup_bot exec_dg_st,
                      'd::bounded_semilattice_sup_bot exec_dg_st) dg_state) \<squnion> b)
     = fun_of_dg_st_for gs a \<squnion> fun_of_dg_st_for gs b"
  by (simp add: fun_of_dg_st_for_def sup_dg_state_def fun_of_exec_dg_st_for_def
    fun_of_resolved_st_q_for_sup)

lemma fun_of_dg_st_for_mono:
  "(a::('c::bounded_semilattice_sup_bot exec_dg_st, 'd::bounded_semilattice_sup_bot exec_dg_st) dg_state) \<le> b
     \<Longrightarrow> fun_of_dg_st_for gs a \<le> fun_of_dg_st_for gs b"
  by (auto simp: fun_of_dg_st_for_def less_eq_dg_state_def fun_of_exec_dg_st_for_def
    fun_of_resolved_st_q_for_mono)

lemma location_vname_location_of [simp]:
  "location_vname (location_of gs x) = x"
  by (simp add: location_of_def)

text \<open>
  The two state representations disagree on what an unrepresented location
  means.  The executable carrier is sparse: a location a placement never
  materializes reads back as \<open>bot\<close>, "no value is recorded here".  The abstract
  carrier is total: \<^const>\<open>project_abs_on\<close> classifies every location as local
  or side but never restricts \<^emph>\<open>which\<close> locations exist, so an abstract value
  at a location outside a node's own scope is still whatever the transfer
  function produced there, not \<open>bot\<close> -- collapsing it to \<open>bot\<close> would assert
  "no concrete state reaches here", which is false for a location the node
  simply never mentions.  \<open>complete_abs_on\<close> is the correct completion: read
  through the scope, and complete with a caller-supplied \<open>outside\<close> value
  everywhere else.  For a domain where every value is bounded by a single
  greatest element, \<open>outside\<close> can be that top element, and the completed
  bound is trivially large enough outside the scope; the lemma is stated
  against an arbitrary \<open>outside\<close> so it does not depend on such an element
  existing.
\<close>

definition complete_abs_on ::
  "(vname => bool) => location set => (vname => 'a) =>
    ('a::bot) exec_dg_st => 'a abs_state"
where
  "complete_abs_on gs universe outside s x =
    (if location_of gs x \<in> universe then fun_of_exec_dg_st_for gs s x
     else outside x)"

lemma complete_abs_on_inside:
  "location_of gs x \<in> universe \<Longrightarrow>
    complete_abs_on gs universe outside s x = fun_of_exec_dg_st_for gs s x"
  by (simp add: complete_abs_on_def)

lemma complete_abs_on_outside:
  "location_of gs x \<notin> universe \<Longrightarrow>
    complete_abs_on gs universe outside s x = outside x"
  by (simp add: complete_abs_on_def)

text \<open>
  The upgrade from scoped agreement to a full inequality against the
  completed lift.  \<open>dg_refines_on\<close> only claims equality on a finite scope; a
  \<^const>\<open>part_post_solution\<close> obligation is an inequality against the \<^emph>\<open>whole\<close>
  abstract state.  Inside the scope, the executable side's own inequality
  (from its part_post_solution) transports verbatim through the scoped
  equality.  Outside the scope, the obligation is discharged against
  whatever \<open>outside\<close> value the completed bound uses there, not against
  \<open>bot\<close>; the caller supplies the bound \<open>abs_val x \<le> outside x\<close>, which for a
  domain with a greatest element is free.
\<close>

lemma le_lift_if_dg_refines_on_and_le:
  fixes exec_val exec_bound :: "('a::bounded_semilattice_sup_bot) exec_dg_st"
    and outside :: "vname => 'a"
  assumes refines: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q exec_val location = abs_val (location_vname location)"
    and outside_le: "\<And>x. location_of gs x \<notin> universe \<Longrightarrow> abs_val x \<le> outside x"
    and le: "exec_val \<le> exec_bound"
  shows "abs_val \<le> complete_abs_on gs universe outside exec_bound"
proof (rule le_funI)
  fix x
  show "abs_val x \<le> complete_abs_on gs universe outside exec_bound x"
  proof (cases "location_of gs x \<in> universe")
    case True
    have "abs_val x = lookup_resolved_st_q exec_val (location_of gs x)"
      using refines[OF True] by simp
    also have "\<dots> \<le> lookup_resolved_st_q exec_bound (location_of gs x)"
      using le by (simp add: le_resolved_st_q_iff)
    also have "\<dots> = complete_abs_on gs universe outside exec_bound x"
      unfolding complete_abs_on_def fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def
      using True by simp
    finally show ?thesis .
  next
    case False
    have "abs_val x \<le> outside x" by (rule outside_le[OF False])
    also have "\<dots> = complete_abs_on gs universe outside exec_bound x"
      using False by (simp add: complete_abs_on_def)
    finally show ?thesis .
  qed
qed

subsection \<open>The generic completed-readback constructor\<close>

text \<open>
  \<open>completed_sigma_abs\<close> builds the abstract witness fed to a hook-generated
  equation system directly from the executable solution: the executable
  readback at every node's own scope, completed to \<open>outside\<close> beyond it, and
  the executable readback straight through elsewhere (the shared \<open>G\<close> side
  channel, which needs no completion since \<^const>\<open>complete_abs_on\<close>'s scope
  argument is per-node, not per-channel). An analysis instance's own
  completed sigma (its \<open>_sigma_abs\<close>) is this constructor applied to its own
  executable TD solution, classifier, node-scope function, and completion
  value -- not a fresh case split over \<open>Inl\<close>/\<open>Inr\<close>.
\<close>

definition completed_sigma_abs ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<Rightarrow> location list) \<Rightarrow> 'a \<Rightarrow>
   (pp \<times> 'c + unit \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st, 'a exec_dg_st) dg_state) \<Rightarrow>
   pp \<times> 'c + unit \<Rightarrow> ('a abs_state, 'a abs_state) dg_state"
where
  "completed_sigma_abs gs locations_of outside exec_sigma k =
    (case k of
       Inl (v, ctx) \<Rightarrow> DG
         (complete_abs_on gs (set (locations_of v)) (\<lambda>_. outside)
           (locals (exec_sigma (Inl (v, ctx)))))
         (fun_of_exec_dg_st_for gs (globs (exec_sigma (Inl (v, ctx)))))
     | Inr () \<Rightarrow> fun_of_dg_st_for gs (exec_sigma (Inr ())))"

lemma completed_sigma_abs_Inl:
  "completed_sigma_abs gs locations_of outside exec_sigma (Inl (v, ctx)) = DG
     (complete_abs_on gs (set (locations_of v)) (\<lambda>_. outside)
       (locals (exec_sigma (Inl (v, ctx)))))
     (fun_of_exec_dg_st_for gs (globs (exec_sigma (Inl (v, ctx)))))"
  by (simp add: completed_sigma_abs_def)

lemma completed_sigma_abs_Inr:
  "completed_sigma_abs gs locations_of outside exec_sigma (Inr ()) =
     fun_of_dg_st_for gs (exec_sigma (Inr ()))"
  by (simp add: completed_sigma_abs_def split: unit.split)

text \<open>
  The executable TD solution scoped-refines its own completed readback at
  every node, by construction of \<^const>\<open>complete_abs_on\<close>: an instance needs
  only the canonical-scope side condition (that every location its own
  \<open>locations_of\<close> lists resolves back to itself under \<open>gs\<close> --
  \<open>scope_locations_canonical\<close> discharges this whenever \<open>locations_of\<close>
  is a \<^const>\<open>scope_locations\<close> instance), not a fresh per-node argument.
\<close>

lemma dg_refines_on_completed_sigma_abs:
  fixes exec_sigma :: "pp \<times> 'c + unit \<Rightarrow>
    ('a::bounded_semilattice_sup_bot exec_dg_st, 'a exec_dg_st) dg_state"
  assumes canonical: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      location = location_of gs (location_vname location)"
  shows
    "dg_refines_on (set (locations_of v))
       (exec_sigma (Inl (v, ctx)))
       (completed_sigma_abs gs locations_of outside exec_sigma (Inl (v, ctx)))"
proof (rule dg_refines_onI)
  fix location assume loc: "location \<in> set (locations_of v)"
  show "lookup_resolved_st_q (locals (exec_sigma (Inl (v, ctx)))) location =
      locals (completed_sigma_abs gs locations_of outside exec_sigma (Inl (v, ctx)))
        (location_vname location)"
    using canonical[OF loc] loc
    by (simp add: completed_sigma_abs_Inl complete_abs_on_def
      fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)
next
  fix location assume loc: "location \<in> set (locations_of v)"
  show "lookup_resolved_st_q (globs (exec_sigma (Inl (v, ctx)))) location =
      globs (completed_sigma_abs gs locations_of outside exec_sigma (Inl (v, ctx)))
        (location_vname location)"
    using canonical[OF loc]
    by (simp add: completed_sigma_abs_Inl
      fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)
qed

text \<open>The side/global channel needs no completion at all: it scoped-refines
  over every canonical location, not just a node's own scope, since
  \<open>completed_sigma_abs\<close> reads it back plainly.\<close>

lemma dg_refines_on_completed_sigma_abs_side:
  fixes exec_sigma :: "pp \<times> 'c + unit \<Rightarrow>
    ('a::bounded_semilattice_sup_bot exec_dg_st, 'a exec_dg_st) dg_state"
  assumes canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (locals (exec_sigma (Inr ()))) location =
       locals (completed_sigma_abs gs locations_of outside exec_sigma (Inr ())) (location_vname location)"
    "lookup_resolved_st_q (globs (exec_sigma (Inr ()))) location =
       globs (completed_sigma_abs gs locations_of outside exec_sigma (Inr ())) (location_vname location)"
  using canonical
  by (simp_all add: completed_sigma_abs_Inr fun_of_dg_st_for_def
    fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)

subsection \<open>Executable unit (diagonal) step and combine\<close>

text \<open>
  Executable diagonal step and combine operations act on \<open>'a exec_dg_st\<close>.  Their proofs are
  domain-independent: any executable transfer that commutes through \<open>fun_of_exec_dg_st_for\<close> yields a
  commuting D/G step.
\<close>

definition unit_step_st ::
  "(('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st) \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_step_st f d g = (let res = f (combine_resolved_st_q d g) in (restrict_global_resolved_q res, restrict_local_resolved_q res))"

text \<open>Executable mirror of the abstract-side \<^const>\<open>unit_combine_step_env_for\<close>/
  \<^const>\<open>unit_combine_step_assign_for\<close> split.\<close>
definition unit_combine_step_st_env ::
  "('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_combine_step_st_env dc de g =
     (let m = combine_resolved_st_q dc g
      in (restrict_global_resolved_q m, restrict_local_resolved_q m))"

lemma unit_step_st_commute_for:
  assumes "\<And>s. fun_of_exec_dg_st_for gs (f_st s) = f_abs (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (unit_step_st f_st d g)
           = unit_step_for gs f_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  using assms
  unfolding fun_of_exec_dg_st_for_def
  by (simp add: unit_step_st_def unit_step_for_def restrict_local_for_def
                restrict_global_for_def fun_of_resolved_st_q_for_sup
                fun_of_resolved_st_q_for_restrict_local fun_of_resolved_st_q_for_restrict_global
                Let_def fun_eq_iff)




text \<open>Generic combine-assign: the destination write goes through
  \<^const>\<open>combine_assign_resolved_q\<close> at whatever classifier \<open>gs\<close> the caller's
  writes and reads already agree on.\<close>
definition unit_combine_step_st_assign_for ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_combine_step_st_assign_for gs dst de g merged =
     (let res = combine_assign_resolved_q gs dst
                  (lookup_resolved_st_q de (location_of gs ret_var))
                  (fst merged \<squnion> snd merged)
      in (restrict_global_resolved_q res, restrict_local_resolved_q res))"





text \<open>Generic diagonal executable D/G specification: the only classifier-dependent
  field is \<open>dgs_combine_assign\<close> -- \<^const>\<open>unit_combine_step_st_env\<close> already reads
  the local/global split off the incoming states' own location tags, needing no
  classifier of its own (cf.\ \<open>restrict_local_resolved_q\<close>/\<open>restrict_global_resolved_q\<close>).\<close>
definition unit_dg_spec_st_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (vname list \<Rightarrow> exp list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_spec"
where
  "unit_dg_spec_st_for gs tf_st enter_st = \<lparr>
    dgs_skip       = unit_step_st (tf_st EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_st (tf_st (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_st (tf_st (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_st (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
    dgs_body       = (\<lambda>p. unit_step_st (tf_st EA_Nop)),
    dgs_return     = (\<lambda>e p. unit_step_st (tf_st (EA_Ret e p I32))),
    dgs_enter      = (\<lambda>xs es. unit_step_st (enter_st xs es)),
    dgs_event      = (\<lambda>ev. case ev of Check_Event bc \<Rightarrow> unit_step_st (tf_st (EA_Check bc))),
    dgs_caller_cont    = (\<lambda>ci d g. d),
    dgs_combine_env    = (\<lambda>ci. unit_combine_step_st_env),
    dgs_combine_assign = (\<lambda>ci. unit_combine_step_st_assign_for gs (ci_dst ci))
  \<rparr>"

text \<open>
  Field-projection shape lemmas for \<^const>\<open>unit_dg_spec_st_for\<close>, classifier-parametric
  in \<open>gs\<close>: every field but \<open>dgs_combine_assign\<close> is a bare \<^const>\<open>unit_step_st\<close>
  application, so its \<open>fst\<close>/\<open>snd\<close> unfold to the global/local restriction of the underlying
  transfer with no further reasoning about \<open>gs\<close>. A caller reasoning about a concrete
  \<open>unit_dg_spec_st_for gs tf_st enter_st\<close> instance cites these instead of re-deriving the
  record/\<open>Let\<close> unfold at each site.\<close>

lemma fst_unit_step_st [simp]:
  "fst (unit_step_st f d g) = restrict_global_resolved_q (f (combine_resolved_st_q d g))"
  unfolding unit_step_st_def Let_def by simp

lemma snd_unit_step_st [simp]:
  "snd (unit_step_st f d g) = restrict_local_resolved_q (f (combine_resolved_st_q d g))"
  unfolding unit_step_st_def Let_def by simp

lemma fst_dgs_skip_for:
  "fst (dgs_skip (unit_dg_spec_st_for gs tf_st enter_st) d g)
     = restrict_global_resolved_q (tf_st EA_Nop (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_skip_for:
  "snd (dgs_skip (unit_dg_spec_st_for gs tf_st enter_st) d g)
     = restrict_local_resolved_q (tf_st EA_Nop (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_assign_for:
  "fst (dgs_assign (unit_dg_spec_st_for gs tf_st enter_st) x e d g)
     = restrict_global_resolved_q (tf_st (EA_Assign x e) (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_assign_for:
  "snd (dgs_assign (unit_dg_spec_st_for gs tf_st enter_st) x e d g)
     = restrict_local_resolved_q (tf_st (EA_Assign x e) (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_enter_for:
  "fst (dgs_enter (unit_dg_spec_st_for gs tf_st enter_st) xs es d g)
     = restrict_global_resolved_q (enter_st xs es (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_enter_for:
  "snd (dgs_enter (unit_dg_spec_st_for gs tf_st enter_st) xs es d g)
     = restrict_local_resolved_q (enter_st xs es (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

text \<open>The caller half of \<open>enter\<close> is the identity on a diagonal executable carrier:
  a \<^typ>\<open>'a exec_dg_st\<close> holds one tagged value per location and no relation
  between locations, so a call has nothing to invalidate in it.  It is a field
  like any other, and the correspondence theorem below covers it explicitly
  rather than leaving it as an unstated structural assumption.\<close>

lemma dgs_caller_cont_unit_dg_spec_st_for [simp]:
  "dgs_caller_cont (unit_dg_spec_st_for gs tf_st enter_st) ci d g = d"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_combine_env_for:
  "fst (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = restrict_global_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma snd_dgs_combine_env_for:
  "snd (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = restrict_local_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma fst_dgs_combine_assign_for:
  "fst (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) ci de g merged)
     = restrict_global_resolved_q (combine_assign_resolved_q gs (ci_dst ci)
         (lookup_resolved_st_q de (location_of gs ret_var)) (fst merged \<squnion> snd merged))"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_assign_for_def Let_def by simp

lemma snd_dgs_combine_assign_for:
  "snd (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) ci de g merged)
     = restrict_local_resolved_q (combine_assign_resolved_q gs (ci_dst ci)
         (lookup_resolved_st_q de (location_of gs ret_var)) (fst merged \<squnion> snd merged))"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_assign_for_def Let_def by simp

text \<open>Not \<open>[simp]\<close>: the whole-function shape competes with the pointwise
  \<open>fun_of_resolved_st_q_for_restrict_local\<close>/\<open>fun_of_resolved_st_q_for_restrict_global\<close>
  normal form other proofs already rely on. Cited explicitly where the
  whole-function shape is what's needed.\<close>
lemma fun_of_resolved_st_q_for_restrict_local_for:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_local_for_def fun_of_resolved_st_q_for_restrict_local)

lemma fun_of_resolved_st_q_for_restrict_global_for:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_global_for_def fun_of_resolved_st_q_for_restrict_global)

lemma unit_combine_step_st_commute_for:
  "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
       (dgs_combine (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = dgs_combine (unit_dg_spec_for gs tf) ci
         (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  unfolding dgs_combine_unit_dg_spec_for
  unfolding dgs_combine_def
    unit_dg_spec_st_for_def unit_combine_step_st_env_def unit_combine_step_st_assign_for_def
    fun_of_exec_dg_st_for_def
  by (simp add: Let_def combine_collect_abs_def fun_of_resolved_st_q_for_def
                fun_of_resolved_st_q_for_sup fun_of_resolved_st_q_for_restrict_local
                fun_of_resolved_st_q_for_restrict_global fun_of_resolved_st_q_for_combine
                fun_of_resolved_st_q_for_combine_assign combine_env_abs_for_eq_restrict
                fun_of_resolved_st_q_for_restrict_local_for
                fun_of_resolved_st_q_for_restrict_global_for ac_simps)


lemma dg_spec_step_unit_st_for:
  assumes reduces: "action_reduces tf_st"
  shows "dg_spec_step (unit_dg_spec_st_for gs tf_st enter_st) a = unit_step_st (tf_st a)"
proof -
  interpret action_reduces tf_st by (rule reduces)
  show ?thesis
  proof (cases a)
    case (EA_Ret e p rk)
    then show ?thesis
      unfolding unit_dg_spec_st_for_def
      by (cases e) (simp_all add: ret_none ret_some)
  qed (simp_all add: unit_dg_spec_st_for_def check)
qed

end
