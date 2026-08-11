section \<open>Executable transport for the native D/G spine\<close>

text \<open>
  The verified solver uses the executable association-list carrier \<open>'a exec_dg_st\<close>, while soundness
  is stated over function-valued abstract states.  \<open>fun_of_dg_st\<close> lifts the refinement
  morphism \<open>fun_of_exec_dg_st\<close> to the D/G product and commutes with equation evaluation.

  D/G lattice operations are componentwise, so the product inherits the order, join, bottom,
  equality, and widening operations required by the solver.
\<close>

theory Exec_DG_Bridge
  imports
    "Voblint_Core.DG_Soundness"
    "Voblint_Core.Exec_Bridge"
    "Voblint_Core.TD_Side_Eff_Keyed_Gen"
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
      transfer read_node write_node =
    QueryL read_node (\<lambda>local. QueryG () (\<lambda>side.
      let result = transfer (locals local \<squnion> globs side)
      in Side () (DG bot
          (project_abs_on (owner_of write_node) source_global publish_side result))
        (Answer (DG
          (project_abs_on (owner_of write_node) source_global keep_local result)
          bot))))"

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
   (vname list => aexp list =>
     ('a::bounded_semilattice_sup_bot) abs_state => 'a abs_state) =>
   vname list => aexp list => pp => pp =>
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
      combine destination caller callee write_node =
    QueryL caller (\<lambda>caller_state. QueryL callee (\<lambda>callee_state.
      QueryG () (\<lambda>side.
        let result = combine destination (locals caller_state)
          (locals callee_state) (globs side)
        in Side () (DG bot
            (project_abs_on (owner_of write_node) source_global publish_side result))
          (Answer (DG
            (project_abs_on (owner_of write_node) source_global keep_local result)
            bot)))))"

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
  "completed_sigma_abs gs locations_of outside exec_sigma key =
    (case key of
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
  domain-independent: any executable transfer that commutes through \<open>fun_of_exec_dg_st\<close> yields a
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
   \<Rightarrow> (vname list \<Rightarrow> aexp list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_spec"
where
  "unit_dg_spec_st_for gs tf_st enter_st = \<lparr>
    dgs_nop        = unit_step_st (tf_st EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_st (tf_st (EA_Assign x e))),
    dgs_random     = (\<lambda>x. unit_step_st (tf_st (EA_Random x))),
    dgs_assume     = (\<lambda>b. unit_step_st (tf_st (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. unit_step_st (tf_st (EA_AssumeNot b))),
    dgs_enter      = (\<lambda>xs es. unit_step_st (enter_st xs es)),
    dgs_combine_env    = unit_combine_step_st_env,
    dgs_combine_assign = unit_combine_step_st_assign_for gs
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

lemma fst_dgs_nop_for:
  "fst (dgs_nop (unit_dg_spec_st_for gs tf_st enter_st) d g)
     = restrict_global_resolved_q (tf_st EA_Nop (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_nop_for:
  "snd (dgs_nop (unit_dg_spec_st_for gs tf_st enter_st) d g)
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

lemma fst_dgs_combine_env_for:
  "fst (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) dc de g)
     = restrict_global_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma snd_dgs_combine_env_for:
  "snd (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) dc de g)
     = restrict_local_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma fst_dgs_combine_assign_for:
  "fst (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) dst de g merged)
     = restrict_global_resolved_q (combine_assign_resolved_q gs dst
         (lookup_resolved_st_q de (location_of gs ret_var)) (fst merged \<squnion> snd merged))"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_assign_for_def Let_def by simp

lemma snd_dgs_combine_assign_for:
  "snd (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) dst de g merged)
     = restrict_local_resolved_q (combine_assign_resolved_q gs dst
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
       (dgs_combine (unit_dg_spec_st_for gs tf_st enter_st) dst dc de g)
     = dgs_combine (unit_dg_spec_for gs tf) dst
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
    unfolding unit_dg_spec_st_for_def
    by (cases a) (simp_all add: ret_none ret_some check split: option.splits)
qed

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
      transfer read_node write_node =
    QueryL read_node (\<lambda>local. QueryG () (\<lambda>side.
      let result = transfer (locals local \<squnion> globs side)
      in Side () (DG bot
          (proj (owner_of write_node) (locations_of write_node)
            publish_side result))
        (Answer (DG
          (proj (owner_of write_node) (locations_of write_node)
            keep_local result) bot))))"

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
   (vname list => aexp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   vname list => aexp list => pp => pp =>
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
   (vname list => aexp list =>
     ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st) =>
   vname list => aexp list => pp => pp =>
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
    "vname list => aexp list =>
      ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_enter ::
      "vname list => aexp list => 'a abs_state => 'a abs_state"
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
    "vname list => aexp list =>
      ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and abstract_enter ::
      "vname list => aexp list => 'a abs_state => 'a abs_state"
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
      combine destination caller callee write_node =
    QueryL caller (\<lambda>caller_state. QueryL callee (\<lambda>callee_state.
      QueryG () (\<lambda>side.
        let result = combine destination (locals caller_state)
          (locals callee_state) (globs side)
        in Side () (DG bot
            (proj (owner_of write_node)
              (locations_of write_node) publish_side result))
          (Answer (DG
            (proj (owner_of write_node)
              (locations_of write_node) keep_local result) bot)))))"

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
  fixes enter :: "vname list => aexp list =>
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
  fixes enter :: "vname list => aexp list =>
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
   (vname list => aexp list =>
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
   (vname list => aexp list => 'a exec_dg_st => 'a exec_dg_st) =>
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
   (vname list => aexp list =>
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
   (vname list => aexp list => 'a exec_dg_st => 'a exec_dg_st) =>
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
   (vname list \<Rightarrow> aexp list \<Rightarrow>
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
   (vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow>
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

subsection \<open>The executable D/G equation generator\<close>

text \<open>
  The executable generator is the same polymorphic seeded keyed generator
  (\<open>side_cfg_T_eff_keyed_seed_dg\<close>) the abstract \<open>sound_dg_spec.dg_gen\<close> uses,
  instantiated at an \<open>'a exec_dg_st\<close>-valued analysis spec.  Unit context (\<open>gkey = (\<lambda>_. ())\<close>),
  no procedure-entry seed (\<open>frame_seed = (\<lambda>_. bot)\<close>).
\<close>

definition dg_cmb_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree"
where
  "dg_cmb_of S route ctx ca cc ex =
     (case ca of CallEdge dst _ _ \<Rightarrow>
       map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx)) (dg_spec_combine_tree S dst cc ex)))"

definition dg_extra_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg
     \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) strategy_tree list"
where
  "dg_extra_of S g route ctx v =
     map (\<lambda>(cl, ca). case ca of CallEdge dst fs as \<Rightarrow>
       map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx))
         (dg_edge_tree (dgs_enter S fs as) cl))) (entry_call_list g v)"

definition dg_gen_of ::
  "(('d::bounded_semilattice_sup_bot), ('h::bounded_semilattice_sup_bot)) dg_spec \<Rightarrow> cfg \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'h
     \<Rightarrow> (pp \<times> unit, unit, ('d, 'h) dg_state) eqsT"
where
  "dg_gen_of S g bot0 s0d s0g =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ())
       (\<lambda>_ _ _ _. ()) (dg_cmb_of S) (dg_extra_of S g) g S bot0 s0d s0g"

subsection \<open>Side-effect commutation for the generator\<close>

lemma sides_of_rhs_Inl_bot: "sides_of_rhs t \<sigma> (Inl a) = bot"
  by (induction t arbitrary: \<sigma>) (auto simp: Let_def)

subsection \<open>Generic \<open>se_constraint_holds\<close> builders\<close>

text \<open>
  The most important missing abstraction is assembling a node's
  \<open>se_constraint_holds\<close> obligation for the abstract, hook-generated equation
  system from a scoped \<^const>\<open>dg_refines_on\<close> fact -- itself already produced
  by composing the item-1 hook-wrapper equations, the item-2
  singleton-generator reductions, and a domain transfer-agreement lemma.
  \<open>outside\<close> is deliberately an arbitrary bound (as in
  \<open>le_lift_if_dg_refines_on_and_le\<close>) rather than a fixed top element, so no
  domain has to supply one it does not have; an instance's own completed
  sigma (\<^const>\<open>completed_sigma_abs\<close>) unfolds \<open>complete_abs_on\<close>/
  \<open>fun_of_exec_dg_st_for\<close> back to whatever concrete bound it fixed.
\<close>

lemma complete_abs_on_bot_le_fun_of_exec_dg_st_for:
  fixes exec_bound :: "'a::order_bot exec_dg_st" and universe :: "location set"
  shows "complete_abs_on gs universe (\<lambda>_. bot) exec_bound \<le> fun_of_exec_dg_st_for gs exec_bound"
  by (rule le_funI) (simp add: complete_abs_on_def fun_of_exec_dg_st_for_def)

lemma local_bound_of_dg_refines:
  fixes v :: pp
    and exec_local :: "'a::bounded_semilattice_sup_bot exec_dg_st"
    and abs_local :: "'a abs_state"
  assumes exec_le: "exec_local \<le> exec_bound"
    and dg_ref: "dg_refines_on (set (locations_of v))
        (DG exec_local exec_side) (DG abs_local abs_side)"
    and outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
        abs_local x \<le> outside x"
  shows "abs_local \<le> complete_abs_on gs (set (locations_of v)) outside exec_bound"
proof -
  have refines: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q exec_local location = abs_local (location_vname location)"
    using dg_refines_onD_local[OF dg_ref] by simp
  show ?thesis
    by (rule le_lift_if_dg_refines_on_and_le[OF refines outside_le exec_le])
qed

lemma side_bound_of_dg_refines:
  fixes v :: pp
    and exec_side :: "'a::bounded_semilattice_sup_bot exec_dg_st"
    and abs_side :: "'a abs_state"
  assumes dg_ref_side: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q exec_side location = abs_side (location_vname location)"
    and outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
        abs_side x \<le> bot"
    and le: "exec_side \<le> exec_bound"
  shows "abs_side \<le> fun_of_exec_dg_st_for gs exec_bound"
proof -
  have lifted: "abs_side \<le> complete_abs_on gs (set (locations_of v)) (\<lambda>_. bot) exec_bound"
    by (rule le_lift_if_dg_refines_on_and_le[OF dg_ref_side outside_le le])
  show ?thesis
    using order_trans[OF lifted complete_abs_on_bot_le_fun_of_exec_dg_st_for] .
qed

text \<open>Bundling the two halves of \<open>se_constraint_holds\<close> at a node: the local
  bound and the side bound above, plus the structural fact just proved
  (\<open>sides_of_rhs_Inl_bot\<close>) that side effects at a node never touch \<open>Inl\<close>
  keys.\<close>

lemma se_constraint_holds_of_dg_refines:
  fixes v_key :: 'k
    and abs_local_val :: "'a::bounded_semilattice_sup_bot abs_state"
    and abs_side_val :: "'a abs_state"
  assumes local_le: "abs_local_val \<le> locals (sigma (Inl v_key))"
    and side_le: "abs_side_val \<le> globs (sigma (Inr ()))"
    and traverse_locals: "locals traverse_val = abs_local_val"
    and traverse_globs_bot: "globs traverse_val = bot"
    and sides_val_Inl_bot: "\<And>x. sides_val (Inl x) = bot"
    and sides_locals_bot: "locals (sides_val (Inr ())) = bot"
    and sides_globs: "globs (sides_val (Inr ())) = abs_side_val"
  shows "traverse_val \<le> sigma (Inl v_key) \<and> sides_val \<le> sigma"
proof (intro conjI le_funI)
  show "traverse_val \<le> sigma (Inl v_key)"
    unfolding less_eq_dg_state_def
    using local_le traverse_locals traverse_globs_bot by simp
next
  fix k show "sides_val k \<le> sigma k"
  proof (cases k)
    case (Inl x)    then show ?thesis
      by (simp add: sides_val_Inl_bot less_eq_dg_state_def bot_dg_state_def)
  next
    case (Inr y)
    then show ?thesis
      using side_le sides_locals_bot sides_globs by (simp add: less_eq_dg_state_def)
  qed
qed

subsection \<open>Generic per-node post-solution transport\<close>

text \<open>
  \<open>placed_hook_se_edge\<close> fuses what an instance would otherwise prove in two
  steps -- a \<^const>\<open>dg_refines_on\<close> bridge from a raw transfer-agreement
  hypothesis, then \<open>se_constraint_holds_of_dg_refines\<close> -- into one
  call, generic over the CFG, the placement policy, and the domain.
  \<^const>\<open>placed_dg_gen_of_strict\<close> and \<^const>\<open>placed_abs_dg_gen_of\<close> are
  unfolded internally at the single-incoming-edge/no-calls node shape, so no
  instance needs its own single-edge reduction lemma.
  \<^const>\<open>completed_sigma_abs\<close> is fixed as the abstract valuation, so the
  outside-scope bound at every node comes from \<^const>\<open>complete_abs_on\<close>
  instead of being re-derived per instance.
\<close>

lemma placed_hook_se_edge:
  fixes gs :: "vname => bool"
    and owner_of :: "pp => pname"
    and locations_of :: "pp => location list"
    and keep_local publish_side :: "scoped_location => bool"
    and transfer_st :: "edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and transfer_abs :: "edge_action => 'a abs_state => 'a abs_state"
    and enter_st :: "vname list => aexp list => 'a exec_dg_st => 'a exec_dg_st"
    and enter_abs :: "vname list => aexp list => 'a abs_state => 'a abs_state"
    and g :: cfg and bot0 :: "'a exec_dg_st" and s0d s0g :: "'a exec_dg_st"
    and bot0_abs :: "'a abs_state" and s0d_abs s0g_abs :: "'a abs_state" and top_val :: 'a
    and sigma_exec :: "pp \<times> unit + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
    and v u :: pp and a :: edge_action
  defines "sigma_abs \<equiv> completed_sigma_abs gs locations_of top_val sigma_exec"
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "intra_predecessor_list g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0_eq: "bot0 = bot" and bot0_abs_eq: "bot0_abs = bot"
    and top_ge: "\<And>y. y \<le> top_val"
    and se: "se_constraint_holds
      (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (v, ())"
    and canonical: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      location = location_of gs (location_vname location)"
    and raw: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)) location =
      transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs) (location_vname location)"
    and side_outside_raw: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      publish_side (owner_of v, location_of gs x) \<longrightarrow>
      transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs) x \<le> bot"
  shows "se_constraint_holds
    (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
      bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (v, ())"
proof -
  have exec_eq: "eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec =
      DG (project_resolved_on_strict (owner_of v) (locations_of v) keep_local
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec))) bot"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: not_entry pred no_combine no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      traverse_rhs_placed_dg_edge_of_strict dg_hook_D_def dg_hook_G_def)
  have exec_sides: "sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()) =
      DG bot (project_resolved_on_strict (owner_of v) (locations_of v) publish_side
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)))"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: not_entry pred no_combine no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      sides_of_rhs_placed_dg_edge_of_strict dg_hook_D_def dg_hook_G_def)
  have abs_eq: "eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs =
      DG (project_abs_on (owner_of v) gs keep_local
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs))) bot"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: not_entry pred no_combine no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      traverse_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def)
  have abs_sides: "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()) =
      DG bot (project_abs_on (owner_of v) gs publish_side
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)))"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: not_entry pred no_combine no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
      sides_of_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def)
  have bridge: "dg_refines_on (set (locations_of v))
      (DG (project_resolved_on_strict (owner_of v) (locations_of v) keep_local
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)))
        (project_resolved_on_strict (owner_of v) (locations_of v) publish_side
            (transfer_st a (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec))))
      (DG (project_abs_on (owner_of v) gs keep_local
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)))
        (project_abs_on (owner_of v) gs publish_side
            (transfer_abs a (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs))))"
    by (rule dg_refines_on_project_strict[OF raw canonical])
  have dg_ref: "dg_refines_on (set (locations_of v))
      (DG (locals (eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
              transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec))
        (globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
              transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()))))
      (DG (locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
              bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs))
        (globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
              bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()))))"
    using bridge by (simp add: exec_eq exec_sides abs_eq abs_sides)
  have exec_le: "locals (eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (v, ()) sigma_exec) \<le>
      locals (sigma_exec (Inl (v, ())))"
    using se_constraint_holds_local[OF se] by (simp add: less_eq_dg_state_def)
  have exec_side_le: "globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ())) \<le>
      globs (sigma_exec (Inr ()))"
    using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  have outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) x \<le> top_val"
    by (simp add: abs_eq project_abs_on_def project_component_def top_ge)
  have local_le: "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) \<le> locals (sigma_abs (Inl (v, ())))"
    using local_bound_of_dg_refines[
        where locations_of = locations_of and outside = "\<lambda>_. top_val",
        OF exec_le dg_ref outside_le]
    by (simp add: sigma_abs_def completed_sigma_abs_Inl)
  have side_outside_le: "\<And>x. location_of gs x \<notin> set (locations_of v) \<Longrightarrow>
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) x \<le> bot"
    by (simp add: abs_sides project_abs_on_def project_component_def side_outside_raw)
  have dg_ref_side: "\<And>location. location \<in> set (locations_of v) \<Longrightarrow>
      lookup_resolved_st_q (globs (sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
          transfer_st enter_st g bot0 s0d s0g (v, ())) sigma_exec (Inr ()))) location =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
          bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) (location_vname location)"
    using dg_refines_onD_side[OF dg_ref] by simp
  have side_le: "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
    using side_bound_of_dg_refines[OF dg_ref_side side_outside_le exec_side_le]
    by (simp add: sigma_abs_def completed_sigma_abs_Inr)
  show ?thesis
    unfolding se_constraint_holds_def
  proof (rule se_constraint_holds_of_dg_refines)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) \<le> locals (sigma_abs (Inl (v, ())))"
      by (rule local_le)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
      by (rule side_le)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) =
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs)"
      by (rule refl)
    show "globs (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (v, ()) sigma_abs) = bot"
      by (simp add: abs_eq)
    fix x show "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inl x) = bot"
      by (simp add: sides_of_rhs_Inl_bot)
  next
    show "locals (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) = bot"
      by (simp add: abs_sides)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ())) =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (v, ())) sigma_abs (Inr ()))"
      by (rule refl)
  qed
qed

text \<open>
  \<open>placed_hook_se_entry\<close> is the entry-node counterpart of \<open>placed_hook_se_edge\<close>:
  the seed values \<open>s0d\<close>/\<open>s0g\<close> take the place of a predecessor's traversal
  value, so the obligation is a direct agreement between the two seeds
  instead of a per-edge transfer-agreement hypothesis.
\<close>

lemma placed_hook_se_entry:
  fixes gs :: "vname => bool"
    and owner_of :: "pp => pname"
    and locations_of :: "pp => location list"
    and keep_local publish_side :: "scoped_location => bool"
    and transfer_st :: "edge_action => ('a::bounded_semilattice_sup_bot) exec_dg_st => 'a exec_dg_st"
    and transfer_abs :: "edge_action => 'a abs_state => 'a abs_state"
    and enter_st :: "vname list => aexp list => 'a exec_dg_st => 'a exec_dg_st"
    and enter_abs :: "vname list => aexp list => 'a abs_state => 'a abs_state"
    and g :: cfg and bot0 :: "'a exec_dg_st" and s0d s0g :: "'a exec_dg_st"
    and bot0_abs :: "'a abs_state" and s0d_abs s0g_abs :: "'a abs_state" and top_val :: 'a
    and sigma_exec :: "pp \<times> unit + unit => ('a exec_dg_st, 'a exec_dg_st) dg_state"
  defines "sigma_abs \<equiv> completed_sigma_abs gs locations_of top_val sigma_exec"
  assumes entry_no_edge: "intra_predecessor_list g (cfg_entry g) = []"
    and entry_no_combine: "return_call_action_list g (cfg_entry g) = []"
    and entry_no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0_eq: "bot0 = bot" and bot0_abs_eq: "bot0_abs = bot"
    and top_ge: "\<And>y. y \<le> top_val"
    and se: "se_constraint_holds
      (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (cfg_entry g, ())) sigma_exec (cfg_entry g, ())"
    and local_raw: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
      lookup_resolved_st_q s0d location = s0d_abs (location_vname location)"
    and side_raw: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
      lookup_resolved_st_q s0g location = s0g_abs (location_vname location)"
    and side_outside_raw: "\<And>x. location_of gs x \<notin> set (locations_of (cfg_entry g)) \<Longrightarrow>
      s0g_abs x \<le> bot"
  shows "se_constraint_holds
    (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
      bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (cfg_entry g, ())"
proof -
  have exec_eq: "eq (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g) (cfg_entry g, ()) sigma_exec = DG s0d bot"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have exec_sides: "sides_of_rhs (placed_dg_gen_of_strict gs owner_of locations_of keep_local publish_side
        transfer_st enter_st g bot0 s0d s0g (cfg_entry g, ())) sigma_exec (Inr ()) = DG bot s0g"
    unfolding placed_dg_gen_of_strict_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have abs_eq: "eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs = DG s0d_abs bot"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have abs_sides: "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ()) = DG bot s0g_abs"
    unfolding placed_abs_dg_gen_of_def
    by (simp add: entry_no_edge entry_no_combine entry_no_enter bot0_abs_eq
      side_cfg_T_eff_keyed_seed_trees_def Let_def)
  have local_le: "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) \<le> locals (sigma_abs (Inl (cfg_entry g, ())))"
  proof -
    have exec_le: "s0d \<le> locals (sigma_exec (Inl (cfg_entry g, ())))"
      using se_constraint_holds_local[OF se] by (simp add: exec_eq less_eq_dg_state_def)
    have refines: "\<And>location. location \<in> set (locations_of (cfg_entry g)) \<Longrightarrow>
        lookup_resolved_st_q s0d location = s0d_abs (location_vname location)"
      by (rule local_raw)
    have outside: "\<And>x. location_of gs x \<notin> set (locations_of (cfg_entry g)) \<Longrightarrow> s0d_abs x \<le> top_val"
      by (simp add: top_ge)
    have lifted: "s0d_abs \<le> complete_abs_on gs (set (locations_of (cfg_entry g))) (\<lambda>_. top_val)
        (locals (sigma_exec (Inl (cfg_entry g, ()))))"
      by (rule le_lift_if_dg_refines_on_and_le[
          where gs = gs and universe = "set (locations_of (cfg_entry g))" and outside = "\<lambda>_. top_val",
          OF refines outside exec_le])
    show ?thesis
      unfolding abs_eq
      by (simp add: sigma_abs_def completed_sigma_abs_Inl lifted)
  qed
  have side_le: "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
  proof -
    have exec_le: "s0g \<le> globs (sigma_exec (Inr ()))"
      using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
      by (simp add: exec_sides less_eq_dg_state_def)
    have lifted: "s0g_abs \<le> fun_of_exec_dg_st_for gs (globs (sigma_exec (Inr ())))"
      by (rule side_bound_of_dg_refines[
          where locations_of = locations_of and v = "cfg_entry g" and gs = gs,
          OF side_raw side_outside_raw exec_le])
    show ?thesis
      unfolding abs_sides
      by (simp add: sigma_abs_def completed_sigma_abs_Inr lifted)
  qed
  show ?thesis
    unfolding se_constraint_holds_def
  proof (rule se_constraint_holds_of_dg_refines)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) \<le> locals (sigma_abs (Inl (cfg_entry g, ())))"
      by (rule local_le)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) \<le> globs (sigma_abs (Inr ()))"
      by (rule side_le)
    show "locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) =
      locals (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs)"
      by (rule refl)
    show "globs (eq (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs) (cfg_entry g, ()) sigma_abs) = bot"
      by (simp add: abs_eq)
    fix x show "sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inl x) = bot"
      by (simp add: sides_of_rhs_Inl_bot)
  next
    show "locals (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) = bot"
      by (simp add: abs_sides)
    show "globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ())) =
      globs (sides_of_rhs (placed_abs_dg_gen_of gs owner_of keep_local publish_side transfer_abs enter_abs g
        bot0_abs s0d_abs s0g_abs (cfg_entry g, ())) sigma_abs (Inr ()))"
      by (rule refl)
  qed
qed



lemma sides_dg_edge_tree_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (dg_edge_tree step_st u) \<tau>_st k)
       = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (step_abs (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl u)))) (fun_of_exec_dg_st_for gs (globs (\<tau>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (fst (step_st (locals (\<tau>_st (Inl u))) (globs (\<tau>_st (Inr ())))))"
    using H[of "locals (\<tau>_st (Inl u))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_edge_tree_Inr fun_of_dg_st_for_def fun_of_resolved_st_q_for_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: sides_dg_edge_tree_Inl fun_of_dg_st_for_bot)
qed


lemma sides_dg_combine_tree_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (dg_combine_tree comb_st dst cc ex) \<tau>_st k)
       = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> \<tau>_st) k"
proof (cases k)
  case (Inr b)
  have hg: "fst (comb_abs dst (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl cc)))) (fun_of_exec_dg_st_for gs (locals (\<tau>_st (Inl ex)))) (fun_of_exec_dg_st_for gs (globs (\<tau>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (fst (comb_st dst (locals (\<tau>_st (Inl cc))) (locals (\<tau>_st (Inl ex))) (globs (\<tau>_st (Inr ())))))"
    using H[of dst "locals (\<tau>_st (Inl cc))" "locals (\<tau>_st (Inl ex))" "globs (\<tau>_st (Inr ()))"]
    by (metis map_prod_simp fst_conv surj_pair)
  show ?thesis using Inr
    by (simp add: sides_dg_combine_tree_Inr fun_of_dg_st_for_def fun_of_resolved_st_q_for_bot hg o_def flip: bot_fun_def)
next
  case (Inl a)
  show ?thesis using Inl
    by (simp add: dg_combine_tree_def fun_of_dg_st_for_bot)
qed

lemma sides_wrap_reduce:
  "sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk t)) \<sigma> (Inr gk)
     = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum lk (\<lambda>_. gk) z)) (Inr ())"
  apply (subst sides_map_gtree_unit[where r="\<lambda>_. gk", simplified])
  apply (subst sides_map_ltree_Inr)
  apply (simp add: sum.map_comp o_def)
  done


lemma sides_wrapped_edge_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_for_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_for gs (sides_of_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_edge_tree_commute_for)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_for_bot)
  qed
qed


lemma sides_wrapped_combine_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st k)
       = sides_of_rhs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl a)
  show ?thesis by (simp add: Inl sides_of_rhs_Inl_bot fun_of_dg_st_for_bot)
next
  case (Inr b)
  show ?thesis
  proof (cases "b = gk")
    case True
    have "fun_of_dg_st_for gs (sides_of_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z)) (Inr ()))
        = sides_of_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk (\<lambda>_. gk) z))) (Inr ())"
      using H by (rule sides_dg_combine_tree_commute_for)
    thus ?thesis by (simp add: Inr True sides_wrap_reduce o_def)
  next
    case False
    hence nb: "b \<notin> range (\<lambda>_::unit. gk)" by simp
    show ?thesis by (simp add: Inr sides_map_gtree_off[OF nb] fun_of_dg_st_for_bot)
  qed
qed


subsection \<open>Dependency commutation for the generator\<close>

text \<open>
  The generator trees are non-branching (\<open>QueryL\<close> then \<open>QueryG\<close> then \<open>Answer\<close>/\<open>Side\<close>),
  so the queried-unknown set is structural: independent of the analysis step values and
  the valuation.  Hence dependencies transport verbatim.
\<close>

lemma dep_aux_dg_edge_tree: "dep_aux \<sigma> (dg_edge_tree step u) = {Inl u, Inr ()}"
  by (simp add: dg_edge_tree_def dep_aux_def)

lemma dep_aux_dg_combine_tree: "dep_aux \<sigma> (dg_combine_tree comb dst cc ex) = {Inl cc, Inl ex, Inr ()}"
  by (auto simp: dg_combine_tree_def dep_aux_def)

lemma dep_aux_Side: "dep_aux \<sigma> (Side y d t) = dep_aux \<sigma> t"
  by (simp add: dep_aux_def)

lemma dep_aux_map_gtree:
  "dep_aux \<sigma> (map_gtree r t) = map_sum id r ` dep_aux (\<lambda>z. \<sigma> (map_sum id r z)) t"
  by (induction t arbitrary: \<sigma>) (auto simp: dep_aux_def)

lemma dep_aux_wrapped_edge_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_edge_tree)

lemma dep_aux_wrapped_combine_eq:
  "dep_aux \<sigma>_st (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_st dst cc ex)))
     = dep_aux \<sigma>_abs (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_combine_tree comb_abs dst cc ex)))"
  by (simp add: dep_aux_map_gtree dep_aux_map_ltree dep_aux_dg_combine_tree)

lemma dep_aux_side_rhs_fold_dg_commute:
  assumes "list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs) ts_st ts_abs"
  shows "dep_aux \<sigma>_st (side_rhs_fold_dg acc_st ts_st) = dep_aux \<sigma>_abs (side_rhs_fold_dg acc_abs ts_abs)"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: dep_aux_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hd: "dep_aux \<sigma>_st t_st = dep_aux \<sigma>_abs t_abs" using Cons.hyps(1) by simp
  have ih: "dep_aux \<sigma>_st (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st)
          = dep_aux \<sigma>_abs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) ts_abs)"
    by (rule Cons.IH)
  show ?case by (simp add: dep_aux_seqcomp hd ih)
qed

subsection \<open>Classifier-parametric fold transport\<close>

text \<open>
  Fold-commute lemmas reading through the generic \<open>fun_of_exec_dg_st_for gs\<close>/
  \<open>fun_of_dg_st_for gs\<close> readback.  \<open>dep_aux_side_rhs_fold_dg_commute\<close> already
  never mentions a readback, so it transports unchanged.
\<close>

lemma side_acc_dg_commute_for:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))
           ts_st ts_abs"
  shows "fun_of_exec_dg_st_for gs (side_acc_dg acc_st \<sigma>_st ts_st)
           = side_acc_dg (fun_of_exec_dg_st_for gs acc_st) (fun_of_dg_st_for gs \<circ> \<sigma>_st) ts_abs"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st rule: list_all2_induct)
  case Nil
  thus ?case by simp
next
  case (Cons t_st ts_st t_abs ts_abs)
  have hl: "fun_of_exec_dg_st_for gs (locals (traverse_rhs t_st \<sigma>_st))
              = locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))"
    using Cons.hyps(1) by (metis fun_of_dg_st_for_simps(1))
  have h: "fun_of_exec_dg_st_for gs (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st))
           = fun_of_exec_dg_st_for gs acc_st \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))"
    unfolding fun_of_exec_dg_st_for_def
    by (simp add: fun_of_resolved_st_q_for_sup hl[unfolded fun_of_exec_dg_st_for_def])
  show ?case
    by (metis (no_types, lifting) Cons.IH h side_acc_dg.simps(2))
qed

lemma sides_side_rhs_fold_dg_commute_for:
  assumes "list_all2 (\<lambda>t_st t_abs.
             fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k))
           ts_st ts_abs"
  shows "fun_of_dg_st_for gs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st k)
           = sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
  using assms
proof (induction ts_st ts_abs arbitrary: acc_st acc_abs rule: list_all2_induct)
  case Nil
  thus ?case by (simp add: fun_of_dg_st_for_bot bot_fun_def)
next
  case (Cons t_st ts_st t_abs ts_abs)
  have sd: "fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
    using Cons.hyps(1) by simp
  have ih: "fun_of_dg_st_for gs (sides_of_rhs (side_rhs_fold_dg (acc_st \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st k)
          = sides_of_rhs (side_rhs_fold_dg (acc_abs \<squnion> locals (traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))) ts_abs) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp fun_of_dg_st_for_sup sd ih comp_def)
qed

subsection \<open>Scoped fold transport\<close>

text \<open>
  Scoped counterparts of \<open>side_acc_dg_commute_for\<close> and
  \<open>sides_side_rhs_fold_dg_commute_for\<close>: instead of full \<open>fun_of_dg_st_for\<close>
  equality per tree, each tree's output need only \<^const>\<open>dg_refines_on\<close> a finite
  scope.  \<^const>\<open>dg_refines_on\<close> is closed under \<open>\<squnion>\<close> (\<open>dg_refines_on_sup\<close>) and holds
  trivially at \<open>bot\<close> (\<open>dg_refines_on_bot\<close>), so the fold argument is the same
  induction as the classifier-parametric version, just carried through
  \<open>dg_refines_on\<close> instead of equality.  Locals and sides are wrapped as
  \<open>DG _ bot\<close> / \<open>DG bot _\<close> so \<^const>\<open>dg_refines_on\<close>'s own locals/globs pairing
  can be reused unchanged.
\<close>

lemma bot_abs_state_apply [simp]:
  "(bot :: ('a::bot) abs_state) x = bot"
  by (simp add: bot_fun_def)

text \<open>
  Proved pointwise: \<open>lookup_resolved_st_q ... loc :: 'a\<close> and \<open>abs_val x :: 'a\<close> are
  both scalar, so the induction never touches a function-typed \<open>bot\<close> as a whole
  value --- the earlier attempt through \<^const>\<open>dg_refines_on\<close>'s \<open>DG _ bot\<close>
  wrapping kept producing syntactically different (though equal) eta-forms of
  \<open>bot :: 'a abs_state\<close> that \<open>simp\<close> would not always bridge.  The DG-wrapped
  \<^const>\<open>dg_refines_on\<close> statements below are recovered as thin corollaries of
  the pointwise facts.
\<close>

lemma side_acc_dg_lookup_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc))
           ts_st ts_abs"
    and acc_refines: "\<forall>loc\<in>universe. lookup_resolved_st_q acc_st loc = acc_abs (location_vname loc)"
  shows "\<forall>loc\<in>universe. lookup_resolved_st_q (side_acc_dg acc_st \<sigma>_st ts_st) loc =
      side_acc_dg acc_abs \<sigma>_abs ts_abs (location_vname loc)"
proof -
  have general: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc))
           ts_st ts_abs \<Longrightarrow>
      (\<forall>loc\<in>universe. lookup_resolved_st_q p loc = q (location_vname loc)) \<Longrightarrow>
      (\<forall>loc\<in>universe. lookup_resolved_st_q (side_acc_dg p \<sigma>_st ts_st) loc =
        side_acc_dg q \<sigma>_abs ts_abs (location_vname loc))"
    for p q ts_st ts_abs
  proof (induction ts_st ts_abs arbitrary: p q rule: list_all2_induct)
    case Nil
    thus ?case by simp
  next
    case (Cons t_st ts_st t_abs ts_abs)
    have hd: "\<forall>loc\<in>universe. lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) loc =
        locals (traverse_rhs t_abs \<sigma>_abs) (location_vname loc)"
      using Cons.hyps(1) by simp
    have step: "\<forall>loc\<in>universe. lookup_resolved_st_q (p \<squnion> locals (traverse_rhs t_st \<sigma>_st)) loc =
        (q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) (location_vname loc)"
      using Cons.prems hd by (simp add: sup_fun_def)
    show ?case
      using Cons.IH[where p = "p \<squnion> locals (traverse_rhs t_st \<sigma>_st)"
        and q = "q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)", OF step]
      by (metis side_acc_dg.simps(2))
  qed
  show ?thesis using list_refines acc_refines by (rule general)
qed

lemma side_acc_dg_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. dg_refines_on universe
             (DG (locals (traverse_rhs t_st \<sigma>_st)) bot)
             (DG (locals (traverse_rhs t_abs \<sigma>_abs)) bot))
           ts_st ts_abs"
    and acc_refines: "dg_refines_on universe (DG acc_st bot) (DG acc_abs bot)"
  shows "dg_refines_on universe
    (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)
    (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot)"
proof (rule dg_refines_onI)
  fix location assume loc: "location \<in> universe"
  have lr: "list_all2 (\<lambda>t_st t_abs. \<forall>l\<in>universe.
             lookup_resolved_st_q (locals (traverse_rhs t_st \<sigma>_st)) l =
             locals (traverse_rhs t_abs \<sigma>_abs) (location_vname l)) ts_st ts_abs"
    using list_refines by (rule list_all2_mono) (fastforce dest: dg_refines_onD_local)
  have ar: "\<forall>l\<in>universe. lookup_resolved_st_q acc_st l = acc_abs (location_vname l)"
    using acc_refines by (fastforce dest: dg_refines_onD_local)
  have combined: "\<forall>l\<in>universe. lookup_resolved_st_q (side_acc_dg acc_st \<sigma>_st ts_st) l =
      side_acc_dg acc_abs \<sigma>_abs ts_abs (location_vname l)"
    using ar lr side_acc_dg_lookup_refines_on by blast
  show "lookup_resolved_st_q (locals (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)) location =
      locals (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot) (location_vname location)"
    using combined loc by simp
next
  fix location assume "location \<in> universe"
  show "lookup_resolved_st_q (globs (DG (side_acc_dg acc_st \<sigma>_st ts_st) bot)) location =
      globs (DG (side_acc_dg acc_abs \<sigma>_abs ts_abs) bot) (location_vname location)"
    by simp
qed

lemma sides_side_rhs_fold_dg_lookup_refines_on:
  assumes sides_refines: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc))
           ts_st ts_abs"
  shows "\<forall>loc\<in>universe.
      lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))) loc =
      globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())) (location_vname loc)"
proof -
  have general: "list_all2 (\<lambda>t_st t_abs. \<forall>loc\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc))
           ts_st ts_abs \<Longrightarrow>
      (\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg p ts_st) \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs (side_rhs_fold_dg q ts_abs) \<sigma>_abs (Inr ())) (location_vname loc))"
    for p q ts_st ts_abs
  proof (induction ts_st ts_abs arbitrary: p q rule: list_all2_induct)
    case Nil
    thus ?case by (simp add: bot_dg_state_def) 
  next
    case (Cons t_st ts_st t_abs ts_abs)
    have sd: "\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname loc)"
      using Cons.hyps(1) by simp
    have ih: "\<forall>loc\<in>universe.
        lookup_resolved_st_q (globs (sides_of_rhs
          (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t_st \<sigma>_st)) ts_st) \<sigma>_st (Inr ()))) loc =
        globs (sides_of_rhs
          (side_rhs_fold_dg (q \<squnion> locals (traverse_rhs t_abs \<sigma>_abs)) ts_abs) \<sigma>_abs (Inr ()))
          (location_vname loc)"
      by (rule Cons.IH)
    show ?case
      using sd ih
      by (simp add: sides_of_rhs_seqcomp sup_dg_state_def sup_fun_def)
  qed
  show ?thesis using sides_refines by (rule general)
qed

lemma sides_side_rhs_fold_dg_refines_on:
  assumes list_refines: "list_all2 (\<lambda>t_st t_abs. dg_refines_on universe
             (DG (locals (traverse_rhs t_st \<sigma>_st)) bot)
             (DG (locals (traverse_rhs t_abs \<sigma>_abs)) bot)
           \<and> dg_refines_on universe
             (DG bot (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))))
             (DG bot (globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())))))
           ts_st ts_abs"
  shows "dg_refines_on universe
    (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))
    (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ()))))"
proof (rule dg_refines_onI)
  fix location assume "location \<in> universe"
  show "lookup_resolved_st_q
      (locals (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))) location =
      locals (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())))) (location_vname location)"
    by simp
next
  fix location assume loc: "location \<in> universe"
  have sr: "list_all2 (\<lambda>t_st t_abs. \<forall>l\<in>universe.
             lookup_resolved_st_q (globs (sides_of_rhs t_st \<sigma>_st (Inr ()))) l =
             globs (sides_of_rhs t_abs \<sigma>_abs (Inr ())) (location_vname l)) ts_st ts_abs"
    using list_refines by (rule list_all2_mono) (fastforce dest: dg_refines_onD_side)
  have combined: "\<forall>l\<in>universe.
      lookup_resolved_st_q (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))) l =
      globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ())) (location_vname l)"
    by (rule sides_side_rhs_fold_dg_lookup_refines_on[OF sr])
  show "lookup_resolved_st_q
      (globs (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_st ts_st) \<sigma>_st (Inr ()))))) location =
      globs (DG bot (globs (sides_of_rhs (side_rhs_fold_dg acc_abs ts_abs) \<sigma>_abs (Inr ()))))
        (location_vname location)"
    using combined loc by simp
qed

text \<open>
  Support and default transport through the same two folds, needed
  alongside the \<open>_refines_on\<close> facts above to invoke the inequality-lifting
  lemma at the generator level: the fold's own accumulator and each folded
  tree's local output are both scope-bounded and bot-defaulted (by the
  strict projection), so the whole fold is too.
\<close>

lemma side_acc_dg_support_bounded:
  fixes acc :: "('a::bounded_semilattice_sup_bot) exec_dg_st"
  assumes acc_bounded: "set (effective_support (rep_resolved_st acc)) \<subseteq> scope"
    and trees_bounded: "\<forall>t \<in> set ts.
      set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma)))) \<subseteq> scope"
  shows "set (effective_support (rep_resolved_st (side_acc_dg acc sigma ts))) \<subseteq> scope"
proof -
  have general: "set (effective_support (rep_resolved_st p)) \<subseteq> scope \<Longrightarrow>
      (\<forall>t \<in> set ts. set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma)))) \<subseteq> scope) \<Longrightarrow>
      set (effective_support (rep_resolved_st (side_acc_dg p sigma ts))) \<subseteq> scope"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by simp
  next
    case (Cons t ts)
    have step: "set (effective_support (rep_resolved_st
        (p \<squnion> locals (traverse_rhs t sigma)))) \<subseteq> scope"
    proof -
      have "set (effective_support (rep_resolved_st (p \<squnion> locals (traverse_rhs t sigma)))) \<subseteq>
          set (effective_support (rep_resolved_st p)) \<union>
          set (effective_support (rep_resolved_st (locals (traverse_rhs t sigma))))"
        by (rule effective_support_rep_sup_resolved_st_q)
      also have "\<dots> \<subseteq> scope"
        using Cons.prems by auto
      finally show ?thesis .
    qed
    show ?case
      using Cons.IH[OF step] Cons.prems by simp
  qed
  show ?thesis using acc_bounded trees_bounded by (rule general)
qed

lemma side_acc_dg_default_bot:
  fixes acc :: "('a::bounded_semilattice_sup_bot) exec_dg_st"
  assumes acc_default: "resolved_default (rep_resolved_st acc) = (\<lambda>_. bot)"
    and trees_default: "\<forall>t \<in> set ts.
      resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) = (\<lambda>_. bot)"
  shows "resolved_default (rep_resolved_st (side_acc_dg acc sigma ts)) = (\<lambda>_. bot)"
proof -
  have general: "resolved_default (rep_resolved_st p) = (\<lambda>_. bot) \<Longrightarrow>
      (\<forall>t \<in> set ts. resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) = (\<lambda>_. bot)) \<Longrightarrow>
      resolved_default (rep_resolved_st (side_acc_dg p sigma ts)) = (\<lambda>_. bot)"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by simp
  next
    case (Cons t ts)
    have step: "resolved_default (rep_resolved_st
        (p \<squnion> locals (traverse_rhs t sigma))) = (\<lambda>_. bot)"
    proof -
      have "resolved_default (rep_resolved_st (p \<squnion> locals (traverse_rhs t sigma))) loc =
          resolved_default (rep_resolved_st p) loc \<squnion>
          resolved_default (rep_resolved_st (locals (traverse_rhs t sigma))) loc" for loc
        by (rule resolved_default_rep_sup_resolved_st_q)
      then show ?thesis
        using Cons.prems by (simp add: fun_eq_iff)
    qed
    show ?case
      using Cons.IH[OF step] Cons.prems by simp
  qed
  show ?thesis using acc_default trees_default by (rule general)
qed

lemma sides_side_rhs_fold_dg_support_bounded:
  assumes trees_bounded: "\<forall>t \<in> set ts.
    set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope"
  shows "set (effective_support (rep_resolved_st
    (globs (sides_of_rhs (side_rhs_fold_dg acc ts) sigma (Inr ()))))) \<subseteq> scope"
proof -
  have general: "(\<forall>t \<in> set ts.
      set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope) \<Longrightarrow>
      set (effective_support (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg p ts) sigma (Inr ()))))) \<subseteq> scope"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case by (simp add: bot_dg_state_def)
  next
    case (Cons t ts)
    have hd: "set (effective_support (rep_resolved_st
        (globs (sides_of_rhs t sigma (Inr ()))))) \<subseteq> scope"
      using Cons.prems by simp
    have ih: "set (effective_support (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg
          (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ()))))) \<subseteq> scope"
      by (rule Cons.IH) (use Cons.prems in simp)
    show ?case
    proof -
      have "set (effective_support (rep_resolved_st
          (globs (sides_of_rhs (side_rhs_fold_dg p (t # ts)) sigma (Inr ()))))) =
        set (effective_support (rep_resolved_st
          (globs (sides_of_rhs t sigma (Inr ())) \<squnion>
           globs (sides_of_rhs
             (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))))"
        by (simp add: sides_of_rhs_seqcomp sup_dg_state_def)
      also have "\<dots> \<subseteq>
          set (effective_support (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ()))))) \<union>
          set (effective_support (rep_resolved_st
            (globs (sides_of_rhs
              (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))))"
        by (rule effective_support_rep_sup_resolved_st_q)
      also have "\<dots> \<subseteq> scope" using hd ih by auto
      finally show ?thesis .
    qed
  qed
  show ?thesis using trees_bounded by (rule general)
qed

lemma sides_side_rhs_fold_dg_default_bot:
  assumes trees_default: "\<forall>t \<in> set ts.
    resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)"
  shows "resolved_default (rep_resolved_st
    (globs (sides_of_rhs (side_rhs_fold_dg acc ts) sigma (Inr ())))) = (\<lambda>_. bot)"
proof -
  have general: "(\<forall>t \<in> set ts.
      resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)) \<Longrightarrow>
      resolved_default (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg p ts) sigma (Inr ())))) = (\<lambda>_. bot)"
    for p ts
  proof (induction ts arbitrary: p)
    case Nil
    thus ?case 
      by (auto simp add: bot_dg_state_def resolved_default_rep_bot_resolved_st_q)
  next
    case (Cons t ts)
    have hd: "resolved_default (rep_resolved_st
        (globs (sides_of_rhs t sigma (Inr ())))) = (\<lambda>_. bot)"
      using Cons.prems by simp
    have ih: "resolved_default (rep_resolved_st
        (globs (sides_of_rhs (side_rhs_fold_dg
          (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))) = (\<lambda>_. bot)"
      by (rule Cons.IH) (use Cons.prems in simp)
    show ?case
    proof -
      have "resolved_default (rep_resolved_st
          (globs (sides_of_rhs (side_rhs_fold_dg p (t # ts)) sigma (Inr ())))) =
        resolved_default (rep_resolved_st
          (globs (sides_of_rhs t sigma (Inr ())) \<squnion>
           globs (sides_of_rhs
             (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ()))))"
        by (simp add: sides_of_rhs_seqcomp sup_dg_state_def)
      also have "\<dots> = (\<lambda>loc.
          resolved_default (rep_resolved_st (globs (sides_of_rhs t sigma (Inr ())))) loc \<squnion>
          resolved_default (rep_resolved_st
            (globs (sides_of_rhs
              (side_rhs_fold_dg (p \<squnion> locals (traverse_rhs t sigma)) ts) sigma (Inr ())))) loc)"
        by (rule ext) (rule resolved_default_rep_sup_resolved_st_q)
      also have "\<dots> = (\<lambda>_. bot)"
        using hd ih by (simp add: fun_eq_iff)
      finally show ?thesis .
    qed
  qed
  show ?thesis using trees_default by (rule general)
qed

subsection \<open>Bundled per-tree transport relation\<close>

text \<open>
  \<open>dg_tree_st_commute \<sigma>_st t_st t_abs\<close> is the reusable transport contract for a
  single strategy tree: its executable denotation, its side-effect map, and its
  static dependencies all agree (through \<open>fun_of_dg_st\<close>) with the abstract tree
  read against the pushed-forward valuation \<open>fun_of_dg_st \<circ> \<sigma>_st\<close>.  It bundles
  the three commutation obligations the equation-system transport threads through
  the accumulator fold.

  The intra per-edge trees are discharged generically below from a componentwise
  analysis step.  The opaque \<open>cmb\<close>/\<open>extra\<close> trees --- whose \<^const>\<open>Side\<close> targets
  may be computed inside a \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> continuation (a routed
  callee seed) --- are supplied by the instance as bundled hypotheses; the bridge
  never assumes their side targets are syntactically fixed.

  The context is bound as \<open>ctx\<close>, never \<open>c\<close>: an unqualified \<open>c\<close> is captured by the
  imported constant \<open>state.c\<close>, which silently pins these theorems to a single
  context and produces a proof that only looks polymorphic.
\<close>

definition dg_tree_st_commute_for ::
  "(vname => bool)
   \<Rightarrow> ('u + 'k \<Rightarrow> (('a::bounded_semilattice_sup_bot) exec_dg_st, ('b::bounded_semilattice_sup_bot) exec_dg_st) dg_state)
   \<Rightarrow> ('u, 'k, ('a exec_dg_st, 'b exec_dg_st) dg_state) strategy_tree
   \<Rightarrow> ('u, 'k, ('a abs_state, 'b abs_state) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs \<longleftrightarrow>
     fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
   \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k)
   \<and> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st) t_abs"

lemma dg_tree_st_commute_for_trav:
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
  by (simp add: dg_tree_st_commute_for_def)

lemma dg_tree_st_commute_for_sides:
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs
     \<Longrightarrow> fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
  by (simp add: dg_tree_st_commute_for_def)

lemma dg_tree_st_commute_for_dep:
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs
     \<Longrightarrow> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st) t_abs"
  by (simp add: dg_tree_st_commute_for_def)

lemma dg_list_commute_trav_for:
  "list_all2 (dg_tree_st_commute_for gs \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st)
                    = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_for_def)

lemma dg_list_commute_travsides_for:
  "list_all2 (dg_tree_st_commute_for gs \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
              \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k)) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_for_def)

lemma dg_list_commute_dep_for:
  "list_all2 (dg_tree_st_commute_for gs \<sigma>_st) ts_st ts_abs
     \<Longrightarrow> list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st) t_abs) ts_st ts_abs"
  by (erule list_all2_mono) (simp add: dg_tree_st_commute_for_def)

text \<open>The intra per-edge tree, relabelled by an arbitrary global key \<open>gk\<close> and
  local relabel \<open>lk\<close>, satisfies the bundled relation whenever the analysis step
  commutes componentwise.\<close>


lemma dg_tree_st_commute_wrapped_edge_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "dg_tree_st_commute_for gs \<sigma>_st
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  unfolding dg_tree_st_commute_for_def
  by (intro conjI allI
        traverse_wrapped_edge_commute_for[where step_st=step_st and step_abs=step_abs, OF H]
        sides_wrapped_edge_commute_for[where step_st=step_st and step_abs=step_abs, OF H]
        dep_aux_wrapped_edge_eq)

subsection \<open>Per-node tree-list transport for the generator\<close>

text \<open>
  The concatenated per-node tree list --- intra predecessors, combine trees, and
  \<open>extra\<close> trees --- transports elementwise.  Intra edges follow from \<open>Hstep\<close>;
  the combine and extra trees are the instance's bundled hypotheses.
\<close>


lemma seed_dg_list_commute_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "list_all2 (dg_tree_st_commute_for gs \<sigma>_st)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_st route_st ctx ca cc ex) (return_call_action_list g v)
      @ extra_st route_st ctx v)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_abs route_abs ctx ca cc ex) (return_call_action_list g v)
      @ extra_abs route_abs ctx v)"
proof -
  have edge_elem: "\<And>u a. dg_tree_st_commute_for gs \<sigma>_st
        (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u)))
        (map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u)))"
    unfolding apply_dg_spec_def
    by (rule dg_tree_st_commute_wrapped_edge_for[where step_st="dg_spec_step S_st a" and step_abs="dg_spec_step S_abs a" for a, OF Hstep])
  show ?thesis
    by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl
                   edge_elem Hcmb Hextra split_beta)
qed

text \<open>Projections of the bundled list relation onto the shapes the accumulator
  fold, side fold, and dependency fold each expect.\<close>


subsection \<open>Equation-system transport for the generic generator\<close>

text \<open>
  The generic transport theorems below carry the executable D/G post-solution to
  the abstract one over unknowns \<^typ>\<open>pp \<times> 'c\<close> with arbitrary global key type
  \<^typ>\<open>'k\<close>.  They fix only the analysis-step commutation \<open>Hstep\<close>; the routed
  combine and enter-seed trees enter through the bundled hypotheses \<open>Hcmb\<close> /
  \<open>Hextra\<close>, so a computed \<^const>\<open>Side\<close> target transports without being pinned.
\<close>


lemma eq_seed_dg_commute_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "fun_of_dg_st_for gs (eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) (v, ctx) \<sigma>_st)
       = eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
               (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) (v, ctx) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have la: "list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st))
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_st a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_st route_st ctx ca cc ex) (return_call_action_list g v) @ extra_st route_st ctx v)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S_abs a u))) (pred_sel g v)
      @ map (\<lambda>(cc, ca, ex). cmb_abs route_abs ctx ca cc ex) (return_call_action_list g v) @ extra_abs route_abs ctx v)"
    by (rule dg_list_commute_trav_for[OF seed_dg_list_commute_for
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  show ?thesis
    unfolding eq_side_cfg_T_eff_keyed_seed_dg
    by (simp add: fun_of_exec_dg_st_for_bot bot_fun_def side_acc_dg_commute_for[OF la] fun_of_exec_dg_st_for_sup flip: bot_fun_def)
qed



lemma sides_seed_dg_commute_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "fun_of_dg_st_for gs (sides_of_rhs
             (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, ctx)) \<sigma>_st k)
       = sides_of_rhs
             (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
                (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g) (v, ctx)) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
             \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k))
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ca, ex). cmb_st route_st ctx ca cc ex) (return_call_action_list g w) @ extra_st route_st ctx w)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ca, ex). cmb_abs route_abs ctx ca cc ex) (return_call_action_list g w) @ extra_abs route_abs ctx w)"
    by (rule dg_list_commute_travsides_for[OF seed_dg_list_commute_for
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  have fold: "\<And>w acc_st k. fun_of_dg_st_for gs (sides_of_rhs (side_rhs_fold_dg acc_st
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
          @ map (\<lambda>(cc, ca, ex). cmb_st route_st ctx ca cc ex) (return_call_action_list g w) @ extra_st route_st ctx w)) \<sigma>_st k)
     = sides_of_rhs (side_rhs_fold_dg (fun_of_exec_dg_st_for gs acc_st)
        (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
          @ map (\<lambda>(cc, ca, ex). cmb_abs route_abs ctx ca cc ex) (return_call_action_list g w) @ extra_abs route_abs ctx w))
          (fun_of_dg_st_for gs \<circ> \<sigma>_st) k"
    by (rule sides_side_rhs_fold_dg_commute_for[OF la])
  have seed: "fun_of_dg_st_for gs (DG bot s0g) =
      DG (fun_of_exec_dg_st_for gs bot) (fun_of_exec_dg_st_for gs s0g)"
    by (simp add: fun_of_dg_st_for_def)
  show ?thesis
    unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
    by (simp add: Let_def fun_upd_apply fun_of_dg_st_for_sup seed fold fun_of_exec_dg_st_for_sup flip: bot_fun_def)
qed



lemma dep_seed_dg_eq_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
  shows "dep_aux \<sigma>_st (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, ctx))
       = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st)
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs bot0' s0d' s0g' (v, ctx))"
proof -
  have la: "\<And>w. list_all2 (\<lambda>t_st t_abs. dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st) t_abs)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_st a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ca, ex). cmb_st route_st ctx ca cc ex) (return_call_action_list g w) @ extra_st route_st ctx w)
    (map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w'. (w', ctx)) (apply_dg_spec S_abs a u))) (pred_sel g w)
      @ map (\<lambda>(cc, ca, ex). cmb_abs route_abs ctx ca cc ex) (return_call_action_list g w) @ extra_abs route_abs ctx w)"
    by (rule dg_list_commute_dep_for[OF seed_dg_list_commute_for
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra]])
  show ?thesis
    unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
    by (simp add: dep_aux_Side dep_aux_side_rhs_fold_dg_commute[OF la])
qed


subsection \<open>The post-solution transport theorem\<close>

text \<open>
  A partial post-solution of the executable context-indexed D/G equation system,
  mapped value-wise through \<open>fun_of_dg_st\<close>, is a partial post-solution of the
  abstract system over the same unknown set --- unknown identity, \<open>vars\<close>, and
  dependencies are unchanged; only the equation values transport.  The routed
  combine and enter-seed trees transport through the bundled \<open>Hcmb\<close> / \<open>Hextra\<close>
  hypotheses, so the dynamic \<^const>\<open>Side\<close> targets are carried over faithfully.
\<close>


theorem part_post_solution_seed_dg_st_to_abs_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
      and pp: "part_post_solution
                 (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
              (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) x (fun_of_dg_st_for gs \<circ> \<sigma>_st) vars"
proof (intro conjI ballI)
  show "x \<in> vars" using pp by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have dl: "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u \<subseteq> vars"
    using pp u by simp
  have "dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st)
          (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g) (v, c))
      = dep_aux \<sigma>_st (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g (v, c))"
    by (rule dep_seed_dg_eq_for
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra, symmetric])
  hence "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) (fun_of_dg_st_for gs \<circ> \<sigma>_st) u
       = dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) \<sigma>_st u"
    unfolding dep\<^sub>L_def dep_def uv by simp
  thus "dep\<^sub>L (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) (fun_of_dg_st_for gs \<circ> \<sigma>_st) u \<subseteq> vars"
    using dl by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st
              \<le> \<sigma>_st (Inl u)" using pp u by simp
  have "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) u (fun_of_dg_st_for gs \<circ> \<sigma>_st)
      = fun_of_dg_st_for gs (eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) u \<sigma>_st)"
      unfolding uv by (simp add: eq_seed_dg_commute_for
            [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
               and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
               and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra])
  also have "\<dots> \<le> fun_of_dg_st_for gs (\<sigma>_st (Inl u))" using le by (rule fun_of_dg_st_for_mono)
  finally show "eq (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) u (fun_of_dg_st_for gs \<circ> \<sigma>_st)
              \<le> (fun_of_dg_st_for gs \<circ> \<sigma>_st) (Inl u)" by simp
next
  fix u assume u: "u \<in> vars"
  obtain v c where uv: "u = (v, c)" by (cases u) auto
  have le: "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st
              \<le> \<sigma>_st" using pp u by simp
  show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g) u) (fun_of_dg_st_for gs \<circ> \<sigma>_st) \<le> fun_of_dg_st_for gs \<circ> \<sigma>_st"
  proof (rule le_funI)
    fix k
    have "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g) u) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k
        = fun_of_dg_st_for gs (sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g u) \<sigma>_st k)"
      unfolding uv by (simp add: sides_seed_dg_commute_for
            [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
               and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
               and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra])
    also have "\<dots> \<le> fun_of_dg_st_for gs (\<sigma>_st k)"
      using le[THEN le_funD] by (rule fun_of_dg_st_for_mono)
    finally show "sides_of_rhs (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
             (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g) u) (fun_of_dg_st_for gs \<circ> \<sigma>_st) k
                \<le> (fun_of_dg_st_for gs \<circ> \<sigma>_st) k" by simp
  qed
qed


subsection \<open>The monovariant (unit-context) specialisation\<close>

lemma dg_tree_st_commute_dg_cmb_of_for:
  assumes Hcomb: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st dst dc de g)
                            = dgs_combine S_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "dg_tree_st_commute_for gs \<sigma>_st (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)
                                  (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)"
  unfolding dg_tree_st_commute_for_def dg_cmb_of_def dg_spec_combine_tree_def
  apply simp
  apply (intro conjI allI
        traverse_wrapped_combine_commute_for[where comb_st="dgs_combine S_st" and comb_abs="dgs_combine S_abs", OF Hcomb]
        sides_wrapped_combine_commute_for[where comb_st="dgs_combine S_st" and comb_abs="dgs_combine S_abs", OF Hcomb]
        dep_aux_wrapped_combine_eq)
  done

lemma dg_extra_of_commute_for:
  assumes Henter:
    "\<And>xs es d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st xs es d g)
      = dgs_enter S_abs xs es (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "list_all2 (dg_tree_st_commute_for gs \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
  unfolding dg_extra_of_def
  by (auto simp: list_all2_map1 list_all2_map2 Henter
      split: call_action.splits
      intro!: list_all2_refl dg_tree_st_commute_wrapped_edge_for)

theorem part_post_solution_dg_st_to_abs_for:
  assumes Hstep: "\<And>a d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g)
                          = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
      and Henter: "\<And>xs es d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st xs es d g)
                            = dgs_enter S_abs xs es (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
      and Hcomb: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st dst dc de g)
                            = dgs_combine S_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
      and pp: "part_post_solution (dg_gen_of S_st g bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution (dg_gen_of S_abs g (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
           x (fun_of_dg_st_for gs \<circ> \<sigma>_st) vars"
proof -
  have hr: "\<And>u c' d ca. (\<lambda>_ _ _ _. ()) u c' d ca = (\<lambda>_ _ _ _. ()) u c' (fun_of_exec_dg_st_for gs d) ca"
    by simp
  have hc: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st
      (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
  proof -
    fix c' ca cc ex
    obtain dst fs as where ca_eq: "ca = CallEdge dst fs as" by (cases ca) auto
    thus "dg_tree_st_commute_for gs \<sigma>_st
        (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
      by (simp add: dg_tree_st_commute_dg_cmb_of_for[OF Hcomb])
  qed
  have he: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
    by (rule dg_extra_of_commute_for[OF Henter])
  from pp have pp':
    "part_post_solution
      (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
        (dg_cmb_of S_st) (dg_extra_of S_st g) g S_st bot0 s0d s0g) x \<sigma>_st vars"
    unfolding dg_gen_of_def .
  show ?thesis
    unfolding dg_gen_of_def
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
             and route_st = "\<lambda>_ _ _ _. ()" and route_abs = "\<lambda>_ _ _ _. ()"
             and cmb_st = "dg_cmb_of S_st" and cmb_abs = "dg_cmb_of S_abs"
             and extra_st = "dg_extra_of S_st g" and extra_abs = "dg_extra_of S_abs g",
           OF Hstep hr hc he pp'])
qed



end

