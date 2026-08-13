theory Exec_Bridge
  imports Exec_Backward Exec_Placement TD_Side_Eff_Bounds TD_Side_RHS_Generator Constraint_System
begin

section \<open>Executable equation-system refinement\<close>

text \<open>
  Generic (domain-agnostic) bridge between executable st side-effecting equation
  systems and abstract abs_state side_cfg_T_eff systems.  Domain theories discharge
  per-tree traverse and side denotation commutation through fun_of_resolved_st_q_for gs.
\<close>

subsection \<open>fun_of_resolved_st_q_for gs homomorphisms for local/global projections\<close>

lemma fun_of_resolved_st_q_for_restrict_local_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_restrict_global_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_combine_env_abs [simp]:
  "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) =
     combine_env\<^sup># gs (fun_of_resolved_st_q_for gs sc)
       (fun_of_resolved_st_q_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) x =
      combine_env\<^sup># gs (fun_of_resolved_st_q_for gs sc)
        (fun_of_resolved_st_q_for gs se) x"
    by (cases "gs x"; simp add: combine_env_abs_def)
qed

subsection \<open>Finite pointwise readback for local/global reconstruction\<close>

text \<open>
  \<open>side_env_lift\<close>'s \<open>Lifted\<close>/\<open>Lifted\<close> case reconstructs via \<open>\<squnion>\<close> pointwise, and
  pointwise function \<open>\<squnion>\<close> is not executable over @{typ vname} (would demand
  @{typ vname} \<open>:: enum\<close>). But a check-report reader only ever asks for one
  variable's value at a time, and pointwise \<open>\<squnion>\<close> distributes over application
  unconditionally -- \<open>(f \<squnion> g) x = f x \<squnion> g x\<close> -- with no invariant on \<open>f\<close>/\<open>g\<close>
  needed. So a per-variable readback straight from the two finite
  \<open>resolved_st_q\<close> slots stays exactly equal to \<open>side_env_lift\<close>, at every \<open>v\<close>,
  without threading an \<open>Inl\<close>-globals-bot solver invariant through the state
  machine: the executable side just re-derives the same pointwise identity the
  abstract \<open>\<squnion>\<close> already satisfies.
\<close>

fun side_env_lift_st :: "(vname => bool) => ('a::bounded_semilattice_sup_bot resolved_st_q) lifted => ('a resolved_st_q) lifted => ('a abs_state) lifted" where
  "side_env_lift_st gs Bot glo = Bot"
| "side_env_lift_st gs (Lifted l) Bot = Lifted (fun_of_resolved_st_q_for gs l)"
| "side_env_lift_st gs (Lifted l) (Lifted g) = Lifted (%x. fun_of_resolved_st_q_for gs l x \<squnion> fun_of_resolved_st_q_for gs g x)"

lemma side_env_lift_st_eq_side_env_lift:
  fixes raw :: "pp + unit => 'a::sound_domain resolved_st_q lifted"
  shows "side_env_lift_st gs (raw (Inl v)) (raw (Inr ())) =
           side_env_lift (map_lift (fun_of_resolved_st_q_for gs) o raw) v"
  unfolding side_env_lift_def glob_env_unit o_def
  by (cases "raw (Inl v)"; cases "raw (Inr ())") (simp_all add: fun_eq_iff)

text \<open>
  Every \<open>[code]\<close> reporting boundary (\<open>interval_td_check_report_code\<close> and
  siblings) unwraps \<^const>\<open>side_env_lift_st\<close>'s result via \<open>case_lifted bot
  id\<close>: a structural \<^const>\<open>Bot\<close> -- the solver never reached this point --
  erases to the domain's canonical all-\<open>bot\<close> environment, and a
  \<^const>\<open>Lifted\<close> witness passes through unchanged. That erasure is only sound
  at a finished reporting boundary, never while a solver is still storing
  state, because it discards the structural/semantic distinction between
  ``not yet known'' and ``provably unreachable''. This lemma pins the
  erasure to the already-proven-sound \<^const>\<open>side_env_lift\<close> construction
  every check-report soundness theorem is stated against, rather than
  leaving it as an unverified consequence of a \<open>[code]\<close> equation.
\<close>
lemma side_env_lift_st_readback:
  fixes raw :: "pp + unit => 'a::sound_domain resolved_st_q lifted"
  shows "case_lifted bot id (side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))) =
           case_lifted bot id (side_env_lift (map_lift (fun_of_resolved_st_q_for gs) o raw) v)"
  by (simp add: side_env_lift_st_eq_side_env_lift)



subsection \<open>Executable projection identities\<close>

lemma restrict_local_resolved_q_combine_resolved_st_q [simp]:
  "restrict_local_resolved_q (combine_resolved_st_q A B) =
     restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_combine_resolved_st_q [simp]:
  "restrict_global_resolved_q (combine_resolved_st_q A B) =
     restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

text \<open>The converse recombination: a local projection joined with a disjoint global
  projection is exactly the routed combine. Left bare (not \<open>[simp]\<close>) since it would
  compete with \<open>restrict_local_resolved_q_split\<close>/\<open>restrict_global_resolved_q_split\<close>
  on the same \<open>restrict_local _ \<squnion> restrict_global _\<close> redex.\<close>
lemma combine_resolved_st_q_eq_restrict_sup:
  "combine_resolved_st_q A B = restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (combine_resolved_st_q A B) =
      lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (combine_resolved_st_q A B) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

text \<open>Effectful executable trees use these projection identities to split combined states.\<close>
lemma restrict_local_resolved_q_split [simp]:
  "restrict_local_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_split [simp]:
  "restrict_global_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed




subsection \<open>Executable effectful transfer record\<close>

text \<open>
  Executable counterpart of the effectful transfer record: per-action strategy-tree
  producers with payloads at @{typ "'a resolved_st_q"} instead of @{typ "'a abs_state"}.
\<close>

type_synonym ('g, 'c) st_edge_tf_tree =
  "pp \<Rightarrow> (pp, 'g, 'c) strategy_tree"

type_synonym ('g, 'c) st_combine_tf_tree =
  "pp \<Rightarrow> pp \<Rightarrow> (pp, 'g, 'c) strategy_tree"

record ('g, 'c) effectful_st_transfer =
  etf_st_nop        :: "('g, 'c) st_edge_tf_tree"
  etf_st_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> ('g, 'c) st_edge_tf_tree"
  etf_st_random     :: "vname \<Rightarrow> ('g, 'c) st_edge_tf_tree"
  etf_st_assume     :: "bexp  \<Rightarrow> ('g, 'c) st_edge_tf_tree"
  etf_st_assume_not :: "bexp  \<Rightarrow> ('g, 'c) st_edge_tf_tree"
  etf_st_enter      :: "vname list \<Rightarrow> aexp list \<Rightarrow> ('g, 'c) st_edge_tf_tree"
  etf_st_combine    :: "vname option \<Rightarrow> ('g, 'c) st_combine_tf_tree"

fun apply_etf_st ::
  "('g, 'c) effectful_st_transfer \<Rightarrow> edge_action \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'c) strategy_tree"
where
  "apply_etf_st etf EA_Nop           u = etf_st_nop etf u"
| "apply_etf_st etf (EA_Assign x a)  u = etf_st_assign etf x a u"
| "apply_etf_st etf (EA_Random x)    u = etf_st_random etf x u"
| "apply_etf_st etf (EA_Assume b)    u = etf_st_assume etf b u"
| "apply_etf_st etf (EA_AssumeNot b) u = etf_st_assume_not etf b u"
| "apply_etf_st etf (EA_Ret e p) u =
     (case e of None \<Rightarrow> etf_st_nop etf u | Some a \<Rightarrow> etf_st_assign etf ret_var a u)"
| "apply_etf_st etf (EA_Check cnd) u = etf_st_nop etf u"

fun etf_combine_st ::
  "('g, 'c) effectful_st_transfer \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'c) strategy_tree"
where
  "etf_combine_st etf dst cc ex = etf_st_combine etf dst cc ex"

subsection \<open>Unit-global executable effectful trees\<close>

text \<open>
  The executable edge and combine trees preserve the unit-global routing shape
  while representing abstract states with @{typ "'a resolved_st_q"}.
\<close>

text \<open>
  Executable mirror of \<^const>\<open>unit_edge_tree\<close>: the payload is
  \<^typ>\<open>'a resolved_st_q lifted\<close>, with the same role-aware \<^const>\<open>Bot\<close> reading
  (AD-51/AD-52) -- a local \<^const>\<open>Bot\<close> is an unreachable CFG point and dominates
  reconstruction via \<^const>\<open>assemble_local_global\<close>; a global \<^const>\<open>Bot\<close> is only
  ``no side contribution yet''.  \<^const>\<open>restrict_local_resolved_q\<close>/
  \<^const>\<open>restrict_global_resolved_q\<close> already carry the local/global tag on
  every \<^typ>\<open>location\<close>, so splitting the reconstructed result needs no
  classifier here.

  The witness-bottom test is a free parameter \<open>is_bot_pred\<close>, not
  \<^const>\<open>is_bot_state\<close> composed with @{const fun_of_resolved_st_q_for}
  directly: that composition quantifies over all of \<^typ>\<open>vname\<close> and has no
  \<open>[code]\<close> equation. Callers supply \<^const>\<open>resolved_st_q_is_bot_for\<close> at a
  concrete program's declared-global list, which is exact -- proved equal to
  \<^const>\<open>is_bot_state\<close> \<circ> @{const fun_of_resolved_st_q_for}
  (@{thm resolved_st_q_is_bot_for_iff}) -- and executable, so every fact this
  theory proves about \<open>is_bot_pred\<close> in the abstract carries over unchanged to
  that instantiation.
\<close>
lemma restrict_local_resolved_q_sup [simp]:
  "restrict_local_resolved_q (a \<squnion> b)
     = restrict_local_resolved_q a \<squnion> restrict_local_resolved_q b"
  by (simp add: resolved_st_q_eq_iff fun_eq_iff split: location.splits)

lemma restrict_global_resolved_q_sup [simp]:
  "restrict_global_resolved_q (a \<squnion> b)
     = restrict_global_resolved_q a \<squnion> restrict_global_resolved_q b"
  by (simp add: resolved_st_q_eq_iff fun_eq_iff split: location.splits)

lemma map_lift_restrict_local_resolved_q_join [simp]:
  "map_lift restrict_local_resolved_q (a \<squnion> b)
     = map_lift restrict_local_resolved_q a \<squnion> map_lift restrict_local_resolved_q b"
  by (cases a; cases b) simp_all

lemma map_lift_restrict_global_resolved_q_join [simp]:
  "map_lift restrict_global_resolved_q (a \<squnion> b)
     = map_lift restrict_global_resolved_q a \<squnion> map_lift restrict_global_resolved_q b"
  by (cases a; cases b) simp_all

definition unit_edge_tree_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool)
   \<Rightarrow> ('a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (unit, 'a resolved_st_q lifted) st_edge_tf_tree"
where
  "unit_edge_tree_st is_bot_pred f u = do {
     su \<leftarrow> read_local u;
     g \<leftarrow> read_global ();
     let res = transfer_lift is_bot_pred f
                 (assemble_local_global su g);
     depend_on () (map_lift restrict_global_resolved_q res)
       (answer (map_lift restrict_local_resolved_q res))
   }"

definition unit_combine_tree_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a resolved_st_q lifted) strategy_tree"
where
  "unit_combine_tree_st is_bot_pred gs dst cc ex = do {
     sc \<leftarrow> read_local cc;
     se \<leftarrow> read_local ex;
     g \<leftarrow> read_global ();
     let res = transfer_lift2 is_bot_pred
                 (combine_collect_resolved_for_q gs dst)
                 (assemble_local_global sc g) (assemble_local_global se g);
     depend_on () (map_lift restrict_global_resolved_q res)
       (answer (map_lift restrict_local_resolved_q res))
   }"

text \<open>
  \<open>unit_edge_contribution_st\<close>/\<open>unit_combine_contribution_st\<close> are the Side-free,
  unsplit counterparts of \<^const>\<open>unit_edge_tree_st\<close>/\<^const>\<open>unit_combine_tree_st\<close>
  (Voblint issue #121): same reads, same computed unsplit \<open>res\<close>, but answered
  directly instead of split-and-published. See \<open>make_side_rhs_tree_eff_st_buffered\<close>
  below.\<close>

definition unit_edge_contribution_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool)
   \<Rightarrow> ('a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (unit, 'a resolved_st_q lifted) st_edge_tf_tree"
where
  "unit_edge_contribution_st is_bot_pred f u = do {
     su \<leftarrow> read_local u;
     g \<leftarrow> read_global ();
     answer (transfer_lift is_bot_pred f (assemble_local_global su g))
   }"

definition unit_combine_contribution_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a resolved_st_q lifted) strategy_tree"
where
  "unit_combine_contribution_st is_bot_pred gs dst cc ex = do {
     sc \<leftarrow> read_local cc;
     se \<leftarrow> read_local ex;
     g \<leftarrow> read_global ();
     answer (transfer_lift2 is_bot_pred (combine_collect_resolved_for_q gs dst)
               (assemble_local_global sc g) (assemble_local_global se g))
   }"

subsection \<open>Placement-aware executable trees\<close>

text \<open>
  The owner and finite location scope are supplied per CFG node.  The executable
  state remains keyed by @{typ location}; only the placement policy observes the
  owner-qualified key.
\<close>

text \<open>
  Unlike the unit-global family above, a placement tree never needs to detect
  a mid-computation witness bottom: its \<open>su\<close>/\<open>g\<close> reads are re-injections of
  \<^const>\<open>project_resolved_on\<close>-restricted fragments, whose \<open>dl\<close>/\<open>dg\<close> defaults
  encode ``outside this fragment's finite scope'', not reachability. Reusing
  \<^const>\<open>assemble_local_global\<close>'s local-\<^const>\<open>Bot\<close>-dominance or
  \<open>transfer_lift\<close>'s \<open>is_bot_pred\<close> witness test here would read that
  scope-restriction default as a reachability claim -- the two conventions
  collide on the same \<^const>\<open>Bot\<close> value for unrelated reasons. So a placed
  tree unwraps \<open>su\<close>/\<open>g\<close> via \<open>case_lifted bot id\<close>, combines with plain \<open>\<squnion>\<close> (the
  pre-lift shape), and republishes unconditionally through \<^const>\<open>Lifted\<close>:
  unreachable program points still arise structurally, from
  \<open>make_side_rhs_tree_eff_st\<close>'s own \<^const>\<open>Bot\<close> fold seed, exactly as they do
  for the unit-global family.
\<close>

definition unit_edge_tree_st_placed ::
  "(pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => ('a::bounded_semilattice_sup_bot resolved_st_q => 'a resolved_st_q)
   => (unit, 'a resolved_st_q lifted) st_edge_tf_tree"
where
  "unit_edge_tree_st_placed owner_of locations_of keep_local publish_side f u = do {
     su \<leftarrow> read_local u;
     g \<leftarrow> read_global ();
     let res = f (case_lifted bot id su \<squnion> case_lifted bot id g);
     depend_on ()
       (Lifted (project_resolved_on (owner_of u) (locations_of u) publish_side res))
       (answer
         (Lifted (project_resolved_on (owner_of u) (locations_of u) keep_local res)))
   }"

definition unit_combine_tree_st_placed ::
  "(vname => bool)
   => (pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => vname option => pp => pp
   => (pp, unit, 'a::bounded_semilattice_sup_bot resolved_st_q lifted) strategy_tree"
where
  "unit_combine_tree_st_placed source_global owner_of locations_of
      keep_local publish_side dst cc ex = do {
     sc \<leftarrow> read_local cc;
     se \<leftarrow> read_local ex;
     g \<leftarrow> read_global ();
     let res =
       combine_collect_resolved_for_q source_global dst
         (case_lifted bot id sc \<squnion> case_lifted bot id g)
         (case_lifted bot id se \<squnion> case_lifted bot id g);
     depend_on ()
       (Lifted (project_resolved_on (owner_of cc) (locations_of cc) publish_side res))
       (answer
         (Lifted (project_resolved_on (owner_of cc) (locations_of cc) keep_local res)))
   }"

definition unit_etf_st_of_transfer_placed ::
  "(vname => bool)
   => (pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => (edge_action => 'a::bounded_semilattice_sup_bot resolved_st_q => 'a resolved_st_q)
   => (vname list => aexp list => 'a resolved_st_q => 'a resolved_st_q)
   => (unit, 'a resolved_st_q lifted) effectful_st_transfer"
where
  "unit_etf_st_of_transfer_placed source_global owner_of locations_of
      keep_local publish_side tf_st enter_st =
    \<lparr> etf_st_nop =
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st EA_Nop),
      etf_st_assign = (\<lambda>x e.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st (EA_Assign x e))),
      etf_st_random = (\<lambda>x.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st (EA_Random x))),
      etf_st_assume = (\<lambda>b.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st (EA_Assume b))),
      etf_st_assume_not = (\<lambda>b.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st (EA_AssumeNot b))),
      etf_st_enter = (\<lambda>xs es.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (enter_st xs es)),
      etf_st_combine =
        unit_combine_tree_st_placed source_global owner_of locations_of
          keep_local publish_side \<rparr>"

lemma apply_etf_st_unit_of_transfer_placed:
  assumes reduces: "action_reduces tf_st"
  shows
    "apply_etf_st
      (unit_etf_st_of_transfer_placed source_global owner_of locations_of
        keep_local publish_side tf_st enter_st) a u =
      unit_edge_tree_st_placed owner_of locations_of keep_local publish_side
        (tf_st a) u"
proof -
  interpret action_reduces tf_st by (rule reduces)
  show ?thesis
    unfolding unit_etf_st_of_transfer_placed_def
    by (cases a) (auto simp: ret_none ret_some check split: option.splits)
qed

lemma etf_st_enter_unit_of_transfer_placed:
  "etf_st_enter
    (unit_etf_st_of_transfer_placed source_global owner_of locations_of
      keep_local publish_side tf_st enter_st) xs es u =
    unit_edge_tree_st_placed owner_of locations_of keep_local publish_side
      (enter_st xs es) u"
  unfolding unit_etf_st_of_transfer_placed_def by simp

lemma etf_combine_st_unit_of_transfer_placed:
  "etf_combine_st
    (unit_etf_st_of_transfer_placed source_global owner_of locations_of
      keep_local publish_side tf_st enter_st) dst cc ex =
    unit_combine_tree_st_placed source_global owner_of locations_of
      keep_local publish_side dst cc ex"
  unfolding unit_etf_st_of_transfer_placed_def by simp

lemma traverse_unit_edge_tree_st_placed:
  "traverse_rhs
    (unit_edge_tree_st_placed owner_of locations_of
      keep_local publish_side f u) sigma_st =
    map_lift (project_resolved_on (owner_of u) (locations_of u) keep_local)
      (Lifted (f (case_lifted bot id (sigma_st (Inl u)) \<squnion> case_lifted bot id (sigma_st (Inr ())))))"
  unfolding unit_edge_tree_st_placed_def by (simp add: Let_def)

lemma sides_unit_edge_tree_st_placed_Inr:
  "sides_of_rhs
    (unit_edge_tree_st_placed owner_of locations_of
      keep_local publish_side f u) sigma_st (Inr ()) =
    map_lift (project_resolved_on (owner_of u) (locations_of u) publish_side)
      (Lifted (f (case_lifted bot id (sigma_st (Inl u)) \<squnion> case_lifted bot id (sigma_st (Inr ())))))"
  unfolding unit_edge_tree_st_placed_def by (simp add: Let_def)

lemma traverse_unit_combine_tree_st_placed:
  "traverse_rhs
    (unit_combine_tree_st_placed source_global owner_of locations_of
      keep_local publish_side dst cc ex) sigma_st =
    map_lift (project_resolved_on (owner_of cc) (locations_of cc) keep_local)
      (Lifted (combine_collect_resolved_for_q source_global dst
        (case_lifted bot id (sigma_st (Inl cc)) \<squnion> case_lifted bot id (sigma_st (Inr ())))
        (case_lifted bot id (sigma_st (Inl ex)) \<squnion> case_lifted bot id (sigma_st (Inr ())))))"
  unfolding unit_combine_tree_st_placed_def by (simp add: Let_def)

lemma sides_unit_combine_tree_st_placed_Inr:
  "sides_of_rhs
    (unit_combine_tree_st_placed source_global owner_of locations_of
      keep_local publish_side dst cc ex) sigma_st (Inr ()) =
    map_lift (project_resolved_on (owner_of cc) (locations_of cc) publish_side)
      (Lifted (combine_collect_resolved_for_q source_global dst
        (case_lifted bot id (sigma_st (Inl cc)) \<squnion> case_lifted bot id (sigma_st (Inr ())))
        (case_lifted bot id (sigma_st (Inl ex)) \<squnion> case_lifted bot id (sigma_st (Inr ())))))"
  unfolding unit_combine_tree_st_placed_def by (simp add: Let_def)

text \<open>
  A placed edge/combine tree's payload is \<^typ>\<open>'a resolved_st_q lifted\<close>, but the
  local/side split reads back one shared witness through two different
  projections (\<open>keep_local\<close>, \<open>publish_side\<close>). \<open>case_lifted\<close> unwraps before
  recombining -- \<^const>\<open>Bot\<close> stays \<^const>\<open>Bot\<close> on both projections, and a
  \<^const>\<open>Lifted\<close> witness recombines exactly as \<open>lookup_project_resolved_on_join\<close>
  already establishes at the raw level.
\<close>
lemma case_lifted_lookup_project_resolved_on_join:
  fixes r :: "('a::bounded_semilattice_sup_bot) resolved_st_q lifted"
  assumes relevant: "target \<in> set locs"
    and covered: "keep_local (owner, target) \<or> publish_side (owner, target)"
  shows
    "case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
      (map_lift (project_resolved_on owner locs keep_local) r \<squnion>
       map_lift (project_resolved_on owner locs publish_side) r) =
     case_lifted bot (\<lambda>s. lookup_resolved_st_q s target) r"
proof (cases r)
  case Bot
  then show ?thesis by simp
next
  case (Lifted v)
  have step:
    "map_lift (project_resolved_on owner locs keep_local) r \<squnion>
       map_lift (project_resolved_on owner locs publish_side) r =
     Lifted (project_resolved_on owner locs keep_local v \<squnion>
       project_resolved_on owner locs publish_side v)"
    using Lifted by simp
  have inner:
    "lookup_resolved_st_q
      (project_resolved_on owner locs keep_local v \<squnion>
       project_resolved_on owner locs publish_side v) target =
     lookup_resolved_st_q v target"
    by (rule lookup_project_resolved_on_join) (use relevant covered in auto)
  show ?thesis
    unfolding Lifted step using inner by simp
qed


subsection \<open>Scoped placement bridge\<close>

locale placed_exec_bridge =
  fixes source_global :: "vname => bool"
    and node_owner :: "pp => pname"
    and locations_of :: "pp => location list"
    and keep_local :: "scoped_location => bool"
    and publish_side :: "scoped_location => bool"
  assumes global_owner_invariant_local:
      "placement_global_invariant keep_local"
    and global_owner_invariant_side:
      "placement_global_invariant publish_side"
    and node_coverage[intro]:
      "target \<in> set (locations_of node) \<Longrightarrow>
       keep_local (node_owner node, target) \<or>
       publish_side (node_owner node, target)"
begin

definition project_local ::
  "pp => ('a::bot) resolved_st_q => 'a resolved_st_q" where
  "project_local node state =
    project_resolved_on (node_owner node) (locations_of node) keep_local state"

definition project_side ::
  "pp => ('a::bot) resolved_st_q => 'a resolved_st_q" where
  "project_side node state =
    project_resolved_on (node_owner node) (locations_of node) publish_side state"

lemma project_recombine_lookup:
  fixes state :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes relevant: "target \<in> set (locations_of node)"
  shows
    "lookup_resolved_st_q
      (project_local node state \<squnion> project_side node state) target =
      lookup_resolved_st_q state target"
proof -
  have covered:
    "keep_local (node_owner node, target) \<or>
     publish_side (node_owner node, target)"
    by (rule node_coverage[OF relevant])
  show ?thesis
    unfolding project_local_def project_side_def
    by (rule lookup_project_resolved_on_join)
       (use relevant covered in auto)
qed

lemma project_recombine_env_abstract:
  fixes state :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes relevant:
    "location_of source_global x \<in> set (locations_of node)"
  shows
    "fun_of_resolved_st_q_for source_global
      (project_local node state \<squnion> project_side node state) x =
      fun_of_resolved_st_q_for source_global state x"
  unfolding fun_of_resolved_st_q_for_def
  by (rule project_recombine_lookup[OF relevant])

lemma project_recombine_refines:
  fixes state :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes refines:
    "resolved_st_q_refines_for source_global state full"
    and relevant:
    "location_of source_global x \<in> set (locations_of node)"
  shows
    "fun_of_resolved_st_q_for source_global
      (project_local node state \<squnion> project_side node state) x = full x"
proof -
  have projected:
    "fun_of_resolved_st_q_for source_global
      (project_local node state \<squnion> project_side node state) x =
     fun_of_resolved_st_q_for source_global state x"
    by (rule project_recombine_env_abstract[OF relevant])
  have refined:
    "fun_of_resolved_st_q_for source_global state x = full x"
    using refines unfolding resolved_st_q_refines_for_def by simp
  show ?thesis using projected refined by simp
qed

lemma edge_recombine_lookup:
  fixes f :: "('a::bounded_semilattice_sup_bot) resolved_st_q => 'a resolved_st_q"
    and sigma :: "pp + unit => 'a resolved_st_q lifted"
  assumes relevant: "target \<in> set (locations_of node)"
  shows
    "case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
      (traverse_rhs
        (unit_edge_tree_st_placed node_owner locations_of
          keep_local publish_side f node) sigma \<squnion>
       sides_of_rhs
        (unit_edge_tree_st_placed node_owner locations_of
          keep_local publish_side f node) sigma (Inr ())) =
      case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
        (Lifted (f (case_lifted bot id (sigma (Inl node)) \<squnion> case_lifted bot id (sigma (Inr ())))))"
proof -
  have covered:
    "keep_local (node_owner node, target) \<or> publish_side (node_owner node, target)"
    by (rule node_coverage[OF relevant])
  show ?thesis
    unfolding traverse_unit_edge_tree_st_placed sides_unit_edge_tree_st_placed_Inr
    by (rule case_lifted_lookup_project_resolved_on_join) (use relevant covered in auto)
qed

lemma entry_recombine_lookup:
  fixes enter :: "vname list => aexp list =>
    ('a::bounded_semilattice_sup_bot) resolved_st_q => 'a resolved_st_q"
    and sigma :: "pp + unit => 'a resolved_st_q lifted"
  assumes relevant: "target \<in> set (locations_of node)"
  shows
    "case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
      (traverse_rhs
        (unit_edge_tree_st_placed node_owner locations_of
          keep_local publish_side (enter parameters arguments) node) sigma \<squnion>
       sides_of_rhs
        (unit_edge_tree_st_placed node_owner locations_of
          keep_local publish_side (enter parameters arguments) node) sigma (Inr ())) =
      case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
        (Lifted (enter parameters arguments
          (case_lifted bot id (sigma (Inl node)) \<squnion> case_lifted bot id (sigma (Inr ())))))"
  by (rule edge_recombine_lookup[OF relevant])

lemma combine_recombine_lookup:
  fixes sigma :: "pp + unit => ('a::bounded_semilattice_sup_bot) resolved_st_q lifted"
  assumes relevant: "target \<in> set (locations_of caller)"
  shows
    "case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
      (traverse_rhs
        (unit_combine_tree_st_placed source_global node_owner locations_of
          keep_local publish_side destination caller callee) sigma \<squnion>
       sides_of_rhs
        (unit_combine_tree_st_placed source_global node_owner locations_of
          keep_local publish_side destination caller callee) sigma (Inr ())) =
      case_lifted bot (\<lambda>s. lookup_resolved_st_q s target)
        (Lifted (combine_collect_resolved_for_q source_global destination
          (case_lifted bot id (sigma (Inl caller)) \<squnion> case_lifted bot id (sigma (Inr ())))
          (case_lifted bot id (sigma (Inl callee)) \<squnion> case_lifted bot id (sigma (Inr ())))))"
proof -
  have covered:
    "keep_local (node_owner caller, target) \<or> publish_side (node_owner caller, target)"
    by (rule node_coverage[OF relevant])
  show ?thesis
    unfolding traverse_unit_combine_tree_st_placed sides_unit_combine_tree_st_placed_Inr
    by (rule case_lifted_lookup_project_resolved_on_join) (use relevant covered in auto)
qed

end



subsection \<open>Unit-global executable transfer-record factory\<close>

text \<open>
  Executable mirror of the abstract-side @{const unit_etf_of_transfer}: builds an
  \<open>effectful_st_transfer\<close> record from a single dispatch function and an enter function,
  both at @{typ "'a resolved_st_q"}.  Domain instances (\<open>Sign_Exec\<close>, \<open>Ivl_Exec\<close>) instantiate this
  once instead of hand-writing the six-field record.
\<close>

definition unit_etf_st_of_transfer ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool)
   \<Rightarrow> (vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (vname list \<Rightarrow> aexp list \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (unit, 'a resolved_st_q lifted) effectful_st_transfer"
where
  "unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st = \<lparr>
    etf_st_nop        = unit_edge_tree_st is_bot_pred (tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. unit_edge_tree_st is_bot_pred (tf_st (EA_Assign x e))),
    etf_st_random     = (\<lambda>x. unit_edge_tree_st is_bot_pred (tf_st (EA_Random x))),
    etf_st_assume     = (\<lambda>b. unit_edge_tree_st is_bot_pred (tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. unit_edge_tree_st is_bot_pred (tf_st (EA_AssumeNot b))),
    etf_st_enter      = (\<lambda>xs es. unit_edge_tree_st is_bot_pred (enter_st xs es)),
    etf_st_combine    = unit_combine_tree_st is_bot_pred gs
  \<rparr>"

lemma apply_etf_st_unit_of_transfer:
  assumes reduces: "action_reduces tf_st"
  shows "apply_etf_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) a u
           = unit_edge_tree_st is_bot_pred (tf_st a) u"
proof -
  interpret action_reduces tf_st by (rule reduces)
  show ?thesis
    unfolding unit_etf_st_of_transfer_def
    by (cases a) (simp_all add: ret_none ret_some check split: option.splits)
qed

lemma etf_combine_st_unit_of_transfer:
  "etf_combine_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex
     = unit_combine_tree_st is_bot_pred gs dst cc ex"
  unfolding unit_etf_st_of_transfer_def by simp

lemma etf_st_enter_unit_of_transfer:
  "etf_st_enter (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) xs es u
     = unit_edge_tree_st is_bot_pred (enter_st xs es) u"
  unfolding unit_etf_st_of_transfer_def by simp

lemma etf_st_enter_exists_unit_of_transfer:
  "\<exists>f. etf_st_enter (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) xs es u
         = unit_edge_tree_st is_bot_pred f u"
  using etf_st_enter_unit_of_transfer by blast

lemma apply_etf_st_exists_unit_of_transfer:
  assumes reduces: "action_reduces tf_st"
  shows "\<exists>f. apply_etf_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) a u
               = unit_edge_tree_st is_bot_pred f u"
  using apply_etf_st_unit_of_transfer[OF reduces] by blast

text \<open>
  \<open>res_edge_st\<close>/\<open>res_combine_st\<close> name the reconstructed input's transfer result
  the same way \<^const>\<open>res_edge\<close>/\<^const>\<open>res_combine\<close> do on the spec side: \<^const>\<open>Bot\<close>
  when either the reconstructed input or \<open>f\<close>'s own result is witness-bottom,
  \<^const>\<open>Lifted\<close> \<open>f\<close>'s result otherwise. The witness-bottom test is the same
  free \<open>is_bot_pred\<close> parameter \<^const>\<open>unit_edge_tree_st\<close> takes.
\<close>
definition res_edge_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool) \<Rightarrow> ('a resolved_st_q \<Rightarrow> 'a resolved_st_q) \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a resolved_st_q lifted) \<Rightarrow> 'a resolved_st_q lifted" where
  "res_edge_st is_bot_pred f u \<sigma>_st =
     transfer_lift is_bot_pred f
       (assemble_local_global (\<sigma>_st (Inl u)) (\<sigma>_st (Inr ())))"

definition res_combine_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a resolved_st_q lifted) \<Rightarrow> 'a resolved_st_q lifted" where
  "res_combine_st is_bot_pred gs dst cc ex \<sigma>_st =
     transfer_lift2 is_bot_pred
       (combine_collect_resolved_for_q gs dst)
       (assemble_local_global (\<sigma>_st (Inl cc)) (\<sigma>_st (Inr ())))
       (assemble_local_global (\<sigma>_st (Inl ex)) (\<sigma>_st (Inr ())))"

lemma traverse_unit_edge_tree_st:
  "traverse_rhs (unit_edge_tree_st is_bot_pred f u) \<sigma>_st =
   map_lift restrict_local_resolved_q (res_edge_st is_bot_pred f u \<sigma>_st)"
  unfolding unit_edge_tree_st_def res_edge_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_st_Inr:
  "sides_of_rhs (unit_edge_tree_st is_bot_pred f u) \<sigma>_st (Inr ()) =
   map_lift restrict_global_resolved_q (res_edge_st is_bot_pred f u \<sigma>_st)"
  unfolding unit_edge_tree_st_def res_edge_st_def by (simp add: Let_def)

lemma traverse_unit_combine_tree_st:
  "traverse_rhs (unit_combine_tree_st is_bot_pred gs dst cc ex) \<sigma>_st =
   map_lift restrict_local_resolved_q (res_combine_st is_bot_pred gs dst cc ex \<sigma>_st)"
  unfolding unit_combine_tree_st_def res_combine_st_def by (simp add: Let_def)

lemma sides_unit_combine_tree_st_Inr:
  "sides_of_rhs (unit_combine_tree_st is_bot_pred gs dst cc ex) \<sigma>_st (Inr ()) =
   map_lift restrict_global_resolved_q (res_combine_st is_bot_pred gs dst cc ex \<sigma>_st)"
  unfolding unit_combine_tree_st_def res_combine_st_def by (simp add: Let_def)

lemma dep_aux_unit_edge_tree_st:
  fixes f :: "'a::sound_domain resolved_st_q \<Rightarrow> 'a resolved_st_q"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  shows "dep_aux \<sigma>1 (unit_edge_tree_st is_bot_pred f u) = dep_aux \<sigma>2 (unit_edge_tree gs g u)"
  unfolding unit_edge_tree_st_def unit_edge_tree_def Let_def by simp


lemma dep_aux_unit_combine_tree_st:
  "dep_aux \<sigma>1 (unit_combine_tree_st is_bot_pred gs dst cc ex) = dep_aux \<sigma>2 (unit_combine_tree gs dst' cc ex)"
  unfolding unit_combine_tree_st_def unit_combine_tree_def Let_def by simp

lemma traverse_unit_edge_contribution_st:
  "traverse_rhs (unit_edge_contribution_st is_bot_pred f u) \<sigma>_st = res_edge_st is_bot_pred f u \<sigma>_st"
  unfolding unit_edge_contribution_st_def res_edge_st_def by simp

lemma sides_of_rhs_unit_edge_contribution_st [simp]:
  "sides_of_rhs (unit_edge_contribution_st is_bot_pred f u) \<sigma>_st = \<bottom>"
  unfolding unit_edge_contribution_st_def by (simp add: bot_fun_def)

lemma traverse_unit_combine_contribution_st:
  "traverse_rhs (unit_combine_contribution_st is_bot_pred gs dst cc ex) \<sigma>_st
     = res_combine_st is_bot_pred gs dst cc ex \<sigma>_st"
  unfolding unit_combine_contribution_st_def res_combine_st_def by simp

lemma sides_of_rhs_unit_combine_contribution_st [simp]:
  "sides_of_rhs (unit_combine_contribution_st is_bot_pred gs dst cc ex) \<sigma>_st = \<bottom>"
  unfolding unit_combine_contribution_st_def by (simp add: bot_fun_def)

lemma dep_aux_unit_edge_contribution_st_eq_unit_edge_tree_st:
  "dep_aux \<sigma> (unit_edge_contribution_st is_bot_pred f u) = dep_aux \<sigma> (unit_edge_tree_st is_bot_pred f u)"
  unfolding unit_edge_contribution_st_def unit_edge_tree_st_def Let_def by simp

lemma dep_aux_unit_combine_contribution_st_eq_unit_combine_tree_st:
  "dep_aux \<sigma> (unit_combine_contribution_st is_bot_pred gs dst cc ex)
     = dep_aux \<sigma> (unit_combine_tree_st is_bot_pred gs dst cc ex)"
  unfolding unit_combine_contribution_st_def unit_combine_tree_st_def Let_def by simp


subsection \<open>Globally-restricted side values\<close>

text \<open>
  \<open>restrict_global_resolved_q\<close> is the idempotent projection onto global variables.  A
  strategy tree is \<open>side_rg\<close> when every \<open>Side\<close> node it can reach (under any query
  answer) carries a value already fixed by that projection.  Unit trees and the
  executable IP fold satisfy this: every side contribution is a
  \<open>restrict_global_resolved_q ...\<close>.  The side-effecting solver then keeps every \<open>Inr\<close> slot
  \<open>restrict_global_resolved_q\<close>-shaped, since the running join of such values stays shaped
  (\<open>restrict_global_resolved_q_sup_restrict_global_resolved_q\<close>, \<open>restrict_global_resolved_q\<close> of \<open>bot\<close>).
\<close>

lemma restrict_global_resolved_q_idem [simp]:
  "restrict_global_resolved_q (restrict_global_resolved_q s) =
     restrict_global_resolved_q s"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q
      (restrict_global_resolved_q s)) =
      lookup_resolved_st_q (restrict_global_resolved_q s)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q
        (restrict_global_resolved_q s)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q s) loc"
      by (cases loc; simp)
  qed
qed

primrec side_rg ::
  "('x, 'g, ('a::bot) resolved_st_q lifted) strategy_tree \<Rightarrow> bool"
where
  "side_rg (Answer d) = True"
| "side_rg (QueryL y f) = (\<forall>v. side_rg (f v))"
| "side_rg (QueryG y f) = (\<forall>v. side_rg (f v))"
| "side_rg (Side y d t) = (map_lift restrict_global_resolved_q d = d \<and> side_rg t)"

lemma side_rg_seqcomp:
  assumes "side_rg t" and "\<And>v. side_rg (k v)"
  shows "side_rg (seqcomp_tree t k)"
  using assms by (induction t arbitrary: k) auto

lemma map_lift_restrict_global_resolved_q_idem [simp]:
  "map_lift restrict_global_resolved_q (map_lift restrict_global_resolved_q x) =
     map_lift restrict_global_resolved_q x"
  by (cases x) simp_all

lemma side_rg_unit_edge_tree_st: "side_rg (unit_edge_tree_st is_bot_pred f u)"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma side_rg_unit_combine_tree_st: "side_rg (unit_combine_tree_st is_bot_pred gs dst cc ex)"
  unfolding unit_combine_tree_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_Inl:
  "sides_of_rhs (unit_edge_tree gs f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_def Let_def by simp

lemma sides_unit_combine_tree_Inl:
  "sides_of_rhs (unit_combine_tree gs dst cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_def Let_def by simp

lemma sides_unit_edge_tree_st_Inl:
  "sides_of_rhs (unit_edge_tree_st is_bot_pred f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_st_def Let_def by simp

lemma sides_unit_combine_tree_st_Inl:
  "sides_of_rhs (unit_combine_tree_st is_bot_pred gs dst cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_st_def Let_def by simp


text \<open>
  \<open>res_edge_st\<close>/\<open>res_combine_st\<close> commute with the spec-side \<^const>\<open>res_edge\<close>/
  \<^const>\<open>res_combine\<close> under \<open>map_lift (fun_of_resolved_st_q_for gs)\<close> as the
  interpretation -- the AD-51/AD-52 exec/spec bridge, restated at the lifted
  level.  \<^const>\<open>combine_collect_resolved_for_q\<close> already commutes with
  \<open>combine\<^sup>#\<close> unconditionally (@{thm fun_of_resolved_st_q_for_combine_collect});
  a single edge transfer \<open>f\<close>/\<open>F\<close> needs the caller's own \<open>commute\<close> fact, since
  \<open>f\<close> is domain-specific. The caller also owes \<open>exact\<close>: \<open>is_bot_pred\<close> must
  itself be extensionally the semantic @{const is_bot_state} test through
  @{const fun_of_resolved_st_q_for} -- true of
  @{const resolved_st_q_is_bot_for} at a program's own declared-global list
  (@{thm resolved_st_q_is_bot_for_iff}) -- so this stays an exact commutation,
  not a refinement.
\<close>
lemma res_edge_st_fun_of_resolved_st_q_for:
  assumes commute: "\<And>s. fun_of_resolved_st_q_for gs (f s) = F (fun_of_resolved_st_q_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (res_edge_st is_bot_pred f u \<sigma>_st) =
         res_edge F u (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  unfolding res_edge_st_def res_edge_def o_def
  by (cases "\<sigma>_st (Inl u)"; cases "\<sigma>_st (Inr ())";
      simp add: commute exact normalize_lift_def split: if_splits)

lemma res_combine_st_fun_of_resolved_st_q_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (res_combine_st is_bot_pred gs dst cc ex \<sigma>_st) =
   res_combine gs dst cc ex (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  unfolding res_combine_st_def res_combine_def o_def
  by (cases "\<sigma>_st (Inl cc)"; cases "\<sigma>_st (Inl ex)"; cases "\<sigma>_st (Inr ())";
      simp add: exact normalize_lift_def split: if_splits)




locale sound_rhs_generator_exec = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and etf_st :: "(unit, 'a resolved_st_q lifted) effectful_st_transfer"
    and F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
    and is_bot_pred :: "'a resolved_st_q \<Rightarrow> bool"
  assumes edge[simp]:
      "\<And>a u. apply_etf etf a u = unit_edge_tree gs (F a) u"
    and edge_st[simp]:
      "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st is_bot_pred (F_st a) u"
    and comb_st[simp]:
      "\<And>cc ex dst.
         etf_combine_st etf_st dst cc ex = unit_combine_tree_st is_bot_pred gs dst cc ex"
    and commute[simp]:
      "\<And>a s.
         fun_of_resolved_st_q_for gs (F_st a s) =
         F a (fun_of_resolved_st_q_for gs s)"
    and is_bot_pred_exact[simp]:
      "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma sides_apply_etf_st:
  "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
   = sides_of_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    by (simp add: edge_st edge sides_unit_edge_tree_st_Inl sides_unit_edge_tree_Inl
                  Let_def bot_fun_def)
next
  case (Inr g')
  then have k_eq: "k = Inr ()" by simp
  show ?thesis
    unfolding k_eq edge_st edge sides_unit_edge_tree_st_Inr sides_unit_edge_tree_Inr
              res_edge_st_def res_edge_def o_def
    by (cases "\<sigma>_st (Inl u)"; cases "\<sigma>_st (Inr ())";
        simp add: commute is_bot_pred_exact normalize_lift_def split: if_splits)
qed

lemma sides_etf_combine_st:
  "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st k)
   = sides_of_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    unfolding comb_st comb
    by (simp add: sides_unit_combine_tree_st_Inl sides_unit_combine_tree_Inl
                  Let_def bot_fun_def)
next
  case (Inr g')
  then have k_eq: "k = Inr ()" by simp
  show ?thesis
    unfolding k_eq comb_st comb sides_unit_combine_tree_st_Inr sides_unit_combine_tree_Inr
              res_combine_st_def res_combine_def o_def
    by (cases "\<sigma>_st (Inl cc)"; cases "\<sigma>_st (Inl ex)"; cases "\<sigma>_st (Inr ())";
        simp add: is_bot_pred_exact normalize_lift_def split: if_splits)
qed



end



subsection \<open>Effectful executable fold\<close>

definition side_contribution_trees_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) strategy_tree list"
where
  "side_contribution_trees_st etf es ens cs =
     map (\<lambda>(u, a). apply_etf_st etf a u) es @
     map (\<lambda>(cl, fs, as). etf_st_enter etf fs as cl) ens @
     map (\<lambda>(cc, dst, ex). etf_combine_st etf dst cc ex) cs"

definition side_acc_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q lifted
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a resolved_st_q lifted)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list \<Rightarrow> 'a resolved_st_q lifted"
where
  "side_acc_eff_st etf acc \<sigma> es ens cs =
     fold_rhs_values acc \<sigma> (side_contribution_trees_st etf es ens cs)"

definition side_rhs_fold_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q lifted
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) strategy_tree"
where
  "side_rhs_fold_eff_st etf acc es ens cs =
     fold_rhs_trees acc (side_contribution_trees_st etf es ens cs)"

lemma side_acc_eff_st_simps [simp]:
  "side_acc_eff_st etf acc \<sigma> [] [] [] = acc"
  "side_acc_eff_st etf acc \<sigma> ((u, a) # es) ens cs =
     side_acc_eff_st etf (acc \<squnion> traverse_rhs (apply_etf_st etf a u) \<sigma>) \<sigma> es ens cs"
  "side_acc_eff_st etf acc \<sigma> [] ((cl, fs, as) # ens) cs =
     side_acc_eff_st etf (acc \<squnion> traverse_rhs (etf_st_enter etf fs as cl) \<sigma>) \<sigma> [] ens cs"
  "side_acc_eff_st etf acc \<sigma> [] [] ((cc, dst, ex) # cs) =
     side_acc_eff_st etf (acc \<squnion> traverse_rhs (etf_combine_st etf dst cc ex) \<sigma>) \<sigma> [] [] cs"
  by (simp_all add: side_acc_eff_st_def side_contribution_trees_st_def)

lemma side_rhs_fold_eff_st_simps [simp]:
  "side_rhs_fold_eff_st etf acc [] [] [] = Answer acc"
  "side_rhs_fold_eff_st etf acc ((u, a) # es) ens cs =
     seqcomp_tree (apply_etf_st etf a u)
       (\<lambda>res. side_rhs_fold_eff_st etf (acc \<squnion> res) es ens cs)"
  "side_rhs_fold_eff_st etf acc [] ((cl, fs, as) # ens) cs =
     seqcomp_tree (etf_st_enter etf fs as cl)
       (\<lambda>res. side_rhs_fold_eff_st etf (acc \<squnion> res) [] ens cs)"
  "side_rhs_fold_eff_st etf acc [] [] ((cc, dst, ex) # cs) =
     seqcomp_tree (etf_combine_st etf dst cc ex)
       (\<lambda>res. side_rhs_fold_eff_st etf (acc \<squnion> res) [] [] cs)"
  by (simp_all add: side_rhs_fold_eff_st_def side_contribution_trees_st_def)

definition make_side_rhs_tree_eff_st ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) strategy_tree"
where
  "make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v =
     (let acc0 = (if v = cfg_entry g then Lifted (bot0_st \<squnion> restrict_local_resolved_q s0_st) else Bot);
          t    = side_rhs_fold_eff_st etf acc0
                   (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)
      in if v = cfg_entry g then depend_on gseed (Lifted (restrict_global_resolved_q s0_st)) t else t)"

definition side_cfg_T_eff_st ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) eqsT"
where
  "side_cfg_T_eff_st g etf bot0_st s0_st gseed = make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed"

subsection \<open>Buffered executable generator: fold Side-free contributions, publish once (issue #121)\<close>

text \<open>
  Executable mirror of \<^theory>\<open>Voblint_Core.TD_Side_Tree\<close>'s
  \<open>make_side_rhs_tree_eff_buffered\<close>/\<open>make_side_rhs_tree_eff_buffered_correspondence\<close>,
  adapted to the executable \<open>resolved_st_q\<close> layer: \<^const>\<open>restrict_local_resolved_q\<close>/
  \<^const>\<open>restrict_global_resolved_q\<close> already carry the local/global tag on every
  \<^typ>\<open>location\<close>, so unlike the spec-level \<open>restrict_local_for gs\<close>/\<open>restrict_global_for
  gs\<close> the split here needs no classifier argument.\<close>

definition make_side_rhs_tree_eff_st_buffered ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) strategy_tree"
where
  "make_side_rhs_tree_eff_st_buffered g etf bot0_st s0_st gseed v =
     (let acc0 = (if v = cfg_entry g then Lifted (bot0_st \<squnion> s0_st) else Bot);
          t    = fold_rhs_trees acc0
                   (side_contribution_trees_st etf
                      (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))
      in do {
        res \<leftarrow> t;
        side_publish gseed (map_lift restrict_global_resolved_q res);
        answer (map_lift restrict_local_resolved_q res)
      })"

definition side_cfg_T_eff_st_buffered ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a resolved_st_q lifted) eqsT"
where
  "side_cfg_T_eff_st_buffered g etf bot0_st s0_st gseed
     = make_side_rhs_tree_eff_st_buffered g etf bot0_st s0_st gseed"

text \<open>
  Correspondence theorem, mirroring
  \<open>make_side_rhs_tree_eff_buffered_correspondence\<close> at the executable layer:
  given the four per-tree obligations relating an \<open>etf_old\<close> (Side-emitting,
  e.g. \<^const>\<open>unit_edge_tree_st\<close>) to an \<open>etf_new\<close> (Side-free, e.g.
  \<open>unit_edge_contribution_st\<close>) -- exactly the facts already proved above for
  Interval's own pair -- the buffered generator over \<open>etf_new\<close> has the
  identical \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value as the original
  generator over \<open>etf_old\<close>, at \<open>bot0_st = bot\<close> (every current call site's
  actual argument). Specialized to \<open>'g = unit\<close>, matching every current
  \<open>side_cfg_T_eff_st\<close> caller.
\<close>

lemma make_side_rhs_tree_eff_st_buffered_correspondence:
  fixes etf_old etf_new :: "(unit, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
  assumes edge_t: "\<And>a u \<sigma>. traverse_rhs (apply_etf_st etf_old a u) \<sigma>
                    = map_lift restrict_local_resolved_q (traverse_rhs (apply_etf_st etf_new a u) \<sigma>)"
    and edge_s: "\<And>a u \<sigma>. sides_of_rhs (apply_etf_st etf_old a u) \<sigma> (Inr ())
                    = map_lift restrict_global_resolved_q (traverse_rhs (apply_etf_st etf_new a u) \<sigma>)"
    and edge_free: "\<And>a u \<sigma>. sides_of_rhs (apply_etf_st etf_new a u) \<sigma> = \<bottom>"
    and enter_t: "\<And>fs as cl \<sigma>. traverse_rhs (etf_st_enter etf_old fs as cl) \<sigma>
                    = map_lift restrict_local_resolved_q (traverse_rhs (etf_st_enter etf_new fs as cl) \<sigma>)"
    and enter_s: "\<And>fs as cl \<sigma>. sides_of_rhs (etf_st_enter etf_old fs as cl) \<sigma> (Inr ())
                    = map_lift restrict_global_resolved_q (traverse_rhs (etf_st_enter etf_new fs as cl) \<sigma>)"
    and enter_free: "\<And>fs as cl \<sigma>. sides_of_rhs (etf_st_enter etf_new fs as cl) \<sigma> = \<bottom>"
    and comb_t: "\<And>dst cc ex \<sigma>. traverse_rhs (etf_combine_st etf_old dst cc ex) \<sigma>
                    = map_lift restrict_local_resolved_q (traverse_rhs (etf_combine_st etf_new dst cc ex) \<sigma>)"
    and comb_s: "\<And>dst cc ex \<sigma>. sides_of_rhs (etf_combine_st etf_old dst cc ex) \<sigma> (Inr ())
                    = map_lift restrict_global_resolved_q (traverse_rhs (etf_combine_st etf_new dst cc ex) \<sigma>)"
    and comb_free: "\<And>dst cc ex \<sigma>. sides_of_rhs (etf_combine_st etf_new dst cc ex) \<sigma> = \<bottom>"
  shows "traverse_rhs (make_side_rhs_tree_eff_st_buffered g etf_new bot s0_st () v) \<sigma>
          = traverse_rhs (make_side_rhs_tree_eff_st g etf_old bot s0_st () v) \<sigma>"
    (is ?T)
    and "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g etf_new bot s0_st () v) \<sigma> (Inr ())
          = sides_of_rhs (make_side_rhs_tree_eff_st g etf_old bot s0_st () v) \<sigma> (Inr ())"
    (is ?S)
proof -
  define cs :: "(pp, unit, 'a resolved_st_q lifted) strategy_tree list"
    where "cs = side_contribution_trees_st etf_new
                  (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  have cs_old_eq: "side_contribution_trees_st etf_old
                     (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)
                 = map (\<lambda>(u,a). apply_etf_st etf_old a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_st_enter etf_old fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_st etf_old dst cc ex) (return_call_list g v)"
    by (simp add: side_contribution_trees_st_def etf_combine_st.simps)
  have cs_new_eq: "cs = map (\<lambda>(u,a). apply_etf_st etf_new a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_st_enter etf_new fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_st etf_new dst cc ex) (return_call_list g v)"
    unfolding cs_def by (simp add: side_contribution_trees_st_def etf_combine_st.simps)
  have free: "\<And>c \<sigma>'. c \<in> set cs \<Longrightarrow> sides_of_rhs c \<sigma>' = \<bottom>"
    unfolding cs_new_eq using edge_free enter_free comb_free by (auto split: prod.splits)
  let ?acc0new = "if v = cfg_entry g then Lifted (bot \<squnion> s0_st) else Bot"
  have acc0_split: "map_lift restrict_local_resolved_q ?acc0new
       = (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_resolved_q s0_st) else Bot)"
    by (cases "v = cfg_entry g") simp_all
  have restrict_global_acc0: "map_lift restrict_global_resolved_q ?acc0new
       = (if v = cfg_entry g then Lifted (restrict_global_resolved_q s0_st) else Bot)"
    by (cases "v = cfg_entry g") simp_all
  have tvT: "traverse_rhs (fold_rhs_trees ?acc0new cs) \<sigma>
       = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new"
    by (rule traverse_fold_rhs_trees_char)
  have seed_swap: "foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new
       = ?acc0new \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>"
    using foldr_sup_seed_swap[of "\<lambda>t. traverse_rhs t \<sigma>" cs "?acc0new" "\<bottom>"] by fastforce
  have map_join_local: "map_lift restrict_local_resolved_q
        (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>)
     = foldr (\<lambda>t acc'. map_lift restrict_local_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>"
    by (induction cs) simp_all
  have map_join_global: "map_lift restrict_global_resolved_q
        (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>)
     = foldr (\<lambda>t acc'. map_lift restrict_global_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>"
    by (induction cs) simp_all
  have edge_seg_t:
    "foldr (\<lambda>t acc'. map_lift restrict_local_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(u,a). apply_etf_st etf_new a u) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(u,a). apply_etf_st etf_old a u) xs) seed"
    for xs :: "(pp \<times> edge_action) list" and seed
    by (induction xs arbitrary: seed) (auto simp: edge_t split: prod.splits)
  have enter_seg_t:
    "foldr (\<lambda>t acc'. map_lift restrict_local_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cl,fs,as). etf_st_enter etf_new fs as cl) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(cl,fs,as). etf_st_enter etf_old fs as cl) xs) seed"
    for xs :: "(pp \<times> vname list \<times> aexp list) list" and seed
    by (induction xs arbitrary: seed) (auto simp: enter_t split: prod.splits)
  have comb_seg_t:
    "foldr (\<lambda>t acc'. map_lift restrict_local_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cc,dst,ex). etf_combine_st etf_new dst cc ex) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(cc,dst,ex). etf_combine_st etf_old dst cc ex) xs) seed"
    for xs :: "(pp \<times> vname option \<times> pp) list" and seed
    by (induction xs arbitrary: seed) (auto simp del: etf_combine_st.simps simp: comb_t split: prod.splits)
  have elem_local: "foldr (\<lambda>t acc'. map_lift restrict_local_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>
       = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
           (side_contribution_trees_st etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding cs_new_eq cs_old_eq foldr_append edge_seg_t enter_seg_t comb_seg_t by (rule refl)
  have edge_seg_s:
    "foldr (\<lambda>t acc'. map_lift restrict_global_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(u,a). apply_etf_st etf_new a u) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(u,a). apply_etf_st etf_old a u) xs) seed"
    for xs :: "(pp \<times> edge_action) list" and seed
    by (induction xs arbitrary: seed) (auto simp: edge_s split: prod.splits)
  have enter_seg_s:
    "foldr (\<lambda>t acc'. map_lift restrict_global_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cl,fs,as). etf_st_enter etf_new fs as cl) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(cl,fs,as). etf_st_enter etf_old fs as cl) xs) seed"
    for xs :: "(pp \<times> vname list \<times> aexp list) list" and seed
    by (induction xs arbitrary: seed) (auto simp: enter_s split: prod.splits)
  have comb_seg_s:
    "foldr (\<lambda>t acc'. map_lift restrict_global_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cc,dst,ex). etf_combine_st etf_new dst cc ex) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(cc,dst,ex). etf_combine_st etf_old dst cc ex) xs) seed"
    for xs :: "(pp \<times> vname option \<times> pp) list" and seed
    by (induction xs arbitrary: seed) (auto simp del: etf_combine_st.simps simp: comb_s split: prod.splits)
  have elem_global: "foldr (\<lambda>t acc'. map_lift restrict_global_resolved_q (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>
       = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc')
           (side_contribution_trees_st etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding cs_new_eq cs_old_eq foldr_append edge_seg_s enter_seg_s comb_seg_s by (rule refl)
  have told_sides_char: "sides_of_rhs
        (fold_rhs_trees \<bottom> (side_contribution_trees_st etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))) \<sigma> (Inr ())
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc')
         (side_contribution_trees_st etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    by (rule sides_of_rhs_fold_rhs_trees_char)
  define t_old where "t_old = side_rhs_fold_eff_st etf_old
        (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_resolved_q s0_st) else Bot)
        (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  have t_old_sides_indep: "sides_of_rhs t_old \<sigma> (Inr ())
     = sides_of_rhs
         (fold_rhs_trees \<bottom> (side_contribution_trees_st etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))) \<sigma> (Inr ())"
    unfolding t_old_def side_rhs_fold_eff_st_def sides_of_rhs_fold_rhs_trees_char
    by simp
  have t_old_traverse: "traverse_rhs t_old \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
         (side_contribution_trees_st etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))
         (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_resolved_q s0_st) else Bot)"
    unfolding t_old_def side_rhs_fold_eff_st_def traverse_fold_rhs_trees_char by simp
  have t_old_traverse_seed_swap: "traverse_rhs t_old \<sigma>
       = (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_resolved_q s0_st) else Bot)
         \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
             (side_contribution_trees_st etf_old
                (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding t_old_traverse
    using foldr_sup_seed_swap[of "\<lambda>t. traverse_rhs t \<sigma>"
            "side_contribution_trees_st etf_old
               (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g))
               (return_call_list g (cfg_entry g))"
            "Lifted (bot \<squnion> restrict_local_resolved_q s0_st)" "\<bottom>"]
    by simp
  have buffered_traverse: "traverse_rhs (make_side_rhs_tree_eff_st_buffered g etf_new bot s0_st () v) \<sigma>
       = map_lift restrict_local_resolved_q (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new)"
    unfolding make_side_rhs_tree_eff_st_buffered_def Let_def cs_def[symmetric]
    by (simp add: traverse_seqcomp tvT)
  have buffered_sides: "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g etf_new bot s0_st () v) \<sigma> (Inr ())
       = map_lift restrict_global_resolved_q (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new)"
    unfolding make_side_rhs_tree_eff_st_buffered_def Let_def cs_def[symmetric]
    by (simp add: sides_of_rhs_seqcomp_at sides_of_rhs_fold_rhs_trees_bot[OF free] tvT)
  have old_traverse: "traverse_rhs (make_side_rhs_tree_eff_st g etf_old bot s0_st () v) \<sigma>
       = traverse_rhs t_old \<sigma>"
    unfolding make_side_rhs_tree_eff_st_def Let_def t_old_def side_rhs_fold_eff_st_def
    by (simp add: traverse_seqcomp)
  have old_sides: "sides_of_rhs (make_side_rhs_tree_eff_st g etf_old bot s0_st () v) \<sigma> (Inr ())
       = (if v = cfg_entry g then Lifted (restrict_global_resolved_q s0_st) else Bot)
         \<squnion> sides_of_rhs t_old \<sigma> (Inr ())"
    unfolding make_side_rhs_tree_eff_st_def Let_def t_old_def side_rhs_fold_eff_st_def
    by (smt (verit, best) all_sides.simps(4) all_sides_eq_sides_Inr_unit
        sup_lifted.simps(1))
  have T: ?T
    unfolding buffered_traverse old_traverse seed_swap
    using elem_local map_join_local t_old_traverse_seed_swap by auto
  have S: ?S
    unfolding buffered_sides old_sides seed_swap
    using elem_global map_join_global t_old_sides_indep told_sides_char
    by auto
  from T S show ?T ?S by simp_all
qed

text \<open>
  \<^const>\<open>dep_aux\<close> companion to
  \<open>make_side_rhs_tree_eff_st_buffered_correspondence\<close>: \<^const>\<open>Side\<close> nodes are
  transparent to \<^const>\<open>dep_aux\<close> (it tracks reads, not writes), so the
  buffered generator's single trailing \<open>depend_on\<close>/\<open>answer\<close> wrapper
  contributes no dependency at all and the whole-generator \<^const>\<open>dep_aux\<close>
  reduces to the union of its Side-free contribution list's own
  \<^const>\<open>dep_aux\<close> values via \<open>dep_aux_fold_rhs_trees_char\<close> -- exactly
  paralleling \<open>cs_old_eq\<close>/\<open>cs_new_eq\<close> above, without needing the
  seed-swap/segment machinery the value correspondence required.
\<close>
lemma make_side_rhs_tree_eff_st_buffered_dep_aux:
  fixes etf_old etf_new :: "(unit, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
  assumes edge_d: "\<And>a u \<sigma>. dep_aux \<sigma> (apply_etf_st etf_old a u) = dep_aux \<sigma> (apply_etf_st etf_new a u)"
    and enter_d: "\<And>fs as cl \<sigma>. dep_aux \<sigma> (etf_st_enter etf_old fs as cl) = dep_aux \<sigma> (etf_st_enter etf_new fs as cl)"
    and comb_d: "\<And>dst cc ex \<sigma>. dep_aux \<sigma> (etf_combine_st etf_old dst cc ex) = dep_aux \<sigma> (etf_combine_st etf_new dst cc ex)"
  shows "dep_aux \<sigma> (make_side_rhs_tree_eff_st_buffered g etf_new bot s0_st () v)
          = dep_aux \<sigma> (make_side_rhs_tree_eff_st g etf_old bot s0_st () v)"
proof -
  define cs :: "(pp, unit, 'a resolved_st_q lifted) strategy_tree list"
    where "cs = side_contribution_trees_st etf_new
                  (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  have cs_old_eq: "side_contribution_trees_st etf_old
                     (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)
                 = map (\<lambda>(u,a). apply_etf_st etf_old a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_st_enter etf_old fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_st etf_old dst cc ex) (return_call_list g v)"
    by (simp add: side_contribution_trees_st_def etf_combine_st.simps)
  have cs_new_eq: "cs = map (\<lambda>(u,a). apply_etf_st etf_new a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_st_enter etf_new fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_st etf_new dst cc ex) (return_call_list g v)"
    unfolding cs_def by (simp add: side_contribution_trees_st_def etf_combine_st.simps)
  have union_eq: "(\<Union>c\<in>set cs. dep_aux \<sigma> c)
       = (\<Union>c\<in>set (side_contribution_trees_st etf_old
             (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)). dep_aux \<sigma> c)"
    unfolding cs_new_eq cs_old_eq set_append set_map
    using edge_d enter_d comb_d by (auto split: prod.splits)
  show ?thesis
    unfolding make_side_rhs_tree_eff_st_buffered_def make_side_rhs_tree_eff_st_def
              Let_def cs_def[symmetric] side_rhs_fold_eff_st_def
    by (simp add: dep_aux_fold_rhs_trees_char union_eq)
qed

text \<open>
  Side-free counterpart of \<^const>\<open>unit_etf_st_of_transfer\<close>, built from
  \<^const>\<open>unit_edge_contribution_st\<close>/\<^const>\<open>unit_combine_contribution_st\<close>
  instead of \<^const>\<open>unit_edge_tree_st\<close>/\<^const>\<open>unit_combine_tree_st\<close>, over the
  identical \<open>tf_st\<close>/\<open>enter_st\<close> domain-transfer functions. Every domain that
  builds its production \<open>effectful_st_transfer\<close> via \<^const>\<open>unit_etf_st_of_transfer\<close>
  (Interval, Sign, Parity) gets a buffered contribution counterpart, and the
  buffered-generator correspondence with it, for free from
  \<open>unit_etf_st_of_transfer_buffered_correspondence\<close> below -- no per-domain proof.
\<close>
definition unit_etf_st_contribution_of_transfer ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool)
   \<Rightarrow> (vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (vname list \<Rightarrow> aexp list \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (unit, 'a resolved_st_q lifted) effectful_st_transfer"
where
  "unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st = \<lparr>
    etf_st_nop        = unit_edge_contribution_st is_bot_pred (tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. unit_edge_contribution_st is_bot_pred (tf_st (EA_Assign x e))),
    etf_st_random     = (\<lambda>x. unit_edge_contribution_st is_bot_pred (tf_st (EA_Random x))),
    etf_st_assume     = (\<lambda>b. unit_edge_contribution_st is_bot_pred (tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. unit_edge_contribution_st is_bot_pred (tf_st (EA_AssumeNot b))),
    etf_st_enter      = (\<lambda>xs es. unit_edge_contribution_st is_bot_pred (enter_st xs es)),
    etf_st_combine    = unit_combine_contribution_st is_bot_pred gs
  \<rparr>"

lemma apply_etf_st_unit_of_transfer_contribution:
  assumes reduces: "action_reduces tf_st"
  shows "apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u
           = unit_edge_contribution_st is_bot_pred (tf_st a) u"
proof -
  interpret action_reduces tf_st by (rule reduces)
  show ?thesis
    unfolding unit_etf_st_contribution_of_transfer_def
    by (cases a) (simp_all add: ret_none ret_some check split: option.splits)
qed

lemma etf_combine_st_unit_of_transfer_contribution:
  "etf_combine_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex
     = unit_combine_contribution_st is_bot_pred gs dst cc ex"
  unfolding unit_etf_st_contribution_of_transfer_def by simp

lemma etf_st_enter_unit_of_transfer_contribution:
  "etf_st_enter (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) xs es u
     = unit_edge_contribution_st is_bot_pred (enter_st xs es) u"
  unfolding unit_etf_st_contribution_of_transfer_def by simp

lemma unit_etf_st_of_transfer_buffered_correspondence:
  assumes reduces: "action_reduces tf_st"
  shows "traverse_rhs (make_side_rhs_tree_eff_st_buffered g
            (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v) \<sigma>
          = traverse_rhs (make_side_rhs_tree_eff_st g
            (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v) \<sigma>"
    (is ?T)
    and "sides_of_rhs (make_side_rhs_tree_eff_st_buffered g
            (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v) \<sigma> (Inr ())
          = sides_of_rhs (make_side_rhs_tree_eff_st g
            (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v) \<sigma> (Inr ())"
    (is ?S)
proof -
  have et: "\<And>a u \<sigma>'. traverse_rhs (apply_etf_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) a u) \<sigma>'
                = map_lift restrict_local_resolved_q
                    (traverse_rhs (apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u) \<sigma>')"
    by (simp add: apply_etf_st_unit_of_transfer[OF reduces]
                  apply_etf_st_unit_of_transfer_contribution[OF reduces]
                  traverse_unit_edge_contribution_st traverse_unit_edge_tree_st)
  have es: "\<And>a u \<sigma>'. sides_of_rhs (apply_etf_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) a u) \<sigma>' (Inr ())
                = map_lift restrict_global_resolved_q
                    (traverse_rhs (apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u) \<sigma>')"
    by (simp add: apply_etf_st_unit_of_transfer[OF reduces]
                  apply_etf_st_unit_of_transfer_contribution[OF reduces]
                  traverse_unit_edge_contribution_st sides_unit_edge_tree_st_Inr)
  have ef: "\<And>a u \<sigma>'. sides_of_rhs (apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u) \<sigma>' = \<bottom>"
    by (simp add: apply_etf_st_unit_of_transfer_contribution[OF reduces])
  have nt: "\<And>fs as cl \<sigma>'. traverse_rhs (etf_st_enter (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) fs as cl) \<sigma>'
                = map_lift restrict_local_resolved_q
                    (traverse_rhs (etf_st_enter (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) fs as cl) \<sigma>')"
    by (simp add: etf_st_enter_unit_of_transfer etf_st_enter_unit_of_transfer_contribution
                  traverse_unit_edge_contribution_st traverse_unit_edge_tree_st)
  have ns: "\<And>fs as cl \<sigma>'. sides_of_rhs (etf_st_enter (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) fs as cl) \<sigma>' (Inr ())
                = map_lift restrict_global_resolved_q
                    (traverse_rhs (etf_st_enter (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) fs as cl) \<sigma>')"
    by (simp add: etf_st_enter_unit_of_transfer etf_st_enter_unit_of_transfer_contribution
                  traverse_unit_edge_contribution_st sides_unit_edge_tree_st_Inr)
  have nf: "\<And>fs as cl \<sigma>'. sides_of_rhs (etf_st_enter (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) fs as cl) \<sigma>' = \<bottom>"
    by (simp add: etf_st_enter_unit_of_transfer_contribution)
  have ct: "\<And>dst cc ex \<sigma>'. traverse_rhs (etf_combine_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex) \<sigma>'
                = map_lift restrict_local_resolved_q
                    (traverse_rhs (etf_combine_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex) \<sigma>')"
    by (simp del: etf_combine_st.simps
        add: etf_combine_st_unit_of_transfer etf_combine_st_unit_of_transfer_contribution
                  traverse_unit_combine_contribution_st traverse_unit_combine_tree_st)
  have cst: "\<And>dst cc ex \<sigma>'. sides_of_rhs (etf_combine_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex) \<sigma>' (Inr ())
                = map_lift restrict_global_resolved_q
                    (traverse_rhs (etf_combine_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex) \<sigma>')"
    by (simp del: etf_combine_st.simps
        add: etf_combine_st_unit_of_transfer etf_combine_st_unit_of_transfer_contribution
                  traverse_unit_combine_contribution_st sides_unit_combine_tree_st_Inr)
  have cf: "\<And>dst cc ex \<sigma>'. sides_of_rhs (etf_combine_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex) \<sigma>' = \<bottom>"
    by (simp del: etf_combine_st.simps add: etf_combine_st_unit_of_transfer_contribution)
  show ?T ?S
    using make_side_rhs_tree_eff_st_buffered_correspondence[OF et es ef nt ns nf ct cst cf]
    by simp_all
qed

lemma unit_etf_st_of_transfer_buffered_dep_aux:
  assumes reduces: "action_reduces tf_st"
  shows "dep_aux \<sigma> (make_side_rhs_tree_eff_st_buffered g
            (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v)
          = dep_aux \<sigma> (make_side_rhs_tree_eff_st g
            (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) bot s0_st () v)"
proof -
  have ed: "\<And>a u \<sigma>'. dep_aux \<sigma>' (apply_etf_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) a u)
                = dep_aux \<sigma>' (apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u)"
    by (simp add: apply_etf_st_unit_of_transfer[OF reduces]
                  apply_etf_st_unit_of_transfer_contribution[OF reduces]
                  dep_aux_unit_edge_contribution_st_eq_unit_edge_tree_st)
  have nd: "\<And>fs as cl \<sigma>'. dep_aux \<sigma>' (etf_st_enter (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) fs as cl)
                = dep_aux \<sigma>' (etf_st_enter (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) fs as cl)"
    by (simp add: etf_st_enter_unit_of_transfer etf_st_enter_unit_of_transfer_contribution
                  dep_aux_unit_edge_contribution_st_eq_unit_edge_tree_st)
  have cd: "\<And>dst cc ex \<sigma>'. dep_aux \<sigma>' (etf_combine_st (unit_etf_st_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex)
                = dep_aux \<sigma>' (etf_combine_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex)"
    by (simp del: etf_combine_st.simps
        add: etf_combine_st_unit_of_transfer etf_combine_st_unit_of_transfer_contribution
                  dep_aux_unit_combine_contribution_st_eq_unit_combine_tree_st)
  show ?thesis
    using make_side_rhs_tree_eff_st_buffered_dep_aux[OF ed nd cd] by simp
qed


lemma side_rg_fold_rhs_trees:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> side_rg t"
  shows "side_rg (fold_rhs_trees acc ts)"
  using assms
  by (induction ts arbitrary: acc) (auto intro: side_rg_seqcomp)

text \<open>
  \<^const>\<open>side_rg\<close> companion for the buffered generator: since a Side-free
  contribution tree contains no \<^const>\<open>Side\<close> node at all, \<^const>\<open>side_rg\<close>
  holds of it independently of any correspondence with the original
  generator, and the buffered generator's single trailing \<open>side_publish\<close>
  write is itself idempotent-restricted
  (\<open>map_lift_restrict_global_resolved_q_idem\<close>), so \<open>side_rg\<close> holds of
  the whole buffered tree under exactly the same three per-tree obligations
  \<open>side_rg_make_side_rhs_tree_eff_st\<close> already needs for the original.
\<close>
lemma side_rg_unit_edge_contribution_st:
  "side_rg (unit_edge_contribution_st is_bot_pred f u)"
  unfolding unit_edge_contribution_st_def by simp

lemma side_rg_unit_combine_contribution_st:
  "side_rg (unit_combine_contribution_st is_bot_pred gs dst cc ex)"
  unfolding unit_combine_contribution_st_def by simp

lemma side_rg_make_side_rhs_tree_eff_st_buffered:
  assumes "\<And>a u. side_rg (apply_etf_st etf a u)"
    and "\<And>cl fs as. side_rg (etf_st_enter etf fs as cl)"
    and "\<And>cc ex dst. side_rg (etf_combine_st etf dst cc ex)"
  shows "side_rg (make_side_rhs_tree_eff_st_buffered g etf bot0_st s0_st gseed v)"
  unfolding make_side_rhs_tree_eff_st_buffered_def Let_def
  apply (rule side_rg_seqcomp)
   apply (rule side_rg_fold_rhs_trees)
   unfolding side_contribution_trees_st_def
   using assms apply (auto split: prod.splits)
  done

lemma side_rg_unit_etf_st_contribution_of_transfer:
  assumes reduces: "action_reduces tf_st"
  shows "side_rg (make_side_rhs_tree_eff_st_buffered g
           (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) bot0_st s0_st gseed v)"
proof (rule side_rg_make_side_rhs_tree_eff_st_buffered)
  show "\<And>a u. side_rg (apply_etf_st (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) a u)"
    by (simp add: apply_etf_st_unit_of_transfer_contribution[OF reduces]
                  side_rg_unit_edge_contribution_st)
  show "\<And>cl fs as. side_rg (etf_st_enter
           (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) fs as cl)"
    by (simp add: etf_st_enter_unit_of_transfer_contribution side_rg_unit_edge_contribution_st)
  show "\<And>cc ex dst. side_rg (etf_combine_st
           (unit_etf_st_contribution_of_transfer is_bot_pred gs tf_st enter_st) dst cc ex)"
    by (simp del: etf_combine_st.simps
        add: etf_combine_st_unit_of_transfer_contribution side_rg_unit_combine_contribution_st)
qed

lemma side_rg_side_rhs_fold_eff_st:
  assumes "\<And>a u. side_rg (apply_etf_st etf a u)"
    and "\<And>cl fs as. side_rg (etf_st_enter etf fs as cl)"
    and "\<And>cc ex dst. side_rg (etf_combine_st etf dst cc ex)"
  shows "side_rg (side_rhs_fold_eff_st etf acc es ens cs)"
  unfolding side_rhs_fold_eff_st_def
  apply (rule side_rg_fold_rhs_trees)
  unfolding side_contribution_trees_st_def
  using assms by (auto split: prod.splits)

lemma side_rg_make_side_rhs_tree_eff_st:
  assumes "\<And>a u. side_rg (apply_etf_st etf a u)"
    and "\<And>cl fs as. side_rg (etf_st_enter etf fs as cl)"
    and "\<And>cc ex dst. side_rg (etf_combine_st etf dst cc ex)"
  shows "side_rg (make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v)"
  unfolding make_side_rhs_tree_eff_st_def Let_def
  by (simp add: side_rg_side_rhs_fold_eff_st[OF assms])

lemma traverse_side_rhs_fold_eff_st:
  "traverse_rhs (side_rhs_fold_eff_st etf acc es ens cs) \<sigma>_st =
   side_acc_eff_st etf acc \<sigma>_st es ens cs"
  unfolding side_rhs_fold_eff_st_def side_acc_eff_st_def
  by (rule traverse_fold_rhs_trees)

lemma eq_side_cfg_T_eff_st:
  "eq (side_cfg_T_eff_st g etf bot0_st s0_st gseed) v \<sigma>_st =
     side_acc_eff_st etf
       (if v = cfg_entry g then Lifted (bot0_st \<squnion> restrict_local_resolved_q s0_st) else Bot)
       \<sigma>_st (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  unfolding side_cfg_T_eff_st_def make_side_rhs_tree_eff_st_def
  by (simp add: traverse_side_rhs_fold_eff_st Let_def)

subsection \<open>Tree denotation commutation for folds\<close>


lemma side_contribution_trees_rel:
  assumes edge: "\<And>u a. (u, a) \<in> set es \<Longrightarrow>
      R (apply_etf_st etf_st a u) (apply_etf etf a u)"
    and enter: "\<And>cl fs as. (cl, fs, as) \<in> set ens \<Longrightarrow>
      R (etf_st_enter etf_st fs as cl) (etf_enter etf fs as cl)"
    and combine: "\<And>cc dst ex. (cc, dst, ex) \<in> set cs \<Longrightarrow>
      R (etf_combine_st etf_st dst cc ex) (etf_combine etf dst cc ex)"
  shows "list_all2 R
      (side_contribution_trees_st etf_st es ens cs)
      (side_contribution_trees etf es ens cs)"
proof -
  have edges: "list_all2 R
      (map (\<lambda>(u, a). apply_etf_st etf_st a u) es)
      (map (\<lambda>(u, a). apply_etf etf a u) es)"
    using edge by (induction es) (auto split: prod.splits)
  have entries: "list_all2 R
      (map (\<lambda>(cl, fs, as). etf_st_enter etf_st fs as cl) ens)
      (map (\<lambda>(cl, fs, as). etf_enter etf fs as cl) ens)"
    using enter by (induction ens) (auto split: prod.splits)
  have combines: "list_all2 R
      (map (\<lambda>(cc, dst, ex). etf_combine_st etf_st dst cc ex) cs)
      (map (\<lambda>(cc, dst, ex). etf_combine etf dst cc ex) cs)"
    using combine by (induction cs) (auto split: prod.splits)
  have suffix: "list_all2 R
      (map (\<lambda>(cl, fs, as). etf_st_enter etf_st fs as cl) ens @
       map (\<lambda>(cc, dst, ex). etf_combine_st etf_st dst cc ex) cs)
      (map (\<lambda>(cl, fs, as). etf_enter etf fs as cl) ens @
       map (\<lambda>(cc, dst, ex). etf_combine etf dst cc ex) cs)"
    by (rule list_all2_appendI[OF entries combines])
  show ?thesis
    unfolding side_contribution_trees_st_def side_contribution_trees_def
    by (rule list_all2_appendI[OF edges suffix])
qed
lemma map_lift_fun_of_resolved_st_q_for_sup [simp]:
  "map_lift (fun_of_resolved_st_q_for gs) (a \<squnion> b) =
   map_lift (fun_of_resolved_st_q_for gs) a \<squnion> map_lift (fun_of_resolved_st_q_for gs) b"
  by (cases a; cases b; simp)

lemma map_lift_fun_of_resolved_st_q_for_mono:
  assumes "x \<le> y"
  shows "map_lift (fun_of_resolved_st_q_for gs) x \<le> map_lift (fun_of_resolved_st_q_for gs) y"
  using assms by (cases x; cases y; simp add: fun_of_resolved_st_q_for_mono)

lemma fold_rhs_values_fun_of_resolved_st_q_for:
  assumes rel: "list_all2
    (\<lambda>t_st t. \<forall>\<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
                         traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)) ts_st ts"
  shows "map_lift (fun_of_resolved_st_q_for gs) (fold_rhs_values acc_st \<sigma>_st ts_st) =
         fold_rhs_values (map_lift (fun_of_resolved_st_q_for gs) acc_st) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) ts"
  using rel
proof (induction arbitrary: acc_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have head: "map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
              traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
    using Cons.hyps(1) by blast
  show ?case
    by (simp add: head Cons.IH sup_fun_def comp_def)
qed

lemma side_acc_eff_st_fun_of_resolved_st_q_for:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (side_acc_eff_st etf_st acc_st \<sigma>_st es ens cs) =
         side_acc_eff etf (map_lift (fun_of_resolved_st_q_for gs) acc_st) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) es ens cs"
proof -
  have trees: "list_all2
      (\<lambda>t_st t. \<forall>\<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
                           traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st))
      (side_contribution_trees_st etf_st es ens cs)
      (side_contribution_trees etf es ens cs)"
    apply (rule side_contribution_trees_rel)
      subgoal using tr_edge by blast
      subgoal using tr_enter by blast
      subgoal using tr_comb by blast
    done
  show ?thesis
    unfolding side_acc_eff_st_def side_acc_eff_def
    by (rule fold_rhs_values_fun_of_resolved_st_q_for[OF trees])
qed

lemma sides_fold_rhs_trees_acc_indep:
  "sides_of_rhs (fold_rhs_trees acc1 ts) \<sigma> =
   sides_of_rhs (fold_rhs_trees acc2 ts) \<sigma>"
proof (induction ts arbitrary: acc1 acc2)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (rule ext)
    fix x
    have rest:
      "sides_of_rhs
         (fold_rhs_trees (acc1 \<squnion> traverse_rhs t \<sigma>) ts) \<sigma> x =
       sides_of_rhs
         (fold_rhs_trees (acc2 \<squnion> traverse_rhs t \<sigma>) ts) \<sigma> x"
      using Cons.IH[of "acc1 \<squnion> traverse_rhs t \<sigma>"
                       "acc2 \<squnion> traverse_rhs t \<sigma>"]
      by (rule fun_cong)
    show "sides_of_rhs (fold_rhs_trees acc1 (t # ts)) \<sigma> x =
          sides_of_rhs (fold_rhs_trees acc2 (t # ts)) \<sigma> x"
      by (simp add: sides_of_rhs_seqcomp_at rest)
  qed
qed

lemma sides_side_rhs_fold_eff_st_acc_indep:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
  shows "sides_of_rhs (side_rhs_fold_eff_st etf_st acc1 es ens cs) \<sigma>
         = sides_of_rhs (side_rhs_fold_eff_st etf_st acc2 es ens cs) \<sigma>"
  unfolding side_rhs_fold_eff_st_def
  by (rule sides_fold_rhs_trees_acc_indep)


lemma sides_eff_fold_st_edge_step:
  "sides_of_rhs (side_rhs_fold_eff_st etf_st acc ((u, a) # es) ens cs) \<sigma> gk
   = sides_of_rhs (apply_etf_st etf_st a u) \<sigma> gk
     \<squnion> sides_of_rhs (side_rhs_fold_eff_st etf_st acc es ens cs) \<sigma> gk"
  by (metis (no_types, lifting) side_rhs_fold_eff_st_simps(2) sides_of_rhs_seqcomp_at
      sides_side_rhs_fold_eff_st_acc_indep)

lemma sides_eff_fold_st_enter_step:
  "sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] ((cl, fs, as) # ens) cs) \<sigma> gk
   = sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma> gk
     \<squnion> sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] ens cs) \<sigma> gk"
  by (metis (no_types, lifting) side_rhs_fold_eff_st_simps(3) sides_of_rhs_seqcomp_at
      sides_side_rhs_fold_eff_st_acc_indep)

lemma sides_eff_fold_st_combine_step:
  "sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] [] ((cc, dst, ex) # cs)) \<sigma> gk
   = sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma> gk
     \<squnion> sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] [] cs) \<sigma> gk"
  by (metis (no_types, lifting) side_rhs_fold_eff_st_simps(4) sides_of_rhs_seqcomp_at
      sides_side_rhs_fold_eff_st_acc_indep)

lemma fold_rhs_trees_sides_fun_of_resolved_st_q_for:
  assumes rel: "list_all2
    (\<lambda>t_st t. \<forall>\<sigma>_st gk. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs t_st \<sigma>_st gk) =
                            sides_of_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk) ts_st ts"
  shows "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (fold_rhs_trees acc_st ts_st) \<sigma>_st gk) =
         sides_of_rhs (fold_rhs_trees acc ts) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
  using rel
proof (induction arbitrary: acc_st acc)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have head: "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs t_st \<sigma>_st gk) =
              sides_of_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
    using Cons.hyps(1) by blast
  have rest: "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) \<sigma>_st gk) =
      sides_of_rhs (fold_rhs_trees (acc \<squnion> traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)) ts)
        (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp_at head rest comp_def)
qed

lemma side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gk. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gk)
                = sides_of_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
  assumes sd_enter:
    "\<And>cl fs as \<sigma>_st gk. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gk)
                = sides_of_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
  assumes sd_comb:
    "\<And>cc ex dst \<sigma>_st gk. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gk)
                = sides_of_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
  shows "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (side_rhs_fold_eff_st etf_st acc es ens cs) \<sigma>_st gk)
         = sides_of_rhs (side_rhs_fold_eff etf (map_lift (fun_of_resolved_st_q_for gs) acc) es ens cs)
             (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
proof -
  have trees: "list_all2
      (\<lambda>t_st t. \<forall>\<sigma>_st gk. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs t_st \<sigma>_st gk) =
                              sides_of_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk)
      (side_contribution_trees_st etf_st es ens cs)
      (side_contribution_trees etf es ens cs)"
    apply (rule side_contribution_trees_rel)
      subgoal using sd_edge by blast
      subgoal using sd_enter by blast
      subgoal using sd_comb by blast
    done
  show ?thesis
    unfolding side_rhs_fold_eff_st_def side_rhs_fold_eff_def
    by (rule fold_rhs_trees_sides_fun_of_resolved_st_q_for[OF trees])
qed


lemma fold_rhs_trees_dep_fun_of_resolved_st_q_for:
  assumes rel: "list_all2
    (\<lambda>t_st t.
      (\<forall>\<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
                    traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)) \<and>
      (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t_st = dep_aux \<sigma>2 t)) ts_st ts"
  shows "dep_aux \<sigma>_st (fold_rhs_trees acc_st ts_st) =
         dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) (fold_rhs_trees (map_lift (fun_of_resolved_st_q_for gs) acc_st) ts)"
  using rel
proof (induction arbitrary: acc_st \<sigma>_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have dep: "dep_aux \<sigma>_st t_st = dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) t"
    using Cons.hyps(1) by blast
  have tr: "map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
            traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
    using Cons.hyps(1) by blast
  have acc_tr: "map_lift (fun_of_resolved_st_q_for gs) (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) =
      map_lift (fun_of_resolved_st_q_for gs) acc_st \<squnion> traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
    by (simp add: tr)
  have ih': "dep_aux \<sigma>_st
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) =
      dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)
        (fold_rhs_trees (map_lift (fun_of_resolved_st_q_for gs) (acc_st \<squnion> traverse_rhs t_st \<sigma>_st)) ts)"
    by (rule Cons.IH)
  have ih: "dep_aux \<sigma>_st
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) =
      dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)
        (fold_rhs_trees (map_lift (fun_of_resolved_st_q_for gs) acc_st \<squnion>
          traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)) ts)"
    using ih' acc_tr by simp
  show ?case
    by (simp add: dep_aux_seqcomp dep ih comp_def)
qed

lemma dep_aux_side_rhs_fold_eff_st_eq:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_enter:
    "\<And>cl fs as \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_st_enter etf_st fs as cl)
                = dep_aux \<sigma>2 (etf_enter etf fs as cl)"
  assumes dep_comb:
    "\<And>cc ex dst \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st dst cc ex)
                = dep_aux \<sigma>2 (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st acc es ens cs)
       = dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) (side_rhs_fold_eff etf (map_lift (fun_of_resolved_st_q_for gs) acc) es ens cs)"
proof -
  have trees: "list_all2
      (\<lambda>t_st t.
        (\<forall>\<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs t_st \<sigma>_st) =
                      traverse_rhs t (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)) \<and>
        (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t_st = dep_aux \<sigma>2 t))
      (side_contribution_trees_st etf_st es ens cs)
      (side_contribution_trees etf es ens cs)"
    apply (rule side_contribution_trees_rel)
      subgoal using tr_edge dep_edge by blast
      subgoal using tr_enter dep_enter by blast
      subgoal using tr_comb dep_comb by blast
    done
  show ?thesis
    unfolding side_rhs_fold_eff_st_def side_rhs_fold_eff_def
    by (rule fold_rhs_trees_dep_fun_of_resolved_st_q_for[OF trees])
qed


lemma dep_aux_make_side_rhs_tree_eff_st_eq:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_enter:
    "\<And>cl fs as \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_st_enter etf_st fs as cl)
                = dep_aux \<sigma>2 (etf_enter etf fs as cl)"
  assumes dep_comb:
    "\<And>cc ex dst \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st dst cc ex)
                = dep_aux \<sigma>2 (etf_combine etf dst cc ex)"
  shows "dep_aux \<sigma>_st (make_side_rhs_tree_eff_st g etf_st bot0_st s0_st gseed v)
       = dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)
           (make_side_rhs_tree_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed v)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using True
    by (simp add: dep_aux_side_rhs_fold_eff_st_eq[OF tr_edge tr_enter tr_comb dep_edge dep_enter dep_comb])
next
  case False
  show ?thesis unfolding make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using False
    by (simp add: dep_aux_side_rhs_fold_eff_st_eq[OF tr_edge tr_enter tr_comb dep_edge dep_enter dep_comb])
qed


subsection \<open>Generic \<open>st\<close> post-solution transport\<close>

text \<open>
  Every executable generator variant maps its \<open>'a resolved_st_q\<close> post-solution to an abstract
  \<^const>\<open>part_post_solution\<close> under \<^const>\<open>fun_of_resolved_st_q_for\<close>, and the lifting is identical:
  it depends only on three commutation facts about the specific generator --- \<open>eq\<close>,
  \<open>sides_of_rhs\<close>, and \<open>dep_aux\<close> commute with \<^const>\<open>fun_of_resolved_st_q_for\<close>.  This lemma packages
  that lifting once; each concrete generator supplies the three facts and applies it.
\<close>

lemma part_post_solution_st_to_abs_transport:
  fixes T_st :: "'u \<Rightarrow> ('u, 'g, ('a::bounded_semilattice_sup_bot) resolved_st_q) strategy_tree"
    and T_abs :: "'u \<Rightarrow> ('u, 'g, 'a abs_state) strategy_tree"
  assumes EQ: "\<And>v \<sigma>. fun_of_resolved_st_q_for gs (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_resolved_st_q_for gs (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k)) (T_abs v)"
    and pp: "part_post_solution T_st x sigma_st vars"
  shows "part_post_solution T_abs x (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using pp by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) v \<subseteq> vars"
      using pp v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) (Inl v)"
    proof -
      have le_st: "eq T_st v sigma_st \<le> sigma_st (Inl v)" using pp v_in by simp
      show ?thesis using fun_of_resolved_st_q_for_mono[where gs=gs, OF le_st] EQ by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using pp v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) k"
        using fun_of_resolved_st_q_for_mono[where gs=gs, OF le_st] SIDES by simp
    qed
  qed
qed

text \<open>
  The exact analogue: an \<^emph>\<open>exact\<close> \<^const>\<open>part_solution\<close> of the executable generator maps,
  under \<^const>\<open>fun_of_resolved_st_q_for\<close>, to an exact \<^const>\<open>part_solution\<close> of its abstract image.  The
  two abbreviations differ only in the \<open>eq\<close> conjunct (\<open>=\<close> vs \<open>\<le>\<close>); the same three
  commutation facts carry it, with the \<open>eq\<close> branch using the equality directly.  This is
  the enabler for certifying a concrete run whose exactness is established per run
  (via a decidable reverse-inequality \<open>eval\<close> check) against an abstract soundness
  theorem that needs an exact fixpoint.
\<close>

lemma part_solution_st_to_abs_transport:
  fixes T_st :: "'u \<Rightarrow> ('u, 'g, ('a::bounded_semilattice_sup_bot) resolved_st_q) strategy_tree"
    and T_abs :: "'u \<Rightarrow> ('u, 'g, 'a abs_state) strategy_tree"
  assumes EQ: "\<And>v \<sigma>. fun_of_resolved_st_q_for gs (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_resolved_st_q_for gs (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_resolved_st_q_for gs (\<sigma> k)) (T_abs v)"
    and ps: "part_solution T_st x sigma_st vars"
  shows "part_solution T_abs x (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using ps by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) v \<subseteq> vars"
      using ps v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) = (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) (Inl v)"
    proof -
      have eq_st: "eq T_st v sigma_st = sigma_st (Inl v)" using ps v_in by simp
      show ?thesis
        using EQ[where v=v and \<sigma>=sigma_st] eq_st by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using ps v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_resolved_st_q_for gs (sigma_st k)) k"
        using fun_of_resolved_st_q_for_mono[where gs=gs, OF le_st] SIDES by simp
    qed
  qed
qed

subsection \<open>Transport: executable effectful post-solution to abstract effectful post-solution\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
  fixes g :: cfg
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q lifted) effectful_st_transfer"
  fixes etf :: "('g, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st :: "'a resolved_st_q"
  fixes gseed :: 'g
  assumes tr_edge:
    "\<And>a u \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
               = sides_of_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
  assumes sd_enter:
    "\<And>cl fs as \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
                = sides_of_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
  assumes sd_comb:
    "\<And>cc ex dst \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gg)
                = sides_of_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_enter:
    "\<And>cl fs as \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_st_enter etf_st fs as cl)
                = dep_aux \<sigma>2 (etf_enter etf fs as cl)"
  assumes dep_comb:
    "\<And>cc ex dst \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st dst cc ex)
                = dep_aux \<sigma>2 (etf_combine etf dst cc ex)"
begin


private lemma fun_of_resolved_st_q_for_eq_cfg_eff_st:
  "map_lift (fun_of_resolved_st_q_for gs) (eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st) =
   eq (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed) v (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  unfolding eq_side_cfg_T_eff_st eq_side_cfg_T_eff
  by (cases "v = cfg_entry g")
     (simp_all add: side_acc_eff_st_fun_of_resolved_st_q_for[OF tr_edge tr_enter tr_comb])

text \<open>
  Rather than replaying the raw \<open>Side\<close>-node function-update by hand, this uses
  \<open>side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for\<close> pointwise at the
  entry node's \<open>gseed\<close>-override key: both sides update the same key with the same
  join, so the update commutes with \<open>map_lift (fun_of_resolved_st_q_for gs)\<close>
  exactly as the un-updated fold already does.
\<close>
private lemma fun_of_resolved_st_q_for_sides_cfg_eff_st:
  "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v) \<sigma>_st gkey)
   = sides_of_rhs (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed v)
       (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gkey"
proof (cases "v = cfg_entry g")
  case True
  have fold_sides:
    "\<And>gk. map_lift (fun_of_resolved_st_q_for gs)
        (sides_of_rhs (side_rhs_fold_eff_st etf_st (Lifted (bot0_st \<squnion> restrict_local_resolved_q s0_st))
          (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st gk)
      = sides_of_rhs (side_rhs_fold_eff etf (Lifted (fun_of_resolved_st_q_for gs bot0_st \<squnion> restrict_local_for gs (fun_of_resolved_st_q_for gs s0_st)))
          (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
        (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gk"
    by (simp add: side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for[OF sd_edge sd_enter sd_comb])
  show ?thesis
    unfolding side_cfg_T_eff_st_def side_cfg_T_eff_def
      make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using True
    by (cases "gkey = Inr gseed") (simp_all add: fold_sides Let_def)
next
  case False
  show ?thesis unfolding side_cfg_T_eff_st_def side_cfg_T_eff_def
    make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using False
    by (simp add: side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for[OF sd_edge sd_enter sd_comb])
qed


text \<open>
  An executable post-solution of @{const side_cfg_T_eff_st} maps to a
  @{const part_post_solution} of @{const side_cfg_T_eff} when per-tree traverse,
  side, and dependency denotations commute through @{const fun_of_resolved_st_q_for}.
\<close>

theorem part_post_solution_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed)
           x (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  have deps: "\<And>v. v \<in> vars \<Longrightarrow>
      dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v
    = dep\<^sub>L (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed)
             (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) v"
  proof -
    fix v
    have eq: "dep_aux \<sigma>_st (make_side_rhs_tree_eff_st g etf_st bot0_st s0_st gseed v) =
              dep_aux (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)
                (make_side_rhs_tree_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed v)"
      by (rule dep_aux_make_side_rhs_tree_eff_st_eq[OF tr_edge tr_enter tr_comb dep_edge dep_enter dep_comb])
    show "dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v =
          dep\<^sub>L (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed)
                 (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) v"
      by (simp add: dep\<^sub>L_def dep_def side_cfg_T_eff_st_def side_cfg_T_eff_def eq)
  qed
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed)
              (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) v \<subseteq> vars"
      using pp_st v_in deps[OF v_in] by auto
    show "eq (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed) v
             (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) \<le> (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st
                   \<le> \<sigma>_st (Inl v)"
        using pp_st v_in by simp
      show ?thesis
        using map_lift_fun_of_resolved_st_q_for_mono[where gs=gs, OF le_st]
              fun_of_resolved_st_q_for_eq_cfg_eff_st[where v=v] by simp
    qed
    show "sides_of_rhs (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed v)
             (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) \<le> map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v) \<sigma>_st k \<le> \<sigma>_st k"
        using pp_st v_in by (simp add: le_fun_def)
      show "sides_of_rhs
               (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) gseed v)
               (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) k \<le> (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) k"
        using map_lift_fun_of_resolved_st_q_for_mono[where gs=gs, OF le_st]
              fun_of_resolved_st_q_for_sides_cfg_eff_st[where v=v and gkey=k] by simp
    qed
  qed
qed

end


lemma map_lift_fun_of_resolved_st_q_for_map_lift_restrict_local_resolved_q:
  "map_lift (fun_of_resolved_st_q_for gs) (map_lift restrict_local_resolved_q x) =
   map_lift (restrict_local_for gs) (map_lift (fun_of_resolved_st_q_for gs) x)"
  by (cases x; simp)

lemma part_post_solution_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::sound_domain) resolved_st_q lifted) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes Fe_st :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st :: "'a resolved_st_q"
  fixes is_bot_pred :: "'a resolved_st_q \<Rightarrow> bool"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree gs (F a) u"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree gs dst cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st is_bot_pred (F_st a) u"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st is_bot_pred gs dst cc ex"
  assumes commute: "\<And>a s. fun_of_resolved_st_q_for gs (F_st a s) = F a (fun_of_resolved_st_q_for gs s)"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
  assumes enter_st: "\<And>cl fs as. etf_st_enter etf_st fs as cl = unit_edge_tree_st is_bot_pred (Fe_st fs as) cl"
  assumes commute_enter: "\<And>fs as s. fun_of_resolved_st_q_for gs (Fe_st fs as s) = Fe fs as (fun_of_resolved_st_q_for gs s)"
  assumes is_bot_pred_exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_st g etf_st bot0_st s0_st ()) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff gs g etf (fun_of_resolved_st_q_for gs bot0_st) (fun_of_resolved_st_q_for gs s0_st) ())
           x (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) vars"
proof -
  interpret sound_rhs_generator_exec gs etf F etf_st F_st is_bot_pred
    using edge comb edge_st comb_st commute is_bot_pred_exact by unfold_locales
  have tr_edge:
    "\<And>a u \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  proof -
    fix a u \<sigma>_st
    show "map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
      unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
      by (simp add: map_lift_fun_of_resolved_st_q_for_map_lift_restrict_local_resolved_q
                    res_edge_st_fun_of_resolved_st_q_for
                      [where f = "F_st a" and F = "F a", OF commute[of a] is_bot_pred_exact])
  qed
  have tr_comb:
    "\<And>cc ex dst \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
     = traverse_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
    unfolding comb_st comb traverse_unit_combine_tree_st traverse_unit_combine_tree
    by (simp add: map_lift_fun_of_resolved_st_q_for_map_lift_restrict_local_resolved_q
                  res_combine_st_fun_of_resolved_st_q_for[OF is_bot_pred_exact])
  have sd_edge:
    "\<And>a u \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
     = sides_of_rhs (apply_etf etf a u) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
    using sides_apply_etf_st .
  have sd_comb:
    "\<And>cc ex dst \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gg)
     = sides_of_rhs (etf_combine etf dst cc ex) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
    using sides_etf_combine_st .
  have dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
     = dep_aux \<sigma>2 (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  have dep_comb:
    "\<And>cc ex dst \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st dst cc ex)
     = dep_aux \<sigma>2 (etf_combine etf dst cc ex)"
    by (subst comb_st, subst comb, simp add: dep_aux_unit_combine_tree_st)
  have tr_enter:
    "\<And>cl fs as \<sigma>_st. map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
     = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  proof -
    fix cl fs as \<sigma>_st
    show "map_lift (fun_of_resolved_st_q_for gs) (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
     = traverse_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
      unfolding enter_st enter traverse_unit_edge_tree_st traverse_unit_edge_tree
      by (simp add: map_lift_fun_of_resolved_st_q_for_map_lift_restrict_local_resolved_q
                    res_edge_st_fun_of_resolved_st_q_for
                      [where f = "Fe_st fs as" and F = "Fe fs as", OF commute_enter[of fs as]])
  qed
  have sd_enter:
    "\<And>cl fs as \<sigma>_st gg. map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
     = sides_of_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
  proof -
    fix cl fs as and \<sigma>_st :: "pp + unit \<Rightarrow> 'a resolved_st_q lifted" and gg
    show "map_lift (fun_of_resolved_st_q_for gs) (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
        = sides_of_rhs (etf_enter etf fs as cl) (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st) gg"
    proof (cases gg)
      case (Inl u')
      then show ?thesis
        by (simp add: enter_st enter sides_unit_edge_tree_st_Inl sides_unit_edge_tree_Inl
                      Let_def bot_fun_def)
    next
      case (Inr g')
      then have gg_eq: "gg = Inr ()" by simp
      show ?thesis
        unfolding gg_eq enter_st enter sides_unit_edge_tree_st_Inr sides_unit_edge_tree_Inr
                  res_edge_st_def res_edge_def o_def
        by (cases "\<sigma>_st (Inl cl)"; cases "\<sigma>_st (Inr ())";
            simp add: commute_enter normalize_lift_def split: if_splits)
    qed
  qed
  have dep_enter:
    "\<And>cl fs as \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_st_enter etf_st fs as cl)
     = dep_aux \<sigma>2 (etf_enter etf fs as cl)"
    by (simp add: enter_st enter dep_aux_unit_edge_tree_st)
  show ?thesis
    using part_post_solution_st_to_abs_eff[OF tr_edge tr_enter tr_comb sd_edge sd_enter sd_comb
        dep_edge dep_enter dep_comb pp_st]
    by simp
qed



lemma map_lift_fun_of_resolved_st_q_for_map_lift_restrict_global_resolved_q:
  "map_lift (fun_of_resolved_st_q_for gs) (map_lift restrict_global_resolved_q x) =
   map_lift (restrict_global_for gs) (map_lift (fun_of_resolved_st_q_for gs) x)"
  by (cases x; simp)

lemma inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs:
  fixes sigma_st :: "pp + unit \<Rightarrow> ('a::sound_domain) resolved_st_q lifted"
  assumes rg: "\<And>gg. sigma_st (Inr gg) = map_lift restrict_global_resolved_q (sigma_st (Inr gg))"
  shows "inr_slot_locals_bot gs (map_lift (fun_of_resolved_st_q_for gs) \<circ> sigma_st)"
  unfolding inr_slot_locals_bot_iff_Inr_restrict_global
proof (intro allI)
  fix gg
  show "(map_lift (fun_of_resolved_st_q_for gs) \<circ> sigma_st) (Inr gg)
      = map_lift (restrict_global_for gs) ((map_lift (fun_of_resolved_st_q_for gs) \<circ> sigma_st) (Inr gg))"
  proof -
    have "map_lift (fun_of_resolved_st_q_for gs) (sigma_st (Inr gg))
        = map_lift (fun_of_resolved_st_q_for gs) (map_lift restrict_global_resolved_q (sigma_st (Inr gg)))"
      using rg by simp
    thus ?thesis
      by (simp add: o_def map_lift_fun_of_resolved_st_q_for_map_lift_restrict_global_resolved_q)
  qed
qed

text \<open>
  The unit equation system has every reachable \<open>Side\<close> contribution
  \<open>restrict_global_resolved_q\<close>-shaped.  This is the structural precondition the
  side-effecting solver consumes to keep its \<open>Inr\<close> slots \<open>restrict_global_resolved_q\<close>-shaped
  (the solver-side induction lives where the side solver's \<open>solve\<close> is in scope).
\<close>

lemma side_rg_side_cfg_T_eff_st_unit:
  fixes etf_st :: "(unit, ('a::sound_domain) resolved_st_q lifted) effectful_st_transfer"
  fixes is_bot_pred :: "'a resolved_st_q \<Rightarrow> bool"
  assumes edge_st: "\<And>a u. \<exists>f. apply_etf_st etf_st a u = unit_edge_tree_st is_bot_pred f u"
  assumes enter_st: "\<And>cl fs as. \<exists>f. etf_st_enter etf_st fs as cl = unit_edge_tree_st is_bot_pred f cl"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st is_bot_pred gs dst cc ex"
  shows "side_rg (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v)"
  unfolding side_cfg_T_eff_st_def
proof (rule side_rg_make_side_rhs_tree_eff_st)
  fix a u show "side_rg (apply_etf_st etf_st a u)"
    using edge_st[of a u] side_rg_unit_edge_tree_st by auto
next
  fix cl fs as show "side_rg (etf_st_enter etf_st fs as cl)"
    using enter_st side_rg_unit_edge_tree_st by metis
next
  fix cc ex dst show "side_rg (etf_combine_st etf_st dst cc ex)"
    using comb_st[where cc=cc and ex=ex and dst=dst] side_rg_unit_combine_tree_st by auto
qed

end








