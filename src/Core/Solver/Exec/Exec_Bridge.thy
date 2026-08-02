theory Exec_Bridge
  imports Exec_Backward Exec_Placement TD_Side_Eff_Bounds TD_Side_RHS_Generator Constraint_System
begin

section \<open>Executable equation-system refinement\<close>

text \<open>
  Generic (domain-agnostic) bridge between executable st side-effecting equation
  systems and abstract abs_state side_cfg_T_eff systems.  Domain theories discharge
  per-tree traverse and side denotation commutation through fun_of_resolved_st_q_for is_global.
\<close>

subsection \<open>fun_of_resolved_st_q_for is_global homomorphisms for local/global projections\<close>

lemma fun_of_resolved_st_q_for_restrict_local_abs [simp]:
  "fun_of_resolved_st_q_for is_global (restrict_local_resolved_q s) = restrict_local (fun_of_resolved_st_q_for is_global s)"
  unfolding restrict_local_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_restrict_global_abs [simp]:
  "fun_of_resolved_st_q_for is_global (restrict_global_resolved_q s) = restrict_global (fun_of_resolved_st_q_for is_global s)"
  unfolding restrict_global_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_combine_abs [simp]:
  "fun_of_resolved_st_q_for is_global (combine_resolved_st_q sc se) =
     combine_abs is_global (fun_of_resolved_st_q_for is_global sc)
       (fun_of_resolved_st_q_for is_global se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for is_global (combine_resolved_st_q sc se) x =
      combine_abs is_global (fun_of_resolved_st_q_for is_global sc)
        (fun_of_resolved_st_q_for is_global se) x"
    by (cases "is_global x"; simp add: combine_abs_def)
qed

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
| "apply_etf_st etf (EA_Assume b)    u = etf_st_assume etf b u"
| "apply_etf_st etf (EA_AssumeNot b) u = etf_st_assume_not etf b u"
| "apply_etf_st etf (EA_Ret e p) u =
     (case e of None \<Rightarrow> etf_st_nop etf u | Some a \<Rightarrow> etf_st_assign etf ret_var a u)"

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

definition unit_edge_tree_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> 'a resolved_st_q) \<Rightarrow> (unit, 'a resolved_st_q) st_edge_tf_tree"
where
  "unit_edge_tree_st f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global_resolved_q res)
         (Answer (restrict_local_resolved_q res))))"

definition unit_combine_tree_st ::
  "vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a::bounded_semilattice_sup_bot resolved_st_q) strategy_tree"
where
  "unit_combine_tree_st dst cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = combine_collect_resolved_for_q is_global dst (sc \<squnion> g) (se \<squnion> g) in
       Side () (restrict_global_resolved_q res)
         (Answer (restrict_local_resolved_q res)))))"

subsection \<open>Placement-aware executable trees\<close>

text \<open>
  The owner and finite location scope are supplied per CFG node.  The executable
  state remains keyed by @{typ location}; only the placement policy observes the
  owner-qualified key.
\<close>

definition unit_edge_tree_st_placed ::
  "(pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => ('a::bounded_semilattice_sup_bot resolved_st_q => 'a resolved_st_q)
   => (unit, 'a resolved_st_q) st_edge_tf_tree"
where
  "unit_edge_tree_st_placed owner_of locations_of keep_local publish_side f u =
    QueryL u (\<lambda>su. QueryG () (\<lambda>g.
      let res = f (su \<squnion> g) in
      Side ()
        (project_resolved_on (owner_of u) (locations_of u) publish_side res)
        (Answer
          (project_resolved_on (owner_of u) (locations_of u) keep_local res))))"

definition unit_combine_tree_st_placed ::
  "(vname => bool)
   => (pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => vname option => pp => pp
   => (pp, unit, 'a::bounded_semilattice_sup_bot resolved_st_q) strategy_tree"
where
  "unit_combine_tree_st_placed source_global owner_of locations_of
      keep_local publish_side dst cc ex =
    QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
      let res =
        combine_collect_resolved_for_q source_global dst (sc \<squnion> g)
          (se \<squnion> g)
      in Side ()
        (project_resolved_on
          (owner_of cc) (locations_of cc) publish_side res)
        (Answer
          (project_resolved_on
            (owner_of cc) (locations_of cc) keep_local res)))))"

definition unit_etf_st_of_transfer_placed ::
  "(vname => bool)
   => (pp => pname)
   => (pp => location list)
   => (scoped_location => bool)
   => (scoped_location => bool)
   => (edge_action
     => 'a::bounded_semilattice_sup_bot resolved_st_q
     => 'a resolved_st_q)
   => (vname list => aexp list
     => 'a resolved_st_q => 'a resolved_st_q)
   => (unit, 'a resolved_st_q) effectful_st_transfer"
where
  "unit_etf_st_of_transfer_placed source_global owner_of locations_of
      keep_local publish_side tf_st enter_st =
    \<lparr> etf_st_nop =
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st EA_Nop),
      etf_st_assign = (\<lambda>x e.
        unit_edge_tree_st_placed owner_of locations_of keep_local
          publish_side (tf_st (EA_Assign x e))),
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
  assumes ret_none: "\<And>p. tf_st (EA_Ret None p) = tf_st EA_Nop"
    and ret_some:
      "\<And>a p. tf_st (EA_Ret (Some a) p) =
        tf_st (EA_Assign ret_var a)"
  shows
    "apply_etf_st
      (unit_etf_st_of_transfer_placed source_global owner_of locations_of
        keep_local publish_side tf_st enter_st) a u =
      unit_edge_tree_st_placed owner_of locations_of keep_local publish_side
        (tf_st a) u"
  unfolding unit_etf_st_of_transfer_placed_def
  by (cases a) (auto simp: ret_none ret_some split: option.splits)

lemma etf_st_enter_unit_of_transfer_placed:
  "etf_st_enter
    (unit_etf_st_of_transfer_placed source_global owner_of locations_of
      keep_local publish_side tf_st enter_st) xs es u =
    unit_edge_tree_st_placed owner_of locations_of keep_local publish_side
      (enter_st xs es) u"
  unfolding unit_etf_st_of_transfer_placed_def by simp

lemma traverse_unit_edge_tree_st_placed:
  "traverse_rhs
    (unit_edge_tree_st_placed owner_of locations_of
      keep_local publish_side f u) sigma_st =
    project_resolved_on (owner_of u) (locations_of u) keep_local
      (f (sigma_st (Inl u) \<squnion> sigma_st (Inr ())))"
  unfolding unit_edge_tree_st_placed_def by (simp add: Let_def)

lemma sides_unit_edge_tree_st_placed_Inr:
  "sides_of_rhs
    (unit_edge_tree_st_placed owner_of locations_of
      keep_local publish_side f u) sigma_st (Inr ()) =
    project_resolved_on (owner_of u) (locations_of u) publish_side
      (f (sigma_st (Inl u) \<squnion> sigma_st (Inr ())))"
  unfolding unit_edge_tree_st_placed_def by (simp add: Let_def)

subsection \<open>Unit-global executable transfer-record factory\<close>

text \<open>
  Executable mirror of the abstract-side @{const unit_etf_of_transfer}: builds an
  \<open>effectful_st_transfer\<close> record from a single dispatch function and an enter function,
  both at @{typ "'a resolved_st_q"}.  Domain instances (\<open>Sign_Exec\<close>, \<open>Ivl_Exec\<close>) instantiate this
  once instead of hand-writing the six-field record.
\<close>

definition unit_etf_st_of_transfer ::
  "(edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (vname list \<Rightarrow> aexp list \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (unit, 'a resolved_st_q) effectful_st_transfer"
where
  "unit_etf_st_of_transfer tf_st enter_st = \<lparr>
    etf_st_nop        = unit_edge_tree_st (tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. unit_edge_tree_st (tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. unit_edge_tree_st (tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. unit_edge_tree_st (tf_st (EA_AssumeNot b))),
    etf_st_enter      = (\<lambda>xs es. unit_edge_tree_st (enter_st xs es)),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

lemma apply_etf_st_unit_of_transfer:
  assumes ret_none: "\<And>p. tf_st (EA_Ret None p) = tf_st EA_Nop"
      and ret_some: "\<And>a p. tf_st (EA_Ret (Some a) p) = tf_st (EA_Assign ret_var a)"
  shows "apply_etf_st (unit_etf_st_of_transfer tf_st enter_st) a u = unit_edge_tree_st (tf_st a) u"
  unfolding unit_etf_st_of_transfer_def
  by (cases a) (simp_all add: ret_none ret_some split: option.splits)

lemma etf_combine_st_unit_of_transfer:
  "etf_combine_st (unit_etf_st_of_transfer tf_st enter_st) dst cc ex = unit_combine_tree_st dst cc ex"
  unfolding unit_etf_st_of_transfer_def by simp

lemma etf_st_enter_unit_of_transfer:
  "etf_st_enter (unit_etf_st_of_transfer tf_st enter_st) xs es u = unit_edge_tree_st (enter_st xs es) u"
  unfolding unit_etf_st_of_transfer_def by simp

lemma etf_st_enter_exists_unit_of_transfer:
  "\<exists>f. etf_st_enter (unit_etf_st_of_transfer tf_st enter_st) xs es u = unit_edge_tree_st f u"
  using etf_st_enter_unit_of_transfer by blast

lemma apply_etf_st_exists_unit_of_transfer:
  assumes ret_none: "\<And>p. tf_st (EA_Ret None p) = tf_st EA_Nop"
      and ret_some: "\<And>a p. tf_st (EA_Ret (Some a) p) = tf_st (EA_Assign ret_var a)"
  shows "\<exists>f. apply_etf_st (unit_etf_st_of_transfer tf_st enter_st) a u = unit_edge_tree_st f u"
  using apply_etf_st_unit_of_transfer[OF ret_none ret_some] by blast

lemma traverse_unit_edge_tree_st:
  "traverse_rhs (unit_edge_tree_st f u) \<sigma>_st =
   restrict_local_resolved_q (f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_st_Inr:
  "sides_of_rhs (unit_edge_tree_st f u) \<sigma>_st (Inr ()) =
   restrict_global_resolved_q (f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma traverse_unit_combine_tree_st:
  "traverse_rhs (unit_combine_tree_st dst cc ex) \<sigma>_st =
   restrict_local_resolved_q (combine_collect_resolved_for_q is_global dst (\<sigma>_st (Inl cc) \<squnion> \<sigma>_st (Inr ()))
                                                 (\<sigma>_st (Inl ex) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_combine_tree_st_def by (simp add: Let_def)

lemma sides_unit_combine_tree_st_Inr:
  "sides_of_rhs (unit_combine_tree_st dst cc ex) \<sigma>_st (Inr ()) =
   restrict_global_resolved_q (combine_collect_resolved_for_q is_global dst (\<sigma>_st (Inl cc) \<squnion> \<sigma>_st (Inr ()))
                                                  (\<sigma>_st (Inl ex) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_combine_tree_st_def by (simp add: Let_def)

lemma dep_aux_unit_edge_tree_st:
  fixes f :: "'a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> 'a resolved_st_q"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  shows "dep_aux \<sigma>1 (unit_edge_tree_st f u) = dep_aux \<sigma>2 (unit_edge_tree g u)"
  unfolding unit_edge_tree_st_def unit_edge_tree_def Let_def by simp

lemma dep_aux_unit_combine_tree_st:
  "dep_aux \<sigma>1 (unit_combine_tree_st dst cc ex) = dep_aux \<sigma>2 (unit_combine_tree dst' cc ex)"
  unfolding unit_combine_tree_st_def unit_combine_tree_def Let_def by simp

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
  "('x, 'g, ('a::bot) resolved_st_q) strategy_tree \<Rightarrow> bool"
where
  "side_rg (Answer d) = True"
| "side_rg (QueryL y f) = (\<forall>v. side_rg (f v))"
| "side_rg (QueryG y f) = (\<forall>v. side_rg (f v))"
| "side_rg (Side y d t) = (restrict_global_resolved_q d = d \<and> side_rg t)"

lemma side_rg_seqcomp:
  assumes "side_rg t" and "\<And>v. side_rg (k v)"
  shows "side_rg (seqcomp_tree t k)"
  using assms by (induction t arbitrary: k) auto

lemma side_rg_unit_edge_tree_st: "side_rg (unit_edge_tree_st f u)"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma side_rg_unit_combine_tree_st: "side_rg (unit_combine_tree_st dst cc ex)"
  unfolding unit_combine_tree_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_Inl:
  "sides_of_rhs (unit_edge_tree f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_def Let_def by simp

lemma sides_unit_combine_tree_Inl:
  "sides_of_rhs (unit_combine_tree dst cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_def Let_def by simp

lemma sides_unit_edge_tree_st_Inl:
  "sides_of_rhs (unit_edge_tree_st f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_st_def Let_def by simp

lemma sides_unit_combine_tree_st_Inl:
  "sides_of_rhs (unit_combine_tree_st dst cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_st_def Let_def by simp


locale sound_rhs_generator_exec = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and etf_st :: "(unit, 'a resolved_st_q) effectful_st_transfer"
    and F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  assumes commute: "\<And>a s. fun_of_resolved_st_q_for is_global (F_st a s) = F a (fun_of_resolved_st_q_for is_global s)"
begin

lemma sides_apply_etf_st:
  "fun_of_resolved_st_q_for is_global (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
   = sides_of_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    by (simp add: edge_st edge sides_unit_edge_tree_st_Inl sides_unit_edge_tree_Inl
                  Let_def bot_fun_def)
next
  case (Inr g')
  then show ?thesis
    by (simp add: edge_st edge sides_unit_edge_tree_st_Inr sides_unit_edge_tree_Inr
                  commute fun_of_resolved_st_q_for_sup o_def Let_def)
qed

lemma sides_etf_combine_st:
  "fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st k)
   = sides_of_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    unfolding comb_st comb
    by (simp add: sides_unit_combine_tree_st_Inl sides_unit_combine_tree_Inl
                  Let_def bot_fun_def)
next
  case (Inr g')
  then show ?thesis
    unfolding comb_st comb
    by (simp add: sides_unit_combine_tree_st_Inr sides_unit_combine_tree_Inr
                  fun_of_resolved_st_q_for_sup o_def Let_def)
qed

end

lemma sides_apply_etf_st_unit_transfer:
  fixes etf_st :: "(unit, 'a::bounded_semilattice_sup_bot resolved_st_q) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  assumes commute: "\<And>a s. fun_of_resolved_st_q_for is_global (F_st a s) = F a (fun_of_resolved_st_q_for is_global s)"
  shows "fun_of_resolved_st_q_for is_global (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  show ?thesis by (rule sides_apply_etf_st)
qed

lemma sides_etf_combine_st_unit_transfer:
  fixes etf_st :: "(unit, 'a::bounded_semilattice_sup_bot resolved_st_q) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes commute: "\<And>a s. fun_of_resolved_st_q_for is_global (F_st a s) = F a (fun_of_resolved_st_q_for is_global s)"
  shows "fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st k)
       = sides_of_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  show ?thesis by (rule sides_etf_combine_st)
qed

subsection \<open>Effectful executable fold\<close>

definition side_contribution_trees_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a resolved_st_q) strategy_tree list"
where
  "side_contribution_trees_st etf es ens cs =
     map (\<lambda>(u, a). apply_etf_st etf a u) es @
     map (\<lambda>(cl, fs, as). etf_st_enter etf fs as cl) ens @
     map (\<lambda>(cc, dst, ex). etf_combine_st etf dst cc ex) cs"

definition side_acc_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a resolved_st_q)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list \<Rightarrow> 'a resolved_st_q"
where
  "side_acc_eff_st etf acc \<sigma> es ens cs =
     fold_rhs_values acc \<sigma> (side_contribution_trees_st etf es ens cs)"

definition side_rhs_fold_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> aexp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a resolved_st_q) strategy_tree"
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
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a resolved_st_q) strategy_tree"
where
  "make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v =
     (let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_resolved_q s0_st else bot0_st);
          t    = side_rhs_fold_eff_st etf acc0
                   (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)
      in if v = cfg_entry g then Side gseed (restrict_global_resolved_q s0_st) t else t)"

definition side_cfg_T_eff_st ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer
   \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a resolved_st_q) eqsT"
where
  "side_cfg_T_eff_st g etf bot0_st s0_st gseed = make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed"

lemma side_rg_fold_rhs_trees:
  assumes "\<And>t. t \<in> set ts \<Longrightarrow> side_rg t"
  shows "side_rg (fold_rhs_trees acc ts)"
  using assms
  by (induction ts arbitrary: acc) (auto intro: side_rg_seqcomp)

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
       (if v = cfg_entry g then bot0_st \<squnion> restrict_local_resolved_q s0_st else bot0_st)
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
lemma fold_rhs_values_fun_of_resolved_st_q_for:
  assumes rel: "list_all2
    (\<lambda>t_st t. \<forall>\<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
                         traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)) ts_st ts"
  shows "fun_of_resolved_st_q_for is_global (fold_rhs_values acc_st \<sigma>_st ts_st) =
         fold_rhs_values (fun_of_resolved_st_q_for is_global acc_st) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) ts"
  using rel
proof (induction arbitrary: acc_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have head: "fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
              traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    using Cons.hyps(1) by blast
  show ?case
    by (simp add: fun_of_resolved_st_q_for_sup head Cons.IH sup_fun_def comp_def)
qed

lemma side_acc_eff_st_fun_of_resolved_st_q_for:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  shows "fun_of_resolved_st_q_for is_global (side_acc_eff_st etf_st acc_st \<sigma>_st es ens cs) =
         side_acc_eff etf (fun_of_resolved_st_q_for is_global acc_st) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) es ens cs"
proof -
  have trees: "list_all2
      (\<lambda>t_st t. \<forall>\<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
                           traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st))
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
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
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
    (\<lambda>t_st t. \<forall>\<sigma>_st gk. fun_of_resolved_st_q_for is_global (sides_of_rhs t_st \<sigma>_st gk) =
                            sides_of_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk) ts_st ts"
  shows "fun_of_resolved_st_q_for is_global (sides_of_rhs (fold_rhs_trees acc_st ts_st) \<sigma>_st gk) =
         sides_of_rhs (fold_rhs_trees acc ts) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
  using rel
proof (induction arbitrary: acc_st acc)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have head: "fun_of_resolved_st_q_for is_global (sides_of_rhs t_st \<sigma>_st gk) =
              sides_of_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
    using Cons.hyps(1) by blast
  have rest: "fun_of_resolved_st_q_for is_global (sides_of_rhs
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) \<sigma>_st gk) =
      sides_of_rhs (fold_rhs_trees (acc \<squnion> traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)) ts)
        (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
    by (rule Cons.IH)
  show ?case
    by (simp add: sides_of_rhs_seqcomp_at fun_of_resolved_st_q_for_sup head rest comp_def)
qed

lemma side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gk. fun_of_resolved_st_q_for is_global (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gk)
                = sides_of_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
  assumes sd_enter:
    "\<And>cl fs as \<sigma>_st gk. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gk)
                = sides_of_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
  assumes sd_comb:
    "\<And>cc ex dst \<sigma>_st gk. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gk)
                = sides_of_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
  shows "fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st acc es ens cs) \<sigma>_st gk)
         = sides_of_rhs (side_rhs_fold_eff etf (fun_of_resolved_st_q_for is_global acc) es ens cs)
             (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
proof -
  have trees: "list_all2
      (\<lambda>t_st t. \<forall>\<sigma>_st gk. fun_of_resolved_st_q_for is_global (sides_of_rhs t_st \<sigma>_st gk) =
                              sides_of_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk)
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
      (\<forall>\<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
                    traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)) \<and>
      (\<forall>\<sigma>1 \<sigma>2. dep_aux \<sigma>1 t_st = dep_aux \<sigma>2 t)) ts_st ts"
  shows "dep_aux \<sigma>_st (fold_rhs_trees acc_st ts_st) =
         dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (fold_rhs_trees (fun_of_resolved_st_q_for is_global acc_st) ts)"
  using rel
proof (induction arbitrary: acc_st \<sigma>_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st t ts)
  have dep: "dep_aux \<sigma>_st t_st = dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) t"
    using Cons.hyps(1) by blast
  have tr: "fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
            traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    using Cons.hyps(1) by blast
  have acc_tr: "fun_of_resolved_st_q_for is_global (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) =
      fun_of_resolved_st_q_for is_global acc_st \<squnion> traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    by (simp add: fun_of_resolved_st_q_for_sup tr)
  have ih': "dep_aux \<sigma>_st
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) =
      dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
        (fold_rhs_trees (fun_of_resolved_st_q_for is_global (acc_st \<squnion> traverse_rhs t_st \<sigma>_st)) ts)"
    by (rule Cons.IH)
  have ih: "dep_aux \<sigma>_st
        (fold_rhs_trees (acc_st \<squnion> traverse_rhs t_st \<sigma>_st) ts_st) =
      dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
        (fold_rhs_trees (fun_of_resolved_st_q_for is_global acc_st \<squnion>
          traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)) ts)"
    using ih' acc_tr by simp
  show ?case
    by (simp add: dep_aux_seqcomp dep ih comp_def)
qed

lemma dep_aux_side_rhs_fold_eff_st_eq:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
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
       = dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (side_rhs_fold_eff etf (fun_of_resolved_st_q_for is_global acc) es ens cs)"
proof -
  have trees: "list_all2
      (\<lambda>t_st t.
        (\<forall>\<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs t_st \<sigma>_st) =
                      traverse_rhs t (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)) \<and>
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
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
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
       = dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
           (make_side_rhs_tree_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed v)"
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
  assumes EQ: "\<And>v \<sigma>. fun_of_resolved_st_q_for is_global (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_resolved_st_q_for is_global (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k)) (T_abs v)"
    and pp: "part_post_solution T_st x sigma_st vars"
  shows "part_post_solution T_abs x (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using pp by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) v \<subseteq> vars"
      using pp v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) (Inl v)"
    proof -
      have le_st: "eq T_st v sigma_st \<le> sigma_st (Inl v)" using pp v_in by simp
      show ?thesis using fun_of_resolved_st_q_for_mono[where gs=is_global, OF le_st] EQ by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using pp v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) k"
        using fun_of_resolved_st_q_for_mono[where gs=is_global, OF le_st] SIDES by simp
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
  assumes EQ: "\<And>v \<sigma>. fun_of_resolved_st_q_for is_global (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_resolved_st_q_for is_global (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_resolved_st_q_for is_global (\<sigma> k)) (T_abs v)"
    and ps: "part_solution T_st x sigma_st vars"
  shows "part_solution T_abs x (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using ps by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) v \<subseteq> vars"
      using ps v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) = (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) (Inl v)"
    proof -
      have eq_st: "eq T_st v sigma_st = sigma_st (Inl v)" using ps v_in by simp
      show ?thesis
        using EQ[where v=v and \<sigma>=sigma_st] eq_st by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) \<le> (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using ps v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_resolved_st_q_for is_global (sigma_st k)) k"
        using fun_of_resolved_st_q_for_mono[where gs=is_global, OF le_st] SIDES by simp
    qed
  qed
qed

subsection \<open>Transport: executable effectful post-solution to abstract effectful post-solution\<close>

context
  fixes g :: cfg
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
  fixes etf :: "('g, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st :: "'a resolved_st_q"
  fixes gseed :: 'g
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_enter:
    "\<And>cl fs as \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
                = traverse_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex dst \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
               = sides_of_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
  assumes sd_enter:
    "\<And>cl fs as \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
                = sides_of_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
  assumes sd_comb:
    "\<And>cc ex dst \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gg)
                = sides_of_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
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
  "fun_of_resolved_st_q_for is_global (eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st) =
   eq (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed) v (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
  unfolding eq_side_cfg_T_eff_st eq_side_cfg_T_eff
  by (simp add: side_acc_eff_st_fun_of_resolved_st_q_for[OF tr_edge tr_enter tr_comb])

private lemma fun_of_resolved_st_q_for_sides_cfg_eff_st:
  "fun_of_resolved_st_q_for is_global (sides_of_rhs (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v) \<sigma>_st gkey)
   = sides_of_rhs (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed v)
       (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gkey"
proof (cases "v = cfg_entry g")
  case True
  have fold_sides:
    "\<And>gk. fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st (bot0_st \<squnion> restrict_local_resolved_q s0_st)
        (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st gk)
     = sides_of_rhs (side_rhs_fold_eff etf (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
        (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
       (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gk"
    by (simp add: side_rhs_fold_eff_st_sides_fun_of_resolved_st_q_for[OF sd_edge sd_enter sd_comb])
  show ?thesis unfolding side_cfg_T_eff_st_def side_cfg_T_eff_def
    make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
  proof (simp add: True)
    show "fun_of_resolved_st_q_for is_global ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
            (bot0_st \<squnion> restrict_local_resolved_q s0_st)
            (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st
          in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_resolved_q s0_st)) gkey)
          = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
                (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
             in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st))) gkey"
    proof (cases gkey)
      case (Inl u)
      have "fun_of_resolved_st_q_for is_global ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
              (bot0_st \<squnion> restrict_local_resolved_q s0_st)
              (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_resolved_q s0_st)) (Inl u))
          = fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st
              (bot0_st \<squnion> restrict_local_resolved_q s0_st)
              (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
            \<sigma>_st (Inl u))"
        by (simp add: Let_def)
      also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
            (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
            (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
          (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (Inl u)"
        by (simp add: fold_sides)
      also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
              (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
            (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
          in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st))) (Inl u)"
        by (simp add: Let_def)
      finally show ?thesis by (simp add: Inl)
    next
      case (Inr gk)
      show ?thesis proof (cases "gk = gseed")
        case True
        have "fun_of_resolved_st_q_for is_global ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_resolved_q s0_st)
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st
              in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_resolved_q s0_st)) (Inr gseed))
            = fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_resolved_q s0_st)
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
              \<sigma>_st (Inr gseed) \<squnion> restrict_global_resolved_q s0_st)"
          by (simp add: Let_def True)
        also have "\<dots> = fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_resolved_q s0_st)
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
              \<sigma>_st (Inr gseed)) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st)"
          by simp
        also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
              (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
            (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (Inr gseed) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st)"
          by (simp add: fold_sides)
        also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
              (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st))) (Inr gseed)"
          by (simp add: Let_def True)
        finally show ?thesis by (simp add: Inr True)
      next
        case False
        have "fun_of_resolved_st_q_for is_global ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_resolved_q s0_st)
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g))) \<sigma>_st
              in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_resolved_q s0_st)) (Inr gk))
            = fun_of_resolved_st_q_for is_global (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_resolved_q s0_st)
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
              \<sigma>_st (Inr gk))"
          by (simp add: Let_def False)
        also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
              (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
            (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (Inr gk)"
          by (simp add: fold_sides)
        also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_resolved_st_q_for is_global bot0_st \<squnion> restrict_local (fun_of_resolved_st_q_for is_global s0_st))
                (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g)) (return_call_list g (cfg_entry g)))
              (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_resolved_st_q_for is_global s0_st))) (Inr gk)"
          by (simp add: Let_def False)
        finally show ?thesis by (simp add: Inr)
      qed
    qed
  qed
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
           (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed)
           x (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  have deps: "\<And>v. v \<in> vars \<Longrightarrow>
      dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v
    = dep\<^sub>L (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed)
             (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) v"
  proof -
    fix v
    have eq: "dep_aux \<sigma>_st (make_side_rhs_tree_eff_st g etf_st bot0_st s0_st gseed v) =
              dep_aux (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)
                (make_side_rhs_tree_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed v)"
      by (rule dep_aux_make_side_rhs_tree_eff_st_eq[OF tr_edge tr_enter tr_comb dep_edge dep_enter dep_comb])
    show "dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v =
          dep\<^sub>L (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed)
                 (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) v"
      by (simp add: dep\<^sub>L_def dep_def side_cfg_T_eff_st_def side_cfg_T_eff_def eq)
  qed
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed)
              (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) v \<subseteq> vars"
      using pp_st v_in deps[OF v_in] by auto
    show "eq (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed) v
             (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) \<le> (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st
                   \<le> \<sigma>_st (Inl v)"
        using pp_st v_in by simp
      show ?thesis
        using fun_of_resolved_st_q_for_mono[where gs=is_global, OF le_st] fun_of_resolved_st_q_for_eq_cfg_eff_st[where v=v] by simp
    qed
    show "sides_of_rhs (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed v)
             (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) \<le> fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs
               (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) gseed v)
               (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k \<le> (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) k"
        by (metis comp_apply fun_of_resolved_st_q_for_mono fun_of_resolved_st_q_for_sides_cfg_eff_st le_funD pp_st v_in)
      
       
    qed
  qed
qed

end

lemma part_post_solution_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes Fe_st :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q"
  fixes Fe :: "vname list \<Rightarrow> aexp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st :: "'a resolved_st_q"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex dst. etf_combine etf dst cc ex = unit_combine_tree dst cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  assumes commute: "\<And>a s. fun_of_resolved_st_q_for is_global (F_st a s) = F a (fun_of_resolved_st_q_for is_global s)"
  assumes enter: "\<And>cl fs as. etf_enter etf fs as cl = unit_edge_tree (Fe fs as) cl"
  assumes enter_st: "\<And>cl fs as. etf_st_enter etf_st fs as cl = unit_edge_tree_st (Fe_st fs as) cl"
  assumes commute_enter: "\<And>fs as s. fun_of_resolved_st_q_for is_global (Fe_st fs as s) = Fe fs as (fun_of_resolved_st_q_for is_global s)"
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_st g etf_st bot0_st s0_st ()) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff g etf (fun_of_resolved_st_q_for is_global bot0_st) (fun_of_resolved_st_q_for is_global s0_st) ())
           x (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) vars"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  have tr_edge:
    "\<And>a u \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute o_def Let_def)
  have tr_comb:
    "\<And>cc ex dst \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st)
     = traverse_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    unfolding comb_st comb traverse_unit_combine_tree_st traverse_unit_combine_tree
    by (simp add: o_def Let_def)
  have sd_edge:
    "\<And>a u \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
     = sides_of_rhs (apply_etf etf a u) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
    using sides_apply_etf_st .
  have sd_comb:
    "\<And>cc ex dst \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_combine_st etf_st dst cc ex) \<sigma>_st gg)
     = sides_of_rhs (etf_combine etf dst cc ex) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
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
    "\<And>cl fs as \<sigma>_st. fun_of_resolved_st_q_for is_global (traverse_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st)
     = traverse_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st)"
    unfolding enter_st enter traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute_enter o_def Let_def)
  have sd_enter:
    "\<And>cl fs as \<sigma>_st gg. fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
     = sides_of_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
  proof -
    fix cl fs as and \<sigma>_st :: "pp + unit \<Rightarrow> 'a resolved_st_q" and gg
    show "fun_of_resolved_st_q_for is_global (sides_of_rhs (etf_st_enter etf_st fs as cl) \<sigma>_st gg)
        = sides_of_rhs (etf_enter etf fs as cl) (fun_of_resolved_st_q_for is_global \<circ> \<sigma>_st) gg"
    proof (cases gg)
      case (Inl u')
      then show ?thesis
        by (simp add: enter_st enter sides_unit_edge_tree_st_Inl sides_unit_edge_tree_Inl
                      Let_def bot_fun_def)
    next
      case (Inr g')
      then show ?thesis
        by (simp add: enter_st enter sides_unit_edge_tree_st_Inr sides_unit_edge_tree_Inr
                      commute_enter fun_of_resolved_st_q_for_sup o_def Let_def)
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

lemma inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs:
  fixes sigma_st :: "pp + unit \<Rightarrow> ('a::bounded_semilattice_sup_bot) resolved_st_q"
  assumes rg: "\<And>gg. sigma_st (Inr gg) = restrict_global_resolved_q (sigma_st (Inr gg))"
  shows "inr_slot_locals_bot is_global (fun_of_resolved_st_q_for is_global \<circ> sigma_st)"
  unfolding inr_slot_locals_bot_iff_Inr_restrict_global
proof (intro allI)
  fix gg
  show "(fun_of_resolved_st_q_for is_global \<circ> sigma_st) (Inr gg) = restrict_global ((fun_of_resolved_st_q_for is_global \<circ> sigma_st) (Inr gg))"
  proof -
    have "fun_of_resolved_st_q_for is_global (sigma_st (Inr gg)) = fun_of_resolved_st_q_for is_global (restrict_global_resolved_q (sigma_st (Inr gg)))"
      using rg by simp
    thus ?thesis by (simp add: o_def fun_of_resolved_st_q_for_restrict_global_abs)
  qed
qed

text \<open>
  The unit equation system has every reachable \<open>Side\<close> contribution
  \<open>restrict_global_resolved_q\<close>-shaped.  This is the structural precondition the
  side-effecting solver consumes to keep its \<open>Inr\<close> slots \<open>restrict_global_resolved_q\<close>-shaped
  (the solver-side induction lives where the side solver's \<open>solve\<close> is in scope).
\<close>

lemma side_rg_side_cfg_T_eff_st_unit:
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) resolved_st_q) effectful_st_transfer"
  assumes edge_st: "\<And>a u. \<exists>f. apply_etf_st etf_st a u = unit_edge_tree_st f u"
  assumes enter_st: "\<And>cl fs as. \<exists>f. etf_st_enter etf_st fs as cl = unit_edge_tree_st f cl"
  assumes comb_st: "\<And>cc ex dst. etf_combine_st etf_st dst cc ex = unit_combine_tree_st dst cc ex"
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








