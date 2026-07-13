theory Exec_Bridge
  imports Exec_St TD_Side_Eff_Bounds TD_Side_RHS_Generator Constraint_System
begin

section \<open>S4 bridge: fun_of_st homomorphisms and executable equation-system transport\<close>

text \<open>
  Generic (domain-agnostic) bridge between executable st side-effecting equation
  systems and abstract abs_state side_cfg_T_eff systems.  Domain theories discharge
  per-tree traverse and side denotation commutation through fun_of_st.
\<close>

subsection \<open>fun_of_st homomorphisms for local/global projections\<close>

lemma fun_of_st_restrict_local_st [simp]:
  "fun_of_st (restrict_local_st s) = restrict_local (fun_of_st s)"
  unfolding restrict_local_def
  by (rule ext) simp

lemma fun_of_st_restrict_global_st [simp]:
  "fun_of_st (restrict_global_st s) = restrict_global (fun_of_st s)"
  unfolding restrict_global_def
  by (rule ext) simp

lemma fun_of_st_combine_abs_st [simp]:
  "fun_of_st (combine_abs_st sc se) = combine_abs (fun_of_st sc) (fun_of_st se)"
  unfolding combine_abs_def
  by (rule ext) simp

subsection \<open>Injectivity of fun_of_st and combine-identity lemmas\<close>

lemma fun_of_st_inject:
  "fun_of_st s1 = fun_of_st s2 \<Longrightarrow> s1 = s2"
  by (metis Quotient_rel_abs2 Quotient_st eq_st_def lookup_st.rep_eq)
 

lemma restrict_local_st_combine_abs_st [simp]:
  "restrict_local_st (combine_abs_st A B) = restrict_local_st A"
  by (simp add: combine_abs_st_def fun_of_st_inject restrict_local_combine_eq)
 
lemma restrict_global_st_combine_abs_st [simp]:
  "restrict_global_st (combine_abs_st A B) = restrict_global_st B"
  by (simp add: combine_abs_st_def fun_of_st_inject restrict_global_combine_eq)
 
(* Split lemmas for combine_abs_st projections used by effectful executable trees. *)
lemma restrict_local_st_split [simp]:
  "restrict_local_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_local_st A"
  by (simp add: combine_abs_st_def[symmetric])

lemma restrict_global_st_split [simp]:
  "restrict_global_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_global_st B"
  by (simp add: combine_abs_st_def[symmetric])

subsection \<open>Executable effectful transfer record\<close>

text \<open>
  Executable counterpart of the effectful transfer record: per-action strategy-tree
  producers with payloads at @{typ "'a st"} instead of @{typ "'a abs_state"}.
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
  etf_st_enter      :: "('g, 'c) st_edge_tf_tree"
  etf_st_combine    :: "('g, 'c) st_combine_tf_tree"

fun apply_etf_st ::
  "('g, 'c) effectful_st_transfer \<Rightarrow> edge_action \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'c) strategy_tree"
where
  "apply_etf_st etf EA_Nop           u = etf_st_nop etf u"
| "apply_etf_st etf (EA_Assign x a)  u = etf_st_assign etf x a u"
| "apply_etf_st etf (EA_Assume b)    u = etf_st_assume etf b u"
| "apply_etf_st etf (EA_AssumeNot b) u = etf_st_assume_not etf b u"
| "apply_etf_st etf EA_Enter         u = etf_st_enter etf u"

fun etf_combine_st ::
  "('g, 'c) effectful_st_transfer \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'c) strategy_tree"
where
  "etf_combine_st etf cc ex = etf_st_combine etf cc ex"

subsection \<open>Unit-global executable effectful trees\<close>

text \<open>
  Executable counterparts of @{const unit_edge_tree} and @{const unit_combine_tree}
  from @{theory Voblint_Analysis.TD_Side_CFG}, with payloads at @{typ "'a st"}.
\<close>

definition unit_edge_tree_st ::
  "('a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st) \<Rightarrow> (unit, 'a st) st_edge_tf_tree"
where
  "unit_edge_tree_st f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global_st res)
         (Answer (restrict_local_st res))))"

definition unit_combine_tree_st ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp, unit, 'a::bounded_semilattice_sup_bot st) strategy_tree"
where
  "unit_combine_tree_st cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
       let res = restrict_local_st (sc \<squnion> g) \<squnion> restrict_global_st (se \<squnion> g) in
       Side () (restrict_global_st res)
         (Answer (restrict_local_st res)))))"

text \<open>
  The \<^emph>\<open>clean\<close> (Goblint-sequential) executable edge: writes the base transfer's
  result to the local slot reading \<^emph>\<open>only\<close> that slot (no \<open>\<squnion> g\<close>), and publishes its
  global projection.  The executable mirror of the abstract \<open>clean_edge_tree\<close>;
  \<^const>\<open>unit_edge_tree_st\<close> instead reads \<open>su \<squnion> g\<close>.  Domain-generic --- Sign and
  interval both instantiate it.
\<close>

definition clean_edge_tree_st ::
  "('a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st) \<Rightarrow> 'u \<Rightarrow> ('u, unit, 'a st) strategy_tree" where
  "clean_edge_tree_st f u =
     QueryL u (\<lambda>su. let res = f su in Side () (restrict_global_st res) (Answer res))"

lemma traverse_unit_edge_tree_st:
  "traverse_rhs (unit_edge_tree_st f u) \<sigma>_st =
   restrict_local_st (f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_st_Inr:
  "sides_of_rhs (unit_edge_tree_st f u) \<sigma>_st (Inr ()) =
   restrict_global_st (f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma traverse_unit_combine_tree_st:
  "traverse_rhs (unit_combine_tree_st cc ex) \<sigma>_st =
   restrict_local_st (\<sigma>_st (Inl cc) \<squnion> \<sigma>_st (Inr ()))"
  unfolding unit_combine_tree_st_def
  by (simp add: Let_def restrict_local_st_combine_abs_st restrict_local_st_split)

lemma sides_unit_combine_tree_st_Inr:
  "sides_of_rhs (unit_combine_tree_st cc ex) \<sigma>_st (Inr ()) =
   restrict_global_st (\<sigma>_st (Inl ex) \<squnion> \<sigma>_st (Inr ()))"
  unfolding unit_combine_tree_st_def
  by (simp add: Let_def restrict_global_st_combine_abs_st restrict_global_st_split)

lemma dep_aux_unit_edge_tree_st:
  fixes f :: "'a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  shows "dep_aux \<sigma>1 (unit_edge_tree_st f u) = dep_aux \<sigma>2 (unit_edge_tree g u)"
  unfolding unit_edge_tree_st_def unit_edge_tree_def Let_def by simp

lemma dep_aux_unit_combine_tree_st:
  "dep_aux \<sigma>1 (unit_combine_tree_st cc ex) = dep_aux \<sigma>2 (unit_combine_tree cc ex)"
  unfolding unit_combine_tree_st_def unit_combine_tree_def Let_def by simp

subsection \<open>Globally-restricted side values\<close>

text \<open>
  \<open>restrict_global_st\<close> is the idempotent projection onto global variables.  A
  strategy tree is \<open>side_rg\<close> when every \<open>Side\<close> node it can reach (under any query
  answer) carries a value already fixed by that projection.  Unit trees and the
  executable IP fold satisfy this: every side contribution is a
  \<open>restrict_global_st ...\<close>.  The side-effecting solver then keeps every \<open>Inr\<close> slot
  \<open>restrict_global_st\<close>-shaped, since the running join of such values stays shaped
  (\<open>restrict_global_st_sup_restrict_global_st\<close>, \<open>restrict_global_st\<close> of \<open>bot\<close>).
\<close>

lemma restrict_global_st_idem [simp]:
  "restrict_global_st (restrict_global_st s) = restrict_global_st s"
  by (rule st_eqI_lookup) (simp add: lookup_restrict_global_st)

primrec side_rg ::
  "('x, 'g, ('a::bot) st) strategy_tree \<Rightarrow> bool"
where
  "side_rg (Answer d) = True"
| "side_rg (QueryL y f) = (\<forall>v. side_rg (f v))"
| "side_rg (QueryG y f) = (\<forall>v. side_rg (f v))"
| "side_rg (Side y d t) = (restrict_global_st d = d \<and> side_rg t)"

lemma side_rg_seqcomp:
  assumes "side_rg t" and "\<And>v. side_rg (k v)"
  shows "side_rg (seqcomp_tree t k)"
  using assms by (induction t arbitrary: k) auto

lemma side_rg_unit_edge_tree_st: "side_rg (unit_edge_tree_st f u)"
  unfolding unit_edge_tree_st_def by (simp add: Let_def)

lemma side_rg_unit_combine_tree_st: "side_rg (unit_combine_tree_st cc ex)"
  unfolding unit_combine_tree_st_def by (simp add: Let_def)

lemma sides_unit_edge_tree_Inl:
  "sides_of_rhs (unit_edge_tree f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_def Let_def by simp

lemma sides_unit_combine_tree_Inl:
  "sides_of_rhs (unit_combine_tree cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_def Let_def by simp

lemma sides_unit_edge_tree_st_Inl:
  "sides_of_rhs (unit_edge_tree_st f u) \<sigma> (Inl u') = bot"
  unfolding unit_edge_tree_st_def Let_def by simp

lemma sides_unit_combine_tree_st_Inl:
  "sides_of_rhs (unit_combine_tree_st cc ex) \<sigma> (Inl u') = bot"
  unfolding unit_combine_tree_st_def Let_def by simp


locale sound_rhs_generator_exec = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
    and etf_st :: "(unit, 'a st) effectful_st_transfer"
    and F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
begin

lemma sides_apply_etf_st:
  "fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
   = sides_of_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    by (simp add: edge_st edge sides_unit_edge_tree_st_Inl sides_unit_edge_tree_Inl
                  Let_def fun_of_st_bot bot_fun_def)
next
  case (Inr g')
  then show ?thesis
    by (simp add: edge_st edge sides_unit_edge_tree_st_Inr sides_unit_edge_tree_Inr
                  commute fun_of_st_sup o_def Let_def)
qed

lemma sides_etf_combine_st:
  "fun_of_st (sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma>_st k)
   = sides_of_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    unfolding comb_st comb
    by (simp add: sides_unit_combine_tree_st_Inl sides_unit_combine_tree_Inl
                  Let_def fun_of_st_bot bot_fun_def)
next
  case (Inr g')
  then show ?thesis
    unfolding comb_st comb
    by (simp add: sides_unit_combine_tree_st_Inr sides_unit_combine_tree_Inr
                  fun_of_st_sup o_def Let_def)
qed

end

lemma sides_apply_etf_st_unit_transfer:
  fixes etf_st :: "(unit, 'a::bounded_semilattice_sup_bot st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  shows "fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st) k"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  show ?thesis by (rule sides_apply_etf_st)
qed

lemma sides_etf_combine_st_unit_transfer:
  fixes etf_st :: "(unit, 'a::bounded_semilattice_sup_bot st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  shows "fun_of_st (sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma>_st k)
       = sides_of_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st) k"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  show ?thesis by (rule sides_etf_combine_st)
qed

subsection \<open>Effectful executable fold\<close>

fun side_acc_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a st)
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list \<Rightarrow> 'a st"
where
  "side_acc_eff_st etf acc \<sigma> [] [] = acc"
| "side_acc_eff_st etf acc \<sigma> ((u, a) # ps) cs =
     side_acc_eff_st etf (acc \<squnion> traverse_rhs (apply_etf_st etf a u) \<sigma>) \<sigma> ps cs"
| "side_acc_eff_st etf acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_eff_st etf
       (acc \<squnion> traverse_rhs (etf_combine_st etf cc ex) \<sigma>) \<sigma> [] cs"

fun side_rhs_fold_eff_st ::
  "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a st) strategy_tree"
where
  "side_rhs_fold_eff_st etf acc [] [] = Answer acc"
| "side_rhs_fold_eff_st etf acc ((u, a) # ps) cs =
     seqcomp_tree (apply_etf_st etf a u)
       (\<lambda>res. side_rhs_fold_eff_st etf (acc \<squnion> res) ps cs)"
| "side_rhs_fold_eff_st etf acc [] ((cc, ex) # cs) =
     seqcomp_tree (etf_combine_st etf cc ex)
       (\<lambda>res. side_rhs_fold_eff_st etf (acc \<squnion> res) [] cs)"

definition make_side_rhs_tree_eff_st ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a st) strategy_tree"
where
  "make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v =
     (let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st);
          t    = side_rhs_fold_eff_st etf acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g then Side gseed (restrict_global_st s0_st) t else t)"

definition side_cfg_T_eff_st ::
  "cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_st g etf bot0_st s0_st gseed = make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed"

lemma side_rg_side_rhs_fold_eff_st:
  assumes "\<And>a u. side_rg (apply_etf_st etf a u)"
    and "\<And>cc ex. side_rg (etf_combine_st etf cc ex)"
  shows "side_rg (side_rhs_fold_eff_st etf acc es cs)"
  using assms
  by (induction etf acc es cs rule: side_rhs_fold_eff_st.induct)
     (auto intro: side_rg_seqcomp)

lemma side_rg_make_side_rhs_tree_eff_st:
  assumes "\<And>a u. side_rg (apply_etf_st etf a u)"
    and "\<And>cc ex. side_rg (etf_combine_st etf cc ex)"
  shows "side_rg (make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v)"
  unfolding make_side_rhs_tree_eff_st_def Let_def
  by (simp add: side_rg_side_rhs_fold_eff_st[OF assms])

lemma traverse_side_rhs_fold_eff_st:
  "traverse_rhs (side_rhs_fold_eff_st etf acc es cs) \<sigma>_st =
   side_acc_eff_st etf acc \<sigma>_st es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x
      unfolding side_rhs_fold_eff_st.simps side_acc_eff_st.simps
      by (simp only: traverse_seqcomp Cons.IH)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x
    unfolding side_rhs_fold_eff_st.simps side_acc_eff_st.simps
    by (simp only: traverse_seqcomp Cons.IH)
qed

lemma eq_side_cfg_T_eff_st:
  "eq (side_cfg_T_eff_st g etf bot0_st s0_st gseed) v \<sigma>_st =
     side_acc_eff_st etf
       (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
       \<sigma>_st (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_eff_st_def make_side_rhs_tree_eff_st_def
  by (simp add: traverse_side_rhs_fold_eff_st Let_def)

subsection \<open>Tree denotation commutation for folds\<close>

lemma side_acc_eff_st_fun_of_st:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex \<sigma>_st. fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
  shows "fun_of_st (side_acc_eff_st etf_st acc_st \<sigma>_st es cs) =
         side_acc_eff etf (fun_of_st acc_st) (fun_of_st \<circ> \<sigma>_st) es cs"
proof (induction es arbitrary: acc_st cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc_st)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have "fun_of_st (side_acc_eff_st etf_st acc_st \<sigma>_st [] (x # cs))
        = fun_of_st (side_acc_eff_st etf_st
            (acc_st \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st) \<sigma>_st [] cs)"
      unfolding x by simp
    also have "\<dots> = side_acc_eff etf
            (fun_of_st (acc_st \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st))
            (fun_of_st \<circ> \<sigma>_st) [] cs"
      by (rule Cons.IH)
    also have "\<dots> = side_acc_eff etf (fun_of_st acc_st)
            (fun_of_st \<circ> \<sigma>_st) [] (x # cs)"
      using tr_comb x by auto
    finally show ?case .
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "fun_of_st (side_acc_eff_st etf_st acc_st \<sigma>_st (x # es) cs)
      = fun_of_st (side_acc_eff_st etf_st
          (acc_st \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st) \<sigma>_st es cs)"
    unfolding x by simp
  also have "\<dots> = side_acc_eff etf
          (fun_of_st (acc_st \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st))
          (fun_of_st \<circ> \<sigma>_st) es cs"
    by (rule Cons.IH)
  also have "\<dots> = side_acc_eff etf (fun_of_st acc_st)
          (fun_of_st \<circ> \<sigma>_st) (x # es) cs"
    unfolding x by (simp add: tr_edge)
  finally show ?case .
qed

lemma sides_side_rhs_fold_eff_st_acc_indep:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  shows "sides_of_rhs (side_rhs_fold_eff_st etf_st acc1 es cs) \<sigma>
         = sides_of_rhs (side_rhs_fold_eff_st etf_st acc2 es cs) \<sigma>"
proof (induction es arbitrary: acc1 acc2 cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc1 acc2)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have step: "sides_of_rhs (side_rhs_fold_eff_st etf_st
                  (acc1 \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>) [] cs) \<sigma>
              = sides_of_rhs (side_rhs_fold_eff_st etf_st
                  (acc2 \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>) [] cs) \<sigma>"
      by (rule Cons.IH)
    show ?case unfolding x side_rhs_fold_eff_st.simps
      using step by (simp add: sides_of_rhs_seqcomp)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have step: "sides_of_rhs (side_rhs_fold_eff_st etf_st
                (acc1 \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>) es cs) \<sigma>
            = sides_of_rhs (side_rhs_fold_eff_st etf_st
                (acc2 \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>) es cs) \<sigma>"
    by (rule Cons.IH)
  show ?case unfolding x side_rhs_fold_eff_st.simps
    using step by (simp add: sides_of_rhs_seqcomp)
qed

lemma sides_eff_fold_st_edge_step:
  "sides_of_rhs (side_rhs_fold_eff_st etf_st acc ((u, a) # es) cs) \<sigma> gk
   = sides_of_rhs (apply_etf_st etf_st a u) \<sigma> gk
     \<squnion> sides_of_rhs (side_rhs_fold_eff_st etf_st acc es cs) \<sigma> gk"
proof -
  have "sides_of_rhs (side_rhs_fold_eff_st etf_st
          (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>) es cs) \<sigma> (Inr gg)
      = sides_of_rhs (side_rhs_fold_eff_st etf_st acc es cs) \<sigma> (Inr gg)"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_st_acc_indep])
  thus ?thesis
    by (metis (no_types, lifting) side_rhs_fold_eff_st.simps(2) sides_of_rhs_seqcomp_at
        sides_side_rhs_fold_eff_st_acc_indep) 
qed

lemma sides_eff_fold_st_combine_step:
  "sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] ((cc, ex) # cs)) \<sigma> gk
   = sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma> gk
     \<squnion> sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] cs) \<sigma> gk"
proof -
  have "sides_of_rhs (side_rhs_fold_eff_st etf_st
          (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>) [] cs) \<sigma> (Inr gg)
      = sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] cs) \<sigma> (Inr gg)"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_st_acc_indep])
  thus ?thesis
    by (metis (lifting) side_rhs_fold_eff_st.simps(3) sides_of_rhs_seqcomp_at
        sides_side_rhs_fold_eff_st_acc_indep)
qed

lemma side_rhs_fold_eff_st_sides_fun_of_st:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gk. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gk)
               = sides_of_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st) gk"
  assumes sd_comb:
    "\<And>cc ex \<sigma>_st gk. fun_of_st (sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma>_st gk)
                = sides_of_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st) gk"
  shows "fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st acc es cs) \<sigma>_st gk)
         = sides_of_rhs (side_rhs_fold_eff etf (fun_of_st acc) es cs)
             (fun_of_st \<circ> \<sigma>_st) gk"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have ih: "fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st acc [] cs) \<sigma>_st gk)
            = sides_of_rhs (side_rhs_fold_eff etf (fun_of_st acc) [] cs)
                (fun_of_st \<circ> \<sigma>_st) gk"
      by (rule Cons.IH)
    show ?case unfolding x
      by (metis (no_types, lifting) fun_of_st_sup ih sd_comb side_rhs_fold_eff.simps(3)
          sides_eff_fold_st_combine_step sides_of_rhs_seqcomp_at sides_side_rhs_fold_eff_acc_indep)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have ih: "fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st acc es cs) \<sigma>_st gk)
          = sides_of_rhs (side_rhs_fold_eff etf (fun_of_st acc) es cs)
              (fun_of_st \<circ> \<sigma>_st) gk"
    by (rule Cons.IH)
  show ?case
    by (smt (verit, ccfv_threshold) fun_of_st_sup ih list.discI list.inject sd_edge
        side_rhs_fold_eff.elims sides_eff_fold_st_edge_step sides_of_rhs_seqcomp_at
        sides_side_rhs_fold_eff_acc_indep)  
qed

lemma dep_aux_side_rhs_fold_eff_st_eq:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex \<sigma>_st. fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_comb:
    "\<And>cc ex \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st cc ex)
                = dep_aux \<sigma>2 (etf_combine etf cc ex)"
  shows "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st acc es cs)
       = dep_aux (fun_of_st \<circ> \<sigma>_st) (side_rhs_fold_eff etf (fun_of_st acc) es cs)"
proof (induction es arbitrary: acc cs \<sigma>_st)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc \<sigma>_st)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have e: "dep_aux \<sigma>_st (etf_combine_st etf_st cc ex)
            = dep_aux (fun_of_st \<circ> \<sigma>_st) (etf_combine etf cc ex)"
      by (rule dep_comb)
    have tr: "fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
             = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
      by (rule tr_comb)
    have acc_tr:
      "fun_of_st (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
       = fun_of_st acc \<squnion> traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
    proof -
      have "fun_of_st (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
          = fun_of_st acc \<squnion> fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)"
        by (simp)
      thus ?thesis by (simp only: tr)
    qed
    have ih': "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st
                (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st) [] cs)
            = dep_aux (fun_of_st \<circ> \<sigma>_st) (side_rhs_fold_eff etf
                (fun_of_st (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)) [] cs)"
      by (rule Cons.IH)
    have ih: "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st
                (acc \<squnion> traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st) [] cs)
            = dep_aux (fun_of_st \<circ> \<sigma>_st) (side_rhs_fold_eff etf
                (fun_of_st acc \<squnion> traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)) [] cs)"
      using ih' acc_tr by simp
    show ?case
      by (metis (no_types, lifting) dep_aux_seqcomp e ih side_rhs_fold_eff.simps(3)
          side_rhs_fold_eff_st.simps(3) x) 
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have e: "dep_aux \<sigma>_st (apply_etf_st etf_st a u)
          = dep_aux (fun_of_st \<circ> \<sigma>_st) (apply_etf etf a u)"
    by (rule dep_edge)
  have tr: "fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
           = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
    by (rule tr_edge)
  have acc_tr:
    "fun_of_st (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = fun_of_st acc \<squnion> traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
  proof -
    have "fun_of_st (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
        = fun_of_st acc \<squnion> fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)"
      by (simp)
    thus ?thesis by (simp only: tr)
  qed
  have ih': "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st
              (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st) es cs)
          = dep_aux (fun_of_st \<circ> \<sigma>_st) (side_rhs_fold_eff etf
              (fun_of_st (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)) es cs)"
    by (rule Cons.IH)
  have ih: "dep_aux \<sigma>_st (side_rhs_fold_eff_st etf_st
              (acc \<squnion> traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st) es cs)
          = dep_aux (fun_of_st \<circ> \<sigma>_st) (side_rhs_fold_eff etf
              (fun_of_st acc \<squnion> traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)) es cs)"
    using ih' acc_tr by simp
  show ?case unfolding x side_rhs_fold_eff_st.simps
    by (simp add: dep_aux_seqcomp e ih comp_def)
qed

lemma dep_aux_make_side_rhs_tree_eff_st_eq:
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex \<sigma>_st. fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_comb:
    "\<And>cc ex \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st cc ex)
                = dep_aux \<sigma>2 (etf_combine etf cc ex)"
  shows "dep_aux \<sigma>_st (make_side_rhs_tree_eff_st g etf_st bot0_st s0_st gseed v)
       = dep_aux (fun_of_st \<circ> \<sigma>_st)
           (make_side_rhs_tree_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed v)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using True
    by (simp add: dep_aux_side_rhs_fold_eff_st_eq[OF tr_edge tr_comb dep_edge dep_comb])
next
  case False
  show ?thesis unfolding make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
    using False
    by (simp add: dep_aux_side_rhs_fold_eff_st_eq[OF tr_edge tr_comb dep_edge dep_comb])
qed

subsection \<open>Generic \<open>st\<close> post-solution transport\<close>

text \<open>
  Every executable generator variant maps its \<open>'a st\<close> post-solution to an abstract
  \<^const>\<open>part_post_solution\<close> under \<^const>\<open>fun_of_st\<close>, and the lifting is identical:
  it depends only on three commutation facts about the specific generator --- \<open>eq\<close>,
  \<open>sides_of_rhs\<close>, and \<open>dep_aux\<close> commute with \<^const>\<open>fun_of_st\<close>.  This lemma packages
  that lifting once; each concrete generator supplies the three facts and applies it.
\<close>

lemma part_post_solution_st_to_abs_transport:
  fixes T_st :: "'u \<Rightarrow> ('u, 'g, ('a::bounded_semilattice_sup_bot) st) strategy_tree"
    and T_abs :: "'u \<Rightarrow> ('u, 'g, 'a abs_state) strategy_tree"
  assumes EQ: "\<And>v \<sigma>. fun_of_st (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_st (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_st (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (T_abs v)"
    and pp: "part_post_solution T_st x sigma_st vars"
  shows "part_post_solution T_abs x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using pp by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_st (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_st (sigma_st k)) v \<subseteq> vars"
      using pp v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_st (sigma_st k)) \<le> (\<lambda>k. fun_of_st (sigma_st k)) (Inl v)"
    proof -
      have le_st: "eq T_st v sigma_st \<le> sigma_st (Inl v)" using pp v_in by simp
      show ?thesis using fun_of_st_mono[OF le_st] EQ by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (sigma_st k)) \<le> (\<lambda>k. fun_of_st (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using pp v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_st (sigma_st k)) k"
        using fun_of_st_mono[OF le_st] SIDES by simp
    qed
  qed
qed

text \<open>
  The exact analogue: an \<^emph>\<open>exact\<close> \<^const>\<open>part_solution\<close> of the executable generator maps,
  under \<^const>\<open>fun_of_st\<close>, to an exact \<^const>\<open>part_solution\<close> of its abstract image.  The
  two abbreviations differ only in the \<open>eq\<close> conjunct (\<open>=\<close> vs \<open>\<le>\<close>); the same three
  commutation facts carry it, with the \<open>eq\<close> branch using the equality directly.  This is
  the enabler for certifying a concrete run whose exactness is established per run
  (via a decidable reverse-inequality \<open>eval\<close> check) against an abstract soundness
  theorem that needs an exact fixpoint.
\<close>

lemma part_solution_st_to_abs_transport:
  fixes T_st :: "'u \<Rightarrow> ('u, 'g, ('a::bounded_semilattice_sup_bot) st) strategy_tree"
    and T_abs :: "'u \<Rightarrow> ('u, 'g, 'a abs_state) strategy_tree"
  assumes EQ: "\<And>v \<sigma>. fun_of_st (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_st (\<sigma> k))"
    and SIDES: "\<And>v \<sigma> k. fun_of_st (sides_of_rhs (T_st v) \<sigma> k)
                  = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
    and DEP: "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (T_abs v)"
    and ps: "part_solution T_st x sigma_st vars"
  shows "part_solution T_abs x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using ps by simp
  have deps: "\<And>v. dep\<^sub>L T_st sigma_st v = dep\<^sub>L T_abs (\<lambda>k. fun_of_st (sigma_st k)) v"
    using DEP by (simp add: dep\<^sub>L_def dep_def)
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L T_abs (\<lambda>k. fun_of_st (sigma_st k)) v \<subseteq> vars"
      using ps v_in deps by auto
    show "eq T_abs v (\<lambda>k. fun_of_st (sigma_st k)) = (\<lambda>k. fun_of_st (sigma_st k)) (Inl v)"
    proof -
      have eq_st: "eq T_st v sigma_st = sigma_st (Inl v)" using ps v_in by simp
      show ?thesis using arg_cong[where f = fun_of_st, OF eq_st] EQ by simp
    qed
    show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (sigma_st k)) \<le> (\<lambda>k. fun_of_st (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (T_st v) sigma_st k \<le> sigma_st k"
        using ps v_in by (simp add: le_fun_def)
      show "sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (sigma_st k)) k
              \<le> (\<lambda>k. fun_of_st (sigma_st k)) k"
        using fun_of_st_mono[OF le_st] SIDES by simp
    qed
  qed
qed

subsection \<open>Transport: executable effectful post-solution to abstract effectful post-solution\<close>

context
  fixes g :: cfg
  fixes etf_st :: "('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "('g, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st :: "'a st"
  fixes gseed :: 'g
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
               = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
  assumes tr_comb:
    "\<And>cc ex \<sigma>_st. fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
                = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
  assumes sd_edge:
    "\<And>a u \<sigma>_st gg. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
               = sides_of_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st) gg"
  assumes sd_comb:
    "\<And>cc ex \<sigma>_st gg. fun_of_st (sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma>_st gg)
                = sides_of_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st) gg"
  assumes dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
               = dep_aux \<sigma>2 (apply_etf etf a u)"
  assumes dep_comb:
    "\<And>cc ex \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st cc ex)
                = dep_aux \<sigma>2 (etf_combine etf cc ex)"
begin

private lemma fun_of_st_eq_cfg_eff_st:
  "fun_of_st (eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st) =
   eq (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed) v (fun_of_st \<circ> \<sigma>_st)"
  unfolding eq_side_cfg_T_eff_st eq_side_cfg_T_eff
  by (simp add: side_acc_eff_st_fun_of_st[OF tr_edge tr_comb])

private lemma fun_of_st_sides_cfg_eff_st:
  "fun_of_st (sides_of_rhs (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v) \<sigma>_st gkey)
   = sides_of_rhs (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed v)
       (fun_of_st \<circ> \<sigma>_st) gkey"
proof (cases "v = cfg_entry g")
  case True
  have fold_sides:
    "\<And>gk. fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st (bot0_st \<squnion> restrict_local_st s0_st)
        (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>_st gk)
     = sides_of_rhs (side_rhs_fold_eff etf (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
        (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
       (fun_of_st \<circ> \<sigma>_st) gk"
    by (simp add: side_rhs_fold_eff_st_sides_fun_of_st[OF sd_edge sd_comb])
  show ?thesis unfolding side_cfg_T_eff_st_def side_cfg_T_eff_def
    make_side_rhs_tree_eff_st_def make_side_rhs_tree_eff_def Let_def
  proof (simp add: True)
    show "fun_of_st ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
            (bot0_st \<squnion> restrict_local_st s0_st)
            (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>_st
          in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_st s0_st)) gkey)
          = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
                (fun_of_st \<circ> \<sigma>_st)
             in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_st s0_st))) gkey"
    proof (cases gkey)
      case (Inl u)
      have "fun_of_st ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
              (bot0_st \<squnion> restrict_local_st s0_st)
              (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>_st
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_st s0_st)) (Inl u))
          = fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st
              (bot0_st \<squnion> restrict_local_st s0_st)
              (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
            \<sigma>_st (Inl u))"
        by (simp add: Let_def)
      also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
            (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
            (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
          (fun_of_st \<circ> \<sigma>_st) (Inl u)"
        by (simp add: fold_sides)
      also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
              (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
            (fun_of_st \<circ> \<sigma>_st)
          in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_st s0_st))) (Inl u)"
        by (simp add: Let_def)
      finally show ?thesis by (simp add: Inl)
    next
      case (Inr gk)
      show ?thesis proof (cases "gk = gseed")
        case True
        have "fun_of_st ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_st s0_st)
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>_st
              in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_st s0_st)) (Inr gseed))
            = fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_st s0_st)
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
              \<sigma>_st (Inr gseed) \<squnion> restrict_global_st s0_st)"
          by (simp add: Let_def True)
        also have "\<dots> = fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_st s0_st)
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
              \<sigma>_st (Inr gseed)) \<squnion> restrict_global (fun_of_st s0_st)"
          by simp
        also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
              (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
            (fun_of_st \<circ> \<sigma>_st) (Inr gseed) \<squnion> restrict_global (fun_of_st s0_st)"
          by (simp add: fold_sides)
        also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
              (fun_of_st \<circ> \<sigma>_st)
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_st s0_st))) (Inr gseed)"
          by (simp add: Let_def True)
        finally show ?thesis by (simp add: Inr True)
      next
        case False
        have "fun_of_st ((let m = sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_st s0_st)
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))) \<sigma>_st
              in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global_st s0_st)) (Inr gk))
            = fun_of_st (sides_of_rhs (side_rhs_fold_eff_st etf_st
                (bot0_st \<squnion> restrict_local_st s0_st)
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
              \<sigma>_st (Inr gk))"
          by (simp add: Let_def False)
        also have "\<dots> = sides_of_rhs (side_rhs_fold_eff etf
              (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
              (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
            (fun_of_st \<circ> \<sigma>_st) (Inr gk)"
          by (simp add: fold_sides)
        also have "\<dots> = (let m = sides_of_rhs (side_rhs_fold_eff etf
                (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
                (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g)))
              (fun_of_st \<circ> \<sigma>_st)
            in m(Inr gseed := m (Inr gseed) \<squnion> restrict_global (fun_of_st s0_st))) (Inr gk)"
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
    by (simp add: side_rhs_fold_eff_st_sides_fun_of_st[OF sd_edge sd_comb])
qed

text \<open>
  An executable post-solution of @{const side_cfg_T_eff_st} maps to a
  @{const part_post_solution} of @{const side_cfg_T_eff} when per-tree traverse,
  side, and dependency denotations commute through @{const fun_of_st}.
\<close>

theorem part_post_solution_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed)
           x (fun_of_st \<circ> \<sigma>_st) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  have deps: "\<And>v. v \<in> vars \<Longrightarrow>
      dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v
    = dep\<^sub>L (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed)
             (fun_of_st \<circ> \<sigma>_st) v"
  proof -
    fix v
    have eq: "dep_aux \<sigma>_st (make_side_rhs_tree_eff_st g etf_st bot0_st s0_st gseed v) =
              dep_aux (fun_of_st \<circ> \<sigma>_st)
                (make_side_rhs_tree_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed v)"
      by (rule dep_aux_make_side_rhs_tree_eff_st_eq[OF tr_edge tr_comb dep_edge dep_comb])
    show "dep\<^sub>L (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) \<sigma>_st v =
          dep\<^sub>L (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed)
                 (fun_of_st \<circ> \<sigma>_st) v"
      by (simp add: dep\<^sub>L_def dep_def side_cfg_T_eff_st_def side_cfg_T_eff_def eq)
  qed
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed)
              (fun_of_st \<circ> \<sigma>_st) v \<subseteq> vars"
      using pp_st v_in deps[OF v_in] by auto
    show "eq (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed) v
             (fun_of_st \<circ> \<sigma>_st) \<le> (fun_of_st \<circ> \<sigma>_st) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed) v \<sigma>_st
                   \<le> \<sigma>_st (Inl v)"
        using pp_st v_in by simp
      show ?thesis
        using fun_of_st_mono[OF le_st] fun_of_st_eq_cfg_eff_st[where v=v] by simp
    qed
    show "sides_of_rhs (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed v)
             (fun_of_st \<circ> \<sigma>_st) \<le> fun_of_st \<circ> \<sigma>_st"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs
               (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) gseed v)
               (fun_of_st \<circ> \<sigma>_st) k \<le> (fun_of_st \<circ> \<sigma>_st) k"
        by (metis comp_apply fun_of_st_mono fun_of_st_sides_cfg_eff_st le_funD pp_st v_in)
      
       
    qed
  qed
qed

end

lemma part_post_solution_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st :: "'a st"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_st g etf_st bot0_st s0_st ()) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
           x (fun_of_st \<circ> \<sigma>_st) vars"
proof -
  interpret sound_rhs_generator_exec etf F etf_st F_st
    using edge comb edge_st comb_st commute by unfold_locales
  have tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st)"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute o_def Let_def)
  have tr_comb:
    "\<And>cc ex \<sigma>_st. fun_of_st (traverse_rhs (etf_combine_st etf_st cc ex) \<sigma>_st)
     = traverse_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st)"
    unfolding comb_st comb traverse_unit_combine_tree_st traverse_unit_combine_tree
    by (simp add: o_def Let_def)
  have sd_edge:
    "\<And>a u \<sigma>_st gg. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st gg)
     = sides_of_rhs (apply_etf etf a u) (fun_of_st \<circ> \<sigma>_st) gg"
    using sides_apply_etf_st .
  have sd_comb:
    "\<And>cc ex \<sigma>_st gg. fun_of_st (sides_of_rhs (etf_combine_st etf_st cc ex) \<sigma>_st gg)
     = sides_of_rhs (etf_combine etf cc ex) (fun_of_st \<circ> \<sigma>_st) gg"
    using sides_etf_combine_st .
  have dep_edge:
    "\<And>a u \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (apply_etf_st etf_st a u)
     = dep_aux \<sigma>2 (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  have dep_comb:
    "\<And>cc ex \<sigma>1 \<sigma>2. dep_aux \<sigma>1 (etf_combine_st etf_st cc ex)
     = dep_aux \<sigma>2 (etf_combine etf cc ex)"
    by (subst comb_st, subst comb, simp add: dep_aux_unit_combine_tree_st)
  show ?thesis
    using part_post_solution_st_to_abs_eff[OF tr_edge tr_comb sd_edge sd_comb dep_edge dep_comb pp_st]
    by simp
qed

lemma inr_slot_locals_bot_fun_of_st_restrict_global_st:
  fixes sigma_st :: "pp + unit \<Rightarrow> ('a::bounded_semilattice_sup_bot) st"
  assumes rg: "\<And>gg. sigma_st (Inr gg) = restrict_global_st (sigma_st (Inr gg))"
  shows "inr_slot_locals_bot (fun_of_st \<circ> sigma_st)"
  unfolding inr_slot_locals_bot_iff_Inr_restrict_global
proof (intro allI)
  fix gg
  show "(fun_of_st \<circ> sigma_st) (Inr gg) = restrict_global ((fun_of_st \<circ> sigma_st) (Inr gg))"
  proof -
    have "fun_of_st (sigma_st (Inr gg)) = fun_of_st (restrict_global_st (sigma_st (Inr gg)))"
      using rg by simp
    thus ?thesis by (simp add: o_def fun_of_st_restrict_global_st)
  qed
qed

text \<open>
  The unit equation system has every reachable \<open>Side\<close> contribution
  \<open>restrict_global_st\<close>-shaped.  This is the structural precondition the
  side-effecting solver consumes to keep its \<open>Inr\<close> slots \<open>restrict_global_st\<close>-shaped
  (the solver-side induction lives where the side solver's \<open>solve\<close> is in scope).
\<close>

lemma side_rg_side_cfg_T_eff_st_unit:
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  assumes edge_st: "\<And>a u. \<exists>f. apply_etf_st etf_st a u = unit_edge_tree_st f u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  shows "side_rg (side_cfg_T_eff_st g etf_st bot0_st s0_st gseed v)"
  unfolding side_cfg_T_eff_st_def
proof (rule side_rg_make_side_rhs_tree_eff_st)
  fix a u show "side_rg (apply_etf_st etf_st a u)"
    using edge_st[of a u] side_rg_unit_edge_tree_st by auto
next
  fix cc ex show "side_rg (etf_combine_st etf_st cc ex)"
    using comb_st[of cc ex] side_rg_unit_combine_tree_st by auto
qed

end
