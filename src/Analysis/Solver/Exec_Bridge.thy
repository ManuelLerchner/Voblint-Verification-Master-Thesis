theory Exec_Bridge
  imports Exec_St TD_Side_Eff_Bounds
begin

section \<open>S4 bridge: fun_of_st homomorphisms and executable equation-system transport\<close>

text \<open>
  This theory provides the generic (domain-agnostic) half of the S4 soundness bridge.

  1. fun_of_st homomorphisms for the local/global split operations defined in
     Exec_St.thy: restrict_local_st, restrict_global_st, combine_abs_st link to
     their abs_state counterparts restrict_local, restrict_global, combine_abs
     (TD_Side_CFG) via the fun_of_st coercion.

  2. A strategy-tree builder side_rhs_fold_st at 'a st, parameterised over an
     executable transfer function (edge_action => 'a st => 'a st).

  3. Evaluation folds side_acc_st and side_glob_st, plus the analogues of the
     traverse / sides_of_rhs lemmas.

  4. Simulation: given commutation (fun_of_st . apply_tf_st a = apply_tf tf a . fun_of_st),
     fun_of_st intertwines the executable and abstract folds.

  5. make_side_rhs_tree_st / side_cfg_T_st: the full executable equation system.

  6. Transport theorem: a part_post_solution of side_cfg_T_st (at 'a st) maps via
     fun_of_st to a part_post_solution of side_cfg_T_eff (etf_from_tf tf).
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
 
(* Direct split lemmas needed for side_rhs_fold_st combine case *)
lemma restrict_local_st_split [simp]:
  "restrict_local_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_local_st A"
  by (simp add: combine_abs_st_def[symmetric])

lemma restrict_global_st_split [simp]:
  "restrict_global_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_global_st B"
  by (simp add: combine_abs_st_def[symmetric])

subsection \<open>Executable IP fold: side_acc_st and side_glob_st\<close>

text \<open>
  side_acc_st is the 'a st analog of side_acc (TD_Side_Tree): it folds
  the transfer function over incoming ordinary edges, then over combine triples.
  The transfer parameter tf_st :: edge_action => 'a st => 'a st replaces apply_tf.
\<close>

fun side_acc_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st
   \<Rightarrow> (pp + unit \<Rightarrow> 'a st)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> 'a st"
where
  "side_acc_st tf_st acc \<sigma> [] [] = acc"
| "side_acc_st tf_st acc \<sigma> ((u, a) # ps) cs =
     side_acc_st tf_st
       (acc \<squnion> restrict_local_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))))
       \<sigma> ps cs"
| "side_acc_st tf_st acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_st tf_st
       (acc \<squnion> restrict_local_st (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())))
       \<sigma> [] cs"

fun side_glob_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> (pp + unit \<Rightarrow> 'a st)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> 'a st"
where
  "side_glob_st tf_st \<sigma> [] [] = bot"
| "side_glob_st tf_st \<sigma> ((u, a) # ps) cs =
     side_glob_st tf_st \<sigma> ps cs
       \<squnion> restrict_global_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
| "side_glob_st tf_st \<sigma> [] ((cc, ex) # cs) =
     side_glob_st tf_st \<sigma> [] cs
       \<squnion> restrict_global_st (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"

subsection \<open>Set-invariance of the IP folds (join is ACI)\<close>

text \<open>
  \<open>side_acc_st\<close> and \<open>side_glob_st\<close> are joins (\<open>\<squnion>\<close>) over the edge / combine
  lists, and \<open>\<squnion>\<close> is commutative, associative and idempotent, so the result
  depends only on the *sets* of edges / combines, not their order or multiplicity.
  The equation system thus does not depend on the particular \<open>predecessor_list\<close>
  enumeration order, only on the predecessor *set* the soundness chain fixes.
\<close>

lemma side_acc_st_fold:
  "side_acc_st tf_st acc \<sigma> es cs =
   acc \<squnion> Finite_Set.fold (\<squnion>) bot
     ((\<lambda>(u, a). restrict_local_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))) ` set es
      \<union> (\<lambda>(cc, ex). restrict_local_st (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ()))) ` set cs)"
proof -
  interpret comp_fun_idem "sup :: 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st" by (rule comp_fun_idem_sup)
  show ?thesis
  proof (induction es arbitrary: acc cs)
    case Nil
    show ?case
    proof (induction cs arbitrary: acc)
      case Nil show ?case by simp
    next
      case (Cons c cs)
      obtain cc ex where c: "c = (cc, ex)" by (cases c)
      show ?case
        using Cons.IH by (simp add: c fold_insert_idem ac_simps)
    qed
  next
    case (Cons e es)
    obtain u a where e: "e = (u, a)" by (cases e)
    show ?case
      using Cons.IH
      by (simp add: e fold_insert_idem image_Un[symmetric] Un_insert_left ac_simps)
  qed
qed

lemma side_glob_st_fold:
  "side_glob_st tf_st \<sigma> es cs =
   Finite_Set.fold (\<squnion>) bot
     ((\<lambda>(u, a). restrict_global_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))) ` set es
      \<union> (\<lambda>(cc, ex). restrict_global_st (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))) ` set cs)"
proof -
  interpret comp_fun_idem "sup :: 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st" by (rule comp_fun_idem_sup)
  show ?thesis
  proof (induction es arbitrary: cs)
    case Nil
    show ?case
    proof (induction cs)
      case Nil show ?case by simp
    next
      case (Cons c cs)
      obtain cc ex where c: "c = (cc, ex)" by (cases c)
      show ?case
        using Cons.IH by (simp add: c fold_insert_idem ac_simps)
    qed
  next
    case (Cons e es)
    obtain u a where e: "e = (u, a)" by (cases e)
    show ?case
      using Cons.IH
      by (simp add: e fold_insert_idem image_Un[symmetric] Un_insert_left ac_simps)
  qed
qed

lemma side_acc_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "side_acc_st tf_st acc \<sigma> es1 cs1 = side_acc_st tf_st acc \<sigma> es2 cs2"
  by (simp add: side_acc_st_fold assms)

lemma side_glob_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "side_glob_st tf_st \<sigma> es1 cs1 = side_glob_st tf_st \<sigma> es2 cs2"
  by (simp add: side_glob_st_fold assms)

subsection \<open>Simulation: fun_of_st intertwines the executable and abstract folds\<close>

lemma side_acc_st_fun_of_st:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_acc_st tf_st acc_st \<sigma>_st es cs) =
         side_acc tf (\<squnion>) (fun_of_st acc_st) (fun_of_st \<circ> \<sigma>_st) es cs"
proof (induction es arbitrary: acc_st cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc_st)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (metis (mono_tags, opaque_lifting) comp_def fun_of_st_restrict_local_st fun_of_st_sup
          side_acc.simps(3) side_acc_st.simps(3))
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH
    by (metis (mono_tags, opaque_lifting) commute comp_apply fun_of_st_restrict_local_st fun_of_st_sup
        side_acc.simps(2) side_acc_st.simps(2))
qed

lemma side_glob_st_fun_of_st:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_glob_st tf_st \<sigma>_st es cs) =
         side_glob tf (\<squnion>) (fun_of_st \<circ> \<sigma>_st) es cs"
proof (induction es arbitrary: cs)
  case Nil
  then show ?case
  proof (induction cs)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (metis (mono_tags, opaque_lifting) comp_apply fun_of_st_restrict_global_st fun_of_st_sup
          side_glob.simps(3) side_glob_st.simps(3))
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH
    by (metis (no_types, opaque_lifting) commute comp_apply fun_of_st_restrict_global_st fun_of_st_sup
        side_glob.simps(2) side_glob_st.simps(2))
   
qed

subsection \<open>Simulation against the effectful shim fold\<close>

text \<open>
  fun_of_st simulation against the effectful shim fold side_acc_eff (etf_from_tf tf)
  and its global side contributions.  These lemmas drive the transport theorem
  part_post_solution_st_to_abs_eff without going through the pure fold.
\<close>

lemma side_acc_st_fun_of_st_eff:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_acc_st tf_st acc_st \<sigma>_st es cs) =
         side_acc_eff (etf_from_tf tf) (fun_of_st acc_st) (fun_of_st \<circ> \<sigma>_st) es cs"
proof (induction es arbitrary: acc_st cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc_st)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have "fun_of_st (side_acc_st tf_st acc_st \<sigma>_st [] (x # cs))
        = fun_of_st (side_acc_st tf_st
            (acc_st \<squnion> restrict_local_st (\<sigma>_st (Inl cc) \<squnion> \<sigma>_st (Inr ()))) \<sigma>_st [] cs)"
      unfolding x by simp
    also have "... = side_acc_eff (etf_from_tf tf)
            (fun_of_st (acc_st \<squnion> restrict_local_st (\<sigma>_st (Inl cc) \<squnion> \<sigma>_st (Inr ()))))
            (fun_of_st \<circ> \<sigma>_st) [] cs"
      by (rule Cons.IH)
    also have "... = side_acc_eff (etf_from_tf tf) (fun_of_st acc_st)
            (fun_of_st \<circ> \<sigma>_st) [] (x # cs)"
      unfolding x
      by (simp add: side_acc_eff.simps(3) traverse_pure_combine_tree
            fun_of_st_sup fun_of_st_restrict_local_st o_def)
    finally show ?case .
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "fun_of_st (side_acc_st tf_st acc_st \<sigma>_st (x # es) cs)
      = fun_of_st (side_acc_st tf_st
          (acc_st \<squnion> restrict_local_st (tf_st a (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))) \<sigma>_st es cs)"
    unfolding x by simp
  also have "... = side_acc_eff (etf_from_tf tf)
          (fun_of_st (acc_st \<squnion> restrict_local_st (tf_st a (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))))
          (fun_of_st \<circ> \<sigma>_st) es cs"
    by (rule Cons.IH)
  also have "... = side_acc_eff (etf_from_tf tf) (fun_of_st acc_st)
          (fun_of_st \<circ> \<sigma>_st) (x # es) cs"
    unfolding x
    by (simp add: side_acc_eff.simps(2) traverse_pure_edge_tree
          fun_of_st_sup fun_of_st_restrict_local_st commute o_def)
  finally show ?case .
qed

lemma sides_eff_fold_edge_step:
  "sides_of_rhs (side_rhs_fold_eff etf acc ((u, a) # es) cs) \<sigma> (Inr ())
   = sides_of_rhs (apply_etf etf a u) \<sigma> (Inr ())
     \<squnion> sides_of_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> (Inr ())"
proof -
  have "sides_of_rhs (side_rhs_fold_eff etf
          (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) es cs) \<sigma> (Inr ())
      = sides_of_rhs (side_rhs_fold_eff etf acc es cs) \<sigma> (Inr ())"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_acc_indep])
  thus ?thesis by (simp add: side_rhs_fold_eff.simps sides_of_rhs_seqcomp sup_apply)
qed

lemma sides_eff_fold_combine_step:
  "sides_of_rhs (side_rhs_fold_eff etf acc [] ((cc, ex) # cs)) \<sigma> (Inr ())
   = sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr ())
     \<squnion> sides_of_rhs (side_rhs_fold_eff etf acc [] cs) \<sigma> (Inr ())"
proof -
  have "sides_of_rhs (side_rhs_fold_eff etf
          (acc \<squnion> traverse_rhs (etf_combine etf cc ex) \<sigma>) [] cs) \<sigma> (Inr ())
      = sides_of_rhs (side_rhs_fold_eff etf acc [] cs) \<sigma> (Inr ())"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_acc_indep])
  thus ?thesis by (simp add: side_rhs_fold_eff.simps sides_of_rhs_seqcomp sup_apply)
qed

lemma side_glob_st_fun_of_st_eff:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_glob_st tf_st \<sigma>_st es cs) =
         sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc es cs) (fun_of_st \<circ> \<sigma>_st) (Inr ())"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have ih: "fun_of_st (side_glob_st tf_st \<sigma>_st [] cs)
            = sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc [] cs) (fun_of_st \<circ> \<sigma>_st) (Inr ())"
      by (rule Cons.IH)
    have "fun_of_st (side_glob_st tf_st \<sigma>_st [] (x # cs))
        = restrict_global (fun_of_st (\<sigma>_st (Inl ex)) \<squnion> fun_of_st (\<sigma>_st (Inr ())))
          \<squnion> sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc [] cs) (fun_of_st \<circ> \<sigma>_st) (Inr ())"
      unfolding x by (simp add: fun_of_st_sup fun_of_st_restrict_global_st ih sup.commute)
    also have "... = sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc [] (x # cs))
            (fun_of_st \<circ> \<sigma>_st) (Inr ())"
      unfolding x
      by (simp del: side_rhs_fold_eff.simps
            add: sides_eff_fold_combine_step sides_pure_combine_tree_Inr o_def sup.commute)
    finally show ?case .
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have ih: "fun_of_st (side_glob_st tf_st \<sigma>_st es cs)
          = sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc es cs) (fun_of_st \<circ> \<sigma>_st) (Inr ())"
    by (rule Cons.IH)
  have "fun_of_st (side_glob_st tf_st \<sigma>_st (x # es) cs)
      = restrict_global (apply_tf tf a (fun_of_st (\<sigma>_st (Inl u)) \<squnion> fun_of_st (\<sigma>_st (Inr ()))))
        \<squnion> sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc es cs) (fun_of_st \<circ> \<sigma>_st) (Inr ())"
    unfolding x
    by (simp add: fun_of_st_sup fun_of_st_restrict_global_st commute ih sup.commute)
  also have "... = sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc (x # es) cs)
          (fun_of_st \<circ> \<sigma>_st) (Inr ())"
    unfolding x
    by (simp del: side_rhs_fold_eff.simps
          add: sides_eff_fold_edge_step sides_pure_edge_tree_Inr o_def sup.commute)
  finally show ?case .
qed

subsection \<open>Strategy tree: side_rhs_fold_st\<close>

text \<open>
  The strategy tree at 'a st, mirroring side_rhs_fold (TD_Side_Tree).
  Parameterised over tf_st :: edge_action => 'a st => 'a st.
\<close>

fun side_rhs_fold_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> (pp, unit, 'a st) strategy_tree"
where
  "side_rhs_fold_st tf_st acc [] [] = Answer acc"
| "side_rhs_fold_st tf_st acc ((u, a) # ps) cs =
     QueryL u (\<lambda>su. QueryG () (\<lambda>glob.
       let res = tf_st a (su \<squnion> glob)
       in Side () (restrict_global_st res)
            (side_rhs_fold_st tf_st (acc \<squnion> restrict_local_st res) ps cs)))"
| "side_rhs_fold_st tf_st acc [] ((cc, ex) # cs) =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>glob.
       let res = restrict_local_st (sc \<squnion> glob) \<squnion> restrict_global_st (se \<squnion> glob)
       in Side () (restrict_global_st res)
            (side_rhs_fold_st tf_st (acc \<squnion> restrict_local_st res) [] cs))))"

lemma traverse_side_rhs_fold_st:
  "traverse_rhs (side_rhs_fold_st tf_st acc es cs) \<sigma>_st =
   side_acc_st tf_st acc \<sigma>_st es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (simp add: Let_def restrict_local_st_combine_abs_st)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma sides_side_rhs_fold_st_Inr:
  "sides_of_rhs (side_rhs_fold_st tf_st acc es cs) \<sigma>_st (Inr ()) =
   side_glob_st tf_st \<sigma>_st es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH
      by (simp add: Let_def restrict_global_st_combine_abs_st)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma sides_side_rhs_fold_st_Inl:
  "sides_of_rhs (side_rhs_fold_st tf_st acc es cs) \<sigma>_st (Inl u) = bot"
proof (induction es arbitrary: acc cs)
  case Nil
  then show ?case
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    show ?case unfolding x using Cons.IH by (simp add: Let_def)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

subsection \<open>Executable equation system: make_side_rhs_tree_st / side_cfg_T_st\<close>

definition make_side_rhs_tree_st ::
  "cfg
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a st) strategy_tree"
where
  "make_side_rhs_tree_st g tf_st bot0_st s0_st v =
     (let acc0 = (if v = cfg_entry g
                  then bot0_st \<squnion> restrict_local_st s0_st
                  else bot0_st);
          t    = side_rhs_fold_st tf_st acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g
         then Side () (restrict_global_st s0_st) t
         else t)"

definition side_cfg_T_st ::
  "cfg
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st \<Rightarrow> 'a st
   \<Rightarrow> (pp, unit, 'a st) eqsT"
where
  "side_cfg_T_st g tf_st bot0_st s0_st = make_side_rhs_tree_st g tf_st bot0_st s0_st"

lemma eq_side_cfg_T_st:
  "eq (side_cfg_T_st g tf_st bot0_st s0_st) v \<sigma>_st =
     side_acc_st tf_st
       (if v = cfg_entry g
        then bot0_st \<squnion> restrict_local_st s0_st
        else bot0_st)
       \<sigma>_st (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_st_def make_side_rhs_tree_st_def
  by (simp add: traverse_side_rhs_fold_st Let_def)

lemma sides_make_side_rhs_tree_st_Inr:
  "sides_of_rhs (make_side_rhs_tree_st g tf_st bot0_st s0_st v) \<sigma>_st (Inr ())
   = side_glob_st tf_st \<sigma>_st (predecessor_list g v) (combine_predecessor_list g v)
      \<squnion> (if v = cfg_entry g then restrict_global_st s0_st else bot)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def
    using True by (simp add: sides_side_rhs_fold_st_Inr)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def
    using False by (simp add: sides_side_rhs_fold_st_Inr)
qed

lemma sides_make_side_rhs_tree_st_Inl:
  "sides_of_rhs (make_side_rhs_tree_st g tf_st bot0_st s0_st v) \<sigma>_st (Inl u) = bot"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def
    using True apply (auto simp add: sides_side_rhs_fold_st_Inl)
    by (metis Inl_Inr_False fun_upd_apply sides_side_rhs_fold_st_Inl)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def
    using False by (simp add: sides_side_rhs_fold_st_Inl)
qed

subsection \<open>dep_aux of side_rhs_fold_st equals dep_aux of side_rhs_fold\<close>

text \<open>
  Both tree builders traverse the same QueryL / QueryG nodes in the same order;
  they differ only in the computation at each step.  dep_aux is purely structural:
  it follows lambdas with the given sigma but the result is independent of which
  sigma or acc is used (the acc lives inside Side nodes, which dep_aux ignores).
  Therefore both instantiations produce identical dep_aux sets.  Proved by
  simultaneous induction on es/cs, instantiating the IH with the specific
  accumulator that arises in each branch.
\<close>

lemma dep_aux_side_rhs_fold_st_set:
  "dep_aux \<sigma> (side_rhs_fold_st tf_st acc es cs) =
   (\<Union>(u, a)\<in>set es. {Inl u, Inr ()}) \<union> (\<Union>(cc, ex)\<in>set cs. {Inl cc, Inl ex, Inr ()})"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by (simp add: dep_aux.simps side_rhs_fold_st.simps)
  next
    case (Cons c cs)
    obtain cc ex where c: "c = (cc, ex)" by (cases c)
    show ?case unfolding c
      by (simp add: dep_aux.simps side_rhs_fold_st.simps Let_def Cons.IH)
  qed
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  show ?case unfolding e
    by (simp add: dep_aux.simps side_rhs_fold_st.simps Let_def Cons.IH)
qed

lemma dep_aux_side_rhs_fold_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "dep_aux \<sigma> (side_rhs_fold_st tf_st acc es1 cs1)
       = dep_aux \<sigma>' (side_rhs_fold_st tf_st acc' es2 cs2)"
  by (simp add: dep_aux_side_rhs_fold_st_set assms)

lemma dep_aux_make_side_rhs_tree_st:
  "dep_aux \<sigma> (make_side_rhs_tree_st g tf_st bot0_st s0_st v)
   = dep_aux \<sigma> (side_rhs_fold_st tf_st
        (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
        (predecessor_list g v) (combine_predecessor_list g v))"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def using True by simp
next
  case False
  show ?thesis unfolding make_side_rhs_tree_st_def Let_def using False by simp
qed

subsection \<open>Transport: executable part_post_solution \<open>\<Rightarrow>\<close> effectful part_post_solution\<close>

text \<open>
  The shim effectful fold queries exactly the same unknowns as the executable
  st fold: each edge contributes its source local and the global, each combine
  its call/exit locals and the global.  So both dep_aux sets coincide.
\<close>
lemma dep_aux_side_rhs_fold_eff_from_tf_set:
  "dep_aux \<sigma> (side_rhs_fold_eff (etf_from_tf tf) acc es cs) =
   (\<Union>(u, a)\<in>set es. {Inl u, Inr ()}) \<union> (\<Union>(cc, ex)\<in>set cs. {Inl cc, Inl ex, Inr ()})"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons c cs)
    obtain cc ex where c: "c = (cc, ex)" by (cases c)
    show ?case unfolding c
      by (simp add: side_rhs_fold_eff.simps dep_aux_seqcomp etf_combine_from_tf
            pure_combine_tree_def Let_def Cons.IH)
  qed
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  show ?case unfolding e
    by (simp add: side_rhs_fold_eff.simps dep_aux_seqcomp apply_etf_from_tf
          pure_edge_tree_def Let_def Cons.IH)
qed

lemma dep_aux_make_side_rhs_tree_st_eq_eff:
  "dep_aux \<sigma>_st (make_side_rhs_tree_st g tf_st bot0_st s0_st v) =
   dep_aux \<sigma>_abs (make_side_rhs_tree_eff g (etf_from_tf tf) bot0 s0 v)"
  by (simp add: dep_aux_make_side_rhs_tree_st dep_aux_make_side_rhs_tree_eff
        dep_aux_side_rhs_fold_st_set dep_aux_side_rhs_fold_eff_from_tf_set)

text \<open>The shim fold only side-effects the global slot, so local sides are bot.\<close>
lemma sides_side_rhs_fold_eff_from_tf_Inl:
  "sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) acc es cs) \<sigma> (Inl u) = bot"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons c cs)
    obtain cc ex where c: "c = (cc, ex)" by (cases c)
    show ?case unfolding c
      by (simp add: side_rhs_fold_eff.simps sides_of_rhs_seqcomp sup_apply
            etf_combine_from_tf pure_combine_tree_def Let_def Cons.IH)
  qed
next
  case (Cons e es)
  obtain w b where e: "e = (w, b)" by (cases e)
  show ?case unfolding e
    by (simp add: side_rhs_fold_eff.simps sides_of_rhs_seqcomp sup_apply
          apply_etf_from_tf pure_edge_tree_def Let_def Cons.IH)
qed

lemma sides_make_side_rhs_tree_eff_from_tf_Inl:
  "sides_of_rhs (make_side_rhs_tree_eff g (etf_from_tf tf) bot0 s0 v) \<sigma> (Inl u) = bot"
  unfolding make_side_rhs_tree_eff_def
  by (simp add: sides_side_rhs_fold_eff_from_tf_Inl Let_def)

context
  fixes g :: cfg
  fixes tf :: "('a::bounded_semilattice_sup_bot) domain_transfer"
  fixes tf_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes bot0_st s0_st :: "'a st"
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
begin

private lemma fun_of_st_eq_st_eff:
  "fun_of_st (eq (side_cfg_T_st g tf_st bot0_st s0_st) v \<sigma>_st) =
   eq (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st)) v (fun_of_st \<circ> \<sigma>_st)"
  unfolding eq_side_cfg_T_st eq_side_cfg_T_eff
  by (simp add: side_acc_st_fun_of_st_eff[OF commute]
                fun_of_st_sup fun_of_st_restrict_local_st)

private lemma fun_of_st_sides_st_Inr_eff:
  "fun_of_st (sides_of_rhs (side_cfg_T_st g tf_st bot0_st s0_st v) \<sigma>_st (Inr ())) =
   sides_of_rhs (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st) v)
     (fun_of_st \<circ> \<sigma>_st) (Inr ())"
proof (cases "v = cfg_entry g")
  case True
  have acc_eq:
    "sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf)
         (fun_of_st bot0_st \<squnion> restrict_local (fun_of_st s0_st))
         (predecessor_list g v) (combine_predecessor_list g v))
       (fun_of_st \<circ> \<sigma>_st) (Inr ()) =
     sides_of_rhs (side_rhs_fold_eff (etf_from_tf tf) (fun_of_st bot0_st)
         (predecessor_list g v) (combine_predecessor_list g v))
       (fun_of_st \<circ> \<sigma>_st) (Inr ())"
    by (rule fun_cong[OF sides_side_rhs_fold_eff_acc_indep])
  show ?thesis
    unfolding side_cfg_T_st_def side_cfg_T_eff_def
              make_side_rhs_tree_st_def make_side_rhs_tree_eff_def
    using True
    using acc_eq by (auto simp add: sides_side_rhs_fold_st_Inr Let_def
                  side_glob_st_fun_of_st_eff[OF commute, where acc="fun_of_st bot0_st"]
                  acc_eq fun_of_st_sup fun_of_st_restrict_global_st)
next
  case False
  show ?thesis
    unfolding side_cfg_T_st_def side_cfg_T_eff_def
              make_side_rhs_tree_st_def make_side_rhs_tree_eff_def
    using False
    by (simp add: sides_side_rhs_fold_st_Inr Let_def
                  side_glob_st_fun_of_st_eff[OF commute, where acc="fun_of_st bot0_st"]
                  fun_of_st_sup)
qed

text \<open>
  Executable post-solution maps directly to a part_post_solution of the effectful
  shim equation system \<open>side_cfg_T_eff (etf_from_tf tf)\<close>.  Proof structure:
  (a) the local equation bound transfers via fun_of_st_eq_st_eff;
  (b) the global side-effect bound via fun_of_st_sides_st_Inr_eff;
  (c) local sides are bot by sides_make_side_rhs_tree_eff_from_tf_Inl;
  (d) dependencies agree by dep_aux_make_side_rhs_tree_st_eq_eff.
\<close>
theorem part_post_solution_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_st g tf_st bot0_st s0_st) x \<sigma>_st vars"
  shows
    "part_post_solution
       (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st))
       x (fun_of_st \<circ> \<sigma>_st) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  have deps: "\<And>v. v \<in> vars \<Longrightarrow>
      dep\<^sub>L (side_cfg_T_st g tf_st bot0_st s0_st) \<sigma>_st v
    = dep\<^sub>L (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st))
             (fun_of_st \<circ> \<sigma>_st) v"
  proof -
    fix v
    have eq: "dep_aux \<sigma>_st (make_side_rhs_tree_st g tf_st bot0_st s0_st v) =
              dep_aux (fun_of_st \<circ> \<sigma>_st)
                (make_side_rhs_tree_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st) v)"
      by (rule dep_aux_make_side_rhs_tree_st_eq_eff)
    show "dep\<^sub>L (side_cfg_T_st g tf_st bot0_st s0_st) \<sigma>_st v =
          dep\<^sub>L (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st))
                 (fun_of_st \<circ> \<sigma>_st) v"
      by (simp add: dep\<^sub>L_def dep_def side_cfg_T_st_def side_cfg_T_eff_def eq)
  qed
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st))
              (fun_of_st \<circ> \<sigma>_st) v \<subseteq> vars"
      using pp_st v_in deps[OF v_in] by auto
    show "eq (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st)) v
             (fun_of_st \<circ> \<sigma>_st) \<le> (fun_of_st \<circ> \<sigma>_st) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_st g tf_st bot0_st s0_st) v \<sigma>_st \<le> \<sigma>_st (Inl v)"
        using pp_st v_in by simp
      have sim: "fun_of_st (eq (side_cfg_T_st g tf_st bot0_st s0_st) v \<sigma>_st) =
                 eq (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st))
                    v (fun_of_st \<circ> \<sigma>_st)"
        by (rule fun_of_st_eq_st_eff)
      from fun_of_st_mono[OF le_st] sim show ?thesis by (simp add: o_def)
    qed
    show "sides_of_rhs (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st) v)
             (fun_of_st \<circ> \<sigma>_st) \<le> fun_of_st \<circ> \<sigma>_st"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs
               (side_cfg_T_eff g (etf_from_tf tf) (fun_of_st bot0_st) (fun_of_st s0_st) v)
               (fun_of_st \<circ> \<sigma>_st) k
            \<le> (fun_of_st \<circ> \<sigma>_st) k"
        apply (cases k)
        apply auto
        apply (simp add: side_cfg_T_eff_def sides_make_side_rhs_tree_eff_from_tf_Inl)
        by (metis fun_of_st_mono fun_of_st_sides_st_Inr_eff le_fun_def pp_st v_in)
    qed
  qed
qed

end


end
