theory Exec_Bridge
  imports Exec_St TD_Side_IP_Mono "Voblint_CFG.Exec_CFG"
begin

section \<open>S4 bridge: fun_of_st homomorphisms and executable equation-system transport\<close>

text \<open>
  This theory provides the generic (domain-agnostic) half of the S4 soundness bridge.

  1. fun_of_st homomorphisms for the local/global split operations defined in
     Exec_St.thy: restrict_local_st, restrict_global_st, combine_abs_st link to
     their abs_state counterparts restrict_local, restrict_global, combine_abs
     (TD_Side_CFG) via the fun_of_st coercion.

  2. A strategy-tree builder side_rhs_fold_ip_st at 'a st, parameterised over an
     executable transfer function (edge_action => 'a st => 'a st).

  3. Evaluation folds side_acc_ip_st and side_glob_ip_st, plus the analogues of the
     traverse / sides_of_rhs lemmas.

  4. Simulation: given commutation (fun_of_st . apply_tf_st a = apply_tf tf a . fun_of_st),
     fun_of_st intertwines the executable and abstract folds.

  5. make_side_rhs_tree_ip_st / side_cfg_T_ip_st: the full executable equation system.

  6. Transport theorem: a part_post_solution of side_cfg_T_ip_st (at 'a st) maps via
     fun_of_st to a part_post_solution of side_cfg_T_ip (at 'a abs_state).

  7. Code equations that redirect predecessor_list / combine_predecessor_list on a
     compiled program to the executable list-based versions from Exec_CFG.
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
 
(* Direct split lemmas needed for side_rhs_fold_ip_st combine case *)
lemma restrict_local_st_split [simp]:
  "restrict_local_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_local_st A"
  by (simp add: combine_abs_st_def[symmetric])

lemma restrict_global_st_split [simp]:
  "restrict_global_st (restrict_local_st A \<squnion> restrict_global_st B) = restrict_global_st B"
  by (simp add: combine_abs_st_def[symmetric])

subsection \<open>Executable IP fold: side_acc_ip_st and side_glob_ip_st\<close>

text \<open>
  side_acc_ip_st is the 'a st analog of side_acc_ip (TD_Side_IP_Tree): it folds
  the transfer function over incoming ordinary edges, then over combine triples.
  The transfer parameter tf_st :: edge_action => 'a st => 'a st replaces apply_tf.
\<close>

fun side_acc_ip_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st
   \<Rightarrow> (pp + unit \<Rightarrow> 'a st)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> 'a st"
where
  "side_acc_ip_st tf_st acc \<sigma> [] [] = acc"
| "side_acc_ip_st tf_st acc \<sigma> ((u, a) # ps) cs =
     side_acc_ip_st tf_st
       (acc \<squnion> restrict_local_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))))
       \<sigma> ps cs"
| "side_acc_ip_st tf_st acc \<sigma> [] ((cc, ex) # cs) =
     side_acc_ip_st tf_st
       (acc \<squnion> restrict_local_st (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())))
       \<sigma> [] cs"

fun side_glob_ip_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> (pp + unit \<Rightarrow> 'a st)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> 'a st"
where
  "side_glob_ip_st tf_st \<sigma> [] [] = bot"
| "side_glob_ip_st tf_st \<sigma> ((u, a) # ps) cs =
     side_glob_ip_st tf_st \<sigma> ps cs
       \<squnion> restrict_global_st (tf_st a (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
| "side_glob_ip_st tf_st \<sigma> [] ((cc, ex) # cs) =
     side_glob_ip_st tf_st \<sigma> [] cs
       \<squnion> restrict_global_st (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ()))"

subsection \<open>Set-invariance of the IP folds (join is ACI)\<close>

text \<open>
  \<open>side_acc_ip_st\<close> and \<open>side_glob_ip_st\<close> are joins (\<open>\<squnion>\<close>) over the edge / combine
  lists, and \<open>\<squnion>\<close> is commutative, associative and idempotent, so the result
  depends only on the *sets* of edges / combines, not their order or multiplicity.
  This is what lets a solver post-solution over the code-generated
  \<open>predecessor_list_prog\<close> enumeration transfer to the \<open>predecessor_list\<close>
  (sorted) enumeration the soundness chain is stated over.
\<close>

lemma side_acc_ip_st_fold:
  "side_acc_ip_st tf_st acc \<sigma> es cs =
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

lemma side_glob_ip_st_fold:
  "side_glob_ip_st tf_st \<sigma> es cs =
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

lemma side_acc_ip_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "side_acc_ip_st tf_st acc \<sigma> es1 cs1 = side_acc_ip_st tf_st acc \<sigma> es2 cs2"
  by (simp add: side_acc_ip_st_fold assms)

lemma side_glob_ip_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "side_glob_ip_st tf_st \<sigma> es1 cs1 = side_glob_ip_st tf_st \<sigma> es2 cs2"
  by (simp add: side_glob_ip_st_fold assms)

subsection \<open>Simulation: fun_of_st intertwines the executable and abstract folds\<close>

lemma side_acc_ip_st_fun_of_st:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_acc_ip_st tf_st acc_st \<sigma>_st es cs) =
         side_acc_ip tf (\<squnion>) (fun_of_st acc_st) (fun_of_st \<circ> \<sigma>_st) es cs"
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
          side_acc_ip.simps(3) side_acc_ip_st.simps(3))
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH
    by (metis (mono_tags, opaque_lifting) commute comp_apply fun_of_st_restrict_local_st fun_of_st_sup
        side_acc_ip.simps(2) side_acc_ip_st.simps(2))
qed

lemma side_glob_ip_st_fun_of_st:
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "fun_of_st (side_glob_ip_st tf_st \<sigma>_st es cs) =
         side_glob_ip tf (\<squnion>) (fun_of_st \<circ> \<sigma>_st) es cs"
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
          side_glob_ip.simps(3) side_glob_ip_st.simps(3))
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH
    by (metis (no_types, opaque_lifting) commute comp_apply fun_of_st_restrict_global_st fun_of_st_sup
        side_glob_ip.simps(2) side_glob_ip_st.simps(2))
   
qed

subsection \<open>Strategy tree: side_rhs_fold_ip_st\<close>

text \<open>
  The strategy tree at 'a st, mirroring side_rhs_fold_ip (TD_Side_IP_Tree).
  Parameterised over tf_st :: edge_action => 'a st => 'a st.
\<close>

fun side_rhs_fold_ip_st ::
  "(edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> pp) list
   \<Rightarrow> (pp, unit, 'a st) strategy_tree"
where
  "side_rhs_fold_ip_st tf_st acc [] [] = Answer acc"
| "side_rhs_fold_ip_st tf_st acc ((u, a) # ps) cs =
     QueryL u (\<lambda>su. QueryG () (\<lambda>glob.
       let res = tf_st a (su \<squnion> glob)
       in Side () (restrict_global_st res)
            (side_rhs_fold_ip_st tf_st (acc \<squnion> restrict_local_st res) ps cs)))"
| "side_rhs_fold_ip_st tf_st acc [] ((cc, ex) # cs) =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>glob.
       let res = restrict_local_st (sc \<squnion> glob) \<squnion> restrict_global_st (se \<squnion> glob)
       in Side () (restrict_global_st res)
            (side_rhs_fold_ip_st tf_st (acc \<squnion> restrict_local_st res) [] cs))))"

lemma traverse_side_rhs_fold_ip_st:
  "traverse_rhs (side_rhs_fold_ip_st tf_st acc es cs) \<sigma>_st =
   side_acc_ip_st tf_st acc \<sigma>_st es cs"
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

lemma sides_side_rhs_fold_ip_st_Inr:
  "sides_of_rhs (side_rhs_fold_ip_st tf_st acc es cs) \<sigma>_st (Inr ()) =
   side_glob_ip_st tf_st \<sigma>_st es cs"
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

lemma sides_side_rhs_fold_ip_st_Inl:
  "sides_of_rhs (side_rhs_fold_ip_st tf_st acc es cs) \<sigma>_st (Inl u) = bot"
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

subsection \<open>Executable equation system: make_side_rhs_tree_ip_st / side_cfg_T_ip_st\<close>

definition make_side_rhs_tree_ip_st ::
  "cfg
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> pp
   \<Rightarrow> (pp, unit, 'a st) strategy_tree"
where
  "make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v =
     (let acc0 = (if v = cfg_entry g
                  then bot0_st \<squnion> restrict_local_st s0_st
                  else bot0_st);
          t    = side_rhs_fold_ip_st tf_st acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g
         then Side () (restrict_global_st s0_st) t
         else t)"

definition side_cfg_T_ip_st ::
  "cfg
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st \<Rightarrow> 'a st
   \<Rightarrow> (pp, unit, 'a st) eqsT"
where
  "side_cfg_T_ip_st g tf_st bot0_st s0_st = make_side_rhs_tree_ip_st g tf_st bot0_st s0_st"

lemma eq_side_cfg_T_ip_st:
  "eq (side_cfg_T_ip_st g tf_st bot0_st s0_st) v \<sigma>_st =
     side_acc_ip_st tf_st
       (if v = cfg_entry g
        then bot0_st \<squnion> restrict_local_st s0_st
        else bot0_st)
       \<sigma>_st (predecessor_list g v) (combine_predecessor_list g v)"
  unfolding side_cfg_T_ip_st_def make_side_rhs_tree_ip_st_def
  by (simp add: traverse_side_rhs_fold_ip_st Let_def)

lemma sides_make_side_rhs_tree_ip_st_Inr:
  "sides_of_rhs (make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v) \<sigma>_st (Inr ())
   = side_glob_ip_st tf_st \<sigma>_st (predecessor_list g v) (combine_predecessor_list g v)
      \<squnion> (if v = cfg_entry g then restrict_global_st s0_st else bot)"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def
    using True by (simp add: sides_side_rhs_fold_ip_st_Inr)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def
    using False by (simp add: sides_side_rhs_fold_ip_st_Inr)
qed

lemma sides_make_side_rhs_tree_ip_st_Inl:
  "sides_of_rhs (make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v) \<sigma>_st (Inl u) = bot"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def
    using True apply (auto simp add: sides_side_rhs_fold_ip_st_Inl)
    by (metis Inl_Inr_False fun_upd_apply sides_side_rhs_fold_ip_st_Inl)
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def
    using False by (simp add: sides_side_rhs_fold_ip_st_Inl)
qed

subsection \<open>dep_aux of side_rhs_fold_ip_st equals dep_aux of side_rhs_fold_ip\<close>

text \<open>
  Both tree builders traverse the same QueryL / QueryG nodes in the same order;
  they differ only in the computation at each step.  dep_aux is purely structural:
  it follows lambdas with the given sigma but the result is independent of which
  sigma or acc is used (the acc lives inside Side nodes, which dep_aux ignores).
  Therefore both instantiations produce identical dep_aux sets.  Proved by
  simultaneous induction on es/cs, instantiating the IH with the specific
  accumulator that arises in each branch.
\<close>

lemma dep_aux_side_rhs_fold_ip_st_eq_ip:
  "dep_aux \<sigma>_st (side_rhs_fold_ip_st tf_st acc es cs) =
   dep_aux \<sigma>_abs (side_rhs_fold_ip tf join acc' es cs)"
proof (induction es arbitrary: acc acc' cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc acc')
    case Nil thus ?case by simp
  next
    case (Cons c cs acc acc')
    obtain cc ex where c: "c = (cc, ex)" by (cases c)
    show ?case unfolding c
      apply (simp add: dep_aux.simps side_rhs_fold_ip_st.simps side_rhs_fold_ip.simps Let_def)
      by (metis Cons.IH)
  qed
next
  case (Cons e es acc acc' cs)
  obtain u a where e: "e = (u, a)" by (cases e)
  show ?case unfolding e
    apply (simp add: dep_aux.simps side_rhs_fold_ip_st.simps side_rhs_fold_ip.simps Let_def)
    by (metis Cons.IH)
qed

lemma dep_aux_side_rhs_fold_ip_st_set:
  "dep_aux \<sigma> (side_rhs_fold_ip_st tf_st acc es cs) =
   (\<Union>(u, a)\<in>set es. {Inl u, Inr ()}) \<union> (\<Union>(cc, ex)\<in>set cs. {Inl cc, Inl ex, Inr ()})"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by (simp add: dep_aux.simps side_rhs_fold_ip_st.simps)
  next
    case (Cons c cs)
    obtain cc ex where c: "c = (cc, ex)" by (cases c)
    show ?case unfolding c
      by (simp add: dep_aux.simps side_rhs_fold_ip_st.simps Let_def Cons.IH)
  qed
next
  case (Cons e es)
  obtain u a where e: "e = (u, a)" by (cases e)
  show ?case unfolding e
    by (simp add: dep_aux.simps side_rhs_fold_ip_st.simps Let_def Cons.IH)
qed

lemma dep_aux_side_rhs_fold_ip_st_cong:
  assumes "set es1 = set es2" and "set cs1 = set cs2"
  shows "dep_aux \<sigma> (side_rhs_fold_ip_st tf_st acc es1 cs1)
       = dep_aux \<sigma>' (side_rhs_fold_ip_st tf_st acc' es2 cs2)"
  by (simp add: dep_aux_side_rhs_fold_ip_st_set assms)

lemma dep_aux_make_side_rhs_tree_ip_st:
  "dep_aux \<sigma> (make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v)
   = dep_aux \<sigma> (side_rhs_fold_ip_st tf_st
        (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
        (predecessor_list g v) (combine_predecessor_list g v))"
proof (cases "v = cfg_entry g")
  case True
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def using True by simp
next
  case False
  show ?thesis unfolding make_side_rhs_tree_ip_st_def Let_def using False by simp
qed

lemma dep_aux_make_side_rhs_tree_ip_st_eq_ip:
  "dep_aux \<sigma>_st (make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v) =
   dep_aux \<sigma>_abs (make_side_rhs_tree_ip g tf join bot0 s0 v)"
  by (simp add: dep_aux_make_side_rhs_tree_ip_st dep_aux_make_side_rhs_tree_ip
                dep_aux_side_rhs_fold_ip_st_eq_ip)

subsection \<open>Transport: executable part_post_solution \<open>\<Rightarrow>\<close> abstract part_post_solution\<close>

text \<open>
  Given that fun_of_st commutes with the per-edge transfer function tf_st (the
  commutation hypothesis), any part_post_solution of the executable equation system
  side_cfg_T_ip_st at 'a st maps via fun_of_st to a part_post_solution of the
  abstract side_cfg_T_ip at 'a abs_state.

  The proof structure: for each program point v in vars,
  (a) the local equation bound transfers by fun_of_st_mono + simulation;
  (b) the global side-effect bound transfers similarly;
  (c) the local side (Inl) is bot in both systems;
  (d) dependency inclusion is structural (same QueryL/QueryG pattern).
\<close>

context
  fixes g :: cfg
  fixes tf :: "('a::bounded_semilattice_sup_bot) domain_transfer"
  fixes tf_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes bot0_st s0_st :: "'a st"
  assumes commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
begin

private lemma fun_of_st_eq_ip_st:
  "fun_of_st (eq (side_cfg_T_ip_st g tf_st bot0_st s0_st) v \<sigma>_st) =
   eq (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st)) v (fun_of_st \<circ> \<sigma>_st)"
  unfolding eq_side_cfg_T_ip_st eq_side_cfg_T_ip
  by (simp add: side_acc_ip_st_fun_of_st[OF commute]
                fun_of_st_sup fun_of_st_restrict_local_st)

private lemma fun_of_st_sides_ip_st_Inr:
  "fun_of_st (sides_of_rhs (side_cfg_T_ip_st g tf_st bot0_st s0_st v) \<sigma>_st (Inr ())) =
   sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st) v)
     (fun_of_st \<circ> \<sigma>_st) (Inr ())"
  unfolding side_cfg_T_ip_def make_side_rhs_tree_ip_def
  unfolding side_cfg_T_ip_st_def
  by (simp add: commute make_side_rhs_tree_ip_st_def side_glob_ip_st_fun_of_st
      sides_side_rhs_fold_ip_Inr sides_side_rhs_fold_ip_st_Inr)
 

theorem part_post_solution_st_to_abs:
  assumes pp_st:
    "part_post_solution (side_cfg_T_ip_st g tf_st bot0_st s0_st) x \<sigma>_st vars"
  shows
    "part_post_solution
       (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st))
       x (fun_of_st \<circ> \<sigma>_st) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  have deps: "\<And>v. v \<in> vars \<Longrightarrow>
      dep\<^sub>L (side_cfg_T_ip_st g tf_st bot0_st s0_st) \<sigma>_st v
    = dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st))
             (fun_of_st \<circ> \<sigma>_st) v"
  proof -
    fix v
    have eq: "dep_aux \<sigma>_st (make_side_rhs_tree_ip_st g tf_st bot0_st s0_st v) =
              dep_aux (fun_of_st \<circ> \<sigma>_st)
                (make_side_rhs_tree_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st) v)"
      by (rule dep_aux_make_side_rhs_tree_ip_st_eq_ip)
    show "dep\<^sub>L (side_cfg_T_ip_st g tf_st bot0_st s0_st) \<sigma>_st v =
          dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st))
                 (fun_of_st \<circ> \<sigma>_st) v"
      by (simp add: dep\<^sub>L_def dep_def side_cfg_T_ip_st_def side_cfg_T_ip_def eq)
  qed
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st))
              (fun_of_st \<circ> \<sigma>_st) v \<subseteq> vars"
      using pp_st v_in deps[OF v_in] by auto
    show "eq (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st)) v
             (fun_of_st \<circ> \<sigma>_st) \<le> (fun_of_st \<circ> \<sigma>_st) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_ip_st g tf_st bot0_st s0_st) v \<sigma>_st \<le> \<sigma>_st (Inl v)"
        using pp_st v_in by simp
      have sim: "fun_of_st (eq (side_cfg_T_ip_st g tf_st bot0_st s0_st) v \<sigma>_st) =
                 eq (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st))
                    v (fun_of_st \<circ> \<sigma>_st)"
        by (rule fun_of_st_eq_ip_st)
      from fun_of_st_mono[OF le_st] sim show ?thesis by (simp add: o_def)
    qed
    show "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st) v)
             (fun_of_st \<circ> \<sigma>_st) \<le> fun_of_st \<circ> \<sigma>_st"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs
               (side_cfg_T_ip g tf (\<squnion>) (fun_of_st bot0_st) (fun_of_st s0_st) v)
               (fun_of_st \<circ> \<sigma>_st) k
            \<le> (fun_of_st \<circ> \<sigma>_st) k"
        apply(cases k)
        apply(auto)
        apply (simp add: side_cfg_T_ip_def sides_make_side_rhs_tree_ip_Inl)
        by (metis fun_of_st_mono fun_of_st_sides_ip_st_Inr le_fun_def pp_st v_in)
    qed
  qed
qed

end

subsection \<open>Code-generating equation system over the list-built CFG\<close>

text \<open>
  \<open>side_cfg_T_ip_st\<close> calls \<open>predecessor_list (compile_prog ...)\<close>, which does not
  code-generate (sorting needs a \<open>to_nat\<close>-based \<open>edge_action\<close> linorder).
  \<open>side_cfg_T_ip_st_prog\<close> is the same construction reading the predecessor /
  combine lists off the executable list-built CFG (\<open>predecessor_list_prog\<close> /
  \<open>combine_predecessor_list_prog\<close> from Exec_CFG), so it code-generates and can be
  fed to the vendored solver.  When the two enumerations agree as lists (they do
  for straight-line programs, where every point has at most one predecessor), the
  two equation systems are equal, so a solver post-solution of the \<open>prog\<close> system
  is a post-solution of the \<open>compile_prog\<close> system that the soundness chain uses.
\<close>

definition side_cfg_T_ip_st_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) st \<Rightarrow> 'a st)
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> (pp, unit, 'a st) eqsT"
where
  "side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v =
     (let g = compile_prog \<Pi> ps main;
          acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st);
          t = side_rhs_fold_ip_st tf_st acc0
                (predecessor_list_prog \<Pi> ps main v)
                (combine_predecessor_list_prog \<Pi> ps main v)
      in if v = cfg_entry g then Side () (restrict_global_st s0_st) t else t)"

lemma side_cfg_T_ip_st_prog_eq:
  assumes pl: "\<And>v. predecessor_list_prog \<Pi> ps main v
                  = predecessor_list (compile_prog \<Pi> ps main) v"
      and cl: "\<And>v. combine_predecessor_list_prog \<Pi> ps main v
                  = combine_predecessor_list (compile_prog \<Pi> ps main) v"
  shows "side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st
         = side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st"
  unfolding side_cfg_T_ip_st_prog_def side_cfg_T_ip_st_def make_side_rhs_tree_ip_st_def
  by (rule ext) (simp add: Let_def pl cl)

text \<open>
  When the two enumerations agree only as *sets* (the general case -- any program
  point may have several predecessors), the trees differ but their \<open>eq\<close>, \<open>sides\<close>
  and \<open>dep\<close> coincide (the IP folds are set-invariant), so a post-solution of the
  \<open>prog\<close> system is a post-solution of the \<open>compile_prog\<close> system.
\<close>

lemma eq_side_cfg_T_ip_st_prog:
  "eq (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st) v \<sigma> =
     side_acc_ip_st tf_st
       (if v = cfg_entry (compile_prog \<Pi> ps main)
        then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
       \<sigma> (predecessor_list_prog \<Pi> ps main v) (combine_predecessor_list_prog \<Pi> ps main v)"
  unfolding side_cfg_T_ip_st_prog_def Let_def
  by (simp add: traverse_side_rhs_fold_ip_st)

lemma sides_side_cfg_T_ip_st_prog_Inr:
  "sides_of_rhs (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v) \<sigma> (Inr ()) =
     side_glob_ip_st tf_st \<sigma> (predecessor_list_prog \<Pi> ps main v)
        (combine_predecessor_list_prog \<Pi> ps main v)
       \<squnion> (if v = cfg_entry (compile_prog \<Pi> ps main) then restrict_global_st s0_st else bot)"
  unfolding side_cfg_T_ip_st_prog_def Let_def
  by (cases "v = cfg_entry (compile_prog \<Pi> ps main)")
     (simp_all add: sides_side_rhs_fold_ip_st_Inr)

lemma sides_side_cfg_T_ip_st_prog_Inl:
  "sides_of_rhs (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v) \<sigma> (Inl u) = bot"
  unfolding side_cfg_T_ip_st_prog_def Let_def
  by (cases "v = cfg_entry (compile_prog \<Pi> ps main)")
     (simp_all add: sides_side_rhs_fold_ip_st_Inl Let_def)

lemma dep_aux_side_cfg_T_ip_st_prog:
  "dep_aux \<sigma> (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v)
   = dep_aux \<sigma> (side_rhs_fold_ip_st tf_st
        (if v = cfg_entry (compile_prog \<Pi> ps main)
         then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
        (predecessor_list_prog \<Pi> ps main v) (combine_predecessor_list_prog \<Pi> ps main v))"
  unfolding side_cfg_T_ip_st_prog_def Let_def
  by (cases "v = cfg_entry (compile_prog \<Pi> ps main)") (simp_all add: dep_aux.simps)

lemma side_cfg_T_ip_st_prog_part_post:
  assumes pl: "\<And>v. set (predecessor_list_prog \<Pi> ps main v)
                  = set (predecessor_list (compile_prog \<Pi> ps main) v)"
      and cl: "\<And>v. set (combine_predecessor_list_prog \<Pi> ps main v)
                  = set (combine_predecessor_list (compile_prog \<Pi> ps main) v)"
      and pp: "part_post_solution (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st) x \<sigma> vars"
  shows "part_post_solution (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st) x \<sigma> vars"
proof -
  have EQ: "eq (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st) v \<sigma>
          = eq (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st) v \<sigma>" for v
    by (simp add: eq_side_cfg_T_ip_st eq_side_cfg_T_ip_st_prog
          side_acc_ip_st_cong[OF pl cl])
  have SI: "sides_of_rhs (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st v) \<sigma>
          = sides_of_rhs (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v) \<sigma>" for v
  proof (rule ext)
    fix k
    show "sides_of_rhs (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st v) \<sigma> k
        = sides_of_rhs (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st v) \<sigma> k"
    proof (cases k)
      case (Inl u)
      then show ?thesis
        by (simp add: side_cfg_T_ip_st_def sides_make_side_rhs_tree_ip_st_Inl
              sides_side_cfg_T_ip_st_prog_Inl)
    next
      case (Inr y)
      then show ?thesis
        by (simp add: side_cfg_T_ip_st_def sides_make_side_rhs_tree_ip_st_Inr
              sides_side_cfg_T_ip_st_prog_Inr side_glob_ip_st_cong[OF pl cl])
    qed
  qed
  have DEP: "dep\<^sub>L (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st) \<sigma> v
           = dep\<^sub>L (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st) \<sigma> v" for v
    by (simp add: dep\<^sub>L_def dep_def side_cfg_T_ip_st_def
          dep_aux_make_side_rhs_tree_ip_st dep_aux_side_cfg_T_ip_st_prog
          dep_aux_side_rhs_fold_ip_st_set pl cl)
  from pp show ?thesis by (simp add: EQ SI DEP)
qed

text \<open>
  The two enumerations always agree as sets (both equal @{const predecessors} /
  @{const combine_predecessors} of the compiled CFG), so the transfer needs no
  side conditions: a solver post-solution of the code-generated \<open>prog\<close> system is
  a post-solution of the \<open>compile_prog\<close> system the soundness chain uses.
\<close>

lemma side_cfg_T_ip_st_prog_part_post':
  assumes "part_post_solution (side_cfg_T_ip_st_prog \<Pi> ps main tf_st bot0_st s0_st) x \<sigma> vars"
  shows "part_post_solution (side_cfg_T_ip_st (compile_prog \<Pi> ps main) tf_st bot0_st s0_st) x \<sigma> vars"
proof (rule side_cfg_T_ip_st_prog_part_post[OF _ _ assms])
  show "\<And>v. set (predecessor_list_prog \<Pi> ps main v)
          = set (predecessor_list (compile_prog \<Pi> ps main) v)"
    by (simp add: set_predecessor_list_prog set_predecessor_list compile_prog_finite)
  show "\<And>v. set (combine_predecessor_list_prog \<Pi> ps main v)
          = set (combine_predecessor_list (compile_prog \<Pi> ps main) v)"
    by (simp add: set_combine_predecessor_list_prog set_combine_predecessor_list compile_prog_finite)
qed

end
