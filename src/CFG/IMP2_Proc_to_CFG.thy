theory IMP2_Proc_to_CFG
  imports CFG_Def "Voblint_IMP2.IMP2_Proc"
begin

section \<open>Interprocedural CFG compilation for `com` programs\<close>

text \<open>
  Whole-program layout:
    - each procedure body compiled once at a fresh offset;
    - call sites get enter edges `(call, EA_Enter formals actuals, proc_entry)`;
    - returns use combine metadata `(call, proc_exit, return, dst)` in `combines g`;
      the callee publishes its result into ret_var, so combine only needs dst.
\<close>

type_synonym proc_info =
  "pp * pp * pp set * (pp * edge_action * pp) set * combine_info set"

type_synonym proc_layout = "pname => proc_info option"

fun compile ::
  "proc_table => proc_layout => com => nat =>
   nat * pp * pp * (pp * edge_action * pp) set * combine_info set"
where
    "compile \<Pi> lay SKIP n =
       (n + 2, n, n + 1, {(n, EA_Nop, n + 1)}, {})"

  | "compile \<Pi> lay (Assign x a) n =
       (n + 2, n, n + 1, {(n, EA_Assign x a, n + 1)}, {})"

  | "compile \<Pi> lay (Seq c1 c2) n =
       (let (n1, en1, ex1, E1, C1) = compile \<Pi> lay c1 n;
            (n2, en2, ex2, E2, C2) = compile \<Pi> lay c2 n1
        in  (n2, en1, ex2, 
             E1 Un (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) Un E2,
             C1 Un C2))"

  | "compile \<Pi> lay (If b c1 c2) n =
       (let en  = n;
            (n1, en1, ex1, E1, C1) = compile \<Pi> lay c1 (n + 1);
            (n2, en2, ex2, E2, C2) = compile \<Pi> lay c2 n1;
            xn  = n2
        in  (n2 + 1, en, xn,
             {(en, EA_Assume b,    en1),
              (en, EA_AssumeNot b, en2)}
             Un E1 Un E2
             Un {(ex1, EA_Nop, xn),
                 (ex2, EA_Nop, xn)},
             C1 Un C2))"

  | "compile \<Pi> lay (While b c) n =
       (let head = n;
            (n1, en1, ex1, E1, C1) = compile \<Pi> lay c (n + 1);
            xn  = n1
        in  (n1 + 1, head, xn,
             {(head, EA_Assume b,    en1),
              (head, EA_AssumeNot b, xn)}
             Un E1
             Un {(ex1, EA_Nop, head)},
             C1))"

  | "compile \<Pi> lay (Scope c) n =
       (let (n', en, ex, E, C) = compile \<Pi> lay c (n + 1);
            scope_ex = n'
        in  (n' + 1, n, scope_ex,
             E Un {(n, EA_Enter [] [], en)},
             C Un {(n, ex, scope_ex, None)}))"

  | "compile \<Pi> lay (Call dst p actuals) n =
       (case (\<Pi> p, lay p) of
          (Some decl, Some (en_p, ex_p, Ns_p, E_p, C_p)) =>
            (n + 2, n, n + 1,
             {(n, EA_Enter (formals decl) actuals, en_p)},
             {(n, ex_p, n + 1, dst)})
        | _ => (n + 2, n, n, {}, {}))"

  | "compile \<Pi> lay Restore n =
       (n, n, n, {}, {})"

definition known_proc_layout :: "proc_table => pname list => proc_layout => proc_layout" where
  "known_proc_layout \<Pi> ps lay =
     (\<lambda>p. case lay p of
            Some info => Some info
          | None => if p \<in> set ps \<and> \<Pi> p \<noteq> None then Some (0, 0, {}, {}, {}) else None)"

fun compile_procs_layout ::
  "proc_table => pname list => proc_layout => nat => nat * proc_layout"
where
    "compile_procs_layout \<Pi> [] lay n = (n, lay)"

  | "compile_procs_layout \<Pi> (p # ps) lay n =
       (case \<Pi> p of
          None => compile_procs_layout \<Pi> ps lay n
        | Some decl =>
            (let complete_lay = known_proc_layout \<Pi> (p # ps) lay;
                 (n', en, ex, E, C) = compile \<Pi> complete_lay (with_result (body decl) (result decl)) n;
                 lay' = (case lay p of
                           None => (lay (p := Some (en, ex, {n..<n'}, {}, {})))
                         | Some _ => lay);
                 (n'', lay'') = compile_procs_layout \<Pi> ps lay' n'
             in  (n'', lay'')))"

fun compile_procs_bodies ::
  "proc_table => pname list => proc_layout => proc_layout => nat =>
   nat * proc_layout * (pp * edge_action * pp) set * combine_info set"
where
    "compile_procs_bodies \<Pi> [] base_lay full_lay n = (n, full_lay, {}, {})"

  | "compile_procs_bodies \<Pi> (p # ps) base_lay full_lay n =
       (case \<Pi> p of
          None => compile_procs_bodies \<Pi> ps base_lay full_lay n
        | Some decl =>
            (let (n', en, ex, E, C) = compile \<Pi> base_lay (with_result (body decl) (result decl)) n;
                 full_lay' = (case full_lay p of
                                None => (full_lay (p := Some (en, ex, {n..<n'}, E, C)))
                              | Some _ => full_lay);
                 (n'', full_lay'', Eacc, Cacc) = compile_procs_bodies \<Pi> ps base_lay full_lay' n'
             in  (n'', full_lay'', E Un Eacc, C Un Cacc)))"

definition compile_procs_list ::
  "proc_table => pname list => proc_layout => nat =>
   nat * proc_layout * (pp * edge_action * pp) set * combine_info set"
where
  "compile_procs_list \<Pi> ps lay n =
     (let (n', base_lay) = compile_procs_layout \<Pi> ps lay n;
          (n'', full_lay, E, C) = compile_procs_bodies \<Pi> ps base_lay lay n
      in (n'', full_lay, E, C))"


definition proc_info_pp_list :: "proc_info \<Rightarrow> pp list" where
  "proc_info_pp_list info =
     (case info of (en, ex, Ns, E, C) \<Rightarrow> sorted_list_of_set ({en, ex} \<union> Ns))"

definition proc_info_nodes :: "proc_info \<Rightarrow> pp set" where
  "proc_info_nodes info = set (proc_info_pp_list info)"

fun fold_proc_pps :: "pname list \<Rightarrow> proc_layout \<Rightarrow> pp set" where
  "fold_proc_pps [] lay = {}"
| "fold_proc_pps (p # ps) lay =
     (case lay p of
        None \<Rightarrow> fold_proc_pps ps lay
      | Some info \<Rightarrow> proc_info_nodes info \<union> fold_proc_pps ps lay)"

definition main_region_pp_list ::
  "proc_info \<Rightarrow> pname list \<Rightarrow> proc_layout \<Rightarrow> pp list" where
  "main_region_pp_list info ps lay =
     sorted_list_of_set (proc_info_nodes info - fold_proc_pps ps lay)"

type_synonym proc_region_list = "pname option \<times> pp list"

fun proc_list_regions :: "pname list \<Rightarrow> proc_layout \<Rightarrow> proc_region_list list" where
  "proc_list_regions [] lay = []"
| "proc_list_regions (p # ps) lay =
     (case lay p of
        None \<Rightarrow> proc_list_regions ps lay
      | Some info \<Rightarrow> (Some p, proc_info_pp_list info) # proc_list_regions ps lay)"

definition compile_prog_with_regions ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> cfg \<times> proc_region_list list" where
  "compile_prog_with_regions \<Pi> ps main =
     (let (n1, lay, E_proc, C_proc) = compile_procs_list \<Pi> ps (\<lambda>_. None) 0;
          (n2, en, ex, E_main, C_main) = compile \<Pi> lay main n1;
          g = mk_cfg en ex (E_proc \<union> E_main) (C_proc \<union> C_main);
          main_reg = (None, main_region_pp_list (en, ex, {n1..<n2}, E_main, C_main) ps lay)
      in  (g, main_reg # proc_list_regions ps lay))"

definition compile_prog ::
  "proc_table => pname list => com => cfg"
where
  "compile_prog \<Pi> ps main = fst (compile_prog_with_regions \<Pi> ps main)"

definition compile_prog_regions ::
  "proc_table => pname list => com => proc_region_list list"
where
  "compile_prog_regions \<Pi> ps main = snd (compile_prog_with_regions \<Pi> ps main)"

text \<open>
  Reusable simp bundle for evaluating @{const compile_prog} on a concrete program.
  After unfolding with these rules, blast closes the resulting set
  equality (Suc-form on both sides after @{thm [source] eval_nat_numeral}).
  For programs without procedure calls, auto alone suffices.
\<close>
lemmas compile_eval_simps =
  compile_prog_def compile_prog_with_regions_def compile_procs_list_def
  known_proc_layout_def eval_nat_numeral



subsection \<open>Freshness / finiteness\<close>

lemma compile_counter_mono:
  "compile \<Pi> lay c n = (n', en, ex, E, C) \<Longrightarrow> n \<le> n'"
proof (induction c arbitrary: n n' en ex E C rule: com.induct)
  case SKIP then show ?case by auto
next
  case (Assign x a) then show ?case by auto
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and n': "n' = n2"
    by (auto split: prod.splits)
  show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] n' by simp
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 (Suc n) = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and n': "n' = Suc n2"
    by (auto split: prod.splits)
  show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] n' by simp
next
  case (While b c)
  then obtain n1 en1 ex1 E1 C1 where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and n': "n' = Suc n1"
    by (auto split: prod.splits)
  show ?case using While.IH[OF c] n' by simp
next
  case (Scope c)
  then obtain n1 en1 ex1 E1 C1 scope_ex where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and n': "n' = Suc n1"
    and ex: "ex = scope_ex"
    by (auto split: prod.splits)
  show ?case using Scope.IH[OF c] n' by simp
next
  case (Call dst p actuals) then show ?case by (auto split: option.splits prod.splits)
next
  case Restore then show ?case by auto
qed

lemma compile_finite:
  "compile \<Pi> lay c n = (n', en, ex, E, C) \<Longrightarrow> finite E \<and> finite C"
proof (induction c arbitrary: n n' en ex E C rule: com.induct)
  case SKIP
  then show ?case by auto
next
  case (Assign x a)
  then show ?case by auto
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and E: "E = E1 Un (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) Un E2"
    and C: "C = C1 Un C2"
    by (auto split: prod.splits)
  show ?case unfolding E C using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] by simp
next
  case (If b c1 c2)
  then show ?case by (auto split: prod.splits intro: finite_UnI)
next
  case (While b c)
  then show ?case by (auto split: prod.splits intro: finite_UnI)
next
  case (Scope c)
  then show ?case by (auto split: prod.splits intro: finite_UnI)
next
  case (Call dst p actuals)
  then show ?case by (auto split: option.splits prod.splits)
next
  case Restore
  then show ?case by auto
qed

lemma compile_procs_bodies_finite:
  "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)
   \<Longrightarrow> finite E \<and> finite C"
proof (induction ps arbitrary: full_lay n n' full_lay' E C)
  case Nil
  then show ?case by auto
next
  case (Cons p ps)
  then show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons show ?thesis by auto
  next
    case (Some decl)
    with Cons obtain n1 en ex E0 C0 full_lay1 n2 full_lay2 Eacc Cacc where
      cp: "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (n1, en, ex, E0, C0)"
      and rest: "compile_procs_bodies \<Pi> ps base_lay full_lay1 n1 =
                   (n2, full_lay2, Eacc, Cacc)"
      and E: "E = E0 Un Eacc"
      and C: "C = C0 Un Cacc"
      by (auto split: prod.splits option.splits)
    from compile_finite[OF cp] Cons.IH[OF rest] show ?thesis
      unfolding E C by simp
  qed
qed

lemma compile_procs_list_finite:
  "compile_procs_list \<Pi> ps lay n = (n', lay', E, C)
   \<Longrightarrow> finite E \<and> finite C"
  unfolding compile_procs_list_def
  by (auto simp: Let_def split: prod.splits dest: compile_procs_bodies_finite)

lemma compile_prog_finite:
  "finite (edges (compile_prog \<Pi> ps main))
   \<and> finite (combines (compile_prog \<Pi> ps main))"
  unfolding compile_prog_def compile_prog_with_regions_def mk_cfg_def
  by (auto simp: Let_def split: prod.splits
       dest: compile_procs_list_finite compile_finite
       intro: finite_UnI)

subsection \<open>Executable examples\<close>

value "cfg_entry (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"
value "cfg_exit  (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"
value "cfg_edges_list (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"
value "cfg_edges_list (compile_prog (\<lambda>_. None) [] (IMP2_Proc.com.Assign ''x'' (N 1)))"
value "cfg_combines_list (compile_prog (\<lambda>_. None) [] (IMP2_Proc.com.Call None ''f'' []))"




end
