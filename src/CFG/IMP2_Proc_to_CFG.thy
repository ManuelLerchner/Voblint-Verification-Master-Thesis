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
             E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2,
             C1 \<union> C2))"

  | "compile \<Pi> lay (If b c1 c2) n =
       (let en  = n;
            (n1, en1, ex1, E1, C1) = compile \<Pi> lay c1 (n + 1);
            (n2, en2, ex2, E2, C2) = compile \<Pi> lay c2 n1;
            xn  = n2
        in  (n2 + 1, en, xn,
             {(en, EA_Assume b,    en1),
              (en, EA_AssumeNot b, en2)}
             \<union> E1 \<union> E2
             \<union> {(ex1, EA_Nop, xn),
                 (ex2, EA_Nop, xn)},
             C1 \<union> C2))"

  | "compile \<Pi> lay (While b c) n =
       (let head = n;
            (n1, en1, ex1, E1, C1) = compile \<Pi> lay c (n + 1);
            xn  = n1
        in  (n1 + 1, head, xn,
             {(head, EA_Assume b,    en1),
              (head, EA_AssumeNot b, xn)}
             \<union> E1
             \<union> {(ex1, EA_Nop, head)},
             C1))"

  | "compile \<Pi> lay (Scope c) n =
       (let (n', en, ex, E, C) = compile \<Pi> lay c (n + 1);
            scope_ex = n'
        in  (n' + 1, n, scope_ex,
             E \<union> {(n, EA_Enter [] [], en)},
             C \<union> {(n, ex, scope_ex, None)}))"

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
             in  (n'', full_lay'', E \<union> Eacc, C \<union> Cacc)))"

text \<open>
  Two-pass procedure compilation.

  Pass 1 (@{const compile_procs_layout}) records each procedure's entry, exit,
  and node range with empty edge sets, so that a @{term Call} in any body can
  resolve its callee's entry/exit -- including mutual and self recursion.

  Pass 2 (@{const compile_procs_bodies}) recompiles every body against that
  fixed layout (@{term base_lay}) to emit the real edges. Two choices below are
  deliberate, not oversights:
  \<^item> the accumulator starts from the caller-supplied @{term lay} (fresh, all
    @{term None}), not from @{term base_lay}; the per-procedure update writes
    only when the entry is still @{term None}, so seeding it with the already
    @{term Some} @{term base_lay} would skip every procedure and drop all edges.
  \<^item> the body pass restarts the counter at @{term n}, not at pass 1's final
    @{term n'}; since @{const compile}'s counter is layout-independent (lemma
    \<^verbatim>\<open>compile_counter_indep\<close> below) this reproduces the identical
    node numbering pass 1 stored, keeping the @{term "{n..<n'}"} ranges valid.
\<close>
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

text \<open>
  The counter returned by @{const compile} is fixed by the command structure
  alone: the layout only supplies entry/exit targets for edges, never fresh
  node numbers (even the @{term Call} clause returns @{term "n + 2"} in both
  branches). This is what makes the two-pass @{const compile_procs_list} sound:
  the body pass re-runs @{const compile} from the same start counter as the
  layout pass and reproduces the identical node ranges @{term "{n..<n'}"}.
\<close>
lemma compile_counter_indep:
  "fst (compile \<Pi> lay c n) = fst (compile \<Pi> lay' c n)"
  by (induction c arbitrary: n rule: com.induct)
     (auto split: prod.splits option.splits, (metis fst_conv)+)

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
    and E: "E = E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2"
    and C: "C = C1 \<union> C2"
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


subsection \<open>Combine determinism for compiled CFGs\<close>

text \<open>
  \<open>combines\<close> is a primitive field of an arbitrary \<^typ>\<open>cfg\<close>, but for CFGs produced by
  \<^const>\<open>compile_prog\<close> the call node determines the whole combine tuple.  The exit component
  is therefore not independent data in a compiled CFG --- it is the callee procedure's exit
  node, recoverable from the call node --- even though the record stores it (denormalised for
  the solver's node-indexed combine equation).  The proofs are forward range arithmetic on the
  compiler counter; no reverse node-to-source lookup is used.
\<close>

text \<open>Every combine call node emitted by \<^const>\<open>compile\<close> lies in the counter range \<open>[n, n')\<close>.\<close>
lemma compile_combines_call_range:
  "compile \<Pi> lay c n = (n', en, ex, E, C)
   \<Longrightarrow> (cc, ce, cr, cd) \<in> C \<Longrightarrow> n \<le> cc \<and> cc < n'"
proof (induction c arbitrary: n n' en ex E C cc ce cr cd rule: com.induct)
  case SKIP then show ?case by auto
next
  case (Assign x a) then show ?case by auto
next
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and n': "n' = n2" and C: "C = C1 \<union> C2"
    by (auto split: prod.splits)
  from Seq.prems(2) C consider "(cc, ce, cr, cd) \<in> C1" | "(cc, ce, cr, cd) \<in> C2" by auto
  then show ?case
  proof cases
    case 1
    from Seq.IH(1)[OF c1 this] compile_counter_mono[OF c2] n' show ?thesis by simp
  next
    case 2
    from Seq.IH(2)[OF c2 this] compile_counter_mono[OF c1] n' show ?thesis by simp
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 (Suc n) = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and n': "n' = Suc n2" and C: "C = C1 \<union> C2"
    by (auto split: prod.splits)
  from If.prems(2) C consider "(cc, ce, cr, cd) \<in> C1" | "(cc, ce, cr, cd) \<in> C2" by auto
  then show ?case
  proof cases
    case 1
    from If.IH(1)[OF c1 this] compile_counter_mono[OF c2] n' show ?thesis by simp
  next
    case 2
    from If.IH(2)[OF c2 this] compile_counter_mono[OF c1] n' show ?thesis by simp
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 ex1 E1 C1 where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and n': "n' = Suc n1" and C: "C = C1"
    by (auto split: prod.splits)
  from While.prems(2) C have "(cc, ce, cr, cd) \<in> C1" by simp
  from While.IH[OF c this] n' show ?case by simp
next
  case (Scope c)
  from Scope.prems(1) obtain n1 en1 ex1 E1 C1 where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and n': "n' = Suc n1" and C: "C = C1 \<union> {(n, ex1, n1, None)}"
    by (auto split: prod.splits)
  from Scope.prems(2) C consider "(cc, ce, cr, cd) \<in> C1" | "(cc, ce, cr, cd) = (n, ex1, n1, None)"
    by auto
  then show ?case
  proof cases
    case 1
    from Scope.IH[OF c this] n' show ?thesis by simp
  next
    case 2
    from compile_counter_mono[OF c] n' show ?thesis using \<open>(cc, ce, cr, cd) = (n, ex1, n1, None)\<close> by simp
  qed
next
  case (Call dst p actuals)
  from Call.prems show ?case by (auto split: option.splits prod.splits)
next
  case Restore then show ?case by auto
qed

text \<open>Within one \<^const>\<open>compile\<close> the call node determines the combine tuple.\<close>
lemma compile_combines_functional:
  "compile \<Pi> lay c n = (n', en, ex, E, C)
   \<Longrightarrow> (cc, ce1, cr1, cd1) \<in> C \<Longrightarrow> (cc, ce2, cr2, cd2) \<in> C
   \<Longrightarrow> (ce1, cr1, cd1) = (ce2, cr2, cd2)"
proof (induction c arbitrary: n n' en ex E C cc ce1 cr1 cd1 ce2 cr2 cd2 rule: com.induct)
  case SKIP then show ?case by auto
next
  case (Assign x a) then show ?case by auto
next
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and C: "C = C1 \<union> C2"
    by (auto split: prod.splits)
  have rng1: "\<And>e r d. (cc, e, r, d) \<in> C1 \<Longrightarrow> cc < n1"
    using compile_combines_call_range[OF c1] by blast
  have rng2: "\<And>e r d. (cc, e, r, d) \<in> C2 \<Longrightarrow> n1 \<le> cc"
    using compile_combines_call_range[OF c2] by blast
  from Seq.prems(2) C have m1: "(cc, ce1, cr1, cd1) \<in> C1 \<union> C2" by simp
  from Seq.prems(3) C have m2: "(cc, ce2, cr2, cd2) \<in> C1 \<union> C2" by simp
  from m1 m2 rng1 rng2 consider
      "(cc, ce1, cr1, cd1) \<in> C1 \<and> (cc, ce2, cr2, cd2) \<in> C1"
    | "(cc, ce1, cr1, cd1) \<in> C2 \<and> (cc, ce2, cr2, cd2) \<in> C2"
    by (metis Un_iff linorder_not_le)
  then show ?case
  proof cases
    case 1 thus ?thesis using Seq.IH(1)[OF c1] by blast
  next
    case 2 thus ?thesis using Seq.IH(2)[OF c2] by blast
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
    c1: "compile \<Pi> lay c1 (Suc n) = (n1, en1, ex1, E1, C1)"
    and c2: "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and C: "C = C1 \<union> C2"
    by (auto split: prod.splits)
  have rng1: "\<And>e r d. (cc, e, r, d) \<in> C1 \<Longrightarrow> cc < n1"
    using compile_combines_call_range[OF c1] by blast
  have rng2: "\<And>e r d. (cc, e, r, d) \<in> C2 \<Longrightarrow> n1 \<le> cc"
    using compile_combines_call_range[OF c2] by blast
  from If.prems(2) C have m1: "(cc, ce1, cr1, cd1) \<in> C1 \<union> C2" by simp
  from If.prems(3) C have m2: "(cc, ce2, cr2, cd2) \<in> C1 \<union> C2" by simp
  from m1 m2 rng1 rng2 consider
      "(cc, ce1, cr1, cd1) \<in> C1 \<and> (cc, ce2, cr2, cd2) \<in> C1"
    | "(cc, ce1, cr1, cd1) \<in> C2 \<and> (cc, ce2, cr2, cd2) \<in> C2"
    by (metis Un_iff linorder_not_le)
  then show ?case
  proof cases
    case 1 thus ?thesis using If.IH(1)[OF c1] by blast
  next
    case 2 thus ?thesis using If.IH(2)[OF c2] by blast
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 ex1 E1 C1 where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and C: "C = C1"
    by (auto split: prod.splits)
  from While.prems(2,3) C While.IH[OF c] show ?case by simp
next
  case (Scope c)
  from Scope.prems(1) obtain n1 en1 ex1 E1 C1 where
    c: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and C: "C = C1 \<union> {(n, ex1, n1, None)}"
    by (auto split: prod.splits)
  have rng: "\<And>e r d. (cc, e, r, d) \<in> C1 \<Longrightarrow> Suc n \<le> cc"
    using compile_combines_call_range[OF c] by blast
  from Scope.prems(2) C have m1: "(cc, ce1, cr1, cd1) \<in> C1 \<union> {(n, ex1, n1, None)}" by simp
  from Scope.prems(3) C have m2: "(cc, ce2, cr2, cd2) \<in> C1 \<union> {(n, ex1, n1, None)}" by simp
  from m1 m2 rng consider
      "(cc, ce1, cr1, cd1) \<in> C1 \<and> (cc, ce2, cr2, cd2) \<in> C1"
    | "(cc, ce1, cr1, cd1) = (n, ex1, n1, None) \<and> (cc, ce2, cr2, cd2) = (n, ex1, n1, None)"
    by (metis Un_iff insertE singletonD Suc_n_not_le_n fst_conv)
  then show ?case
  proof cases
    case 1 thus ?thesis using Scope.IH[OF c] by blast
  next
    case 2 thus ?thesis by simp
  qed
next
  case (Call dst p actuals)
  from Call.prems show ?case by (auto split: option.splits prod.splits)
next
  case Restore then show ?case by auto
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
      and E: "E = E0 \<union> Eacc"
      and C: "C = C0 \<union> Cacc"
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


lemma compile_procs_bodies_counter_mono:
  "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C) \<Longrightarrow> n \<le> n'"
proof (induction ps arbitrary: full_lay n n' full_lay' E C)
  case Nil then show ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons.prems have "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)"
      by simp
    from Cons.IH[OF this] show ?thesis .
  next
    case (Some decl)
    with Cons.prems obtain n1 en ex E0 C0 full_lay1 n2 full_lay2 Eacc Cacc where
      cp: "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (n1, en, ex, E0, C0)"
      and rest: "compile_procs_bodies \<Pi> ps base_lay full_lay1 n1 = (n2, full_lay2, Eacc, Cacc)"
      and n': "n' = n2"
      by (auto split: prod.splits option.splits)
    from compile_counter_mono[OF cp] Cons.IH[OF rest] n' show ?thesis by simp
  qed
qed

lemma compile_procs_bodies_combines_range:
  "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)
   \<Longrightarrow> (cc, ce, cr, cd) \<in> C \<Longrightarrow> n \<le> cc \<and> cc < n'"
proof (induction ps arbitrary: full_lay n n' full_lay' E C cc ce cr cd)
  case Nil then show ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons.prems(1) have b: "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)"
      by simp
    from Cons.IH[OF b Cons.prems(2)] show ?thesis .
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 en ex E0 C0 full_lay1 n2 full_lay2 Eacc Cacc where
      cp: "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (n1, en, ex, E0, C0)"
      and rest: "compile_procs_bodies \<Pi> ps base_lay full_lay1 n1 = (n2, full_lay2, Eacc, Cacc)"
      and n': "n' = n2" and C: "C = C0 \<union> Cacc"
      by (auto split: prod.splits option.splits)
    from Cons.prems(2) C consider "(cc, ce, cr, cd) \<in> C0" | "(cc, ce, cr, cd) \<in> Cacc" by auto
    then show ?thesis
    proof cases
      case 1
      from compile_combines_call_range[OF cp 1] compile_procs_bodies_counter_mono[OF rest] n'
      show ?thesis by simp
    next
      case 2
      from Cons.IH[OF rest 2] compile_counter_mono[OF cp] n' show ?thesis by simp
    qed
  qed
qed

lemma compile_procs_bodies_combines_functional:
  "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)
   \<Longrightarrow> (cc, ce1, cr1, cd1) \<in> C \<Longrightarrow> (cc, ce2, cr2, cd2) \<in> C
   \<Longrightarrow> (ce1, cr1, cd1) = (ce2, cr2, cd2)"
proof (induction ps arbitrary: full_lay n n' full_lay' E C cc ce1 cr1 cd1 ce2 cr2 cd2)
  case Nil then show ?case by auto
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    with Cons.prems(1) have b: "compile_procs_bodies \<Pi> ps base_lay full_lay n = (n', full_lay', E, C)"
      by simp
    from Cons.IH[OF b Cons.prems(2) Cons.prems(3)] show ?thesis .
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 en ex E0 C0 full_lay1 n2 full_lay2 Eacc Cacc where
      cp: "compile \<Pi> base_lay (with_result (body decl) (result decl)) n = (n1, en, ex, E0, C0)"
      and rest: "compile_procs_bodies \<Pi> ps base_lay full_lay1 n1 = (n2, full_lay2, Eacc, Cacc)"
      and C: "C = C0 \<union> Cacc"
      by (auto split: prod.splits option.splits)
    have rng0: "\<And>e r d. (cc, e, r, d) \<in> C0 \<Longrightarrow> cc < n1"
      using compile_combines_call_range[OF cp] by blast
    have rngA: "\<And>e r d. (cc, e, r, d) \<in> Cacc \<Longrightarrow> n1 \<le> cc"
      using compile_procs_bodies_combines_range[OF rest] by blast
    from Cons.prems(2) C have m1: "(cc, ce1, cr1, cd1) \<in> C0 \<union> Cacc" by simp
    from Cons.prems(3) C have m2: "(cc, ce2, cr2, cd2) \<in> C0 \<union> Cacc" by simp
    from m1 m2 rng0 rngA consider
        "(cc, ce1, cr1, cd1) \<in> C0 \<and> (cc, ce2, cr2, cd2) \<in> C0"
      | "(cc, ce1, cr1, cd1) \<in> Cacc \<and> (cc, ce2, cr2, cd2) \<in> Cacc"
      by (metis Un_iff linorder_not_le)
    then show ?thesis
    proof cases
      case 1 thus ?thesis using compile_combines_functional[OF cp] by blast
    next
      case 2 thus ?thesis using Cons.IH[OF rest] by blast
    qed
  qed
qed

lemma compile_procs_list_combines_range:
  assumes "compile_procs_list \<Pi> ps lay n = (n', lay', E, C)"
    and "(cc, ce, cr, cd) \<in> C"
  shows "n \<le> cc \<and> cc < n'"
proof -
  from assms(1) obtain n0 base_lay where
    b: "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
    unfolding compile_procs_list_def by (auto simp: Let_def split: prod.splits)
  from compile_procs_bodies_combines_range[OF b assms(2)] show ?thesis .
qed

lemma compile_procs_list_combines_functional:
  assumes "compile_procs_list \<Pi> ps lay n = (n', lay', E, C)"
    and "(cc, ce1, cr1, cd1) \<in> C" and "(cc, ce2, cr2, cd2) \<in> C"
  shows "(ce1, cr1, cd1) = (ce2, cr2, cd2)"
proof -
  from assms(1) obtain n0 base_lay where
    b: "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
    unfolding compile_procs_list_def by (auto simp: Let_def split: prod.splits)
  from compile_procs_bodies_combines_functional[OF b assms(2) assms(3)] show ?thesis .
qed


text \<open>
  Headline: in a compiled CFG the call node determines the whole combine tuple.  In particular
  the exit component --- the callee procedure's exit node --- is not independent data; it is a
  function of the call node.  \<open>combines\<close> stays a primitive \<^typ>\<open>cfg\<close> field (denormalised for the
  solver's node-indexed combine equation), but for \<^const>\<open>compile_prog\<close> outputs this theorem
  records that the denormalisation is redundant.
\<close>
lemma compiled_combines_deterministic:
  assumes "(cc, ce1, cr1, cd1) \<in> combines (compile_prog \<Pi> ps main)"
      and "(cc, ce2, cr2, cd2) \<in> combines (compile_prog \<Pi> ps main)"
  shows "(ce1, cr1, cd1) = (ce2, cr2, cd2)"
proof -
  obtain n1 lay Eproc Cproc where
    procs: "compile_procs_list \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, Eproc, Cproc)"
    by (metis prod_cases4)
  obtain n2 en ex Emain Cmain where
    mainc: "compile \<Pi> lay main n1 = (n2, en, ex, Emain, Cmain)"
    by (metis prod_cases5)
  have comb: "combines (compile_prog \<Pi> ps main) = Cproc \<union> Cmain"
    unfolding compile_prog_def compile_prog_with_regions_def
    by (simp add: procs mainc mk_cfg_def Let_def)
  have rP: "\<And>e r d. (cc, e, r, d) \<in> Cproc \<Longrightarrow> cc < n1"
    using compile_procs_list_combines_range[OF procs] by blast
  have rM: "\<And>e r d. (cc, e, r, d) \<in> Cmain \<Longrightarrow> n1 \<le> cc"
    using compile_combines_call_range[OF mainc] by blast
  from assms(1) comb have m1: "(cc, ce1, cr1, cd1) \<in> Cproc \<union> Cmain" by simp
  from assms(2) comb have m2: "(cc, ce2, cr2, cd2) \<in> Cproc \<union> Cmain" by simp
  from m1 m2 rP rM consider
      "(cc, ce1, cr1, cd1) \<in> Cproc \<and> (cc, ce2, cr2, cd2) \<in> Cproc"
    | "(cc, ce1, cr1, cd1) \<in> Cmain \<and> (cc, ce2, cr2, cd2) \<in> Cmain"
    by (metis Un_iff linorder_not_le)
  then show ?thesis
  proof cases
    case 1 thus ?thesis using compile_procs_list_combines_functional[OF procs] by blast
  next
    case 2 thus ?thesis using compile_combines_functional[OF mainc] by blast
  qed
qed
subsection \<open>Executable examples\<close>

value "cfg_entry (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"
value "cfg_exit  (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"




end
