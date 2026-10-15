theory Run_Report
  imports Analysis_Report MCP_Split
begin

section \<open>The report of a typed run\<close>

text \<open>
  A typed run is reported by the builder a VIMP run uses (\<^const>\<open>report_of\<close>): the typed
  graph, the declared variables, the globals the placement keeps at unknowns of their
  own, the arithmetic obligations of the typed expressions, and the program's
  procedures.
\<close>

subsection \<open>Arithmetic obligations of typed expressions\<close>

text \<open>
  A division or remainder must not divide by zero. A signed addition, subtraction,
  multiplication or division must compute a result its kind represents: C leaves the
  behavior undefined otherwise (ISO/IEC 9899 6.5p5), and Goblint checks the same four
  operators (\<^verbatim>\<open>SignedIntegerOverflowInArithmetic\<close>). A unary minus reaches the
  typed language as a subtraction from zero, and a signed division overflows only on
  the kind's minimum divided by \<open>-1\<close>. An unsigned operation wraps by definition and
  raises no obligation. A remainder raises none either: its mathematical result always
  fits, although C also leaves \<open>INT_MIN % -1\<close> undefined because the quotient does not.

  A conversion must convert a value its target kind represents. Elaboration makes
  every conversion a \<open>TCast\<close> node: an explicit cast, and the implicit conversions of an
  assigned value, an argument and a returned value to the kind of the place they are
  written to. A conversion whose source kind widens into its target cannot change a
  value of the source kind and raises no obligation. Goblint checks conversions to
  signed and unsigned kinds alike (\<open>IntegerOverflowInExplicitCast\<close>,
  \<open>\<dots>InImplicitCast\<close>); so does Voblint, although C defines a conversion to an unsigned
  kind as wraparound and leaves one to a signed kind implementation-defined, not
  undefined. Voblint does not tell an explicit cast from an implicit conversion, since
  elaboration does not record it.

  Every obligation of an expression is raised, however deeply it is nested and
  whatever the value of an enclosing logical operator, since the typed language
  evaluates both operands of one.
\<close>

text \<open>A literal elaborated at a kind is converted to it as well: \<open>x = 300\<close> for an 8-bit
  \<open>x\<close> elaborates to the literal at \<open>x\<close>'s kind, whose value wraps.\<close>

fun arith_obligations :: "exp \<Rightarrow> exp arithmetic_obligation list" where
  "arith_obligations (TN k n) =
     (if n \<in> ik_range k then [] else [Arithmetic_Obligation Conversion_Overflow (TN k n) (TN k n)])"
| "arith_obligations (TVar _ _) = []"
| "arith_obligations (TArith k op a b) =
     arith_obligations a @ arith_obligations b
     @ (if op = ADiv \<or> op = AMod
        then [Arithmetic_Obligation Division_By_Zero (TArith k op a b) b] else [])
     @ (if ik_signed k \<and> op \<noteq> AMod
        then [Arithmetic_Obligation Signed_Overflow (TArith k op a b) (TArith k op a b)] else [])"
| "arith_obligations (TCast k a) =
     arith_obligations a
     @ (if ik_widens (exp_kind a) k then []
        else [Arithmetic_Obligation Conversion_Overflow (TCast k a) a])"
| "arith_obligations (TCmp _ a b) = arith_obligations a @ arith_obligations b"
| "arith_obligations (TNot a) = arith_obligations a"
| "arith_obligations (TAnd a b) = arith_obligations a @ arith_obligations b"
| "arith_obligations (TOr a b) = arith_obligations a @ arith_obligations b"

text \<open>A division obligation is safe when its divisor is not zero, compared at the divisor's
  kind.\<close>

definition arith_condition :: "exp arithmetic_obligation \<Rightarrow> exp" where
  "arith_condition ob =
     TCmp CNe (arithmetic_operand ob) (TN (exp_kind (arithmetic_operand ob)) 0)"

text \<open>
  An overflow obligation is about the value an operation computes before its kind
  wraps it: the mathematical result of an arithmetic node, the converted value of a
  conversion. It is safe when that value lies in the node's kind. The statement does
  not depend on the overflow policy: the policy decides how an analysis abstracts a
  wrapped result, never what the program computes.
\<close>

fun unwrapped :: "exp \<Rightarrow> store \<Rightarrow> int" where
  "unwrapped (TN k n) t = n"
| "unwrapped (TArith k op a b) t = aop_eval op (eval a t) (eval b t)"
| "unwrapped (TCast k a) t = eval a t"
| "unwrapped e t = eval e t"

definition obligation_holds :: "exp arithmetic_obligation \<Rightarrow> store \<Rightarrow> bool" where
  "obligation_holds ob t \<longleftrightarrow>
     (case arithmetic_hazard ob of
        Division_By_Zero \<Rightarrow> eval (arithmetic_operand ob) t \<noteq> 0
      | _ \<Rightarrow> unwrapped (arithmetic_operation ob) t \<in> ik_range (exp_kind (arithmetic_operation ob)))"

abbreviation satisfies :: "store \<Rightarrow> exp arithmetic_obligation \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "s \<Turnstile> ob \<equiv> obligation_holds ob s"

text \<open>
  An overflow obligation is decided as Goblint decides it, from the interval of the
  unwrapped result: the operands' values are asked through \<open>EvalInt\<close>, so every active
  analysis contributes, and their interval components are combined by the operation
  over the integers. The obligation is safe when that interval lies in the kind, and
  certainly violated when it misses the kind. An answer that admits no value is
  read as unknown, as \<^const>\<open>answer_check\<close> reads one.
\<close>

fun answer_ivl :: "answer \<Rightarrow> ivl" where
  "answer_ivl (QLifted d) = int_ivl d"
| "answer_ivl QBot = \<bottom>"
| "answer_ivl QTop = \<top>"

lemma answer_ivl_sound: "n \<in> gamma_answer a \<Longrightarrow> n \<in> gamma_ivl (answer_ivl a)"
  by (cases a) (auto simp: gamma_int_dom_def top_ivl_def ivl_top_def)

text \<open>A literal operand is its own exact interval, and a truth value lies in
  \<open>[0, 1]\<close>, whatever the active analyses answer for them: a domain without
  magnitudes, such as Parity, would otherwise leave even \<open>10 / 3\<close> a possible
  overflow.\<close>

fun operand_ivl :: "exp gchannel \<Rightarrow> exp \<Rightarrow> ivl" where
  "operand_ivl ch (TN k n) = Ivl (Fin (ik_norm k n)) (Fin (ik_norm k n))"
| "operand_ivl ch (TCmp c a b) = answer_ivl (ch (EvalInt (TCmp c a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TNot a) = answer_ivl (ch (EvalInt (TNot a))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TAnd a b) = answer_ivl (ch (EvalInt (TAnd a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TOr a b) = answer_ivl (ch (EvalInt (TOr a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch e = answer_ivl (ch (EvalInt e))"

fun unwrapped_ivl :: "exp gchannel \<Rightarrow> exp \<Rightarrow> ivl" where
  "unwrapped_ivl ch (TN k n) = Ivl (Fin n) (Fin n)"
| "unwrapped_ivl ch (TArith k op a b) = ivl_aop op (operand_ivl ch a) (operand_ivl ch b)"
| "unwrapped_ivl ch (TCast k a) = operand_ivl ch a"
| "unwrapped_ivl ch e = operand_ivl ch e"

lemma unwrapped_ivl_sound:
  assumes "geval_query.channel_holds eval ch t"
  shows "unwrapped e t \<in> gamma_ivl (unwrapped_ivl ch e)"
proof -
  have answer: "eval a t \<in> gamma_ivl (answer_ivl (ch (EvalInt a)))" for a
    using geval_query.channel_holdsD[OF assms, of "EvalInt a"] by (auto intro: answer_ivl_sound)
  have truth: "eval a t \<in> gamma_ivl (Ivl (Fin 0) (Fin 1))"
    if "a \<in> {TCmp c x y | c x y. True} \<union> range TNot \<union> {TAnd x y | x y. True} \<union> {TOr x y | x y. True}"
    for a
    using that by (auto simp: less_eq_eint_def)
  have ans: "eval a t \<in> gamma_ivl (operand_ivl ch a)" for a
    using answer[of a] truth[of a]
    by (cases a) (auto simp: less_eq_eint_def gamma_inf_ivl)
  show ?thesis
  proof (cases e)
    case (TN k n) then show ?thesis by (simp add: less_eq_eint_def)
  qed (simp_all only: unwrapped.simps unwrapped_ivl.simps ans ivl_aop_sound)
qed

definition fits_verdict :: "ikind \<Rightarrow> ivl \<Rightarrow> check_result" where
  "fits_verdict k i =
     (if is_bottom_ivl i then Check_Unknown
      else if i \<le> ik_ivl k then Check_Proved
      else if is_bottom_ivl (i \<sqinter> ik_ivl k) then Check_Refuted
      else Check_Unknown)"

lemma fits_verdict_sound:
  assumes "n \<in> gamma_ivl i"
  shows "fits_verdict k i = Check_Proved \<Longrightarrow> n \<in> ik_range k"
    and "fits_verdict k i = Check_Refuted \<Longrightarrow> n \<notin> ik_range k"
proof -
  show "fits_verdict k i = Check_Proved \<Longrightarrow> n \<in> ik_range k"
    using assms gamma_ivl_mono[of i "ik_ivl k"]
    by (auto simp: fits_verdict_def split: if_splits)
  show "fits_verdict k i = Check_Refuted \<Longrightarrow> n \<notin> ik_range k"
    using assms by (auto simp: fits_verdict_def is_bottom_ivl_correct gamma_inf_ivl split: if_splits)
qed

definition obligation_classify ::
    "sem_conf \<Rightarrow> kind_decls \<Rightarrow> analysis list \<Rightarrow> exp arithmetic_obligation \<Rightarrow> mcp_val
       \<Rightarrow> check_result" where
  "obligation_classify sem ds as ob v =
     (case arithmetic_hazard ob of
        Division_By_Zero \<Rightarrow> mcp_classify sem ds as (arith_condition ob) v
      | _ \<Rightarrow> fits_verdict (exp_kind (arithmetic_operation ob))
              (unwrapped_ivl (mcp_ask sem ds as v) (arithmetic_operation ob)))"

lemma obligation_classify_sound:
  assumes t: "t \<in> mcp.act_gamma ds as v"
  shows "obligation_classify sem ds as ob v = Check_Proved \<Longrightarrow> t \<Turnstile> ob"
    and "obligation_classify sem ds as ob v = Check_Refuted \<Longrightarrow> \<not> t \<Turnstile> ob"
proof -
  have ch: "geval_query.channel_holds eval (mcp_ask sem ds as v) t"
    by (rule mcp.mcp_ask_sound[OF t])
  note fits = fits_verdict_sound[OF unwrapped_ivl_sound[OF ch]]
  have ne: "truthy (eval (arith_condition ob) t) \<longleftrightarrow> eval (arithmetic_operand ob) t \<noteq> 0"
    by (simp add: arith_condition_def)
  show "obligation_classify sem ds as ob v = Check_Proved \<Longrightarrow> t \<Turnstile> ob"
    using fits(1) mcp.mcp_classify_proved[OF t] ne
    by (auto simp: obligation_classify_def obligation_holds_def split: arithmetic_hazard.splits)
  show "obligation_classify sem ds as ob v = Check_Refuted \<Longrightarrow> \<not> t \<Turnstile> ob"
    using fits(2) mcp.mcp_classify_refuted[OF t] ne
    by (auto simp: obligation_classify_def obligation_holds_def split: arithmetic_hazard.splits)
qed

subsection \<open>Where the obligations are decided\<close>

text \<open>
  An expression's obligations are decided at the source of the edge or call that
  evaluates it. One conversion has no expression of its own: a call's result, which
  the caller writes to its destination at the destination's kind. Its obligation is
  decided where the callee returns, on the returned expression, once for each kind a
  caller converts it to. A returned value whose kind widens into the destination's
  raises none. A library call's result, such as \<open>min\<close>'s, is converted without an
  obligation.
\<close>

definition return_sites ::
    "kind_decls \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp arithmetic_obligation list) list" where
  "return_sites ds p =
     (let g = elab_cfg p ds
      in remdups (concat (map (\<lambda>(u, ca, ce, k). case ce_dst ca of
           None \<Rightarrow> []
         | Some x \<Rightarrow> concat (map (\<lambda>(v, a, w). case a of
               EA_Ret (Some e) q \<Rightarrow>
                 if q = callee_of_entry ce \<and> \<not> ik_widens (exp_kind e) (kenv_of ds x)
                 then [(v, [Arithmetic_Obligation Conversion_Overflow (TCast (kenv_of ds x) e) e])]
                 else []
             | _ \<Rightarrow> []) (cfg_intra_list g)))
         (cfg_calls_list g))))"

definition prog_obligation_sites :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp arithmetic_obligation list) list" where
  "prog_obligation_sites ds p =
     obligation_sites arith_obligations (elab_cfg p ds) @ return_sites ds p"

text \<open>The obligations a typed report decides at a point, and what it means for a store
  to meet one: \<open>s \<Turnstile> ob\<close>.\<close>

definition obligations_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> exp arithmetic_obligation set" where
  "obligations_at ds p v = (\<Union>(u, obs) \<in> set (prog_obligation_sites ds p). if u = v then set obs else {})"

lemma mem_obligations_at:
  "ob \<in> obligations_at ds p v \<longleftrightarrow> (\<exists>obs. (v, obs) \<in> set (prog_obligation_sites ds p) \<and> ob \<in> set obs)"
  by (force simp: obligations_at_def split: if_splits)

text \<open>The variables a report lists: every variable an edge or a call of the typed graph
  mentions.\<close>

fun special_vars :: "exp gspecial_call \<Rightarrow> var_id list" where
  "special_vars Nondet_Int = []"
| "special_vars (Min a b) = var_list a @ var_list b"
| "special_vars (Max a b) = var_list a @ var_list b"

fun edge_vars :: "(var_id, exp) gedge_action \<Rightarrow> var_id list" where
  "edge_vars (EA_Assign x e) = x # var_list e"
| "edge_vars (EA_Special sc x) = x # special_vars sc"
| "edge_vars (EA_Assume b) = var_list b"
| "edge_vars (EA_AssumeNot b) = var_list b"
| "edge_vars (EA_Ret e _) = (case e of Some e \<Rightarrow> var_list e | None \<Rightarrow> [])"
| "edge_vars (EA_Check _ e) = var_list e"
| "edge_vars _ = []"

fun call_vars :: "(var_id, exp) gcall_action \<Rightarrow> var_id list" where
  "call_vars (CallEdge dst ps args) =
     (case dst of Some x \<Rightarrow> [x] | None \<Rightarrow> []) @ ps @ concat (map var_list args)"

definition cfg_vars :: "(var_id, exp) gcfg \<Rightarrow> var_id list" where
  "cfg_vars g =
     sorted_list_of_set (set (concat (map (\<lambda>(u, a, w). edge_vars a) (cfg_intra_list g))
                            @ concat (map (\<lambda>(u, ca, e, w). call_vars ca) (cfg_calls_list g))))"

type_synonym report =
  "(voblint_conf, mcp_ctx report_context,
    var_id, exp, var_id, mcp_val) analysis_report"

text \<open>One builder for every context policy and placement: the policy contributes how its
  contexts are ordered and tagged, the placement which globals it keeps at their own
  unknowns.\<close>

definition prog_report_of ::
    "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> var_id list \<Rightarrow> ('c \<Rightarrow> order_key)
       \<Rightarrow> ('c \<Rightarrow> mcp_ctx report_context) \<Rightarrow> (var_id, exp, 'c, var_id, mcp_val) gsolved_run
       \<Rightarrow> report" where
  "prog_report_of conf ds p gs ctx_key ctx_tag sr =
     report_of conf (cfg_vars (elab_cfg p ds)) (elab_cfg p ds) gs
       (prog_obligation_sites ds p) (obligation_classify (conf_sem conf) ds (activation_of (conf_analyses conf)))
       (prog_main_name # prog_procs p) ctx_key ctx_tag
       (mcp_classify (conf_sem conf) ds (activation_of (conf_analyses conf))) sr"

subsection \<open>At entry-state contexts\<close>

text \<open>
  An entry-state context is listed in the order of an injective key: each field's
  formal values, a kind-tagged value keyed by its tag, its kind and its value.
\<close>

fun ikind_key :: "ikind \<Rightarrow> order_key" where
  "ikind_key I8 = Key_Int 0"
| "ikind_key U8 = Key_Int 1"
| "ikind_key I16 = Key_Int 2"
| "ikind_key U16 = Key_Int 3"
| "ikind_key I32 = Key_Int 4"
| "ikind_key U32 = Key_Int 5"
| "ikind_key I64 = Key_Int 6"
| "ikind_key U64 = Key_Int 7"

lemma ikind_key_inject [simp]: "ikind_key a = ikind_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

fun kd_key :: "('a \<Rightarrow> order_key) \<Rightarrow> 'a kd \<Rightarrow> order_key" where
  "kd_key f KBot = Key_List [Key_Int 0]"
| "kd_key f (KD k a) = Key_List [Key_Int 1, ikind_key k, f a]"
| "kd_key f KTop = Key_List [Key_Int 2]"

lemma kd_key_inject:
  assumes "\<And>a b. f a = f b \<Longrightarrow> a = b"
  shows "kd_key f x = kd_key f y \<Longrightarrow> x = y"
  using assms by (cases x; cases y) auto

lemma map_kd_key_inject:
  assumes "\<And>a b. f a = f b \<Longrightarrow> a = b"
  shows "map (kd_key f) xs = map (kd_key f) ys \<Longrightarrow> xs = ys"
  using kd_key_inject[OF assms] by (auto dest: list.inj_map_strong[rotated])

definition int_tuple_key :: "'m int_tuple \<Rightarrow> order_key" where
  "int_tuple_key a = Key_List [ivl_key (it_ivl a), congruence_key (it_cong a)]"

lemma int_tuple_key_inject [simp]: "int_tuple_key a = int_tuple_key b \<longleftrightarrow> a = b"
  unfolding int_tuple_key_def by (cases a; cases b) simp

fun mcp_ctx_key :: "mcp_ctx \<Rightarrow> order_key" where
  "mcp_ctx_key (Product i (Product c (Product (Product tn (Product to tf)) (Product s (Product q u))))) =
     Key_List [Key_List (map (kd_key ivl_key) i), Key_List (map (kd_key congruence_key) c),
               Key_List (map (kd_key int_tuple_key) tn), Key_List (map (kd_key int_tuple_key) to),
               Key_List (map (kd_key int_tuple_key) tf), Key_List (map (kd_key sign_key) s),
               Key_List (map (kd_key parity_key) q), Key_List (map (\<lambda>_. Key_List []) u)]"

lemma inj_mcp_ctx_key: "inj mcp_ctx_key"
proof (rule injI)
  fix a b :: mcp_ctx
  assume eq: "mcp_ctx_key a = mcp_ctx_key b"
  obtain i c tn to tf s q u
    where a: "a = Product i (Product c (Product (Product tn (Product to tf)) (Product s (Product q u))))"
    by (metis analysis_product.exhaust)
  obtain i' c' tn' to' tf' s' q' u'
    where b: "b = Product i' (Product c' (Product (Product tn' (Product to' tf')) (Product s' (Product q' u'))))"
    by (metis analysis_product.exhaust)
  from eq have keys:
    "map (kd_key ivl_key) i = map (kd_key ivl_key) i'"
    "map (kd_key congruence_key) c = map (kd_key congruence_key) c'"
    "map (kd_key int_tuple_key) tn = map (kd_key int_tuple_key) tn'"
    "map (kd_key int_tuple_key) to = map (kd_key int_tuple_key) to'"
    "map (kd_key int_tuple_key) tf = map (kd_key int_tuple_key) tf'"
    "map (kd_key sign_key) s = map (kd_key sign_key) s'"
    "map (kd_key parity_key) q = map (kd_key parity_key) q'"
    "map (\<lambda>_. Key_List []) u = map (\<lambda>_. Key_List []) u'"
    by (simp_all add: a b)
  have "length u = length u'" using keys(8) by (metis length_map)
  then have "u = u'" by (simp add: list_eq_iff_nth_eq)
  moreover have "i = i'" by (rule map_kd_key_inject[OF _ keys(1)]) simp
  moreover have "c = c'" by (rule map_kd_key_inject[OF _ keys(2)]) simp
  moreover have "tn = tn'" by (rule map_kd_key_inject[OF _ keys(3)]) simp
  moreover have "to = to'" by (rule map_kd_key_inject[OF _ keys(4)]) simp
  moreover have "tf = tf'" by (rule map_kd_key_inject[OF _ keys(5)]) simp
  moreover have "s = s'" by (rule map_kd_key_inject[OF _ keys(6)]) simp
  moreover have "q = q'" by (rule map_kd_key_inject[OF _ keys(7)]) simp
  ultimately show "a = b" by (simp add: a b)
qed

subsection \<open>The run\<close>

text \<open>
  A typed run solves the equations of the chosen context policy and placement and
  reports the answer; the logical \<open>None\<close> branch of the executable solve has no report.
  Under flow-insensitive placement each declared global lives at its own unknown.
\<close>

definition cs_run :: "voblint_conf \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> report option" where
  "cs_run conf k ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          key = (\<lambda>ctx. Key_List (map Key_Node ctx));
          tag = (if k = 0 then (\<lambda>_. Report_Unit) else Report_Call_String);
          root = (cfg_exit (elab_cfg p ds), [])
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. prog_report_of conf ds p [] key tag
                                 (mcp_cs.solved_run_of sem ds as k is_global p sol))
               (TD_side_rule_Interp_solve_c r (mcp_cs.equations sem ds as k is_global p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = declared_globals p
              in map_option (\<lambda>sol. prog_report_of conf ds p gs key tag
                                     (mcp_split.solved_run_of sem ds as k gs is_global p sol))
                   (TD_side_rule_Interp_solve_c r (mcp_split.equations sem ds as k gs is_global p)
                      root)))"

definition es_run :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> report option" where
  "es_run conf ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          root = (cfg_exit (elab_cfg p ds), mcp_root_ctx)
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. prog_report_of conf ds p [] mcp_ctx_key Report_Entry
                                 (mcp_es.solved_run_of sem ds as is_global p sol))
               (TD_side_rule_Interp_solve_c r (mcp_es.equations sem ds as is_global p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = declared_globals p
              in map_option (\<lambda>sol. prog_report_of conf ds p gs mcp_ctx_key Report_Entry
                                     (mcp_split_es.solved_run_of sem ds as gs is_global p sol))
                   (TD_side_rule_Interp_solve_c r (mcp_split_es.equations sem ds as gs is_global p)
                      root)))"

definition report_run :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> report option" where
  "report_run conf ds p =
     (case conf_context conf of
        Call_String k \<Rightarrow> cs_run conf k ds p
      | Entry_State \<Rightarrow> es_run conf ds p)"

subsection \<open>What the builder keeps\<close>

text \<open>A check row is a row of the solve's verdict report, and every state the solved
  table covers is listed, whatever the language.\<close>

lemma report_of_check_mem:
  assumes "chk \<in> set (report_checks
             (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr))"
  shows "(check_point chk, check_exp chk, check_verdict chk)
           \<in> set (classify_checks_verdicts g (run_table sr) classify)"
proof -
  from assms have "chk \<in> set (result_checks_of g (run_table sr) classify)"
    by (simp add: report_of_def Let_def)
  then have "(check_point chk, check_exp chk, check_verdict chk)
      \<in> set (map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk))
                 (result_checks_of g (run_table sr) classify))"
    by (simp only: set_map) (rule imageI)
  then show ?thesis by (simp only: result_checks_of_verdicts)
qed

lemma report_of_state_mem:
  assumes fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
    and look: "lookup_table (run_table sr) v ctx = Lifted d"
  shows "Lifted d \<in> report_states_at
           (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr) v"
proof -
  have "lookup_table (run_table sr) v ctx
          \<in> lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
    by (rule imageI[OF lookup_table_LiftedD[OF look]])
  then show ?thesis by (simp only: report_states_at_report_of[OF fin inj] look)
qed

subsection \<open>Soundness\<close>

text \<open>
  A typed report is sound for every typed store that reaches a node from a store whose
  globals are zero at their kinds.
\<close>

text \<open>
  The diagnostics of a typed report are sound for the same stores. A point no
  diagnostic names meets every obligation of the expressions evaluated there at every
  store that reaches it; a refuted obligation fails at every such store. Both read the
  diagnostics off the solved table through \<^const>\<open>obligation_classify\<close>, whichever
  context policy filed it.
\<close>

lemma table_diagnostics_sound:
  fixes rt :: "('c, mcp_val) solved_table"
  assumes fin: "finite (table_contexts rt v)"
    and look: "lookup_table rt v ctx = Lifted st"
    and s: "s \<in> mcp.act_gamma ds as st"
  shows table_diagnostics_safe:
      "(v, obs) \<in> set sites \<Longrightarrow> ob \<in> set obs
         \<Longrightarrow> \<forall>d \<in> set (arithmetic_diagnostics sites rt (obligation_classify sem ds as)).
               diagnostic_point d \<noteq> v
         \<Longrightarrow> s \<Turnstile> ob"
    and table_diagnostics_refuted:
      "d \<in> set (arithmetic_diagnostics sites rt (obligation_classify sem ds as))
         \<Longrightarrow> diagnostic_verdict d = Check_Refuted \<Longrightarrow> diagnostic_point d = v
         \<Longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d"
proof -
  let ?cl = "obligation_classify sem ds as"
  show "s \<Turnstile> ob"
    if site: "(v, obs) \<in> set sites" and ob: "ob \<in> set obs"
      and absent: "\<forall>d \<in> set (arithmetic_diagnostics sites rt ?cl). diagnostic_point d \<noteq> v"
  proof -
    have "point_verdict rt ?cl v ob = Lifted Check_Proved"
      using arithmetic_diagnostics_absent[OF site ob absent]
        point_verdict_not_dead[OF fin look, of ?cl ob]
      by auto
    then have "?cl ob st = Check_Proved"
      by (rule point_verdict_decided[OF _ _ look]) simp
    then show ?thesis by (rule obligation_classify_sound(1)[OF s])
  qed
  show "\<not> s \<Turnstile> diagnostic_obligation d"
    if d: "d \<in> set (arithmetic_diagnostics sites rt ?cl)"
      and r: "diagnostic_verdict d = Check_Refuted" and v: "diagnostic_point d = v"
  proof -
    have "point_verdict rt ?cl v (diagnostic_obligation d) = Lifted Check_Refuted"
      using arithmetic_diagnostics_refuted[OF d r] v by simp
    then have "?cl (diagnostic_obligation d) st = Check_Refuted"
      by (rule point_verdict_decided[OF _ _ look]) simp
    then show ?thesis by (rule obligation_classify_sound(2)[OF s])
  qed
qed

text \<open>
  Everything a typed report guarantees, in one predicate: it lists a row for every check
  edge, and at every store that reaches a node the store lies in a state the report
  lists there, no check there is dead, a proved check holds and a refuted one fails, a
  point no diagnostic names meets every obligation decided there, and a refuted
  obligation fails.
\<close>

definition report_sound :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> report \<Rightarrow> bool" where
  "report_sound conf ds p res \<longleftrightarrow>
     (\<forall>v l e w. (v, EA_Check l e, w) \<in> intra (elab_cfg p ds) \<longrightarrow>
        (\<exists>chk \<in> set (report_checks res). check_point chk = v \<and> check_label chk = l \<and> check_exp chk = e))
   \<and> (\<forall>v s. s \<in> reaching ds p v \<longrightarrow>
        (\<exists>d. Lifted d \<in> report_states_at res v \<and> s \<in> mcp.act_gamma ds (activation_of (conf_analyses conf)) d)
      \<and> (\<forall>chk \<in> set (report_checks res). check_point chk = v \<longrightarrow>
           check_verdict chk \<noteq> Dead
         \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (eval (check_exp chk) s))
         \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (eval (check_exp chk) s)))
      \<and> (\<forall>obs ob. (v, obs) \<in> set (prog_obligation_sites ds p) \<longrightarrow> ob \<in> set obs \<longrightarrow> SAFE res v \<longrightarrow> s \<Turnstile> ob)
      \<and> (\<forall>d \<in> set (report_diagnostics res). diagnostic_verdict d = Check_Refuted
           \<longrightarrow> diagnostic_point d = v \<longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d))"

text \<open>
  A report built from a solved table is sound when the table covers every reaching
  store, whichever context policy and placement filed it. The table's states are listed
  and its verdicts reported, so each guarantee is read off the state a reaching store
  lies in.
\<close>

lemma prog_report_of_sound:
  fixes sr :: "(var_id, exp, 'c, var_id, mcp_val) gsolved_run"
  assumes fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
    and node: "\<And>v. reaching ds p v \<subseteq> (\<Union>ctx. mcp.act_gamma ds (activation_of (conf_analyses conf))
                 (case lookup_table (run_table sr) v ctx of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st))"
  shows "report_sound conf ds p (prog_report_of conf ds p gs ctx_key ctx_tag sr)"
proof -
  let ?res = "prog_report_of conf ds p gs ctx_key ctx_tag sr"
  let ?rt = "run_table sr"
  let ?as = "activation_of (conf_analyses conf)" and ?sem = "conf_sem conf"
  let ?cl = "mcp_classify ?sem ds ?as"
  have checks: "report_checks ?res = result_checks_of (elab_cfg p ds) ?rt ?cl"
    and diags: "report_diagnostics ?res
                  = arithmetic_diagnostics (prog_obligation_sites ds p) ?rt (obligation_classify ?sem ds ?as)"
    by (simp_all add: prog_report_of_def report_of_def Let_def)
  have fin_g: "finite (intra (elab_cfg p ds))" by (simp add: elab_cfg_def compile_prog_finite)
  have rows: "\<exists>chk \<in> set (report_checks ?res). check_point chk = v \<and> check_label chk = l
                \<and> check_exp chk = e"
    if "(v, EA_Check l e, w) \<in> intra (elab_cfg p ds)" for v l e w
    using that fin_g by (force simp: checks result_checks_of_def)
  have at: "(\<exists>d. Lifted d \<in> report_states_at ?res v \<and> s \<in> mcp.act_gamma ds ?as d)
      \<and> (\<forall>chk \<in> set (report_checks ?res). check_point chk = v \<longrightarrow>
           check_verdict chk \<noteq> Dead
         \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (eval (check_exp chk) s))
         \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (eval (check_exp chk) s)))
      \<and> (\<forall>obs ob. (v, obs) \<in> set (prog_obligation_sites ds p) \<longrightarrow> ob \<in> set obs \<longrightarrow> SAFE ?res v \<longrightarrow> s \<Turnstile> ob)
      \<and> (\<forall>d \<in> set (report_diagnostics ?res). diagnostic_verdict d = Check_Refuted
           \<longrightarrow> diagnostic_point d = v \<longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d)"
    if s: "s \<in> reaching ds p v" for v s
  proof -
    obtain ctx st where look: "lookup_table ?rt v ctx = Lifted st"
      and st: "s \<in> mcp.act_gamma ds ?as st"
      using node[of v] s by (auto simp: mcp.act_gamma_bot split: lifted.splits)
    have fin_v: "finite (table_contexts ?rt v)" using fin unfolding table_contexts_def by simp
    have states: "Lifted st \<in> report_states_at ?res v"
      unfolding prog_report_of_def by (rule report_of_state_mem[OF fin inj look])
    have check: "check_verdict chk \<noteq> Dead
        \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (eval (check_exp chk) s))
        \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (eval (check_exp chk) s))"
      if mem: "chk \<in> set (report_checks ?res)" and pt: "check_point chk = v" for chk
    proof -
      from mem obtain u and a :: "(var_id, exp) gedge_action" where chk0: "chk = \<lparr>check_point = u, check_label = ea_check_label a,
          check_exp = ea_check_cond a, check_verdict = point_verdict ?rt ?cl u (ea_check_cond a)\<rparr>"
        unfolding checks result_checks_of_def by auto
      with pt have chk: "chk = \<lparr>check_point = v, check_label = ea_check_label a,
          check_exp = ea_check_cond a, check_verdict = point_verdict ?rt ?cl v (ea_check_cond a)\<rparr>"
        by simp
      have decided: "?cl (ea_check_cond a) st = r"
        if "point_verdict ?rt ?cl v (ea_check_cond a) = Decided r" and "r \<noteq> Check_Unknown" for r
        by (rule point_verdict_decided[OF that look])
      show ?thesis
        using point_verdict_not_dead[OF fin_v look, of ?cl "ea_check_cond a"]
          decided[of Check_Proved] decided[of Check_Refuted]
          mcp.mcp_classify_proved[OF st] mcp.mcp_classify_refuted[OF st]
        by (auto simp: chk)
    qed
    note diag = table_diagnostics_sound[OF fin_v look st, where sem = ?sem]
    show ?thesis using states st check diag unfolding diags by blast
  qed
  show ?thesis unfolding report_sound_def using rows at by blast
qed

text \<open>
  Every answered run is sound. The executable solve's answer is the run the typed
  theorems are about (\<open>solve_c_run\<close>), so its table covers every reaching store
  (\<open>mcp_cs_node_sound\<close> and its siblings for the other policy and placement).
\<close>

lemma report_run_sound:
  assumes wf: "wf_program_compile_input p" and run: "report_run conf ds p = Some res"
  shows "report_sound conf ds p res"
proof -
  let ?sem = "conf_sem conf" and ?as = "conf_analyses conf" and ?r = "conf_globals conf"
  let ?gs = "declared_globals p"
  show ?thesis
  proof (cases "conf_context conf")
    case (Call_String k)
    let ?key = "\<lambda>ctx. Key_List (map Key_Node ctx)"
      and ?tag = "if k = 0 then (\<lambda>_. Report_Unit) else Report_Call_String"
    show ?thesis
    proof (cases "conf_program_globals conf")
      case Program_Globals_Flow_Sensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (mcp_cs.equations ?sem ds ?as k is_global p)
                (mcp_cs.root_query ds p) = Some sol"
        and res: "res = prog_report_of conf ds p [] ?key ?tag
                    (mcp_cs.solved_run_of ?sem ds ?as k is_global p sol)"
        by (auto simp: report_run_def cs_run_def Call_String
            Program_Globals_Flow_Sensitive Let_def dg_pipeline.root_query_def)
      note solved = mcp_cs.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule prog_report_of_sound)
           (use solved mcp_cs.vars_finite_of_terminates[OF solved(1)]
              mcp_cs_node_sound[OF wf solved(1), unfolded mcp_cs.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_call_string_key\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (mcp_split.equations ?sem ds ?as k ?gs is_global p)
                (mcp_split.root_query ds p) = Some sol"
        and res: "res = prog_report_of conf ds p ?gs ?key ?tag
                    (mcp_split.solved_run_of ?sem ds ?as k ?gs is_global p sol)"
        by (auto simp: report_run_def cs_run_def Call_String
            Program_Globals_Flow_Insensitive Let_def dg_pipeline.root_query_def)
      note solved = mcp_split.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule prog_report_of_sound)
           (use solved mcp_split.vars_finite_of_terminates[OF solved(1)]
              mcp_split_node_sound[OF wf solved(1), unfolded mcp_split.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_call_string_key\<close>)
    qed
  next
    case Entry_State
    show ?thesis
    proof (cases "conf_program_globals conf")
      case Program_Globals_Flow_Sensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (mcp_es.equations ?sem ds ?as is_global p)
                (mcp_es.root_query ds p) = Some sol"
        and res: "res = prog_report_of conf ds p [] mcp_ctx_key Report_Entry
                    (mcp_es.solved_run_of ?sem ds ?as is_global p sol)"
        by (auto simp: report_run_def es_run_def Entry_State
            Program_Globals_Flow_Sensitive Let_def dg_pipeline.root_query_def)
      note solved = mcp_es.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule prog_report_of_sound)
           (use solved mcp_es.vars_finite_of_terminates[OF solved(1)]
              mcp_es_node_sound[OF wf solved(1), unfolded mcp_es.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_mcp_ctx_key\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (mcp_split_es.equations ?sem ds ?as ?gs is_global p)
                (mcp_split_es.root_query ds p) = Some sol"
        and res: "res = prog_report_of conf ds p ?gs mcp_ctx_key Report_Entry
                    (mcp_split_es.solved_run_of ?sem ds ?as ?gs is_global p sol)"
        by (auto simp: report_run_def es_run_def Entry_State
            Program_Globals_Flow_Insensitive Let_def dg_pipeline.root_query_def)
      note solved = mcp_split_es.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule prog_report_of_sound)
           (use solved mcp_split_es.vars_finite_of_terminates[OF solved(1)]
              mcp_split_es_node_sound[OF wf solved(1), unfolded mcp_split_es.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_mcp_ctx_key\<close>)
    qed
  qed
qed

text \<open>The guarantees one at a time, as the public theorems read them.\<close>

theorem report_check_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "report_run conf ds p = Some res"
    and chk: "chk \<in> set (report_checks res)"
    and s: "s \<in> reaching ds p (check_point chk)"
  shows "check_verdict chk = Decided Check_Proved \<Longrightarrow> truthy (eval (check_exp chk) s)"
    and "check_verdict chk = Decided Check_Refuted \<Longrightarrow> \<not> truthy (eval (check_exp chk) s)"
  using report_run_sound[OF wf run] chk s unfolding report_sound_def by blast+

theorem report_state_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "report_run conf ds p = Some res"
    and s: "s \<in> reaching ds p v"
  obtains d where "Lifted d \<in> report_states_at res v"
    and "s \<in> mcp.act_gamma ds (activation_of (conf_analyses conf)) d"
  using report_run_sound[OF wf run] s that unfolding report_sound_def by blast

theorem report_point_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "report_run conf ds p = Some res"
    and s: "s \<in> reaching ds p v"
  shows report_obligation_safe:
      "(v, obs) \<in> set (prog_obligation_sites ds p) \<Longrightarrow> ob \<in> set obs \<Longrightarrow> SAFE res v \<Longrightarrow> s \<Turnstile> ob"
    and report_obligation_refuted:
      "d \<in> set (report_diagnostics res) \<Longrightarrow> diagnostic_verdict d = Check_Refuted
         \<Longrightarrow> diagnostic_point d = v \<Longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d"
    and report_check_live:
      "chk \<in> set (report_checks res) \<Longrightarrow> check_point chk = v \<Longrightarrow> check_verdict chk \<noteq> Dead"
  using report_run_sound[OF wf run] s unfolding report_sound_def by blast+

text \<open>A report lists a check row for every check edge of the typed graph, at the edge's
  source and with its label and condition.\<close>

lemma report_check_row:
  assumes wf: "wf_program_compile_input p"
    and run: "report_run conf ds p = Some res"
    and edge: "(v, EA_Check l e, w) \<in> intra (elab_cfg p ds)"
  shows "\<exists>chk \<in> set (report_checks res). check_point chk = v \<and> check_label chk = l
           \<and> check_exp chk = e"
  using report_run_sound[OF wf run] edge unfolding report_sound_def by blast

text \<open>Every obligation of an expression an edge or a call evaluates is one the report
  decides at the edge's or the call's source, and every conversion of a call's result
  is one it decides where the callee returns.\<close>

lemma prog_obligation_site:
  assumes "(v, es) \<in> set (arithmetic_expression_sites (elab_cfg p ds))"
    and "e \<in> set es" and "ob \<in> set (arith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (prog_obligation_sites ds p) \<and> ob \<in> set obs"
  using assms unfolding prog_obligation_sites_def obligation_sites_def by force

lemma prog_obligation_site_intra:
  assumes "(v, a, w) \<in> intra (elab_cfg p ds)"
    and "e \<in> set (edge_expressions a)" and "ob \<in> set (arith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (prog_obligation_sites ds p) \<and> ob \<in> set obs"
  using assms
  by (intro prog_obligation_site[OF arithmetic_expression_sites_intra])
     (simp_all add: elab_cfg_def compile_prog_finite)

lemma prog_obligation_site_call:
  assumes "(v, ca, ce, k) \<in> calls (elab_cfg p ds)"
    and "e \<in> set (ce_args ca)" and "ob \<in> set (arith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (prog_obligation_sites ds p) \<and> ob \<in> set obs"
  using assms
  by (intro prog_obligation_site[OF arithmetic_expression_sites_call])
     (simp_all add: elab_cfg_def compile_prog_finite)

lemma prog_obligation_site_return:
  assumes call: "(u, ca, ce, k) \<in> calls (elab_cfg p ds)" and dst: "ce_dst ca = Some x"
    and ret: "(v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (elab_cfg p ds)"
    and narrows: "\<not> ik_widens (exp_kind e) (kenv_of ds x)"
  shows "(v, [Arithmetic_Obligation Conversion_Overflow (TCast (kenv_of ds x) e) e])
           \<in> set (prog_obligation_sites ds p)"
proof -
  have fin: "finite (intra (elab_cfg p ds))" "finite (calls (elab_cfg p ds))"
    by (simp_all add: elab_cfg_def compile_prog_finite)
  have "(u, ca, ce, k) \<in> set (cfg_calls_list (elab_cfg p ds))"
    and "(v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> set (cfg_intra_list (elab_cfg p ds))"
    using call ret fin by simp_all
  then show ?thesis
    unfolding prog_obligation_sites_def return_sites_def Let_def
    using dst narrows by (force simp: image_iff)
qed

text \<open>What an obligation of each hazard says about a store.\<close>

lemma obligation_holds_overflow [simp]:
  "t \<Turnstile> Arithmetic_Obligation Signed_Overflow (TArith k op a b) x
     \<longleftrightarrow> aop_eval op (eval a t) (eval b t) \<in> ik_range k"
  by (simp add: obligation_holds_def)

lemma obligation_holds_conversion [simp]:
  "t \<Turnstile> Arithmetic_Obligation Conversion_Overflow (TCast k a) x
     \<longleftrightarrow> eval a t \<in> ik_range k"
  "t \<Turnstile> Arithmetic_Obligation Conversion_Overflow (TN k n) x \<longleftrightarrow> n \<in> ik_range k"
  by (simp_all add: obligation_holds_def)

lemma obligation_holds_division [simp]:
  "t \<Turnstile> Arithmetic_Obligation Division_By_Zero e b \<longleftrightarrow> eval b t \<noteq> 0"
  by (simp add: obligation_holds_def)

text \<open>An expression raises an obligation for each of its nodes that can fail, at any
  depth.\<close>

fun subexps :: "exp \<Rightarrow> exp set" where
  "subexps (TArith k op a b) = insert (TArith k op a b) (subexps a \<union> subexps b)"
| "subexps (TCast k a) = insert (TCast k a) (subexps a)"
| "subexps (TCmp c a b) = insert (TCmp c a b) (subexps a \<union> subexps b)"
| "subexps (TNot a) = insert (TNot a) (subexps a)"
| "subexps (TAnd a b) = insert (TAnd a b) (subexps a \<union> subexps b)"
| "subexps (TOr a b) = insert (TOr a b) (subexps a \<union> subexps b)"
| "subexps e = {e}"

lemma arith_obligations_overflow:
  "TArith k op a b \<in> subexps e \<Longrightarrow> ik_signed k \<Longrightarrow> op \<noteq> AMod
     \<Longrightarrow> Arithmetic_Obligation Signed_Overflow (TArith k op a b) (TArith k op a b)
           \<in> set (arith_obligations e)"
  by (induction e) auto

lemma arith_obligations_division:
  "TArith k op a b \<in> subexps e \<Longrightarrow> op = ADiv \<or> op = AMod
     \<Longrightarrow> Arithmetic_Obligation Division_By_Zero (TArith k op a b) b \<in> set (arith_obligations e)"
  by (induction e) auto

lemma arith_obligations_conversion:
  "TCast k a \<in> subexps e \<Longrightarrow> \<not> ik_widens (exp_kind a) k
     \<Longrightarrow> Arithmetic_Obligation Conversion_Overflow (TCast k a) a \<in> set (arith_obligations e)"
  by (induction e) auto

lemma arith_obligations_literal:
  "TN k n \<in> subexps e \<Longrightarrow> n \<notin> ik_range k
     \<Longrightarrow> Arithmetic_Obligation Conversion_Overflow (TN k n) (TN k n) \<in> set (arith_obligations e)"
  by (induction e) (auto simp del: ik_range_iff)
subsection \<open>Rendering a typed report\<close>

text \<open>
  A typed report is rendered by \<^const>\<open>render_report\<close> with a renderer of its own: each
  active analysis shows a kind-tagged value per variable, the order analysis its facts,
  and an entry-state context the formal values of its active fields. Typed analyses keep
  every variable in a point's own state, so no edge reads or writes a global unknown.
\<close>


instantiation order_rel :: (type) join_val
begin
definition vjoin_order_rel :: "'v order_rel \<Rightarrow> 'v order_rel \<Rightarrow> 'v order_rel" where
  "vjoin_order_rel = sup"
instance ..
end

text \<open>An Int value prints the same at every refinement mode, so the report drops the mode.\<close>

definition it_untag :: "'m int_tuple \<Rightarrow> unit int_tuple" where
  "it_untag a = IT (it_ivl a) (it_cong a)"

datatype report_value =
    Interval_Value "ivl kd"
  | Congruence_Value "congruence kd"
  | Int_Value "unit int_tuple kd"
  | Sign_Value "sign kd"
  | Parity_Value "parity kd"
  | Order_Value "(vname \<times> vname) list option"

fun string_of_report_value :: "report_value \<Rightarrow> String.literal" where
  "string_of_report_value (Interval_Value v) = to_string v"
| "string_of_report_value (Congruence_Value v) = to_string v"
| "string_of_report_value (Int_Value v) = to_string v"
| "string_of_report_value (Sign_Value v) = to_string v"
| "string_of_report_value (Parity_Value v) = to_string v"
| "string_of_report_value (Order_Value v) = order_view_string v"

text \<open>A variable is shown by its name, qualified by its procedure when it is local.\<close>

fun var_label :: "var_id \<Rightarrow> vname" where
  "var_label (GlobalId x) = x"
| "var_label (ScopedId f x) = f + STR ''::'' + x"
| "var_label (ReturnId f) = f + STR ''::return''"
| "var_label ReturnVar = STR ''return''"

definition field_view ::
    "('a kd \<Rightarrow> report_value) \<Rightarrow> var_id list \<Rightarrow> 'a tabs lifted \<Rightarrow> report_value field_state" where
  "field_view mk vars d =
     Field_Store (map (\<lambda>x. (var_label x, mk (case d of Bot \<Rightarrow> KBot | Lifted \<sigma> \<Rightarrow> \<sigma> x))) vars)"

text \<open>An order fact relates variables of one procedure's state, so it names each by its
  own name.\<close>

fun var_name :: "var_id \<Rightarrow> vname" where
  "var_name (ScopedId f x) = x"
| "var_name x = var_label x"

definition order_field_view :: "var_id order_rel lifted \<Rightarrow> report_value field_state" where
  "order_field_view d =
     Field_Whole (Order_Value (case d of
        Lifted (OFacts _ ps) \<Rightarrow> Some (map (\<lambda>(a, b). (var_name a, var_name b)) (sorted_list_of_set ps))
      | _ \<Rightarrow> None))"

definition render ::
    "analysis list \<Rightarrow> var_id list \<Rightarrow> mcp_val \<Rightarrow> (analysis, report_value) analysis_view" where
  "render as vars v = map (\<lambda>a. (a, case a of
       Interval \<Rightarrow> field_view Interval_Value vars (slot1 v)
     | Congruence \<Rightarrow> field_view Congruence_Value vars (slot2 v)
     | Ana_Int Refine_Never \<Rightarrow> field_view (Int_Value \<circ> map_kd it_untag) vars (slot3n v)
     | Ana_Int Refine_Once \<Rightarrow> field_view (Int_Value \<circ> map_kd it_untag) vars (slot3o v)
     | Ana_Int Refine_Fixpoint \<Rightarrow> field_view (Int_Value \<circ> map_kd it_untag) vars (slot3f v)
     | Sign \<Rightarrow> field_view Sign_Value vars (slot4 v)
     | Parity \<Rightarrow> field_view Parity_Value vars (slot5 v)
     | Order \<Rightarrow> order_field_view (slot6 v))) as"

fun context_values :: "analysis list \<Rightarrow> mcp_ctx \<Rightarrow> report_value list" where
  "context_values as (Product i (Product c (Product (Product tn (Product to tf)) (Product s (Product q u))))) =
     concat (map (\<lambda>a. case a of
         Interval \<Rightarrow> map Interval_Value i
       | Congruence \<Rightarrow> map Congruence_Value c
       | Ana_Int Refine_Never \<Rightarrow> map (Int_Value \<circ> map_kd it_untag) tn
       | Ana_Int Refine_Once \<Rightarrow> map (Int_Value \<circ> map_kd it_untag) to
       | Ana_Int Refine_Fixpoint \<Rightarrow> map (Int_Value \<circ> map_kd it_untag) tf
       | Sign \<Rightarrow> map Sign_Value s
       | Parity \<Rightarrow> map Parity_Value q
       | Order \<Rightarrow> []) as)"

text \<open>The globals an edge or a call reads and writes, among those kept at their own
  unknowns.\<close>

definition footprints :: "(var_id, exp, var_id) footprints" where
  "footprints =
     \<lparr> fp_edge_reads = gedge_global_reads exp_vars, fp_edge_writes = gedge_global_writes ReturnVar,
       fp_call_reads = gcall_global_reads exp_vars,
       fp_call_writes = (\<lambda>G ca. case ca of CallEdge dst pars args \<Rightarrow>
         global_names_in G (case_option [] (\<lambda>x. [x]) dst @ pars)) \<rparr>"

definition renderer ::
    "(voblint_conf, mcp_ctx, mcp_val, var_id, exp, var_id,
      analysis, report_value) report_renderer" where
  "renderer =
     \<lparr> rr_view = (\<lambda>conf. render (activation_of (conf_analyses conf))),
       rr_context = (\<lambda>conf. context_values (activation_of (conf_analyses conf))),
       rr_footprints = footprints \<rparr>"

definition prog_render_report ::
    "(report_value \<Rightarrow> 'v) \<Rightarrow> report \<Rightarrow> (var_id, exp, var_id, analysis, 'v) run_result" where
  "prog_render_report = render_report renderer"

end
