theory Typed_Report
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

fun tarith_obligations :: "texp \<Rightarrow> texp arithmetic_obligation list" where
  "tarith_obligations (TN k n) =
     (if n \<in> ik_range k then [] else [Arithmetic_Obligation Conversion_Overflow (TN k n) (TN k n)])"
| "tarith_obligations (TVar _ _) = []"
| "tarith_obligations (TArith k op a b) =
     tarith_obligations a @ tarith_obligations b
     @ (if op = ADiv \<or> op = AMod
        then [Arithmetic_Obligation Division_By_Zero (TArith k op a b) b] else [])
     @ (if ik_signed k \<and> op \<noteq> AMod
        then [Arithmetic_Obligation Signed_Overflow (TArith k op a b) (TArith k op a b)] else [])"
| "tarith_obligations (TCast k a) =
     tarith_obligations a
     @ (if ik_widens (texp_kind a) k then []
        else [Arithmetic_Obligation Conversion_Overflow (TCast k a) a])"
| "tarith_obligations (TCmp _ a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TNot a) = tarith_obligations a"
| "tarith_obligations (TAnd a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TOr a b) = tarith_obligations a @ tarith_obligations b"

text \<open>A division obligation is safe when its divisor is not zero, compared at the divisor's
  kind.\<close>

definition tarith_condition :: "texp arithmetic_obligation \<Rightarrow> texp" where
  "tarith_condition ob =
     TCmp CNe (arithmetic_operand ob) (TN (texp_kind (arithmetic_operand ob)) 0)"

text \<open>
  An overflow obligation is about the value an operation computes before its kind
  wraps it: the mathematical result of an arithmetic node, the converted value of a
  conversion. It is safe when that value lies in the node's kind. The statement does
  not depend on the overflow policy: the policy decides how an analysis abstracts a
  wrapped result, never what the program computes.
\<close>

fun tunwrapped :: "texp \<Rightarrow> tstore \<Rightarrow> int" where
  "tunwrapped (TN k n) t = n"
| "tunwrapped (TArith k op a b) t = aop_eval op (teval a t) (teval b t)"
| "tunwrapped (TCast k a) t = teval a t"
| "tunwrapped e t = teval e t"

definition tobligation_holds :: "texp arithmetic_obligation \<Rightarrow> tstore \<Rightarrow> bool" where
  "tobligation_holds ob t \<longleftrightarrow>
     (case arithmetic_hazard ob of
        Division_By_Zero \<Rightarrow> teval (arithmetic_operand ob) t \<noteq> 0
      | _ \<Rightarrow> tunwrapped (arithmetic_operation ob) t \<in> ik_range (texp_kind (arithmetic_operation ob)))"

abbreviation tsatisfies :: "tstore \<Rightarrow> texp arithmetic_obligation \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "s \<Turnstile> ob \<equiv> tobligation_holds ob s"

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

fun operand_ivl :: "texp gchannel \<Rightarrow> texp \<Rightarrow> ivl" where
  "operand_ivl ch (TN k n) = Ivl (Fin (ik_norm k n)) (Fin (ik_norm k n))"
| "operand_ivl ch (TCmp c a b) = answer_ivl (ch (EvalInt (TCmp c a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TNot a) = answer_ivl (ch (EvalInt (TNot a))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TAnd a b) = answer_ivl (ch (EvalInt (TAnd a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch (TOr a b) = answer_ivl (ch (EvalInt (TOr a b))) \<sqinter> Ivl (Fin 0) (Fin 1)"
| "operand_ivl ch e = answer_ivl (ch (EvalInt e))"

fun tunwrapped_ivl :: "texp gchannel \<Rightarrow> texp \<Rightarrow> ivl" where
  "tunwrapped_ivl ch (TN k n) = Ivl (Fin n) (Fin n)"
| "tunwrapped_ivl ch (TArith k op a b) = ivl_aop op (operand_ivl ch a) (operand_ivl ch b)"
| "tunwrapped_ivl ch (TCast k a) = operand_ivl ch a"
| "tunwrapped_ivl ch e = operand_ivl ch e"

lemma tunwrapped_ivl_sound:
  assumes "geval_query.channel_holds teval ch t"
  shows "tunwrapped e t \<in> gamma_ivl (tunwrapped_ivl ch e)"
proof -
  have answer: "teval a t \<in> gamma_ivl (answer_ivl (ch (EvalInt a)))" for a
    using geval_query.channel_holdsD[OF assms, of "EvalInt a"] by (auto intro: answer_ivl_sound)
  have truth: "teval a t \<in> gamma_ivl (Ivl (Fin 0) (Fin 1))"
    if "a \<in> {TCmp c x y | c x y. True} \<union> range TNot \<union> {TAnd x y | x y. True} \<union> {TOr x y | x y. True}"
    for a
    using that by (auto simp: less_eq_eint_def)
  have ans: "teval a t \<in> gamma_ivl (operand_ivl ch a)" for a
    using answer[of a] truth[of a]
    by (cases a) (auto simp: less_eq_eint_def gamma_inf_ivl)
  show ?thesis
  proof (cases e)
    case (TN k n) then show ?thesis by (simp add: less_eq_eint_def)
  qed (simp_all only: tunwrapped.simps tunwrapped_ivl.simps ans ivl_aop_sound)
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

definition tobligation_classify ::
    "sem_conf \<Rightarrow> kind_decls \<Rightarrow> typed_domain list \<Rightarrow> texp arithmetic_obligation \<Rightarrow> tmcp_val
       \<Rightarrow> check_result" where
  "tobligation_classify sem ds as ob v =
     (case arithmetic_hazard ob of
        Division_By_Zero \<Rightarrow> tmcp_classify sem ds as (tarith_condition ob) v
      | _ \<Rightarrow> fits_verdict (texp_kind (arithmetic_operation ob))
              (tunwrapped_ivl (tmcp_ask sem ds as v) (arithmetic_operation ob)))"

lemma tobligation_classify_sound:
  assumes t: "t \<in> tmcp.act_gamma ds as v"
  shows "tobligation_classify sem ds as ob v = Check_Proved \<Longrightarrow> t \<Turnstile> ob"
    and "tobligation_classify sem ds as ob v = Check_Refuted \<Longrightarrow> \<not> t \<Turnstile> ob"
proof -
  have ch: "geval_query.channel_holds teval (tmcp_ask sem ds as v) t"
    by (rule tmcp.mcp_ask_sound[OF t])
  note fits = fits_verdict_sound[OF tunwrapped_ivl_sound[OF ch]]
  have ne: "truthy (teval (tarith_condition ob) t) \<longleftrightarrow> teval (arithmetic_operand ob) t \<noteq> 0"
    by (simp add: tarith_condition_def)
  show "tobligation_classify sem ds as ob v = Check_Proved \<Longrightarrow> t \<Turnstile> ob"
    using fits(1) tmcp.mcp_classify_proved[OF t] ne
    by (auto simp: tobligation_classify_def tobligation_holds_def split: arithmetic_hazard.splits)
  show "tobligation_classify sem ds as ob v = Check_Refuted \<Longrightarrow> \<not> t \<Turnstile> ob"
    using fits(2) tmcp.mcp_classify_refuted[OF t] ne
    by (auto simp: tobligation_classify_def tobligation_holds_def split: arithmetic_hazard.splits)
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

definition treturn_sites ::
    "kind_decls \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> texp arithmetic_obligation list) list" where
  "treturn_sites ds p =
     (let g = typed_cfg p ds
      in remdups (concat (map (\<lambda>(u, ca, ce, k). case ce_dst ca of
           None \<Rightarrow> []
         | Some x \<Rightarrow> concat (map (\<lambda>(v, a, w). case a of
               EA_Ret (Some e) q \<Rightarrow>
                 if q = callee_of_entry ce \<and> \<not> ik_widens (texp_kind e) (kenv_of ds x)
                 then [(v, [Arithmetic_Obligation Conversion_Overflow (TCast (kenv_of ds x) e) e])]
                 else []
             | _ \<Rightarrow> []) (cfg_intra_list g)))
         (cfg_calls_list g))))"

definition tobligation_sites :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> texp arithmetic_obligation list) list" where
  "tobligation_sites ds p =
     obligation_sites tarith_obligations (typed_cfg p ds) @ treturn_sites ds p"

text \<open>The obligations a typed report decides at a point, and what it means for a store
  to meet one: \<open>s \<Turnstile> ob\<close>.\<close>

definition tobligations_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> texp arithmetic_obligation set" where
  "tobligations_at ds p v = (\<Union>(u, obs) \<in> set (tobligation_sites ds p). if u = v then set obs else {})"

lemma mem_tobligations_at:
  "ob \<in> tobligations_at ds p v \<longleftrightarrow> (\<exists>obs. (v, obs) \<in> set (tobligation_sites ds p) \<and> ob \<in> set obs)"
  by (force simp: tobligations_at_def split: if_splits)

text \<open>The variables a report lists: every variable an edge or a call of the typed graph
  mentions.\<close>

fun tspecial_vars :: "texp gspecial_call \<Rightarrow> var_id list" where
  "tspecial_vars Nondet_Int = []"
| "tspecial_vars (Min a b) = tvar_list a @ tvar_list b"
| "tspecial_vars (Max a b) = tvar_list a @ tvar_list b"

fun tedge_vars :: "(var_id, texp) gedge_action \<Rightarrow> var_id list" where
  "tedge_vars (EA_Assign x e) = x # tvar_list e"
| "tedge_vars (EA_Special sc x) = x # tspecial_vars sc"
| "tedge_vars (EA_Assume b) = tvar_list b"
| "tedge_vars (EA_AssumeNot b) = tvar_list b"
| "tedge_vars (EA_Ret e _) = (case e of Some e \<Rightarrow> tvar_list e | None \<Rightarrow> [])"
| "tedge_vars (EA_Check _ e) = tvar_list e"
| "tedge_vars _ = []"

fun tcall_vars :: "(var_id, texp) gcall_action \<Rightarrow> var_id list" where
  "tcall_vars (CallEdge dst ps args) =
     (case dst of Some x \<Rightarrow> [x] | None \<Rightarrow> []) @ ps @ concat (map tvar_list args)"

definition typed_vars :: "(var_id, texp) gcfg \<Rightarrow> var_id list" where
  "typed_vars g =
     sorted_list_of_set (set (concat (map (\<lambda>(u, a, w). tedge_vars a) (cfg_intra_list g))
                            @ concat (map (\<lambda>(u, ca, e, w). tcall_vars ca) (cfg_calls_list g))))"

type_synonym typed_report =
  "(voblint_conf, tmcp_ctx report_context,
    var_id, texp, var_id, tmcp_val) analysis_report"

text \<open>One builder for every context policy and placement: the policy contributes how its
  contexts are ordered and tagged, the placement which globals it keeps at their own
  unknowns.\<close>

definition typed_report_of ::
    "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> var_id list \<Rightarrow> ('c \<Rightarrow> order_key)
       \<Rightarrow> ('c \<Rightarrow> tmcp_ctx report_context) \<Rightarrow> (var_id, texp, 'c, var_id, tmcp_val) gsolved_run
       \<Rightarrow> typed_report" where
  "typed_report_of conf ds p gs ctx_key ctx_tag sr =
     report_of conf (typed_vars (typed_cfg p ds)) (typed_cfg p ds) gs
       (tobligation_sites ds p) (tobligation_classify (conf_sem conf) ds (tactivation (conf_analyses conf)))
       (prog_main_name # prog_procs p) ctx_key ctx_tag
       (tmcp_classify (conf_sem conf) ds (tactivation (conf_analyses conf))) sr"

subsection \<open>At entry-state contexts\<close>

text \<open>
  An entry-state context is listed in the order of an injective key, as a VIMP entry
  state is (\<^const>\<open>entry_ctx_key\<close>): each field's formal values, a kind-tagged value
  keyed by its tag, its kind and its value.
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

fun tmcp_ctx_key :: "tmcp_ctx \<Rightarrow> order_key" where
  "tmcp_ctx_key (Product i (Product c (Product (Product tn (Product to tf)) (Product s (Product q u))))) =
     Key_List [Key_List (map (kd_key ivl_key) i), Key_List (map (kd_key congruence_key) c),
               Key_List (map (kd_key int_tuple_key) tn), Key_List (map (kd_key int_tuple_key) to),
               Key_List (map (kd_key int_tuple_key) tf), Key_List (map (kd_key sign_key) s),
               Key_List (map (kd_key parity_key) q), Key_List (map (\<lambda>_. Key_List []) u)]"

lemma inj_tmcp_ctx_key: "inj tmcp_ctx_key"
proof (rule injI)
  fix a b :: tmcp_ctx
  assume eq: "tmcp_ctx_key a = tmcp_ctx_key b"
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

definition typed_cs_run :: "voblint_conf \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report option" where
  "typed_cs_run conf k ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          key = (\<lambda>ctx. Key_List (map Key_Node ctx));
          tag = (if k = 0 then (\<lambda>_. Report_Unit) else Report_Call_String);
          root = (cfg_exit (typed_cfg p ds), [])
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. typed_report_of conf ds p [] key tag
                                 (typed_mcp.solved_run_of sem ds as k tglobal p sol))
               (TD_side_rule_Interp_solve_c r (typed_mcp.equations sem ds as k tglobal p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = tdeclared_globals p
              in map_option (\<lambda>sol. typed_report_of conf ds p gs key tag
                                     (typed_mcp_split.solved_run_of sem ds as k gs tglobal p sol))
                   (TD_side_rule_Interp_solve_c r (typed_mcp_split.equations sem ds as k gs tglobal p)
                      root)))"

definition typed_es_run :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report option" where
  "typed_es_run conf ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          root = (cfg_exit (typed_cfg p ds), tmcp_root_ctx)
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. typed_report_of conf ds p [] tmcp_ctx_key Report_Entry
                                 (typed_mcp_es.solved_run_of sem ds as tglobal p sol))
               (TD_side_rule_Interp_solve_c r (typed_mcp_es.equations sem ds as tglobal p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = tdeclared_globals p
              in map_option (\<lambda>sol. typed_report_of conf ds p gs tmcp_ctx_key Report_Entry
                                     (typed_mcp_split_es.solved_run_of sem ds as gs tglobal p sol))
                   (TD_side_rule_Interp_solve_c r (typed_mcp_split_es.equations sem ds as gs tglobal p)
                      root)))"

definition typed_report_run :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report option" where
  "typed_report_run conf ds p =
     (case conf_context conf of
        Typed_Call_String k \<Rightarrow> typed_cs_run conf k ds p
      | Typed_Entry_State \<Rightarrow> typed_es_run conf ds p)"

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
  diagnostics off the solved table through \<^const>\<open>tobligation_classify\<close>, whichever
  context policy filed it.
\<close>

lemma table_diagnostics_sound:
  fixes rt :: "('c, tmcp_val) solved_table"
  assumes fin: "finite (table_contexts rt v)"
    and look: "lookup_table rt v ctx = Lifted st"
    and s: "s \<in> tmcp.act_gamma ds as st"
  shows table_diagnostics_safe:
      "(v, obs) \<in> set sites \<Longrightarrow> ob \<in> set obs
         \<Longrightarrow> \<forall>d \<in> set (arithmetic_diagnostics sites rt (tobligation_classify sem ds as)).
               diagnostic_point d \<noteq> v
         \<Longrightarrow> s \<Turnstile> ob"
    and table_diagnostics_refuted:
      "d \<in> set (arithmetic_diagnostics sites rt (tobligation_classify sem ds as))
         \<Longrightarrow> diagnostic_verdict d = Check_Refuted \<Longrightarrow> diagnostic_point d = v
         \<Longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d"
proof -
  let ?cl = "tobligation_classify sem ds as"
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
    then show ?thesis by (rule tobligation_classify_sound(1)[OF s])
  qed
  show "\<not> s \<Turnstile> diagnostic_obligation d"
    if d: "d \<in> set (arithmetic_diagnostics sites rt ?cl)"
      and r: "diagnostic_verdict d = Check_Refuted" and v: "diagnostic_point d = v"
  proof -
    have "point_verdict rt ?cl v (diagnostic_obligation d) = Lifted Check_Refuted"
      using arithmetic_diagnostics_refuted[OF d r] v by simp
    then have "?cl (diagnostic_obligation d) st = Check_Refuted"
      by (rule point_verdict_decided[OF _ _ look]) simp
    then show ?thesis by (rule tobligation_classify_sound(2)[OF s])
  qed
qed

text \<open>
  Everything a typed report guarantees, in one predicate: it lists a row for every check
  edge, and at every store that reaches a node the store lies in a state the report
  lists there, no check there is dead, a proved check holds and a refuted one fails, a
  point no diagnostic names meets every obligation decided there, and a refuted
  obligation fails.
\<close>

definition typed_report_sound :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report \<Rightarrow> bool" where
  "typed_report_sound conf ds p res \<longleftrightarrow>
     (\<forall>v l e w. (v, EA_Check l e, w) \<in> intra (typed_cfg p ds) \<longrightarrow>
        (\<exists>chk \<in> set (report_checks res). check_point chk = v \<and> check_label chk = l \<and> check_exp chk = e))
   \<and> (\<forall>v s. s \<in> reaching ds p v \<longrightarrow>
        (\<exists>d. Lifted d \<in> report_states_at res v \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d)
      \<and> (\<forall>chk \<in> set (report_checks res). check_point chk = v \<longrightarrow>
           check_verdict chk \<noteq> Dead
         \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (teval (check_exp chk) s))
         \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval (check_exp chk) s)))
      \<and> (\<forall>obs ob. (v, obs) \<in> set (tobligation_sites ds p) \<longrightarrow> ob \<in> set obs \<longrightarrow> SAFE res v \<longrightarrow> s \<Turnstile> ob)
      \<and> (\<forall>d \<in> set (report_diagnostics res). diagnostic_verdict d = Check_Refuted
           \<longrightarrow> diagnostic_point d = v \<longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d))"

text \<open>
  A report built from a solved table is sound when the table covers every reaching
  store, whichever context policy and placement filed it. The table's states are listed
  and its verdicts reported, so each guarantee is read off the state a reaching store
  lies in.
\<close>

lemma typed_report_of_sound:
  fixes sr :: "(var_id, texp, 'c, var_id, tmcp_val) gsolved_run"
  assumes fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
    and node: "\<And>v. reaching ds p v \<subseteq> (\<Union>ctx. tmcp.act_gamma ds (tactivation (conf_analyses conf))
                 (case lookup_table (run_table sr) v ctx of Bot \<Rightarrow> \<bottom> | Lifted st \<Rightarrow> st))"
  shows "typed_report_sound conf ds p (typed_report_of conf ds p gs ctx_key ctx_tag sr)"
proof -
  let ?res = "typed_report_of conf ds p gs ctx_key ctx_tag sr"
  let ?rt = "run_table sr"
  let ?as = "tactivation (conf_analyses conf)" and ?sem = "conf_sem conf"
  let ?cl = "tmcp_classify ?sem ds ?as"
  have checks: "report_checks ?res = result_checks_of (typed_cfg p ds) ?rt ?cl"
    and diags: "report_diagnostics ?res
                  = arithmetic_diagnostics (tobligation_sites ds p) ?rt (tobligation_classify ?sem ds ?as)"
    by (simp_all add: typed_report_of_def report_of_def Let_def)
  have fin_g: "finite (intra (typed_cfg p ds))" by (simp add: typed_cfg_def compile_prog_finite)
  have rows: "\<exists>chk \<in> set (report_checks ?res). check_point chk = v \<and> check_label chk = l
                \<and> check_exp chk = e"
    if "(v, EA_Check l e, w) \<in> intra (typed_cfg p ds)" for v l e w
    using that fin_g by (force simp: checks result_checks_of_def)
  have at: "(\<exists>d. Lifted d \<in> report_states_at ?res v \<and> s \<in> tmcp.act_gamma ds ?as d)
      \<and> (\<forall>chk \<in> set (report_checks ?res). check_point chk = v \<longrightarrow>
           check_verdict chk \<noteq> Dead
         \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (teval (check_exp chk) s))
         \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval (check_exp chk) s)))
      \<and> (\<forall>obs ob. (v, obs) \<in> set (tobligation_sites ds p) \<longrightarrow> ob \<in> set obs \<longrightarrow> SAFE ?res v \<longrightarrow> s \<Turnstile> ob)
      \<and> (\<forall>d \<in> set (report_diagnostics ?res). diagnostic_verdict d = Check_Refuted
           \<longrightarrow> diagnostic_point d = v \<longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d)"
    if s: "s \<in> reaching ds p v" for v s
  proof -
    obtain ctx st where look: "lookup_table ?rt v ctx = Lifted st"
      and st: "s \<in> tmcp.act_gamma ds ?as st"
      using node[of v] s by (auto simp: tmcp.act_gamma_bot split: lifted.splits)
    have fin_v: "finite (table_contexts ?rt v)" using fin unfolding table_contexts_def by simp
    have states: "Lifted st \<in> report_states_at ?res v"
      unfolding typed_report_of_def by (rule report_of_state_mem[OF fin inj look])
    have check: "check_verdict chk \<noteq> Dead
        \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (teval (check_exp chk) s))
        \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval (check_exp chk) s))"
      if mem: "chk \<in> set (report_checks ?res)" and pt: "check_point chk = v" for chk
    proof -
      from mem obtain u and a :: "(var_id, texp) gedge_action" where chk0: "chk = \<lparr>check_point = u, check_label = ea_check_label a,
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
          tmcp.mcp_classify_proved[OF st] tmcp.mcp_classify_refuted[OF st]
        by (auto simp: chk)
    qed
    note diag = table_diagnostics_sound[OF fin_v look st, where sem = ?sem]
    show ?thesis using states st check diag unfolding diags by blast
  qed
  show ?thesis unfolding typed_report_sound_def using rows at by blast
qed

text \<open>
  Every answered run is sound. The executable solve's answer is the run the typed
  theorems are about (\<open>solve_c_run\<close>), so its table covers every reaching store
  (\<open>typed_mcp_node_sound\<close> and its siblings for the other policy and placement).
\<close>

lemma typed_report_run_sound:
  assumes wf: "wf_program_compile_input p" and run: "typed_report_run conf ds p = Some res"
  shows "typed_report_sound conf ds p res"
proof -
  let ?sem = "conf_sem conf" and ?as = "conf_analyses conf" and ?r = "conf_globals conf"
  let ?gs = "tdeclared_globals p"
  show ?thesis
  proof (cases "conf_context conf")
    case (Typed_Call_String k)
    let ?key = "\<lambda>ctx. Key_List (map Key_Node ctx)"
      and ?tag = "if k = 0 then (\<lambda>_. Report_Unit) else Report_Call_String"
    show ?thesis
    proof (cases "conf_program_globals conf")
      case Program_Globals_Flow_Sensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (typed_mcp.equations ?sem ds ?as k tglobal p)
                (typed_mcp.root_query ds p) = Some sol"
        and res: "res = typed_report_of conf ds p [] ?key ?tag
                    (typed_mcp.solved_run_of ?sem ds ?as k tglobal p sol)"
        by (auto simp: typed_report_run_def typed_cs_run_def Typed_Call_String
            Program_Globals_Flow_Sensitive Let_def dg_pipeline.root_query_def)
      note solved = typed_mcp.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule typed_report_of_sound)
           (use solved typed_mcp.vars_finite_of_terminates[OF solved(1)]
              typed_mcp_node_sound[OF wf solved(1), unfolded typed_mcp.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_call_string_key\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (typed_mcp_split.equations ?sem ds ?as k ?gs tglobal p)
                (typed_mcp_split.root_query ds p) = Some sol"
        and res: "res = typed_report_of conf ds p ?gs ?key ?tag
                    (typed_mcp_split.solved_run_of ?sem ds ?as k ?gs tglobal p sol)"
        by (auto simp: typed_report_run_def typed_cs_run_def Typed_Call_String
            Program_Globals_Flow_Insensitive Let_def dg_pipeline.root_query_def)
      note solved = typed_mcp_split.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule typed_report_of_sound)
           (use solved typed_mcp_split.vars_finite_of_terminates[OF solved(1)]
              typed_mcp_split_node_sound[OF wf solved(1), unfolded typed_mcp_split.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_call_string_key\<close>)
    qed
  next
    case Typed_Entry_State
    show ?thesis
    proof (cases "conf_program_globals conf")
      case Program_Globals_Flow_Sensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (typed_mcp_es.equations ?sem ds ?as tglobal p)
                (typed_mcp_es.root_query ds p) = Some sol"
        and res: "res = typed_report_of conf ds p [] tmcp_ctx_key Report_Entry
                    (typed_mcp_es.solved_run_of ?sem ds ?as tglobal p sol)"
        by (auto simp: typed_report_run_def typed_es_run_def Typed_Entry_State
            Program_Globals_Flow_Sensitive Let_def dg_pipeline.root_query_def)
      note solved = typed_mcp_es.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule typed_report_of_sound)
           (use solved typed_mcp_es.vars_finite_of_terminates[OF solved(1)]
              typed_mcp_es_node_sound[OF wf solved(1), unfolded typed_mcp_es.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_tmcp_ctx_key\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from run obtain sol where
        sol: "TD_side_rule_Interp_solve_c ?r (typed_mcp_split_es.equations ?sem ds ?as ?gs tglobal p)
                (typed_mcp_split_es.root_query ds p) = Some sol"
        and res: "res = typed_report_of conf ds p ?gs tmcp_ctx_key Report_Entry
                    (typed_mcp_split_es.solved_run_of ?sem ds ?as ?gs tglobal p sol)"
        by (auto simp: typed_report_run_def typed_es_run_def Typed_Entry_State
            Program_Globals_Flow_Insensitive Let_def dg_pipeline.root_query_def)
      note solved = typed_mcp_split_es.solve_c_run[OF sol]
      show ?thesis
        unfolding res
        by (rule typed_report_of_sound)
           (use solved typed_mcp_split_es.vars_finite_of_terminates[OF solved(1)]
              typed_mcp_split_es_node_sound[OF wf solved(1), unfolded typed_mcp_split_es.state_at_unfold] in
             \<open>simp_all add: dg_pipeline.result_def dg_pipeline.sol_vars_def inj_tmcp_ctx_key\<close>)
    qed
  qed
qed

text \<open>The guarantees one at a time, as the public theorems read them.\<close>

theorem typed_report_check_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run conf ds p = Some res"
    and chk: "chk \<in> set (report_checks res)"
    and s: "s \<in> reaching ds p (check_point chk)"
  shows "check_verdict chk = Decided Check_Proved \<Longrightarrow> truthy (teval (check_exp chk) s)"
    and "check_verdict chk = Decided Check_Refuted \<Longrightarrow> \<not> truthy (teval (check_exp chk) s)"
  using typed_report_run_sound[OF wf run] chk s unfolding typed_report_sound_def by blast+

theorem typed_report_state_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run conf ds p = Some res"
    and s: "s \<in> reaching ds p v"
  obtains d where "Lifted d \<in> report_states_at res v"
    and "s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d"
  using typed_report_run_sound[OF wf run] s that unfolding typed_report_sound_def by blast

theorem typed_report_point_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run conf ds p = Some res"
    and s: "s \<in> reaching ds p v"
  shows typed_report_obligation_safe:
      "(v, obs) \<in> set (tobligation_sites ds p) \<Longrightarrow> ob \<in> set obs \<Longrightarrow> SAFE res v \<Longrightarrow> s \<Turnstile> ob"
    and typed_report_obligation_refuted:
      "d \<in> set (report_diagnostics res) \<Longrightarrow> diagnostic_verdict d = Check_Refuted
         \<Longrightarrow> diagnostic_point d = v \<Longrightarrow> \<not> s \<Turnstile> diagnostic_obligation d"
    and typed_report_check_live:
      "chk \<in> set (report_checks res) \<Longrightarrow> check_point chk = v \<Longrightarrow> check_verdict chk \<noteq> Dead"
  using typed_report_run_sound[OF wf run] s unfolding typed_report_sound_def by blast+

text \<open>A report lists a check row for every check edge of the typed graph, at the edge's
  source and with its label and condition.\<close>

lemma typed_report_check_row:
  assumes wf: "wf_program_compile_input p"
    and run: "typed_report_run conf ds p = Some res"
    and edge: "(v, EA_Check l e, w) \<in> intra (typed_cfg p ds)"
  shows "\<exists>chk \<in> set (report_checks res). check_point chk = v \<and> check_label chk = l
           \<and> check_exp chk = e"
  using typed_report_run_sound[OF wf run] edge unfolding typed_report_sound_def by blast

text \<open>Every obligation of an expression an edge or a call evaluates is one the report
  decides at the edge's or the call's source, and every conversion of a call's result
  is one it decides where the callee returns.\<close>

lemma tobligation_site:
  assumes "(v, es) \<in> set (arithmetic_expression_sites (typed_cfg p ds))"
    and "e \<in> set es" and "ob \<in> set (tarith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (tobligation_sites ds p) \<and> ob \<in> set obs"
  using assms unfolding tobligation_sites_def obligation_sites_def by force

lemma tobligation_site_intra:
  assumes "(v, a, w) \<in> intra (typed_cfg p ds)"
    and "e \<in> set (edge_expressions a)" and "ob \<in> set (tarith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (tobligation_sites ds p) \<and> ob \<in> set obs"
  using assms
  by (intro tobligation_site[OF arithmetic_expression_sites_intra])
     (simp_all add: typed_cfg_def compile_prog_finite)

lemma tobligation_site_call:
  assumes "(v, ca, ce, k) \<in> calls (typed_cfg p ds)"
    and "e \<in> set (ce_args ca)" and "ob \<in> set (tarith_obligations e)"
  shows "\<exists>obs. (v, obs) \<in> set (tobligation_sites ds p) \<and> ob \<in> set obs"
  using assms
  by (intro tobligation_site[OF arithmetic_expression_sites_call])
     (simp_all add: typed_cfg_def compile_prog_finite)

lemma tobligation_site_return:
  assumes call: "(u, ca, ce, k) \<in> calls (typed_cfg p ds)" and dst: "ce_dst ca = Some x"
    and ret: "(v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (typed_cfg p ds)"
    and narrows: "\<not> ik_widens (texp_kind e) (kenv_of ds x)"
  shows "(v, [Arithmetic_Obligation Conversion_Overflow (TCast (kenv_of ds x) e) e])
           \<in> set (tobligation_sites ds p)"
proof -
  have fin: "finite (intra (typed_cfg p ds))" "finite (calls (typed_cfg p ds))"
    by (simp_all add: typed_cfg_def compile_prog_finite)
  have "(u, ca, ce, k) \<in> set (cfg_calls_list (typed_cfg p ds))"
    and "(v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> set (cfg_intra_list (typed_cfg p ds))"
    using call ret fin by simp_all
  then show ?thesis
    unfolding tobligation_sites_def treturn_sites_def Let_def
    using dst narrows by (force simp: image_iff)
qed

text \<open>What an obligation of each hazard says about a store.\<close>

lemma tobligation_holds_overflow [simp]:
  "t \<Turnstile> Arithmetic_Obligation Signed_Overflow (TArith k op a b) x
     \<longleftrightarrow> aop_eval op (teval a t) (teval b t) \<in> ik_range k"
  by (simp add: tobligation_holds_def)

lemma tobligation_holds_conversion [simp]:
  "t \<Turnstile> Arithmetic_Obligation Conversion_Overflow (TCast k a) x
     \<longleftrightarrow> teval a t \<in> ik_range k"
  "t \<Turnstile> Arithmetic_Obligation Conversion_Overflow (TN k n) x \<longleftrightarrow> n \<in> ik_range k"
  by (simp_all add: tobligation_holds_def)

lemma tobligation_holds_division [simp]:
  "t \<Turnstile> Arithmetic_Obligation Division_By_Zero e b \<longleftrightarrow> teval b t \<noteq> 0"
  by (simp add: tobligation_holds_def)

text \<open>An expression raises an obligation for each of its nodes that can fail, at any
  depth.\<close>

fun tsubexps :: "texp \<Rightarrow> texp set" where
  "tsubexps (TArith k op a b) = insert (TArith k op a b) (tsubexps a \<union> tsubexps b)"
| "tsubexps (TCast k a) = insert (TCast k a) (tsubexps a)"
| "tsubexps (TCmp c a b) = insert (TCmp c a b) (tsubexps a \<union> tsubexps b)"
| "tsubexps (TNot a) = insert (TNot a) (tsubexps a)"
| "tsubexps (TAnd a b) = insert (TAnd a b) (tsubexps a \<union> tsubexps b)"
| "tsubexps (TOr a b) = insert (TOr a b) (tsubexps a \<union> tsubexps b)"
| "tsubexps e = {e}"

lemma tarith_obligations_overflow:
  "TArith k op a b \<in> tsubexps e \<Longrightarrow> ik_signed k \<Longrightarrow> op \<noteq> AMod
     \<Longrightarrow> Arithmetic_Obligation Signed_Overflow (TArith k op a b) (TArith k op a b)
           \<in> set (tarith_obligations e)"
  by (induction e) auto

lemma tarith_obligations_division:
  "TArith k op a b \<in> tsubexps e \<Longrightarrow> op = ADiv \<or> op = AMod
     \<Longrightarrow> Arithmetic_Obligation Division_By_Zero (TArith k op a b) b \<in> set (tarith_obligations e)"
  by (induction e) auto

lemma tarith_obligations_conversion:
  "TCast k a \<in> tsubexps e \<Longrightarrow> \<not> ik_widens (texp_kind a) k
     \<Longrightarrow> Arithmetic_Obligation Conversion_Overflow (TCast k a) a \<in> set (tarith_obligations e)"
  by (induction e) auto

lemma tarith_obligations_literal:
  "TN k n \<in> tsubexps e \<Longrightarrow> n \<notin> ik_range k
     \<Longrightarrow> Arithmetic_Obligation Conversion_Overflow (TN k n) (TN k n) \<in> set (tarith_obligations e)"
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

datatype typed_value =
    Typed_Interval_Value "ivl kd"
  | Typed_Congruence_Value "congruence kd"
  | Typed_Int_Value "unit int_tuple kd"
  | Typed_Sign_Value "sign kd"
  | Typed_Parity_Value "parity kd"
  | Typed_Order_Value "(vname \<times> vname) list option"

fun string_of_typed_value :: "typed_value \<Rightarrow> String.literal" where
  "string_of_typed_value (Typed_Interval_Value v) = to_string v"
| "string_of_typed_value (Typed_Congruence_Value v) = to_string v"
| "string_of_typed_value (Typed_Int_Value v) = to_string v"
| "string_of_typed_value (Typed_Sign_Value v) = to_string v"
| "string_of_typed_value (Typed_Parity_Value v) = to_string v"
| "string_of_typed_value (Typed_Order_Value v) = order_view_string v"

text \<open>A variable is shown by its name, qualified by its procedure when it is local.\<close>

fun var_label :: "var_id \<Rightarrow> vname" where
  "var_label (GlobalId x) = x"
| "var_label (ScopedId f x) = f + STR ''::'' + x"
| "var_label (ReturnId f) = f + STR ''::return''"
| "var_label ReturnVar = STR ''return''"

definition tfield_view ::
    "('a kd \<Rightarrow> typed_value) \<Rightarrow> var_id list \<Rightarrow> 'a tabs lifted \<Rightarrow> typed_value field_state" where
  "tfield_view mk vars d =
     Field_Store (map (\<lambda>x. (var_label x, mk (case d of Bot \<Rightarrow> KBot | Lifted \<sigma> \<Rightarrow> \<sigma> x))) vars)"

text \<open>An order fact relates variables of one procedure's state, so it names each by its
  own name.\<close>

fun var_name :: "var_id \<Rightarrow> vname" where
  "var_name (ScopedId f x) = x"
| "var_name x = var_label x"

definition order_field_view :: "var_id order_rel lifted \<Rightarrow> typed_value field_state" where
  "order_field_view d =
     Field_Whole (Typed_Order_Value (case d of
        Lifted (OFacts _ ps) \<Rightarrow> Some (map (\<lambda>(a, b). (var_name a, var_name b)) (sorted_list_of_set ps))
      | _ \<Rightarrow> None))"

definition typed_render ::
    "typed_domain list \<Rightarrow> var_id list \<Rightarrow> tmcp_val \<Rightarrow> (typed_domain, typed_value) analysis_view" where
  "typed_render as vars v = map (\<lambda>a. (a, case a of
       Typed_Interval \<Rightarrow> tfield_view Typed_Interval_Value vars (tslot1 v)
     | Typed_Congruence \<Rightarrow> tfield_view Typed_Congruence_Value vars (tslot2 v)
     | Typed_Int Refine_Never \<Rightarrow> tfield_view (Typed_Int_Value \<circ> map_kd it_untag) vars (tslot3n v)
     | Typed_Int Refine_Once \<Rightarrow> tfield_view (Typed_Int_Value \<circ> map_kd it_untag) vars (tslot3o v)
     | Typed_Int Refine_Fixpoint \<Rightarrow> tfield_view (Typed_Int_Value \<circ> map_kd it_untag) vars (tslot3f v)
     | Typed_Sign \<Rightarrow> tfield_view Typed_Sign_Value vars (tslot4 v)
     | Typed_Parity \<Rightarrow> tfield_view Typed_Parity_Value vars (tslot5 v)
     | Typed_Order \<Rightarrow> order_field_view (tslot6 v))) as"

fun typed_ctx_values :: "typed_domain list \<Rightarrow> tmcp_ctx \<Rightarrow> typed_value list" where
  "typed_ctx_values as (Product i (Product c (Product (Product tn (Product to tf)) (Product s (Product q u))))) =
     concat (map (\<lambda>a. case a of
         Typed_Interval \<Rightarrow> map Typed_Interval_Value i
       | Typed_Congruence \<Rightarrow> map Typed_Congruence_Value c
       | Typed_Int Refine_Never \<Rightarrow> map (Typed_Int_Value \<circ> map_kd it_untag) tn
       | Typed_Int Refine_Once \<Rightarrow> map (Typed_Int_Value \<circ> map_kd it_untag) to
       | Typed_Int Refine_Fixpoint \<Rightarrow> map (Typed_Int_Value \<circ> map_kd it_untag) tf
       | Typed_Sign \<Rightarrow> map Typed_Sign_Value s
       | Typed_Parity \<Rightarrow> map Typed_Parity_Value q
       | Typed_Order \<Rightarrow> []) as)"

text \<open>The globals an edge or a call reads and writes, among those kept at their own
  unknowns.\<close>

definition typed_footprints :: "(var_id, texp, var_id) footprints" where
  "typed_footprints =
     \<lparr> fp_edge_reads = gedge_global_reads tvars, fp_edge_writes = gedge_global_writes ReturnVar,
       fp_call_reads = gcall_global_reads tvars,
       fp_call_writes = (\<lambda>G ca. case ca of CallEdge dst pars args \<Rightarrow>
         global_names_in G (case_option [] (\<lambda>x. [x]) dst @ pars)) \<rparr>"

definition typed_renderer ::
    "(voblint_conf, tmcp_ctx, tmcp_val, var_id, texp, var_id,
      typed_domain, typed_value) report_renderer" where
  "typed_renderer =
     \<lparr> rr_view = (\<lambda>conf. typed_render (tactivation (conf_analyses conf))),
       rr_context = (\<lambda>conf. typed_ctx_values (tactivation (conf_analyses conf))),
       rr_footprints = typed_footprints \<rparr>"

definition typed_render_report ::
    "(typed_value \<Rightarrow> 'v) \<Rightarrow> typed_report \<Rightarrow> (var_id, texp, var_id, typed_domain, 'v) run_result" where
  "typed_render_report = render_report typed_renderer"

end
