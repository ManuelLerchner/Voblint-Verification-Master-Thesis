theory Dispatch_Carrier
  imports
    Voblint_Analysis_Sign.Sign_Analyses
    Voblint_Analysis_Interval.Interval_Analyses
    Voblint_Analysis_Int.Int_Analyses
    Voblint_Analysis_Parity.Parity_Analyses
    Voblint_Analysis_Congruence.Congruence_Analyses
begin

section \<open>One value type wide enough for every domain's result\<close>

text \<open>
  A run result crosses the dispatcher without its caller knowing which analysis
  produced it, so every abstract value in it has to have one type.
  \<open>abstract_value\<close> is that type: a tagged union with one constructor per
  selectable domain.

  This is handwritten and stays handwritten. The datatype names each domain's
  own abstract value type, which is domain content rather than registration.
\<close>

datatype abstract_value =
    SignValue sign
  | IntervalValue ivl
  | IntDomValue int_dom
  | ParityValue parity
  | CongruenceValue congruence

text \<open>
  How a value reads is its domain's business: each domain's \<^class>\<open>executable_domain\<close>
  instance carries its own \<^const>\<open>to_string\<close>, and this dispatch is the only rendering a
  run result receives before it leaves Isabelle. It changes no verdict, no point and no
  context identity, so no soundness claim reads it.
\<close>

fun string_of_abstract_value :: "abstract_value \<Rightarrow> String.literal" where
  "string_of_abstract_value (SignValue s) = to_string s"
| "string_of_abstract_value (IntervalValue i) = to_string i"
| "string_of_abstract_value (IntDomValue d) = to_string d"
| "string_of_abstract_value (ParityValue v) = to_string v"
| "string_of_abstract_value (CongruenceValue v) = to_string v"

section \<open>Listing a set of contexts without reading its values' order\<close>

text \<open>
  A solved table covers a \<^emph>\<open>set\<close> of contexts at each point, and a result handed to a
  caller lists them. Listing needs a linear order, but a domain's value type
  already spends its \<^class>\<open>ord\<close> instance on the abstraction order, under which
  \<open>[0,1]\<close> and \<open>[2,3]\<close> are incomparable. \<open>order_key\<close> is a separate type with a
  derived linear order, and \<open>abstract_value_key\<close> maps every value into it
  injectively. Because the map is injective, listing by it drops no context --- and
  because it reads the value's structure rather than its rendering, no printer
  decides what is listed.
\<close>

datatype order_key = Key_Int int | Key_Node cfg_node | Key_List "order_key list"

derive linorder order_key

fun sign_key :: "sign \<Rightarrow> order_key" where
  "sign_key SBot = Key_Int 0"
| "sign_key SNeg = Key_Int 1"
| "sign_key SNonPos = Key_Int 2"
| "sign_key SZero = Key_Int 3"
| "sign_key SNonNeg = Key_Int 4"
| "sign_key SPos = Key_Int 5"
| "sign_key STop = Key_Int 6"

fun parity_key :: "parity \<Rightarrow> order_key" where
  "parity_key PBot = Key_Int 0"
| "parity_key PEven = Key_Int 1"
| "parity_key POdd = Key_Int 2"
| "parity_key PTop = Key_Int 3"

fun eint_key :: "eint \<Rightarrow> order_key" where
  "eint_key MinInf = Key_List [Key_Int 0]"
| "eint_key (Fin n) = Key_List [Key_Int 1, Key_Int n]"
| "eint_key PlusInf = Key_List [Key_Int 2]"

fun ivl_key :: "ivl \<Rightarrow> order_key" where
  "ivl_key (Ivl l u) = Key_List [eint_key l, eint_key u]"

definition congruence_key :: "congruence \<Rightarrow> order_key" where
  "congruence_key v =
     (case Rep_congruence v of
        None \<Rightarrow> Key_List []
      | Some (r, m) \<Rightarrow> Key_List [Key_Int r, Key_Int m])"

definition int_dom_key :: "int_dom \<Rightarrow> order_key" where
  "int_dom_key d =
     Key_List [sign_key (int_sign d), ivl_key (int_ivl d),
               parity_key (int_parity d), congruence_key (int_congruence d)]"

fun abstract_value_key :: "abstract_value \<Rightarrow> order_key" where
  "abstract_value_key (SignValue v) = Key_List [Key_Int 0, sign_key v]"
| "abstract_value_key (IntervalValue v) = Key_List [Key_Int 1, ivl_key v]"
| "abstract_value_key (IntDomValue v) = Key_List [Key_Int 2, int_dom_key v]"
| "abstract_value_key (ParityValue v) = Key_List [Key_Int 3, parity_key v]"
| "abstract_value_key (CongruenceValue v) = Key_List [Key_Int 4, congruence_key v]"

lemma sign_key_inject [simp]: "sign_key a = sign_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma parity_key_inject [simp]: "parity_key a = parity_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma eint_key_inject [simp]: "eint_key a = eint_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma ivl_key_inject [simp]: "ivl_key a = ivl_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma congruence_key_inject [simp]: "congruence_key a = congruence_key b \<longleftrightarrow> a = b"
  unfolding congruence_key_def
  by (auto simp flip: Rep_congruence_inject split: option.splits)

lemma int_dom_key_inject [simp]: "int_dom_key a = int_dom_key b \<longleftrightarrow> a = b"
  unfolding int_dom_key_def by (cases a; cases b) simp

lemma abstract_value_key_inject [simp]:
  "abstract_value_key a = abstract_value_key b \<longleftrightarrow> a = b"
  by (cases a; cases b) simp_all

lemma inj_abstract_value_key: "inj abstract_value_key"
  by (rule injI) simp

end
