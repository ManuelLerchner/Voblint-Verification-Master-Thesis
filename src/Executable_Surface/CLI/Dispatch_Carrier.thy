theory Dispatch_Carrier
  imports
    "Voblint_Domain.Int_Lattice"
    "Voblint_Domain.Order_Lattice"
    "Voblint_CFG.CFG_Def"
begin

section \<open>What each domain's published value needs to be shown and listed\<close>

text \<open>
  A run result carries every published value in one tagged union,
  \<open>abstract_value\<close>, which \<open>MCP_Carrier\<close> generates from the
  analysis manifest with one constructor per registered analysis. What the union
  needs from each domain is domain content and stays here: how an order value is
  listed, and an injective key for every domain's value.

  An order value is listed as its pairs, or \<^const>\<open>None\<close> where the state is
  unreachable, so that a key can tell two apart.
\<close>

definition order_pairs :: "relc \<Rightarrow> (vname \<times> vname) list option" where
  "order_pairs d = (case d of RelBot \<Rightarrow> None | RelC ps \<Rightarrow> Some (sorted_list_of_set ps))"

text \<open>
  A listed order reads as the order it lists. The listing and not the order is what
  the union carries, since only a finite listing has an injective key.
\<close>

definition order_view_string :: "(vname \<times> vname) list option \<Rightarrow> String.literal" where
  "order_view_string v = to_string (case v of None \<Rightarrow> RelBot | Some ps \<Rightarrow> RelC (set ps))"

text \<open>
  What one analysis shows of a state, as Goblint's report shows each component of its
  combined state on its own: a pointwise analysis a value per variable, an analysis whose
  state relates variables one value for the whole state.
\<close>

datatype 'v field_state = Field_Store "(vname \<times> 'v) list" | Field_Whole 'v

fun map_field_state :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v field_state \<Rightarrow> 'w field_state" where
  "map_field_state f (Field_Store bs) = Field_Store (map (\<lambda>(x, v). (x, f v)) bs)"
| "map_field_state f (Field_Whole v) = Field_Whole (f v)"

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

definition literal_key :: "String.literal \<Rightarrow> order_key" where
  "literal_key s = Key_List (map (\<lambda>c. Key_Int (of_char c)) (String.explode s))"

definition order_view_key :: "(vname \<times> vname) list option \<Rightarrow> order_key" where
  "order_view_key v =
     (case v of
        None \<Rightarrow> Key_List []
      | Some ps \<Rightarrow> Key_List [Key_List (map (\<lambda>(a, b). Key_List [literal_key a, literal_key b]) ps)])"

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

lemma literal_key_inject [simp]: "literal_key a = literal_key b \<longleftrightarrow> a = b"
proof
  assume "literal_key a = literal_key b"
  then have "String.explode a = String.explode b"
    unfolding literal_key_def by (auto dest: list.inj_map_strong[rotated])
  then show "a = b" by (simp add: String.explode_inject)
qed simp

lemma order_view_key_inject [simp]: "order_view_key a = order_view_key b \<longleftrightarrow> a = b"
proof
  assume "order_view_key a = order_view_key b"
  then show "a = b"
    unfolding order_view_key_def
    by (auto split: option.splits dest!: list.inj_map_strong[rotated])
qed simp

end
