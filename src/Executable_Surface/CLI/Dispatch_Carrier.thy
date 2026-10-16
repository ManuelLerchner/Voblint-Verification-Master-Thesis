theory Dispatch_Carrier
  imports "Voblint_Analysis_Order.Order_Analysis"
begin

section \<open>What each domain's value needs to be shown and listed\<close>

text \<open>
  A rendered state shows each analysis's part of it, and a report lists the contexts
  it was solved at. What that needs from each domain is domain content and stays here:
  how an order value is shown, and an injective key for every domain's value.
\<close>

text \<open>A report names an order fact's variables by their labels, so it prints the facts
  as an order value over names.\<close>

definition order_view_string :: "(vname \<times> vname) list option \<Rightarrow> String.literal" where
  "order_view_string v =
     to_string (case v of None \<Rightarrow> (OBot :: vname order_rel) | Some ps \<Rightarrow> OFacts False (set ps))"

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
  derived linear order, and each domain's key maps its values into it
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


end
