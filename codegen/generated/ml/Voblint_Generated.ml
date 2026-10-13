
module Bit_Shifts : sig
  val push : Z.t -> Z.t -> Z.t
  val drop : Z.t -> Z.t -> Z.t
end = struct

let rec fold f xs y = match xs with
  [] -> y
  | (x :: xs) -> fold f xs (f x y);;

let rec replicate n x = (if Z.leq n Z.zero then [] else x :: replicate (Z.pred n) x);;

let max_index = Z.of_int max_int;;

let splitIndex i = let (b, s) = Z.div_rem i max_index
  in Z.to_int s :: replicate b max_int;;

let push' i k = Z.shift_left k i;;

let drop' i k = Z.shift_right k i;;

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

let push i = fold push' (splitIndex (Z.abs i));;

let drop i = fold drop' (splitIndex (Z.abs i));;

end;;


module Str_Literal : sig
  val literal_of_asciis : Z.t list -> string
  val asciis_of_literal: string -> Z.t list
end = struct

(* deliberate clones not relying on List._ module *)

let rec length xs = match xs with
    [] -> 0
  | x :: xs -> 1 + length xs;;

let rec nth xs n = match xs with
  (x :: xs) -> if n <= 0 then x else nth xs (n - 1);;

let rec map_range f n =
  if n <= 0
    then []
    else
      let m = n - 1
    in map_range f m @ [f m];;

let implode f xs =
  String.init (length xs) (fun n -> f (nth xs n));;

let explode f s =
  map_range (fun n -> f (String.get s n)) (String.length s);;

let z_128 = Z.of_int 128;;

let check_ascii k =
  if 0 <= k && k < 128
  then k
  else failwith "Non-ASCII character in literal";;

let char_of_ascii k = Char.chr (Z.to_int (Z.rem k z_128));;

let ascii_of_char c = Z.of_int (check_ascii (Char.code c));;

let literal_of_asciis ks = implode char_of_ascii ks;;

let asciis_of_literal s = explode ascii_of_char s;;

end;;

module Generated : sig
  type int = Int_of_integer of Z.t
  val integer_of_int : int -> Z.t
  type 'a set
  type nat
  val integer_of_nat : nat -> Z.t
  val nat_of_integer : Z.t -> nat
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type var_id = GlobalId of string | ScopedId of string * string |
    ReturnId of string | ReturnVar
  type ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64
  type texp
  type exp = N of int | V of string | Plus of exp * exp | Minus of exp * exp |
    Times of exp * exp | Div of exp * exp | Mod of exp * exp | Less of exp * exp
    | LessEq of exp * exp | Greater of exp * exp | GreaterEq of exp * exp |
    NotEq of exp * exp | Eq of exp * exp | Not of exp | And of exp * exp |
    Or of exp * exp | Cast of ikind * exp
  type cfg_node = Statement of nat | FunctionEntry of string |
    FunctionResult of string
  type sign
  type relc
  type ('a, 'b) gcall_action = CallEdge of 'a option * 'a list * 'b list
  type 'a gspecial_call = Nondet_Int | Min of 'a * 'a | Max of 'a * 'a
  type ('a, 'b) gedge_action = EA_Nop | EA_Assign of 'a * 'b |
    EA_Special of 'b gspecial_call * 'a | EA_Assume of 'b | EA_AssumeNot of 'b |
    EA_Body of string | EA_Ret of 'b option * string |
    EA_Check of (nat * nat) * 'b
  type ivl
  type parity
  type congruence
  type int_tuple
  type 'a lifted = Bot | Lifted of 'a
  type check_result = Check_Proved | Check_Refuted | Check_Unknown
  type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint
  type analysis_domain = Sign_Analysis | Interval_Analysis | Parity_Analysis |
    Int_Analysis of refine_mode | Congruence_Analysis | Order_Analysis
  type 'a int_dom_ext
  type ('a, 'b) analysis_product
  type ('a, 'b, 'c) gcom = SKIP of 'a | Assign of 'a * 'b * 'c |
    Check of 'a * (nat * nat) * 'c |
    Seq of ('a, 'b, 'c) gcom * ('a, 'b, 'c) gcom |
    If of 'a * 'c * ('a, 'b, 'c) gcom * ('a, 'b, 'c) gcom |
    While of 'a * 'c * ('a, 'b, 'c) gcom |
    Call of 'a * 'b option * string * 'c list | Return of 'a * 'c option |
    Restore of 'a | Unwind of 'a
  type ('a, 'b, 'c, 'd) gproc_decl_ext =
    Gproc_decl_ext of 'b list * ('a, 'b, 'c) gcom * 'd
  type 'a itself
  type 'a trace_key = Trace_Buffer | Trace_Global of string |
    Trace_Seed of cfg_node * 'a
  type ('a, 'b, 'c) gcfg_ext
  type ('a, 'b, 'c) route_event = Ev_Route of 'a * 'b * 'c
  type typed_answer = Typed_Malformed | Typed_No_Answer |
    Typed_Analysed of (cfg_node * (texp * check_result)) list
  type typed_domain = Typed_Interval | Typed_Congruence | Typed_Int |
    Typed_Order | Typed_Sign | Typed_Parity
  type 'a analysis_context = Context_Unit | Context_Entry of 'a list |
    Context_Call_String of cfg_node list
  type 'a field_state = Field_Store of (string * 'a) list | Field_Whole of 'a
  type abstract_value
  type ('a, 'b, 'c, 'd) trace_printers =
    Trace_Printers of
      ('a -> abstract_value analysis_context) * ('b -> 'a trace_key) *
        ('c -> ((analysis_domain * abstract_value field_state) list) lifted) *
        (string option ->
          'c -> ((analysis_domain * abstract_value field_state) list) lifted) *
        ('d -> ((analysis_domain * abstract_value field_state) list) lifted)
  type globals_rule = Globals_Join | Globals_Per_Origin | Globals_Warrow |
    Globals_Warrow_Per_Origin | Globals_Bounded_Narrowing of nat
  type ('a, 'b, 'c) solver_event = Ev_Start of 'a | Ev_Stop |
    Ev_Query of 'a * 'a * bool * bool | Ev_Query_Wpoint of 'a * bool |
    Ev_Iterate_From_Query of 'a | Ev_Add_Infl of ('a, 'b) sum * 'a |
    Ev_Answer of 'a * 'a * 'c | Ev_Query_Global of 'a * 'b |
    Ev_Answer_Global of 'a * 'b * 'c | Ev_Iterate of 'a * bool * bool * bool |
    Ev_Eq of 'a | Ev_Rhs of 'a * 'c | Ev_Still_Unstable of 'a |
    Ev_Widen of 'a * bool | Ev_Sol of 'a * bool * 'c * 'c * 'c |
    Ev_Wpoint_Remove of 'a * bool | Ev_Wpoint_Clear of 'a * bool |
    Ev_Update of 'a * bool * bool * 'c * 'c | Ev_Iterate_Changed of 'a |
    Ev_Side of 'a * 'b * 'c | Ev_Update_Global of 'a * 'b * bool * 'c * 'c |
    Ev_Destabilize of ('a, 'b) sum | Ev_Stable_Remove of 'a
  type report_context
  type context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString of nat
  type unknown_node = Local_Node of cfg_node * nat | Global_Node of string
  type 'a analysis_answer = Invalid_Activation | Malformed_Program | No_Answer |
    Analysed of 'a
  type program_globals = Program_Globals_Flow_Sensitive |
    Program_Globals_Flow_Insensitive
  type analysis_config =
    Analysis_Config of
      analysis_domain list * globals_rule * context_mode * program_globals
  type analysis_edge = Intra_Dep of (string, exp) gedge_action |
    Enter_Dep of (string, exp) gcall_action |
    Combine_Dep of (string, exp) gcall_action |
    Continue_Dep of (string, exp) gcall_action | Global_Read | Global_Write
  type result_global_unknown = Global_Named of string |
    Global_Seed of string * nat option
  type 'a imp_prog_ext
  type 'a call_route_ext
  type 'a analysis_graph_ext
  type arithmetic_obligation
  type arithmetic_diagnostic
  type ('a, 'b) result_global_ext
  type ('a, 'b) result_state_ext
  type 'a result_check_ext
  type ('a, 'b) run_result_ext
  type 'a analysis_report_ext
  val cfg_entry : ('a, 'b, 'c) gcfg_ext -> cfg_node
  val prog_procs : unit imp_prog_ext -> string list
  val declared_global_vars : 'a imp_prog_ext -> string list
  val prog_table :
    unit imp_prog_ext ->
      string -> (unit, string, exp, unit) gproc_decl_ext option
  val prog_main : unit imp_prog_ext -> (unit, string, exp) gcom
  val run_typed :
    typed_domain ->
      globals_rule -> (var_id * ikind) list -> unit imp_prog_ext -> typed_answer
  val arithmetic_divisor : arithmetic_obligation -> exp
  val prog_cfg : unit imp_prog_ext -> (string, exp, unit) gcfg_ext
  val typed_prog :
    unit imp_prog_ext -> (var_id * ikind) list -> unit imp_prog_ext
  val mk_program :
    (string * (unit, string, exp, unit) gproc_decl_ext) list ->
      (unit, string, exp) gcom -> string list -> unit imp_prog_ext
  val run_voblint :
    analysis_config ->
      unit imp_prog_ext -> unit analysis_report_ext analysis_answer
  val route_targets : 'a call_route_ext -> nat list
  val route_context : 'a call_route_ext -> nat
  val route_point : 'a call_route_ext -> cfg_node
  val cfg_points : (string, exp, unit) gcfg_ext -> cfg_node list
  val state_steps : ('a, 'b) result_state_ext -> (cfg_node * 'a lifted) list
  val state_point : ('a, 'b) result_state_ext -> cfg_node
  val state_value : ('a, 'b) result_state_ext -> 'a lifted
  val global_unknown : ('a, 'b) result_global_ext -> result_global_unknown
  val state_context : ('a, 'b) result_state_ext -> nat
  val global_state : ('a, 'b) result_global_ext -> 'a lifted
  val state_diagnostics :
    ('a, 'b) result_state_ext ->
      (arithmetic_obligation * check_result lifted) list
  val state_checks :
    ('a, 'b) result_state_ext -> (exp * check_result lifted) list
  val render_report :
    (abstract_value -> 'a) ->
      unit analysis_report_ext -> ('a, unit) run_result_ext
  val cfg_call_edges :
    (string, exp, unit) gcfg_ext ->
      (cfg_node * ((string, exp) gcall_action * (cfg_node * cfg_node))) list
  val cfg_intra_edges :
    (string, exp, unit) gcfg_ext ->
      (cfg_node * ((string, exp) gedge_action * cfg_node)) list
  val res_cfg : ('a, 'b) run_result_ext -> (string, exp, unit) gcfg_ext
  val check_exp : 'a result_check_ext -> exp
  val res_graph : ('a, 'b) run_result_ext -> unit analysis_graph_ext
  val route_callee : 'a call_route_ext -> string
  val string_of_abstract_value : abstract_value -> string
  val res_checks : ('a, 'b) run_result_ext -> unit result_check_ext list
  val res_joined :
    ('a, 'b) run_result_ext ->
      (cfg_node *
        (((analysis_domain * 'a field_state) list) lifted *
          (cfg_node *
            ((analysis_domain * 'a field_state) list) lifted) list)) list
  val res_routes : ('a, 'b) run_result_ext -> unit call_route_ext list
  val res_states :
    ('a, 'b) run_result_ext ->
      (((analysis_domain * 'a field_state) list), unit) result_state_ext list
  val check_label : 'a result_check_ext -> nat * nat
  val check_point : 'a result_check_ext -> cfg_node
  val res_globals :
    ('a, 'b) run_result_ext ->
      (((analysis_domain * 'a field_state) list), unit) result_global_ext list
  val res_contexts : ('a, 'b) run_result_ext -> 'a analysis_context list
  val check_verdict : 'a result_check_ext -> check_result lifted
  val prog_stmt_post_order : unit imp_prog_ext -> (string * cfg_node list) list
  val graph_edges :
    'a analysis_graph_ext ->
      (unknown_node * (analysis_edge * unknown_node)) list
  val graph_nodes : 'a analysis_graph_ext -> unknown_node list
  val res_diagnostics : ('a, 'b) run_result_ext -> arithmetic_diagnostic list
  val map_analysis_answer :
    ('a -> 'b) -> 'a analysis_answer -> 'b analysis_answer
  val diagnostic_point : arithmetic_diagnostic -> cfg_node
  val diagnostic_verdict : arithmetic_diagnostic -> check_result
  val arithmetic_operation : arithmetic_obligation -> exp
  val diagnostic_obligation : arithmetic_diagnostic -> arithmetic_obligation
  val diagnostic_occurrence : arithmetic_diagnostic -> nat
end = struct

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

let rec vjoin_fun _B f g = (fun x -> sup _B.sup_semilattice_sup (f x) (g x));;

type 'a join_val = {vjoin : 'a -> 'a -> 'a};;
let vjoin _A = _A.vjoin;;

let rec join_val_fun _B = ({vjoin = vjoin_fun _B} : ('a -> 'b) join_val);;

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec times_inta
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

let zero_inta : int = Int_of_integer Z.zero;;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Z.of_int 1);;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec lcm_integer
  a b = divide_integer (Z.mul (Z.abs a) (Z.abs b))
          ((fun k l -> if Z.equal k Z.zero then Z.abs l else if Z.equal
             l Z.zero then Z.abs k else Z.gcd k l)
            a b);;

let rec lcm_inta
  (Int_of_integer x) (Int_of_integer y) = Int_of_integer (lcm_integer x y);;

let rec gcd_intc
  (Int_of_integer x) (Int_of_integer y) =
    Int_of_integer
      ((fun k l -> if Z.equal k Z.zero then Z.abs l else if Z.equal
         l Z.zero then Z.abs k else Z.gcd k l)
        x y);;

type 'a set = Set of 'a list | Coset of 'a list;;

let rec fold f x1 s = match f, x1, s with f, [], s -> s
               | f, x :: xs, s -> fold f xs (f x s);;

let rec lcm_int (Set xs) = fold lcm_inta xs one_inta;;

let rec gcd_intb (Set xs) = fold gcd_intc xs zero_inta;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

type 'a dvd = {times_dvd : 'a times};;

type 'a gcda =
  {one_gcd : 'a one; zero_gcd : 'a zero; dvd_gcd : 'a dvd;
    gcda : 'a -> 'a -> 'a; lcma : 'a -> 'a -> 'a};;
let gcda _A = _A.gcda;;
let lcma _A = _A.lcma;;

type 'a gcd = {gcd_Gcd : 'a gcda; gcd : 'a set -> 'a; lcm : 'a set -> 'a};;
let gcd _A = _A.gcd;;
let lcm _A = _A.lcm;;

let zero_int = ({zero = zero_inta} : int zero);;

let one_int = ({one = one_inta} : int one);;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

let gcd_inta =
  ({one_gcd = one_int; zero_gcd = zero_int; dvd_gcd = dvd_int; gcda = gcd_intc;
     lcma = lcm_inta}
    : int gcda);;

let gcd_int = ({gcd_Gcd = gcd_inta; gcd = gcd_intb; lcm = lcm_int} : int gcd);;

let rec equal_inta k l = Z.equal (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec uminus_inta k = Int_of_integer (Z.neg (integer_of_int k));;

let rec minus_inta
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec plus_inta
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a power = {one_power : 'a one; times_power : 'a times};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring;
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1;
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors;
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
    ring_comm_ring : 'a ring};;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring;
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
    ring_1_comm_ring_1 : 'a ring_1};;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1;
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors;
    semidom_idom : 'a semidom;
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};;

let plus_int = ({plus = plus_inta} : int plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : int minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : int semiring_0_cancel);;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    int ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : int comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : int comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : int comm_semiring_0_cancel);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : int semiring_1_cancel);;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : int comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : int comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : int comm_semiring_1_cancel);;

let comm_semiring_1_cancel_crossproduct_int =
  ({comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
      comm_semiring_1_cancel_int}
    : int comm_semiring_1_cancel_crossproduct);;

let semiring_no_zero_divisors_int =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_int} :
    int semiring_no_zero_divisors);;

let semiring_1_no_zero_divisors_int =
  ({semiring_1_semiring_1_no_zero_divisors = semiring_1_int;
     semiring_no_zero_divisors_semiring_1_no_zero_divisors =
       semiring_no_zero_divisors_int}
    : int semiring_1_no_zero_divisors);;

let semiring_no_zero_divisors_cancel_int =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_int}
    : int semiring_no_zero_divisors_cancel);;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : int group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : int ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : int ring);;

let ring_no_zero_divisors_int =
  ({ring_ring_no_zero_divisors = ring_int;
     semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
       semiring_no_zero_divisors_cancel_int}
    : int ring_no_zero_divisors);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    int neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : int ring_1);;

let ring_1_no_zero_divisors_int =
  ({ring_1_ring_1_no_zero_divisors = ring_1_int;
     ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int;
     semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
       semiring_1_no_zero_divisors_int}
    : int ring_1_no_zero_divisors);;

let comm_ring_int =
  ({comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int;
     ring_comm_ring = ring_int}
    : int comm_ring);;

let comm_ring_1_int =
  ({comm_ring_comm_ring_1 = comm_ring_int;
     comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int;
     ring_1_comm_ring_1 = ring_1_int}
    : int comm_ring_1);;

let semidom_int =
  ({comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int;
     semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
    : int semidom);;

let idom_int =
  ({comm_ring_1_idom = comm_ring_1_int;
     ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int;
     semidom_idom = semidom_int;
     comm_semiring_1_cancel_crossproduct_idom =
       comm_semiring_1_cancel_crossproduct_int}
    : int idom);;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let rec abs_int i = (if less_int i zero_inta then uminus_inta i else i);;

let rec normalize_int x = abs_int x;;

let rec sgn_int
  i = (if equal_inta i zero_inta then zero_inta
        else (if less_int zero_inta i then one_inta
               else uminus_inta one_inta));;

let rec unit_factor_inta x = sgn_int x;;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial;
    semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

type 'a unit_factor = {unit_factor : 'a -> 'a};;
let unit_factor _A = _A.unit_factor;;

type 'a semidom_divide_unit_factor =
  {semidom_divide_semidom_divide_unit_factor : 'a semidom_divide;
    unit_factor_semidom_divide_unit_factor : 'a unit_factor};;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a normalization_semidom =
  {algebraic_semidom_normalization_semidom : 'a algebraic_semidom;
    semidom_divide_unit_factor_normalization_semidom :
      'a semidom_divide_unit_factor;
    normalize : 'a -> 'a};;
let normalize _A = _A.normalize;;

let rec divide_inta
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

type 'a semiring_gcd =
  {gcd_semiring_gcd : 'a gcda;
    normalization_semidom_semiring_gcd : 'a normalization_semidom};;

type 'a ring_gcd =
  {semiring_gcd_ring_gcd : 'a semiring_gcd;
    comm_ring_1_ring_gcd : 'a comm_ring_1};;

let divide_int = ({divide = divide_inta} : int divide);;

let divide_trivial_int =
  ({one_divide_trivial = one_int; zero_divide_trivial = zero_int;
     divide_divide_trivial = divide_int}
    : int divide_trivial);;

let semidom_divide_int =
  ({divide_trivial_semidom_divide = divide_trivial_int;
     semidom_semidom_divide = semidom_int;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_int}
    : int semidom_divide);;

let unit_factor_int = ({unit_factor = unit_factor_inta} : int unit_factor);;

let semidom_divide_unit_factor_int =
  ({semidom_divide_semidom_divide_unit_factor = semidom_divide_int;
     unit_factor_semidom_divide_unit_factor = unit_factor_int}
    : int semidom_divide_unit_factor);;

let algebraic_semidom_int =
  ({semidom_divide_algebraic_semidom = semidom_divide_int} :
    int algebraic_semidom);;

let normalization_semidom_int =
  ({algebraic_semidom_normalization_semidom = algebraic_semidom_int;
     semidom_divide_unit_factor_normalization_semidom =
       semidom_divide_unit_factor_int;
     normalize = normalize_int}
    : int normalization_semidom);;

let semiring_gcd_int =
  ({gcd_semiring_gcd = gcd_inta;
     normalization_semidom_semiring_gcd = normalization_semidom_int}
    : int semiring_gcd);;

let ring_gcd_int =
  ({semiring_gcd_ring_gcd = semiring_gcd_int;
     comm_ring_1_ring_gcd = comm_ring_1_int}
    : int ring_gcd);;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_inta
  k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_int =
  ({divide_modulo = divide_int; dvd_modulo = dvd_int; modulo = modulo_inta} :
    int modulo);;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a semiring_Gcd =
  {gcd_semiring_Gcd : 'a gcd; semiring_gcd_semiring_Gcd : 'a semiring_gcd};;

let semiring_Gcd_int =
  ({gcd_semiring_Gcd = gcd_int; semiring_gcd_semiring_Gcd = semiring_gcd_int} :
    int semiring_Gcd);;

type 'a idom_divide =
  {idom_idom_divide : 'a idom; semidom_divide_idom_divide : 'a semidom_divide};;

let idom_divide_int =
  ({idom_idom_divide = idom_int;
     semidom_divide_idom_divide = semidom_divide_int}
    : int idom_divide);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};;

type 'a idom_modulo =
  {idom_divide_idom_modulo : 'a idom_divide;
    semidom_modulo_idom_modulo : 'a semidom_modulo};;

let semiring_modulo_int =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int;
     modulo_semiring_modulo = modulo_int}
    : int semiring_modulo);;

let semiring_modulo_trivial_int =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_int;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
    : int semiring_modulo_trivial);;

let semidom_modulo_int =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_int;
     semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_int}
    : int semidom_modulo);;

let idom_modulo_int =
  ({idom_divide_idom_modulo = idom_divide_int;
     semidom_modulo_idom_modulo = semidom_modulo_int}
    : int idom_modulo);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};;

type 'a ring_parity =
  {semiring_parity_ring_parity : 'a semiring_parity;
    comm_ring_1_ring_parity : 'a comm_ring_1};;

let semiring_parity_int =
  ({semiring_modulo_semiring_parity = semiring_modulo_int} :
    int semiring_parity);;

let ring_parity_int =
  ({semiring_parity_ring_parity = semiring_parity_int;
     comm_ring_1_ring_parity = comm_ring_1_int}
    : int ring_parity);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec push_bit_integer n k = Bit_Shifts.push (integer_of_nat n) k;;

let rec bit_integer
  k n = not (Z.equal (Z.logand k (push_bit_integer n (Z.of_int 1))) Z.zero);;

let rec bit_int (Int_of_integer k) n = bit_integer k n;;

type 'a semiring_bits =
  {semiring_parity_semiring_bits : 'a semiring_parity;
    semiring_modulo_trivial_semiring_bits : 'a semiring_modulo_trivial;
    bit : 'a -> nat -> bool};;
let bit _A = _A.bit;;

let semiring_bits_int =
  ({semiring_parity_semiring_bits = semiring_parity_int;
     semiring_modulo_trivial_semiring_bits = semiring_modulo_trivial_int;
     bit = bit_int}
    : int semiring_bits);;

let rec comp f g = (fun x -> f (g x));;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec nat x = comp nat_of_integer integer_of_int x;;

let rec euclidean_size_int x = comp nat abs_int x;;

type 'a euclidean_semiring =
  {semidom_modulo_euclidean_semiring : 'a semidom_modulo;
    euclidean_size : 'a -> nat};;
let euclidean_size _A = _A.euclidean_size;;

type 'a euclidean_ring =
  {euclidean_semiring_euclidean_ring : 'a euclidean_semiring;
    idom_modulo_euclidean_ring : 'a idom_modulo};;

let euclidean_semiring_int =
  ({semidom_modulo_euclidean_semiring = semidom_modulo_int;
     euclidean_size = euclidean_size_int}
    : int euclidean_semiring);;

let euclidean_ring_int =
  ({euclidean_semiring_euclidean_ring = euclidean_semiring_int;
     idom_modulo_euclidean_ring = idom_modulo_int}
    : int euclidean_ring);;

type 'a factorial_semiring =
  {normalization_semidom_factorial_semiring : 'a normalization_semidom};;

type 'a factorial_semiring_gcd =
  {factorial_semiring_factorial_semiring_gcd : 'a factorial_semiring;
    semiring_Gcd_factorial_semiring_gcd : 'a semiring_Gcd};;

type 'a factorial_ring_gcd =
  {factorial_semiring_gcd_factorial_ring_gcd : 'a factorial_semiring_gcd;
    ring_gcd_factorial_ring_gcd : 'a ring_gcd;
    idom_divide_factorial_ring_gcd : 'a idom_divide};;

let factorial_semiring_int =
  ({normalization_semidom_factorial_semiring = normalization_semidom_int} :
    int factorial_semiring);;

let factorial_semiring_gcd_int =
  ({factorial_semiring_factorial_semiring_gcd = factorial_semiring_int;
     semiring_Gcd_factorial_semiring_gcd = semiring_Gcd_int}
    : int factorial_semiring_gcd);;

let factorial_ring_gcd_int =
  ({factorial_semiring_gcd_factorial_ring_gcd = factorial_semiring_gcd_int;
     ring_gcd_factorial_ring_gcd = ring_gcd_int;
     idom_divide_factorial_ring_gcd = idom_divide_int}
    : int factorial_ring_gcd);;

let rec unset_bit_integer
  n k = Z.logand k (Z.lognot (push_bit_integer n (Z.of_int 1)));;

let rec unset_bit_int
  n (Int_of_integer k) = Int_of_integer (unset_bit_integer n k);;

let rec mask_integer n = Z.sub (push_bit_integer n (Z.of_int 1)) (Z.of_int 1);;

let rec take_bit_integer n k = Z.logand k (mask_integer n);;

let rec take_bit_int
  n (Int_of_integer k) = Int_of_integer (take_bit_integer n k);;

let rec push_bit_int
  n (Int_of_integer k) = Int_of_integer (push_bit_integer n k);;

let rec flip_bit_integer n k = Z.logxor k (push_bit_integer n (Z.of_int 1));;

let rec flip_bit_int
  n (Int_of_integer k) = Int_of_integer (flip_bit_integer n k);;

let rec drop_bit_integer n k = Bit_Shifts.drop (integer_of_nat n) k;;

let rec drop_bit_int
  n (Int_of_integer k) = Int_of_integer (drop_bit_integer n k);;

let rec set_bit_integer n k = Z.logor k (push_bit_integer n (Z.of_int 1));;

let rec set_bit_int
  n (Int_of_integer k) = Int_of_integer (set_bit_integer n k);;

let rec mask_int n = Int_of_integer (mask_integer n);;

let rec xor_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logxor k l);;

let rec and_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logand k l);;

let rec or_int
  (Int_of_integer k) (Int_of_integer l) = Int_of_integer (Z.logor k l);;

type 'a semiring_bit_operations =
  {semiring_bits_semiring_bit_operations : 'a semiring_bits;
    anda : 'a -> 'a -> 'a; ora : 'a -> 'a -> 'a; xor : 'a -> 'a -> 'a;
    mask : nat -> 'a; set_bit : nat -> 'a -> 'a; unset_bit : nat -> 'a -> 'a;
    flip_bit : nat -> 'a -> 'a; push_bit : nat -> 'a -> 'a;
    drop_bit : nat -> 'a -> 'a; take_bit : nat -> 'a -> 'a};;
let anda _A = _A.anda;;
let ora _A = _A.ora;;
let xor _A = _A.xor;;
let mask _A = _A.mask;;
let set_bit _A = _A.set_bit;;
let unset_bit _A = _A.unset_bit;;
let flip_bit _A = _A.flip_bit;;
let push_bit _A = _A.push_bit;;
let drop_bit _A = _A.drop_bit;;
let take_bit _A = _A.take_bit;;

let rec not_int (Int_of_integer k) = Int_of_integer (Z.lognot k);;

type 'a ring_bit_operations =
  {semiring_bit_operations_ring_bit_operations : 'a semiring_bit_operations;
    ring_parity_ring_bit_operations : 'a ring_parity; nota : 'a -> 'a};;
let nota _A = _A.nota;;

let semiring_bit_operations_int =
  ({semiring_bits_semiring_bit_operations = semiring_bits_int; anda = and_int;
     ora = or_int; xor = xor_int; mask = mask_int; set_bit = set_bit_int;
     unset_bit = unset_bit_int; flip_bit = flip_bit_int;
     push_bit = push_bit_int; drop_bit = drop_bit_int; take_bit = take_bit_int}
    : int semiring_bit_operations);;

let ring_bit_operations_int =
  ({semiring_bit_operations_ring_bit_operations = semiring_bit_operations_int;
     ring_parity_ring_bit_operations = ring_parity_int; nota = not_int}
    : int ring_bit_operations);;

type 'a normalization_euclidean_semiring =
  {euclidean_semiring_normalization_euclidean_semiring : 'a euclidean_semiring;
    factorial_semiring_normalization_euclidean_semiring :
      'a factorial_semiring};;

type 'a euclidean_semiring_gcd =
  {normalization_euclidean_semiring_euclidean_semiring_gcd :
     'a normalization_euclidean_semiring;
    factorial_semiring_gcd_euclidean_semiring_gcd : 'a factorial_semiring_gcd};;

type 'a euclidean_ring_gcd =
  {euclidean_semiring_gcd_euclidean_ring_gcd : 'a euclidean_semiring_gcd;
    euclidean_ring_euclidean_ring_gcd : 'a euclidean_ring;
    factorial_ring_gcd_euclidean_ring_gcd : 'a factorial_ring_gcd};;

let normalization_euclidean_semiring_int =
  ({euclidean_semiring_normalization_euclidean_semiring =
      euclidean_semiring_int;
     factorial_semiring_normalization_euclidean_semiring =
       factorial_semiring_int}
    : int normalization_euclidean_semiring);;

let euclidean_semiring_gcd_int =
  ({normalization_euclidean_semiring_euclidean_semiring_gcd =
      normalization_euclidean_semiring_int;
     factorial_semiring_gcd_euclidean_semiring_gcd = factorial_semiring_gcd_int}
    : int euclidean_semiring_gcd);;

let euclidean_ring_gcd_int =
  ({euclidean_semiring_gcd_euclidean_ring_gcd = euclidean_semiring_gcd_int;
     euclidean_ring_euclidean_ring_gcd = euclidean_ring_int;
     factorial_ring_gcd_euclidean_ring_gcd = factorial_ring_gcd_int}
    : int euclidean_ring_gcd);;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec equal_boola p pa = match p, pa with false, p -> not p
                      | true, p -> p
                      | p, false -> not p
                      | p, true -> p;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec equal_suma _A _B x0 x1 = match x0, x1 with Inl x1, Inr x2 -> false
                           | Inr x2, Inl x1 -> false
                           | Inr x2, Inr y2 -> eq _B x2 y2
                           | Inl x1, Inl y1 -> eq _A x1 y1;;

let rec equal_sum _A _B = ({equal = equal_suma _A _B} : ('a, 'b) sum equal);;

type var_id = GlobalId of string | ScopedId of string * string |
  ReturnId of string | ReturnVar;;

let rec equal_var_ida
  x0 x1 = match x0, x1 with ReturnId x3, ReturnVar -> false
    | ReturnVar, ReturnId x3 -> false
    | ScopedId (x21, x22), ReturnVar -> false
    | ReturnVar, ScopedId (x21, x22) -> false
    | ScopedId (x21, x22), ReturnId x3 -> false
    | ReturnId x3, ScopedId (x21, x22) -> false
    | GlobalId x1, ReturnVar -> false
    | ReturnVar, GlobalId x1 -> false
    | GlobalId x1, ReturnId x3 -> false
    | ReturnId x3, GlobalId x1 -> false
    | GlobalId x1, ScopedId (x21, x22) -> false
    | ScopedId (x21, x22), GlobalId x1 -> false
    | ReturnId x3, ReturnId y3 -> ((x3 : string) = y3)
    | ScopedId (x21, x22), ScopedId (y21, y22) ->
        ((x21 : string) = y21) && ((x22 : string) = y22)
    | GlobalId x1, GlobalId y1 -> ((x1 : string) = y1)
    | ReturnVar, ReturnVar -> true;;

let equal_var_id = ({equal = equal_var_ida} : var_id equal);;

type ordera = Eqa | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let rec comparator_var_id
  x0 x1 = match x0, x1 with
    GlobalId x, GlobalId y ->
      comparator_of (equal_literal, linorder_literal) x y
    | GlobalId x, ScopedId (ya, yb) -> Lt
    | GlobalId x, ReturnId yc -> Lt
    | GlobalId x, ReturnVar -> Lt
    | ScopedId (x, xa), GlobalId y -> Gt
    | ScopedId (x, xa), ScopedId (ya, yb) ->
        (match comparator_of (equal_literal, linorder_literal) x ya
          with Eqa -> comparator_of (equal_literal, linorder_literal) xa yb
          | Lt -> Lt | Gt -> Gt)
    | ScopedId (x, xa), ReturnId yc -> Lt
    | ScopedId (x, xa), ReturnVar -> Lt
    | ReturnId x, GlobalId y -> Gt
    | ReturnId x, ScopedId (ya, yb) -> Gt
    | ReturnId x, ReturnId yc ->
        comparator_of (equal_literal, linorder_literal) x yc
    | ReturnId x, ReturnVar -> Lt
    | ReturnVar, GlobalId y -> Gt
    | ReturnVar, ScopedId (ya, yb) -> Gt
    | ReturnVar, ReturnId yc -> Gt
    | ReturnVar, ReturnVar -> Eqa;;

let rec le_of_comp
  acomp x y = (match acomp x y with Eqa -> true | Lt -> true | Gt -> false);;

let rec less_eq_var_id x = le_of_comp comparator_var_id x;;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eqa -> false | Lt -> true | Gt -> false);;

let rec less_var_id x = lt_of_comp comparator_var_id x;;

let ord_var_id = ({less_eq = less_eq_var_id; less = less_var_id} : var_id ord);;

let preorder_var_id = ({ord_preorder = ord_var_id} : var_id preorder);;

let order_var_id = ({preorder_order = preorder_var_id} : var_id order);;

let linorder_var_id = ({order_linorder = order_var_id} : var_id linorder);;

type 'a infinite_key = unit;;

let infinite_key_var_id = (() : var_id infinite_key);;

type ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64;;

let rec equal_ikind x0 x1 = match x0, x1 with I64, U64 -> false
                      | U64, I64 -> false
                      | U32, U64 -> false
                      | U64, U32 -> false
                      | U32, I64 -> false
                      | I64, U32 -> false
                      | I32, U64 -> false
                      | U64, I32 -> false
                      | I32, I64 -> false
                      | I64, I32 -> false
                      | I32, U32 -> false
                      | U32, I32 -> false
                      | U16, U64 -> false
                      | U64, U16 -> false
                      | U16, I64 -> false
                      | I64, U16 -> false
                      | U16, U32 -> false
                      | U32, U16 -> false
                      | U16, I32 -> false
                      | I32, U16 -> false
                      | I16, U64 -> false
                      | U64, I16 -> false
                      | I16, I64 -> false
                      | I64, I16 -> false
                      | I16, U32 -> false
                      | U32, I16 -> false
                      | I16, I32 -> false
                      | I32, I16 -> false
                      | I16, U16 -> false
                      | U16, I16 -> false
                      | U8, U64 -> false
                      | U64, U8 -> false
                      | U8, I64 -> false
                      | I64, U8 -> false
                      | U8, U32 -> false
                      | U32, U8 -> false
                      | U8, I32 -> false
                      | I32, U8 -> false
                      | U8, U16 -> false
                      | U16, U8 -> false
                      | U8, I16 -> false
                      | I16, U8 -> false
                      | I8, U64 -> false
                      | U64, I8 -> false
                      | I8, I64 -> false
                      | I64, I8 -> false
                      | I8, U32 -> false
                      | U32, I8 -> false
                      | I8, I32 -> false
                      | I32, I8 -> false
                      | I8, U16 -> false
                      | U16, I8 -> false
                      | I8, I16 -> false
                      | I16, I8 -> false
                      | I8, U8 -> false
                      | U8, I8 -> false
                      | U64, U64 -> true
                      | I64, I64 -> true
                      | U32, U32 -> true
                      | I32, I32 -> true
                      | U16, U16 -> true
                      | I16, I16 -> true
                      | U8, U8 -> true
                      | I8, I8 -> true;;

type 'a kd = KBot | KD of ikind * 'a | KTop;;

let rec equal_kda _A
  x0 x1 = match x0, x1 with KD (x21, x22), KTop -> false
    | KTop, KD (x21, x22) -> false
    | KBot, KTop -> false
    | KTop, KBot -> false
    | KBot, KD (x21, x22) -> false
    | KD (x21, x22), KBot -> false
    | KD (x21, x22), KD (y21, y22) -> equal_ikind x21 y21 && eq _A x22 y22
    | KTop, KTop -> true
    | KBot, KBot -> true;;

let rec equal_kd _A = ({equal = equal_kda _A} : 'a kd equal);;

type 'a bot = {bot : 'a};;
let bot _A = _A.bot;;

type 'a order_bot = {bot_order_bot : 'a bot; order_order_bot : 'a order};;

type 'a bounded_semilattice_sup_bot =
  {semilattice_sup_bounded_semilattice_sup_bot : 'a semilattice_sup;
    order_bot_bounded_semilattice_sup_bot : 'a order_bot};;

type 'a narrowing = {order_narrowing : 'a order; narrow : 'a -> 'a -> 'a};;
let narrow _A = _A.narrow;;

type 'a widening = {order_widening : 'a order; widen : 'a -> 'a -> 'a};;
let widen _A = _A.widen;;

type 'a warrowing =
  {narrowing_warrowing : 'a narrowing; widening_warrowing : 'a widening};;

type 'a top = {top : 'a};;
let top _A = _A.top;;

type 'a order_top = {order_order_top : 'a order; top_order_top : 'a top};;

type 'a executable_domain =
  {bounded_semilattice_sup_bot_executable_domain :
     'a bounded_semilattice_sup_bot;
    order_top_executable_domain : 'a order_top;
    warrowing_executable_domain : 'a warrowing; is_empty : 'a -> bool;
    to_string : 'a -> string};;
let is_empty _A = _A.is_empty;;
let to_string _A = _A.to_string;;

type 'a numeric_domain =
  {executable_domain_numeric_domain : 'a executable_domain;
    gamma : 'a -> int set};;
let gamma _A = _A.gamma;;

type 'a ik_domain =
  {numeric_domain_ik_domain : 'a numeric_domain;
    widen_ik : ikind -> 'a -> 'a -> 'a; narrow_ik : ikind -> 'a -> 'a -> 'a;
    empty_ik : ikind -> 'a -> bool};;
let widen_ik _A = _A.widen_ik;;
let narrow_ik _A = _A.narrow_ik;;
let empty_ik _A = _A.empty_ik;;

let rec sup_kda _A
  x0 b = match x0, b with KBot, b -> b
    | KD (v, va), KBot -> KD (v, va)
    | KTop, KBot -> KTop
    | KD (k, a), KD (l, b) ->
        (if equal_ikind k l
          then KD (k, sup _A.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                        a b)
          else KTop)
    | KD (v, va), KTop -> KTop
    | KTop, KD (v, va) -> KTop
    | KTop, KTop -> KTop;;

let rec sup_kd _A = ({sup = sup_kda _A} : 'a kd sup);;

let rec bot_kda _A = KBot;;

let rec bot_kd _A = ({bot = bot_kda _A} : 'a kd bot);;

let rec less_eq_kd _A
  x0 uu = match x0, uu with KBot, uu -> true
    | KD (v, va), KTop -> true
    | KTop, KTop -> true
    | KD (k, a), KD (l, b) ->
        equal_ikind k l &&
          less_eq
            _A.numeric_domain_ik_domain.executable_domain_numeric_domain.warrowing_executable_domain.widening_warrowing.order_widening.preorder_order.ord_preorder
            a b
    | KD (v, va), KBot -> false
    | KTop, KBot -> false
    | KTop, KD (v, va) -> false;;

let rec less_kd _A a b = less_eq_kd _A a b && not (less_eq_kd _A b a);;

let rec ord_kd _A = ({less_eq = less_eq_kd _A; less = less_kd _A} : 'a kd ord);;

let rec preorder_kd _A = ({ord_preorder = (ord_kd _A)} : 'a kd preorder);;

let rec order_kd _A = ({preorder_order = (preorder_kd _A)} : 'a kd order);;

let rec widen_kd _A
  x0 b = match x0, b with KBot, b -> b
    | KD (v, va), KBot -> KD (v, va)
    | KTop, KBot -> KTop
    | KD (k, a), KD (l, b) ->
        (if equal_ikind k l then KD (k, widen_ik _A k a b) else KTop)
    | KD (v, va), KTop -> KTop
    | KTop, KD (v, va) -> KTop
    | KTop, KTop -> KTop;;

let rec widening_kd _A =
  ({order_widening = (order_kd _A); widen = widen_kd _A} : 'a kd widening);;

let rec order_bot_kd _A =
  ({bot_order_bot = (bot_kd _A); order_order_bot = (order_kd _A)} :
    'a kd order_bot);;

let rec narrow_kd _A
  x0 b = match x0, b with KTop, b -> b
    | KD (k, a), KD (l, b) ->
        (if equal_ikind k l then KD (k, narrow_ik _A k a b) else KD (k, a))
    | KBot, uu -> KBot
    | KD (v, va), KBot -> KBot
    | KD (v, va), KTop -> KBot;;

let rec narrowing_kd _A =
  ({order_narrowing = (order_kd _A); narrow = narrow_kd _A} : 'a kd narrowing);;

let rec warrowing_kd _A =
  ({narrowing_warrowing = (narrowing_kd _A);
     widening_warrowing = (widening_kd _A)}
    : 'a kd warrowing);;

let rec semilattice_sup_kd _A =
  ({sup_semilattice_sup = (sup_kd _A); order_semilattice_sup = (order_kd _A)} :
    'a kd semilattice_sup);;

let rec bounded_semilattice_sup_bot_kd _A =
  ({semilattice_sup_bounded_semilattice_sup_bot = (semilattice_sup_kd _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_kd _A)}
    : 'a kd bounded_semilattice_sup_bot);;

let rec global_name_literala x = x;;

type 'a global_name =
  {infinite_key_global_name : 'a infinite_key; global_name : string -> 'a};;
let global_name _A = _A.global_name;;

let infinite_key_literal = (() : string infinite_key);;

let global_name_literal =
  ({infinite_key_global_name = infinite_key_literal;
     global_name = global_name_literala}
    : string global_name);;

type cop = CLt | CLe | CGt | CGe | CEq | CNe;;

let rec equal_cop x0 x1 = match x0, x1 with CEq, CNe -> false
                    | CNe, CEq -> false
                    | CGe, CNe -> false
                    | CNe, CGe -> false
                    | CGe, CEq -> false
                    | CEq, CGe -> false
                    | CGt, CNe -> false
                    | CNe, CGt -> false
                    | CGt, CEq -> false
                    | CEq, CGt -> false
                    | CGt, CGe -> false
                    | CGe, CGt -> false
                    | CLe, CNe -> false
                    | CNe, CLe -> false
                    | CLe, CEq -> false
                    | CEq, CLe -> false
                    | CLe, CGe -> false
                    | CGe, CLe -> false
                    | CLe, CGt -> false
                    | CGt, CLe -> false
                    | CLt, CNe -> false
                    | CNe, CLt -> false
                    | CLt, CEq -> false
                    | CEq, CLt -> false
                    | CLt, CGe -> false
                    | CGe, CLt -> false
                    | CLt, CGt -> false
                    | CGt, CLt -> false
                    | CLt, CLe -> false
                    | CLe, CLt -> false
                    | CNe, CNe -> true
                    | CEq, CEq -> true
                    | CGe, CGe -> true
                    | CGt, CGt -> true
                    | CLe, CLe -> true
                    | CLt, CLt -> true;;

type aop = AAdd | ASub | AMul | ADiv | AMod;;

let rec equal_aop x0 x1 = match x0, x1 with ADiv, AMod -> false
                    | AMod, ADiv -> false
                    | AMul, AMod -> false
                    | AMod, AMul -> false
                    | AMul, ADiv -> false
                    | ADiv, AMul -> false
                    | ASub, AMod -> false
                    | AMod, ASub -> false
                    | ASub, ADiv -> false
                    | ADiv, ASub -> false
                    | ASub, AMul -> false
                    | AMul, ASub -> false
                    | AAdd, AMod -> false
                    | AMod, AAdd -> false
                    | AAdd, ADiv -> false
                    | ADiv, AAdd -> false
                    | AAdd, AMul -> false
                    | AMul, AAdd -> false
                    | AAdd, ASub -> false
                    | ASub, AAdd -> false
                    | AMod, AMod -> true
                    | ADiv, ADiv -> true
                    | AMul, AMul -> true
                    | ASub, ASub -> true
                    | AAdd, AAdd -> true;;

type texp = TN of ikind * int | TVar of ikind * var_id |
  TArith of ikind * aop * texp * texp | TCast of ikind * texp |
  TCmp of cop * texp * texp | TNot of texp | TAnd of texp * texp |
  TOr of texp * texp;;

let rec equal_texpa
  x0 x1 = match x0, x1 with TAnd (x71, x72), TOr (x81, x82) -> false
    | TOr (x81, x82), TAnd (x71, x72) -> false
    | TNot x6, TOr (x81, x82) -> false
    | TOr (x81, x82), TNot x6 -> false
    | TNot x6, TAnd (x71, x72) -> false
    | TAnd (x71, x72), TNot x6 -> false
    | TCmp (x51, x52, x53), TOr (x81, x82) -> false
    | TOr (x81, x82), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TAnd (x71, x72) -> false
    | TAnd (x71, x72), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TNot x6 -> false
    | TNot x6, TCmp (x51, x52, x53) -> false
    | TCast (x41, x42), TOr (x81, x82) -> false
    | TOr (x81, x82), TCast (x41, x42) -> false
    | TCast (x41, x42), TAnd (x71, x72) -> false
    | TAnd (x71, x72), TCast (x41, x42) -> false
    | TCast (x41, x42), TNot x6 -> false
    | TNot x6, TCast (x41, x42) -> false
    | TCast (x41, x42), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TCast (x41, x42) -> false
    | TArith (x31, x32, x33, x34), TOr (x81, x82) -> false
    | TOr (x81, x82), TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TAnd (x71, x72) -> false
    | TAnd (x71, x72), TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TNot x6 -> false
    | TNot x6, TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TCast (x41, x42) -> false
    | TCast (x41, x42), TArith (x31, x32, x33, x34) -> false
    | TVar (x21, x22), TOr (x81, x82) -> false
    | TOr (x81, x82), TVar (x21, x22) -> false
    | TVar (x21, x22), TAnd (x71, x72) -> false
    | TAnd (x71, x72), TVar (x21, x22) -> false
    | TVar (x21, x22), TNot x6 -> false
    | TNot x6, TVar (x21, x22) -> false
    | TVar (x21, x22), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TVar (x21, x22) -> false
    | TVar (x21, x22), TCast (x41, x42) -> false
    | TCast (x41, x42), TVar (x21, x22) -> false
    | TVar (x21, x22), TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TVar (x21, x22) -> false
    | TN (x11, x12), TOr (x81, x82) -> false
    | TOr (x81, x82), TN (x11, x12) -> false
    | TN (x11, x12), TAnd (x71, x72) -> false
    | TAnd (x71, x72), TN (x11, x12) -> false
    | TN (x11, x12), TNot x6 -> false
    | TNot x6, TN (x11, x12) -> false
    | TN (x11, x12), TCmp (x51, x52, x53) -> false
    | TCmp (x51, x52, x53), TN (x11, x12) -> false
    | TN (x11, x12), TCast (x41, x42) -> false
    | TCast (x41, x42), TN (x11, x12) -> false
    | TN (x11, x12), TArith (x31, x32, x33, x34) -> false
    | TArith (x31, x32, x33, x34), TN (x11, x12) -> false
    | TN (x11, x12), TVar (x21, x22) -> false
    | TVar (x21, x22), TN (x11, x12) -> false
    | TOr (x81, x82), TOr (y81, y82) ->
        equal_texpa x81 y81 && equal_texpa x82 y82
    | TAnd (x71, x72), TAnd (y71, y72) ->
        equal_texpa x71 y71 && equal_texpa x72 y72
    | TNot x6, TNot y6 -> equal_texpa x6 y6
    | TCmp (x51, x52, x53), TCmp (y51, y52, y53) ->
        equal_cop x51 y51 && (equal_texpa x52 y52 && equal_texpa x53 y53)
    | TCast (x41, x42), TCast (y41, y42) ->
        equal_ikind x41 y41 && equal_texpa x42 y42
    | TArith (x31, x32, x33, x34), TArith (y31, y32, y33, y34) ->
        equal_ikind x31 y31 &&
          (equal_aop x32 y32 && (equal_texpa x33 y33 && equal_texpa x34 y34))
    | TVar (x21, x22), TVar (y21, y22) ->
        equal_ikind x21 y21 && equal_var_ida x22 y22
    | TN (x11, x12), TN (y11, y12) ->
        equal_ikind x11 y11 && equal_inta x12 y12;;

let equal_texp = ({equal = equal_texpa} : texp equal);;

let rec comparator_ikind x0 x1 = match x0, x1 with I8, I8 -> Eqa
                           | I8, U8 -> Lt
                           | I8, I16 -> Lt
                           | I8, U16 -> Lt
                           | I8, I32 -> Lt
                           | I8, U32 -> Lt
                           | I8, I64 -> Lt
                           | I8, U64 -> Lt
                           | U8, I8 -> Gt
                           | U8, U8 -> Eqa
                           | U8, I16 -> Lt
                           | U8, U16 -> Lt
                           | U8, I32 -> Lt
                           | U8, U32 -> Lt
                           | U8, I64 -> Lt
                           | U8, U64 -> Lt
                           | I16, I8 -> Gt
                           | I16, U8 -> Gt
                           | I16, I16 -> Eqa
                           | I16, U16 -> Lt
                           | I16, I32 -> Lt
                           | I16, U32 -> Lt
                           | I16, I64 -> Lt
                           | I16, U64 -> Lt
                           | U16, I8 -> Gt
                           | U16, U8 -> Gt
                           | U16, I16 -> Gt
                           | U16, U16 -> Eqa
                           | U16, I32 -> Lt
                           | U16, U32 -> Lt
                           | U16, I64 -> Lt
                           | U16, U64 -> Lt
                           | I32, I8 -> Gt
                           | I32, U8 -> Gt
                           | I32, I16 -> Gt
                           | I32, U16 -> Gt
                           | I32, I32 -> Eqa
                           | I32, U32 -> Lt
                           | I32, I64 -> Lt
                           | I32, U64 -> Lt
                           | U32, I8 -> Gt
                           | U32, U8 -> Gt
                           | U32, I16 -> Gt
                           | U32, U16 -> Gt
                           | U32, I32 -> Gt
                           | U32, U32 -> Eqa
                           | U32, I64 -> Lt
                           | U32, U64 -> Lt
                           | I64, I8 -> Gt
                           | I64, U8 -> Gt
                           | I64, I16 -> Gt
                           | I64, U16 -> Gt
                           | I64, I32 -> Gt
                           | I64, U32 -> Gt
                           | I64, I64 -> Eqa
                           | I64, U64 -> Lt
                           | U64, I8 -> Gt
                           | U64, U8 -> Gt
                           | U64, I16 -> Gt
                           | U64, U16 -> Gt
                           | U64, I32 -> Gt
                           | U64, U32 -> Gt
                           | U64, I64 -> Gt
                           | U64, U64 -> Eqa;;

let rec comparator_cop x0 x1 = match x0, x1 with CLt, CLt -> Eqa
                         | CLt, CLe -> Lt
                         | CLt, CGt -> Lt
                         | CLt, CGe -> Lt
                         | CLt, CEq -> Lt
                         | CLt, CNe -> Lt
                         | CLe, CLt -> Gt
                         | CLe, CLe -> Eqa
                         | CLe, CGt -> Lt
                         | CLe, CGe -> Lt
                         | CLe, CEq -> Lt
                         | CLe, CNe -> Lt
                         | CGt, CLt -> Gt
                         | CGt, CLe -> Gt
                         | CGt, CGt -> Eqa
                         | CGt, CGe -> Lt
                         | CGt, CEq -> Lt
                         | CGt, CNe -> Lt
                         | CGe, CLt -> Gt
                         | CGe, CLe -> Gt
                         | CGe, CGt -> Gt
                         | CGe, CGe -> Eqa
                         | CGe, CEq -> Lt
                         | CGe, CNe -> Lt
                         | CEq, CLt -> Gt
                         | CEq, CLe -> Gt
                         | CEq, CGt -> Gt
                         | CEq, CGe -> Gt
                         | CEq, CEq -> Eqa
                         | CEq, CNe -> Lt
                         | CNe, CLt -> Gt
                         | CNe, CLe -> Gt
                         | CNe, CGt -> Gt
                         | CNe, CGe -> Gt
                         | CNe, CEq -> Gt
                         | CNe, CNe -> Eqa;;

let rec comparator_aop x0 x1 = match x0, x1 with AAdd, AAdd -> Eqa
                         | AAdd, ASub -> Lt
                         | AAdd, AMul -> Lt
                         | AAdd, ADiv -> Lt
                         | AAdd, AMod -> Lt
                         | ASub, AAdd -> Gt
                         | ASub, ASub -> Eqa
                         | ASub, AMul -> Lt
                         | ASub, ADiv -> Lt
                         | ASub, AMod -> Lt
                         | AMul, AAdd -> Gt
                         | AMul, ASub -> Gt
                         | AMul, AMul -> Eqa
                         | AMul, ADiv -> Lt
                         | AMul, AMod -> Lt
                         | ADiv, AAdd -> Gt
                         | ADiv, ASub -> Gt
                         | ADiv, AMul -> Gt
                         | ADiv, ADiv -> Eqa
                         | ADiv, AMod -> Lt
                         | AMod, AAdd -> Gt
                         | AMod, ASub -> Gt
                         | AMod, AMul -> Gt
                         | AMod, ADiv -> Gt
                         | AMod, AMod -> Eqa;;

let rec comparator_texp
  x0 x1 = match x0, x1 with
    TN (x, xa), TN (y, ya) ->
      (match comparator_ikind x y
        with Eqa -> comparator_of (equal_int, linorder_int) xa ya | Lt -> Lt
        | Gt -> Gt)
    | TN (x, xa), TVar (yb, yc) -> Lt
    | TN (x, xa), TArith (yd, ye, yf, yg) -> Lt
    | TN (x, xa), TCast (yh, yi) -> Lt
    | TN (x, xa), TCmp (yj, yk, yl) -> Lt
    | TN (x, xa), TNot ym -> Lt
    | TN (x, xa), TAnd (yn, yo) -> Lt
    | TN (x, xa), TOr (yp, yq) -> Lt
    | TVar (x, xa), TN (y, ya) -> Gt
    | TVar (x, xa), TVar (yb, yc) ->
        (match comparator_ikind x yb with Eqa -> comparator_var_id xa yc
          | Lt -> Lt | Gt -> Gt)
    | TVar (x, xa), TArith (yd, ye, yf, yg) -> Lt
    | TVar (x, xa), TCast (yh, yi) -> Lt
    | TVar (x, xa), TCmp (yj, yk, yl) -> Lt
    | TVar (x, xa), TNot ym -> Lt
    | TVar (x, xa), TAnd (yn, yo) -> Lt
    | TVar (x, xa), TOr (yp, yq) -> Lt
    | TArith (x, xa, xb, xc), TN (y, ya) -> Gt
    | TArith (x, xa, xb, xc), TVar (yb, yc) -> Gt
    | TArith (x, xa, xb, xc), TArith (yd, ye, yf, yg) ->
        (match comparator_ikind x yd
          with Eqa ->
            (match comparator_aop xa ye
              with Eqa ->
                (match comparator_texp xb yf with Eqa -> comparator_texp xc yg
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | TArith (x, xa, xb, xc), TCast (yh, yi) -> Lt
    | TArith (x, xa, xb, xc), TCmp (yj, yk, yl) -> Lt
    | TArith (x, xa, xb, xc), TNot ym -> Lt
    | TArith (x, xa, xb, xc), TAnd (yn, yo) -> Lt
    | TArith (x, xa, xb, xc), TOr (yp, yq) -> Lt
    | TCast (x, xa), TN (y, ya) -> Gt
    | TCast (x, xa), TVar (yb, yc) -> Gt
    | TCast (x, xa), TArith (yd, ye, yf, yg) -> Gt
    | TCast (x, xa), TCast (yh, yi) ->
        (match comparator_ikind x yh with Eqa -> comparator_texp xa yi
          | Lt -> Lt | Gt -> Gt)
    | TCast (x, xa), TCmp (yj, yk, yl) -> Lt
    | TCast (x, xa), TNot ym -> Lt
    | TCast (x, xa), TAnd (yn, yo) -> Lt
    | TCast (x, xa), TOr (yp, yq) -> Lt
    | TCmp (x, xa, xb), TN (y, ya) -> Gt
    | TCmp (x, xa, xb), TVar (yb, yc) -> Gt
    | TCmp (x, xa, xb), TArith (yd, ye, yf, yg) -> Gt
    | TCmp (x, xa, xb), TCast (yh, yi) -> Gt
    | TCmp (x, xa, xb), TCmp (yj, yk, yl) ->
        (match comparator_cop x yj
          with Eqa ->
            (match comparator_texp xa yk with Eqa -> comparator_texp xb yl
              | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | TCmp (x, xa, xb), TNot ym -> Lt
    | TCmp (x, xa, xb), TAnd (yn, yo) -> Lt
    | TCmp (x, xa, xb), TOr (yp, yq) -> Lt
    | TNot x, TN (y, ya) -> Gt
    | TNot x, TVar (yb, yc) -> Gt
    | TNot x, TArith (yd, ye, yf, yg) -> Gt
    | TNot x, TCast (yh, yi) -> Gt
    | TNot x, TCmp (yj, yk, yl) -> Gt
    | TNot x, TNot ym -> comparator_texp x ym
    | TNot x, TAnd (yn, yo) -> Lt
    | TNot x, TOr (yp, yq) -> Lt
    | TAnd (x, xa), TN (y, ya) -> Gt
    | TAnd (x, xa), TVar (yb, yc) -> Gt
    | TAnd (x, xa), TArith (yd, ye, yf, yg) -> Gt
    | TAnd (x, xa), TCast (yh, yi) -> Gt
    | TAnd (x, xa), TCmp (yj, yk, yl) -> Gt
    | TAnd (x, xa), TNot ym -> Gt
    | TAnd (x, xa), TAnd (yn, yo) ->
        (match comparator_texp x yn with Eqa -> comparator_texp xa yo | Lt -> Lt
          | Gt -> Gt)
    | TAnd (x, xa), TOr (yp, yq) -> Lt
    | TOr (x, xa), TN (y, ya) -> Gt
    | TOr (x, xa), TVar (yb, yc) -> Gt
    | TOr (x, xa), TArith (yd, ye, yf, yg) -> Gt
    | TOr (x, xa), TCast (yh, yi) -> Gt
    | TOr (x, xa), TCmp (yj, yk, yl) -> Gt
    | TOr (x, xa), TNot ym -> Gt
    | TOr (x, xa), TAnd (yn, yo) -> Gt
    | TOr (x, xa), TOr (yp, yq) ->
        (match comparator_texp x yp with Eqa -> comparator_texp xa yq | Lt -> Lt
          | Gt -> Gt);;

let rec less_eq_texp x = le_of_comp comparator_texp x;;

let rec less_texp x = lt_of_comp comparator_texp x;;

let ord_texp = ({less_eq = less_eq_texp; less = less_texp} : texp ord);;

let preorder_texp = ({ord_preorder = ord_texp} : texp preorder);;

let order_texp = ({preorder_order = preorder_texp} : texp order);;

let linorder_texp = ({order_linorder = order_texp} : texp linorder);;

type exp = N of int | V of string | Plus of exp * exp | Minus of exp * exp |
  Times of exp * exp | Div of exp * exp | Mod of exp * exp | Less of exp * exp |
  LessEq of exp * exp | Greater of exp * exp | GreaterEq of exp * exp |
  NotEq of exp * exp | Eq of exp * exp | Not of exp | And of exp * exp |
  Or of exp * exp | Cast of ikind * exp;;

let rec equal_expa
  x0 x1 = match x0, x1 with Or (x161, x162), Cast (x171, x172) -> false
    | Cast (x171, x172), Or (x161, x162) -> false
    | And (x151, x152), Cast (x171, x172) -> false
    | Cast (x171, x172), And (x151, x152) -> false
    | And (x151, x152), Or (x161, x162) -> false
    | Or (x161, x162), And (x151, x152) -> false
    | Not x14, Cast (x171, x172) -> false
    | Cast (x171, x172), Not x14 -> false
    | Not x14, Or (x161, x162) -> false
    | Or (x161, x162), Not x14 -> false
    | Not x14, And (x151, x152) -> false
    | And (x151, x152), Not x14 -> false
    | Eq (x131, x132), Cast (x171, x172) -> false
    | Cast (x171, x172), Eq (x131, x132) -> false
    | Eq (x131, x132), Or (x161, x162) -> false
    | Or (x161, x162), Eq (x131, x132) -> false
    | Eq (x131, x132), And (x151, x152) -> false
    | And (x151, x152), Eq (x131, x132) -> false
    | Eq (x131, x132), Not x14 -> false
    | Not x14, Eq (x131, x132) -> false
    | NotEq (x121, x122), Cast (x171, x172) -> false
    | Cast (x171, x172), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Or (x161, x162) -> false
    | Or (x161, x162), NotEq (x121, x122) -> false
    | NotEq (x121, x122), And (x151, x152) -> false
    | And (x151, x152), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Not x14 -> false
    | Not x14, NotEq (x121, x122) -> false
    | NotEq (x121, x122), Eq (x131, x132) -> false
    | Eq (x131, x132), NotEq (x121, x122) -> false
    | GreaterEq (x111, x112), Cast (x171, x172) -> false
    | Cast (x171, x172), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Or (x161, x162) -> false
    | Or (x161, x162), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), And (x151, x152) -> false
    | And (x151, x152), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Not x14 -> false
    | Not x14, GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Eq (x131, x132) -> false
    | Eq (x131, x132), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), NotEq (x121, x122) -> false
    | NotEq (x121, x122), GreaterEq (x111, x112) -> false
    | Greater (x101, x102), Cast (x171, x172) -> false
    | Cast (x171, x172), Greater (x101, x102) -> false
    | Greater (x101, x102), Or (x161, x162) -> false
    | Or (x161, x162), Greater (x101, x102) -> false
    | Greater (x101, x102), And (x151, x152) -> false
    | And (x151, x152), Greater (x101, x102) -> false
    | Greater (x101, x102), Not x14 -> false
    | Not x14, Greater (x101, x102) -> false
    | Greater (x101, x102), Eq (x131, x132) -> false
    | Eq (x131, x132), Greater (x101, x102) -> false
    | Greater (x101, x102), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Greater (x101, x102) -> false
    | Greater (x101, x102), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Greater (x101, x102) -> false
    | LessEq (x91, x92), Cast (x171, x172) -> false
    | Cast (x171, x172), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Or (x161, x162) -> false
    | Or (x161, x162), LessEq (x91, x92) -> false
    | LessEq (x91, x92), And (x151, x152) -> false
    | And (x151, x152), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Not x14 -> false
    | Not x14, LessEq (x91, x92) -> false
    | LessEq (x91, x92), Eq (x131, x132) -> false
    | Eq (x131, x132), LessEq (x91, x92) -> false
    | LessEq (x91, x92), NotEq (x121, x122) -> false
    | NotEq (x121, x122), LessEq (x91, x92) -> false
    | LessEq (x91, x92), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Greater (x101, x102) -> false
    | Greater (x101, x102), LessEq (x91, x92) -> false
    | Less (x81, x82), Cast (x171, x172) -> false
    | Cast (x171, x172), Less (x81, x82) -> false
    | Less (x81, x82), Or (x161, x162) -> false
    | Or (x161, x162), Less (x81, x82) -> false
    | Less (x81, x82), And (x151, x152) -> false
    | And (x151, x152), Less (x81, x82) -> false
    | Less (x81, x82), Not x14 -> false
    | Not x14, Less (x81, x82) -> false
    | Less (x81, x82), Eq (x131, x132) -> false
    | Eq (x131, x132), Less (x81, x82) -> false
    | Less (x81, x82), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Less (x81, x82) -> false
    | Less (x81, x82), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Less (x81, x82) -> false
    | Less (x81, x82), Greater (x101, x102) -> false
    | Greater (x101, x102), Less (x81, x82) -> false
    | Less (x81, x82), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Less (x81, x82) -> false
    | Mod (x71, x72), Cast (x171, x172) -> false
    | Cast (x171, x172), Mod (x71, x72) -> false
    | Mod (x71, x72), Or (x161, x162) -> false
    | Or (x161, x162), Mod (x71, x72) -> false
    | Mod (x71, x72), And (x151, x152) -> false
    | And (x151, x152), Mod (x71, x72) -> false
    | Mod (x71, x72), Not x14 -> false
    | Not x14, Mod (x71, x72) -> false
    | Mod (x71, x72), Eq (x131, x132) -> false
    | Eq (x131, x132), Mod (x71, x72) -> false
    | Mod (x71, x72), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Mod (x71, x72) -> false
    | Mod (x71, x72), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Mod (x71, x72) -> false
    | Mod (x71, x72), Greater (x101, x102) -> false
    | Greater (x101, x102), Mod (x71, x72) -> false
    | Mod (x71, x72), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Mod (x71, x72) -> false
    | Mod (x71, x72), Less (x81, x82) -> false
    | Less (x81, x82), Mod (x71, x72) -> false
    | Div (x61, x62), Cast (x171, x172) -> false
    | Cast (x171, x172), Div (x61, x62) -> false
    | Div (x61, x62), Or (x161, x162) -> false
    | Or (x161, x162), Div (x61, x62) -> false
    | Div (x61, x62), And (x151, x152) -> false
    | And (x151, x152), Div (x61, x62) -> false
    | Div (x61, x62), Not x14 -> false
    | Not x14, Div (x61, x62) -> false
    | Div (x61, x62), Eq (x131, x132) -> false
    | Eq (x131, x132), Div (x61, x62) -> false
    | Div (x61, x62), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Div (x61, x62) -> false
    | Div (x61, x62), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Div (x61, x62) -> false
    | Div (x61, x62), Greater (x101, x102) -> false
    | Greater (x101, x102), Div (x61, x62) -> false
    | Div (x61, x62), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Div (x61, x62) -> false
    | Div (x61, x62), Less (x81, x82) -> false
    | Less (x81, x82), Div (x61, x62) -> false
    | Div (x61, x62), Mod (x71, x72) -> false
    | Mod (x71, x72), Div (x61, x62) -> false
    | Times (x51, x52), Cast (x171, x172) -> false
    | Cast (x171, x172), Times (x51, x52) -> false
    | Times (x51, x52), Or (x161, x162) -> false
    | Or (x161, x162), Times (x51, x52) -> false
    | Times (x51, x52), And (x151, x152) -> false
    | And (x151, x152), Times (x51, x52) -> false
    | Times (x51, x52), Not x14 -> false
    | Not x14, Times (x51, x52) -> false
    | Times (x51, x52), Eq (x131, x132) -> false
    | Eq (x131, x132), Times (x51, x52) -> false
    | Times (x51, x52), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Times (x51, x52) -> false
    | Times (x51, x52), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Times (x51, x52) -> false
    | Times (x51, x52), Greater (x101, x102) -> false
    | Greater (x101, x102), Times (x51, x52) -> false
    | Times (x51, x52), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Times (x51, x52) -> false
    | Times (x51, x52), Less (x81, x82) -> false
    | Less (x81, x82), Times (x51, x52) -> false
    | Times (x51, x52), Mod (x71, x72) -> false
    | Mod (x71, x72), Times (x51, x52) -> false
    | Times (x51, x52), Div (x61, x62) -> false
    | Div (x61, x62), Times (x51, x52) -> false
    | Minus (x41, x42), Cast (x171, x172) -> false
    | Cast (x171, x172), Minus (x41, x42) -> false
    | Minus (x41, x42), Or (x161, x162) -> false
    | Or (x161, x162), Minus (x41, x42) -> false
    | Minus (x41, x42), And (x151, x152) -> false
    | And (x151, x152), Minus (x41, x42) -> false
    | Minus (x41, x42), Not x14 -> false
    | Not x14, Minus (x41, x42) -> false
    | Minus (x41, x42), Eq (x131, x132) -> false
    | Eq (x131, x132), Minus (x41, x42) -> false
    | Minus (x41, x42), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Minus (x41, x42) -> false
    | Minus (x41, x42), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Minus (x41, x42) -> false
    | Minus (x41, x42), Greater (x101, x102) -> false
    | Greater (x101, x102), Minus (x41, x42) -> false
    | Minus (x41, x42), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Minus (x41, x42) -> false
    | Minus (x41, x42), Less (x81, x82) -> false
    | Less (x81, x82), Minus (x41, x42) -> false
    | Minus (x41, x42), Mod (x71, x72) -> false
    | Mod (x71, x72), Minus (x41, x42) -> false
    | Minus (x41, x42), Div (x61, x62) -> false
    | Div (x61, x62), Minus (x41, x42) -> false
    | Minus (x41, x42), Times (x51, x52) -> false
    | Times (x51, x52), Minus (x41, x42) -> false
    | Plus (x31, x32), Cast (x171, x172) -> false
    | Cast (x171, x172), Plus (x31, x32) -> false
    | Plus (x31, x32), Or (x161, x162) -> false
    | Or (x161, x162), Plus (x31, x32) -> false
    | Plus (x31, x32), And (x151, x152) -> false
    | And (x151, x152), Plus (x31, x32) -> false
    | Plus (x31, x32), Not x14 -> false
    | Not x14, Plus (x31, x32) -> false
    | Plus (x31, x32), Eq (x131, x132) -> false
    | Eq (x131, x132), Plus (x31, x32) -> false
    | Plus (x31, x32), NotEq (x121, x122) -> false
    | NotEq (x121, x122), Plus (x31, x32) -> false
    | Plus (x31, x32), GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), Plus (x31, x32) -> false
    | Plus (x31, x32), Greater (x101, x102) -> false
    | Greater (x101, x102), Plus (x31, x32) -> false
    | Plus (x31, x32), LessEq (x91, x92) -> false
    | LessEq (x91, x92), Plus (x31, x32) -> false
    | Plus (x31, x32), Less (x81, x82) -> false
    | Less (x81, x82), Plus (x31, x32) -> false
    | Plus (x31, x32), Mod (x71, x72) -> false
    | Mod (x71, x72), Plus (x31, x32) -> false
    | Plus (x31, x32), Div (x61, x62) -> false
    | Div (x61, x62), Plus (x31, x32) -> false
    | Plus (x31, x32), Times (x51, x52) -> false
    | Times (x51, x52), Plus (x31, x32) -> false
    | Plus (x31, x32), Minus (x41, x42) -> false
    | Minus (x41, x42), Plus (x31, x32) -> false
    | V x2, Cast (x171, x172) -> false
    | Cast (x171, x172), V x2 -> false
    | V x2, Or (x161, x162) -> false
    | Or (x161, x162), V x2 -> false
    | V x2, And (x151, x152) -> false
    | And (x151, x152), V x2 -> false
    | V x2, Not x14 -> false
    | Not x14, V x2 -> false
    | V x2, Eq (x131, x132) -> false
    | Eq (x131, x132), V x2 -> false
    | V x2, NotEq (x121, x122) -> false
    | NotEq (x121, x122), V x2 -> false
    | V x2, GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), V x2 -> false
    | V x2, Greater (x101, x102) -> false
    | Greater (x101, x102), V x2 -> false
    | V x2, LessEq (x91, x92) -> false
    | LessEq (x91, x92), V x2 -> false
    | V x2, Less (x81, x82) -> false
    | Less (x81, x82), V x2 -> false
    | V x2, Mod (x71, x72) -> false
    | Mod (x71, x72), V x2 -> false
    | V x2, Div (x61, x62) -> false
    | Div (x61, x62), V x2 -> false
    | V x2, Times (x51, x52) -> false
    | Times (x51, x52), V x2 -> false
    | V x2, Minus (x41, x42) -> false
    | Minus (x41, x42), V x2 -> false
    | V x2, Plus (x31, x32) -> false
    | Plus (x31, x32), V x2 -> false
    | N x1, Cast (x171, x172) -> false
    | Cast (x171, x172), N x1 -> false
    | N x1, Or (x161, x162) -> false
    | Or (x161, x162), N x1 -> false
    | N x1, And (x151, x152) -> false
    | And (x151, x152), N x1 -> false
    | N x1, Not x14 -> false
    | Not x14, N x1 -> false
    | N x1, Eq (x131, x132) -> false
    | Eq (x131, x132), N x1 -> false
    | N x1, NotEq (x121, x122) -> false
    | NotEq (x121, x122), N x1 -> false
    | N x1, GreaterEq (x111, x112) -> false
    | GreaterEq (x111, x112), N x1 -> false
    | N x1, Greater (x101, x102) -> false
    | Greater (x101, x102), N x1 -> false
    | N x1, LessEq (x91, x92) -> false
    | LessEq (x91, x92), N x1 -> false
    | N x1, Less (x81, x82) -> false
    | Less (x81, x82), N x1 -> false
    | N x1, Mod (x71, x72) -> false
    | Mod (x71, x72), N x1 -> false
    | N x1, Div (x61, x62) -> false
    | Div (x61, x62), N x1 -> false
    | N x1, Times (x51, x52) -> false
    | Times (x51, x52), N x1 -> false
    | N x1, Minus (x41, x42) -> false
    | Minus (x41, x42), N x1 -> false
    | N x1, Plus (x31, x32) -> false
    | Plus (x31, x32), N x1 -> false
    | N x1, V x2 -> false
    | V x2, N x1 -> false
    | Cast (x171, x172), Cast (y171, y172) ->
        equal_ikind x171 y171 && equal_expa x172 y172
    | Or (x161, x162), Or (y161, y162) ->
        equal_expa x161 y161 && equal_expa x162 y162
    | And (x151, x152), And (y151, y152) ->
        equal_expa x151 y151 && equal_expa x152 y152
    | Not x14, Not y14 -> equal_expa x14 y14
    | Eq (x131, x132), Eq (y131, y132) ->
        equal_expa x131 y131 && equal_expa x132 y132
    | NotEq (x121, x122), NotEq (y121, y122) ->
        equal_expa x121 y121 && equal_expa x122 y122
    | GreaterEq (x111, x112), GreaterEq (y111, y112) ->
        equal_expa x111 y111 && equal_expa x112 y112
    | Greater (x101, x102), Greater (y101, y102) ->
        equal_expa x101 y101 && equal_expa x102 y102
    | LessEq (x91, x92), LessEq (y91, y92) ->
        equal_expa x91 y91 && equal_expa x92 y92
    | Less (x81, x82), Less (y81, y82) ->
        equal_expa x81 y81 && equal_expa x82 y82
    | Mod (x71, x72), Mod (y71, y72) -> equal_expa x71 y71 && equal_expa x72 y72
    | Div (x61, x62), Div (y61, y62) -> equal_expa x61 y61 && equal_expa x62 y62
    | Times (x51, x52), Times (y51, y52) ->
        equal_expa x51 y51 && equal_expa x52 y52
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_expa x41 y41 && equal_expa x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_expa x31 y31 && equal_expa x32 y32
    | V x2, V y2 -> ((x2 : string) = y2)
    | N x1, N y1 -> equal_inta x1 y1;;

let equal_exp = ({equal = equal_expa} : exp equal);;

let rec comparator_exp
  x0 x1 = match x0, x1 with
    N x, N y -> comparator_of (equal_int, linorder_int) x y
    | N x, V ya -> Lt
    | N x, Plus (yb, yc) -> Lt
    | N x, Minus (yd, ye) -> Lt
    | N x, Times (yf, yg) -> Lt
    | N x, Div (yh, yi) -> Lt
    | N x, Mod (yj, yk) -> Lt
    | N x, Less (yl, ym) -> Lt
    | N x, LessEq (yn, yo) -> Lt
    | N x, Greater (yp, yq) -> Lt
    | N x, GreaterEq (yr, ys) -> Lt
    | N x, NotEq (yt, yu) -> Lt
    | N x, Eq (yv, yw) -> Lt
    | N x, Not yx -> Lt
    | N x, And (yy, yz) -> Lt
    | N x, Or (za, zb) -> Lt
    | N x, Cast (zc, zd) -> Lt
    | V x, N y -> Gt
    | V x, V ya -> comparator_of (equal_literal, linorder_literal) x ya
    | V x, Plus (yb, yc) -> Lt
    | V x, Minus (yd, ye) -> Lt
    | V x, Times (yf, yg) -> Lt
    | V x, Div (yh, yi) -> Lt
    | V x, Mod (yj, yk) -> Lt
    | V x, Less (yl, ym) -> Lt
    | V x, LessEq (yn, yo) -> Lt
    | V x, Greater (yp, yq) -> Lt
    | V x, GreaterEq (yr, ys) -> Lt
    | V x, NotEq (yt, yu) -> Lt
    | V x, Eq (yv, yw) -> Lt
    | V x, Not yx -> Lt
    | V x, And (yy, yz) -> Lt
    | V x, Or (za, zb) -> Lt
    | V x, Cast (zc, zd) -> Lt
    | Plus (x, xa), N y -> Gt
    | Plus (x, xa), V ya -> Gt
    | Plus (x, xa), Plus (yb, yc) ->
        (match comparator_exp x yb with Eqa -> comparator_exp xa yc | Lt -> Lt
          | Gt -> Gt)
    | Plus (x, xa), Minus (yd, ye) -> Lt
    | Plus (x, xa), Times (yf, yg) -> Lt
    | Plus (x, xa), Div (yh, yi) -> Lt
    | Plus (x, xa), Mod (yj, yk) -> Lt
    | Plus (x, xa), Less (yl, ym) -> Lt
    | Plus (x, xa), LessEq (yn, yo) -> Lt
    | Plus (x, xa), Greater (yp, yq) -> Lt
    | Plus (x, xa), GreaterEq (yr, ys) -> Lt
    | Plus (x, xa), NotEq (yt, yu) -> Lt
    | Plus (x, xa), Eq (yv, yw) -> Lt
    | Plus (x, xa), Not yx -> Lt
    | Plus (x, xa), And (yy, yz) -> Lt
    | Plus (x, xa), Or (za, zb) -> Lt
    | Plus (x, xa), Cast (zc, zd) -> Lt
    | Minus (x, xa), N y -> Gt
    | Minus (x, xa), V ya -> Gt
    | Minus (x, xa), Plus (yb, yc) -> Gt
    | Minus (x, xa), Minus (yd, ye) ->
        (match comparator_exp x yd with Eqa -> comparator_exp xa ye | Lt -> Lt
          | Gt -> Gt)
    | Minus (x, xa), Times (yf, yg) -> Lt
    | Minus (x, xa), Div (yh, yi) -> Lt
    | Minus (x, xa), Mod (yj, yk) -> Lt
    | Minus (x, xa), Less (yl, ym) -> Lt
    | Minus (x, xa), LessEq (yn, yo) -> Lt
    | Minus (x, xa), Greater (yp, yq) -> Lt
    | Minus (x, xa), GreaterEq (yr, ys) -> Lt
    | Minus (x, xa), NotEq (yt, yu) -> Lt
    | Minus (x, xa), Eq (yv, yw) -> Lt
    | Minus (x, xa), Not yx -> Lt
    | Minus (x, xa), And (yy, yz) -> Lt
    | Minus (x, xa), Or (za, zb) -> Lt
    | Minus (x, xa), Cast (zc, zd) -> Lt
    | Times (x, xa), N y -> Gt
    | Times (x, xa), V ya -> Gt
    | Times (x, xa), Plus (yb, yc) -> Gt
    | Times (x, xa), Minus (yd, ye) -> Gt
    | Times (x, xa), Times (yf, yg) ->
        (match comparator_exp x yf with Eqa -> comparator_exp xa yg | Lt -> Lt
          | Gt -> Gt)
    | Times (x, xa), Div (yh, yi) -> Lt
    | Times (x, xa), Mod (yj, yk) -> Lt
    | Times (x, xa), Less (yl, ym) -> Lt
    | Times (x, xa), LessEq (yn, yo) -> Lt
    | Times (x, xa), Greater (yp, yq) -> Lt
    | Times (x, xa), GreaterEq (yr, ys) -> Lt
    | Times (x, xa), NotEq (yt, yu) -> Lt
    | Times (x, xa), Eq (yv, yw) -> Lt
    | Times (x, xa), Not yx -> Lt
    | Times (x, xa), And (yy, yz) -> Lt
    | Times (x, xa), Or (za, zb) -> Lt
    | Times (x, xa), Cast (zc, zd) -> Lt
    | Div (x, xa), N y -> Gt
    | Div (x, xa), V ya -> Gt
    | Div (x, xa), Plus (yb, yc) -> Gt
    | Div (x, xa), Minus (yd, ye) -> Gt
    | Div (x, xa), Times (yf, yg) -> Gt
    | Div (x, xa), Div (yh, yi) ->
        (match comparator_exp x yh with Eqa -> comparator_exp xa yi | Lt -> Lt
          | Gt -> Gt)
    | Div (x, xa), Mod (yj, yk) -> Lt
    | Div (x, xa), Less (yl, ym) -> Lt
    | Div (x, xa), LessEq (yn, yo) -> Lt
    | Div (x, xa), Greater (yp, yq) -> Lt
    | Div (x, xa), GreaterEq (yr, ys) -> Lt
    | Div (x, xa), NotEq (yt, yu) -> Lt
    | Div (x, xa), Eq (yv, yw) -> Lt
    | Div (x, xa), Not yx -> Lt
    | Div (x, xa), And (yy, yz) -> Lt
    | Div (x, xa), Or (za, zb) -> Lt
    | Div (x, xa), Cast (zc, zd) -> Lt
    | Mod (x, xa), N y -> Gt
    | Mod (x, xa), V ya -> Gt
    | Mod (x, xa), Plus (yb, yc) -> Gt
    | Mod (x, xa), Minus (yd, ye) -> Gt
    | Mod (x, xa), Times (yf, yg) -> Gt
    | Mod (x, xa), Div (yh, yi) -> Gt
    | Mod (x, xa), Mod (yj, yk) ->
        (match comparator_exp x yj with Eqa -> comparator_exp xa yk | Lt -> Lt
          | Gt -> Gt)
    | Mod (x, xa), Less (yl, ym) -> Lt
    | Mod (x, xa), LessEq (yn, yo) -> Lt
    | Mod (x, xa), Greater (yp, yq) -> Lt
    | Mod (x, xa), GreaterEq (yr, ys) -> Lt
    | Mod (x, xa), NotEq (yt, yu) -> Lt
    | Mod (x, xa), Eq (yv, yw) -> Lt
    | Mod (x, xa), Not yx -> Lt
    | Mod (x, xa), And (yy, yz) -> Lt
    | Mod (x, xa), Or (za, zb) -> Lt
    | Mod (x, xa), Cast (zc, zd) -> Lt
    | Less (x, xa), N y -> Gt
    | Less (x, xa), V ya -> Gt
    | Less (x, xa), Plus (yb, yc) -> Gt
    | Less (x, xa), Minus (yd, ye) -> Gt
    | Less (x, xa), Times (yf, yg) -> Gt
    | Less (x, xa), Div (yh, yi) -> Gt
    | Less (x, xa), Mod (yj, yk) -> Gt
    | Less (x, xa), Less (yl, ym) ->
        (match comparator_exp x yl with Eqa -> comparator_exp xa ym | Lt -> Lt
          | Gt -> Gt)
    | Less (x, xa), LessEq (yn, yo) -> Lt
    | Less (x, xa), Greater (yp, yq) -> Lt
    | Less (x, xa), GreaterEq (yr, ys) -> Lt
    | Less (x, xa), NotEq (yt, yu) -> Lt
    | Less (x, xa), Eq (yv, yw) -> Lt
    | Less (x, xa), Not yx -> Lt
    | Less (x, xa), And (yy, yz) -> Lt
    | Less (x, xa), Or (za, zb) -> Lt
    | Less (x, xa), Cast (zc, zd) -> Lt
    | LessEq (x, xa), N y -> Gt
    | LessEq (x, xa), V ya -> Gt
    | LessEq (x, xa), Plus (yb, yc) -> Gt
    | LessEq (x, xa), Minus (yd, ye) -> Gt
    | LessEq (x, xa), Times (yf, yg) -> Gt
    | LessEq (x, xa), Div (yh, yi) -> Gt
    | LessEq (x, xa), Mod (yj, yk) -> Gt
    | LessEq (x, xa), Less (yl, ym) -> Gt
    | LessEq (x, xa), LessEq (yn, yo) ->
        (match comparator_exp x yn with Eqa -> comparator_exp xa yo | Lt -> Lt
          | Gt -> Gt)
    | LessEq (x, xa), Greater (yp, yq) -> Lt
    | LessEq (x, xa), GreaterEq (yr, ys) -> Lt
    | LessEq (x, xa), NotEq (yt, yu) -> Lt
    | LessEq (x, xa), Eq (yv, yw) -> Lt
    | LessEq (x, xa), Not yx -> Lt
    | LessEq (x, xa), And (yy, yz) -> Lt
    | LessEq (x, xa), Or (za, zb) -> Lt
    | LessEq (x, xa), Cast (zc, zd) -> Lt
    | Greater (x, xa), N y -> Gt
    | Greater (x, xa), V ya -> Gt
    | Greater (x, xa), Plus (yb, yc) -> Gt
    | Greater (x, xa), Minus (yd, ye) -> Gt
    | Greater (x, xa), Times (yf, yg) -> Gt
    | Greater (x, xa), Div (yh, yi) -> Gt
    | Greater (x, xa), Mod (yj, yk) -> Gt
    | Greater (x, xa), Less (yl, ym) -> Gt
    | Greater (x, xa), LessEq (yn, yo) -> Gt
    | Greater (x, xa), Greater (yp, yq) ->
        (match comparator_exp x yp with Eqa -> comparator_exp xa yq | Lt -> Lt
          | Gt -> Gt)
    | Greater (x, xa), GreaterEq (yr, ys) -> Lt
    | Greater (x, xa), NotEq (yt, yu) -> Lt
    | Greater (x, xa), Eq (yv, yw) -> Lt
    | Greater (x, xa), Not yx -> Lt
    | Greater (x, xa), And (yy, yz) -> Lt
    | Greater (x, xa), Or (za, zb) -> Lt
    | Greater (x, xa), Cast (zc, zd) -> Lt
    | GreaterEq (x, xa), N y -> Gt
    | GreaterEq (x, xa), V ya -> Gt
    | GreaterEq (x, xa), Plus (yb, yc) -> Gt
    | GreaterEq (x, xa), Minus (yd, ye) -> Gt
    | GreaterEq (x, xa), Times (yf, yg) -> Gt
    | GreaterEq (x, xa), Div (yh, yi) -> Gt
    | GreaterEq (x, xa), Mod (yj, yk) -> Gt
    | GreaterEq (x, xa), Less (yl, ym) -> Gt
    | GreaterEq (x, xa), LessEq (yn, yo) -> Gt
    | GreaterEq (x, xa), Greater (yp, yq) -> Gt
    | GreaterEq (x, xa), GreaterEq (yr, ys) ->
        (match comparator_exp x yr with Eqa -> comparator_exp xa ys | Lt -> Lt
          | Gt -> Gt)
    | GreaterEq (x, xa), NotEq (yt, yu) -> Lt
    | GreaterEq (x, xa), Eq (yv, yw) -> Lt
    | GreaterEq (x, xa), Not yx -> Lt
    | GreaterEq (x, xa), And (yy, yz) -> Lt
    | GreaterEq (x, xa), Or (za, zb) -> Lt
    | GreaterEq (x, xa), Cast (zc, zd) -> Lt
    | NotEq (x, xa), N y -> Gt
    | NotEq (x, xa), V ya -> Gt
    | NotEq (x, xa), Plus (yb, yc) -> Gt
    | NotEq (x, xa), Minus (yd, ye) -> Gt
    | NotEq (x, xa), Times (yf, yg) -> Gt
    | NotEq (x, xa), Div (yh, yi) -> Gt
    | NotEq (x, xa), Mod (yj, yk) -> Gt
    | NotEq (x, xa), Less (yl, ym) -> Gt
    | NotEq (x, xa), LessEq (yn, yo) -> Gt
    | NotEq (x, xa), Greater (yp, yq) -> Gt
    | NotEq (x, xa), GreaterEq (yr, ys) -> Gt
    | NotEq (x, xa), NotEq (yt, yu) ->
        (match comparator_exp x yt with Eqa -> comparator_exp xa yu | Lt -> Lt
          | Gt -> Gt)
    | NotEq (x, xa), Eq (yv, yw) -> Lt
    | NotEq (x, xa), Not yx -> Lt
    | NotEq (x, xa), And (yy, yz) -> Lt
    | NotEq (x, xa), Or (za, zb) -> Lt
    | NotEq (x, xa), Cast (zc, zd) -> Lt
    | Eq (x, xa), N y -> Gt
    | Eq (x, xa), V ya -> Gt
    | Eq (x, xa), Plus (yb, yc) -> Gt
    | Eq (x, xa), Minus (yd, ye) -> Gt
    | Eq (x, xa), Times (yf, yg) -> Gt
    | Eq (x, xa), Div (yh, yi) -> Gt
    | Eq (x, xa), Mod (yj, yk) -> Gt
    | Eq (x, xa), Less (yl, ym) -> Gt
    | Eq (x, xa), LessEq (yn, yo) -> Gt
    | Eq (x, xa), Greater (yp, yq) -> Gt
    | Eq (x, xa), GreaterEq (yr, ys) -> Gt
    | Eq (x, xa), NotEq (yt, yu) -> Gt
    | Eq (x, xa), Eq (yv, yw) ->
        (match comparator_exp x yv with Eqa -> comparator_exp xa yw | Lt -> Lt
          | Gt -> Gt)
    | Eq (x, xa), Not yx -> Lt
    | Eq (x, xa), And (yy, yz) -> Lt
    | Eq (x, xa), Or (za, zb) -> Lt
    | Eq (x, xa), Cast (zc, zd) -> Lt
    | Not x, N y -> Gt
    | Not x, V ya -> Gt
    | Not x, Plus (yb, yc) -> Gt
    | Not x, Minus (yd, ye) -> Gt
    | Not x, Times (yf, yg) -> Gt
    | Not x, Div (yh, yi) -> Gt
    | Not x, Mod (yj, yk) -> Gt
    | Not x, Less (yl, ym) -> Gt
    | Not x, LessEq (yn, yo) -> Gt
    | Not x, Greater (yp, yq) -> Gt
    | Not x, GreaterEq (yr, ys) -> Gt
    | Not x, NotEq (yt, yu) -> Gt
    | Not x, Eq (yv, yw) -> Gt
    | Not x, Not yx -> comparator_exp x yx
    | Not x, And (yy, yz) -> Lt
    | Not x, Or (za, zb) -> Lt
    | Not x, Cast (zc, zd) -> Lt
    | And (x, xa), N y -> Gt
    | And (x, xa), V ya -> Gt
    | And (x, xa), Plus (yb, yc) -> Gt
    | And (x, xa), Minus (yd, ye) -> Gt
    | And (x, xa), Times (yf, yg) -> Gt
    | And (x, xa), Div (yh, yi) -> Gt
    | And (x, xa), Mod (yj, yk) -> Gt
    | And (x, xa), Less (yl, ym) -> Gt
    | And (x, xa), LessEq (yn, yo) -> Gt
    | And (x, xa), Greater (yp, yq) -> Gt
    | And (x, xa), GreaterEq (yr, ys) -> Gt
    | And (x, xa), NotEq (yt, yu) -> Gt
    | And (x, xa), Eq (yv, yw) -> Gt
    | And (x, xa), Not yx -> Gt
    | And (x, xa), And (yy, yz) ->
        (match comparator_exp x yy with Eqa -> comparator_exp xa yz | Lt -> Lt
          | Gt -> Gt)
    | And (x, xa), Or (za, zb) -> Lt
    | And (x, xa), Cast (zc, zd) -> Lt
    | Or (x, xa), N y -> Gt
    | Or (x, xa), V ya -> Gt
    | Or (x, xa), Plus (yb, yc) -> Gt
    | Or (x, xa), Minus (yd, ye) -> Gt
    | Or (x, xa), Times (yf, yg) -> Gt
    | Or (x, xa), Div (yh, yi) -> Gt
    | Or (x, xa), Mod (yj, yk) -> Gt
    | Or (x, xa), Less (yl, ym) -> Gt
    | Or (x, xa), LessEq (yn, yo) -> Gt
    | Or (x, xa), Greater (yp, yq) -> Gt
    | Or (x, xa), GreaterEq (yr, ys) -> Gt
    | Or (x, xa), NotEq (yt, yu) -> Gt
    | Or (x, xa), Eq (yv, yw) -> Gt
    | Or (x, xa), Not yx -> Gt
    | Or (x, xa), And (yy, yz) -> Gt
    | Or (x, xa), Or (za, zb) ->
        (match comparator_exp x za with Eqa -> comparator_exp xa zb | Lt -> Lt
          | Gt -> Gt)
    | Or (x, xa), Cast (zc, zd) -> Lt
    | Cast (x, xa), N y -> Gt
    | Cast (x, xa), V ya -> Gt
    | Cast (x, xa), Plus (yb, yc) -> Gt
    | Cast (x, xa), Minus (yd, ye) -> Gt
    | Cast (x, xa), Times (yf, yg) -> Gt
    | Cast (x, xa), Div (yh, yi) -> Gt
    | Cast (x, xa), Mod (yj, yk) -> Gt
    | Cast (x, xa), Less (yl, ym) -> Gt
    | Cast (x, xa), LessEq (yn, yo) -> Gt
    | Cast (x, xa), Greater (yp, yq) -> Gt
    | Cast (x, xa), GreaterEq (yr, ys) -> Gt
    | Cast (x, xa), NotEq (yt, yu) -> Gt
    | Cast (x, xa), Eq (yv, yw) -> Gt
    | Cast (x, xa), Not yx -> Gt
    | Cast (x, xa), And (yy, yz) -> Gt
    | Cast (x, xa), Or (za, zb) -> Gt
    | Cast (x, xa), Cast (zc, zd) ->
        (match comparator_ikind x zc with Eqa -> comparator_exp xa zd | Lt -> Lt
          | Gt -> Gt);;

let rec less_eq_exp x = le_of_comp comparator_exp x;;

let rec less_exp x = lt_of_comp comparator_exp x;;

let ord_exp = ({less_eq = less_eq_exp; less = less_exp} : exp ord);;

let preorder_exp = ({ord_preorder = ord_exp} : exp preorder);;

let order_exp = ({preorder_order = preorder_exp} : exp order);;

let linorder_exp = ({order_linorder = order_exp} : exp linorder);;

type cfg_node = Statement of nat | FunctionEntry of string |
  FunctionResult of string;;

let rec equal_cfg_nodea
  x0 x1 = match x0, x1 with FunctionEntry x2, FunctionResult x3 -> false
    | FunctionResult x3, FunctionEntry x2 -> false
    | Statement x1, FunctionResult x3 -> false
    | FunctionResult x3, Statement x1 -> false
    | Statement x1, FunctionEntry x2 -> false
    | FunctionEntry x2, Statement x1 -> false
    | FunctionResult x3, FunctionResult y3 -> ((x3 : string) = y3)
    | FunctionEntry x2, FunctionEntry y2 -> ((x2 : string) = y2)
    | Statement x1, Statement y1 -> equal_nata x1 y1;;

let equal_cfg_node = ({equal = equal_cfg_nodea} : cfg_node equal);;

let rec comparator_cfg_node
  x0 x1 = match x0, x1 with
    Statement x, Statement y -> comparator_of (equal_nat, linorder_nat) x y
    | Statement x, FunctionEntry ya -> Lt
    | Statement x, FunctionResult yb -> Lt
    | FunctionEntry x, Statement y -> Gt
    | FunctionEntry x, FunctionEntry ya ->
        comparator_of (equal_literal, linorder_literal) x ya
    | FunctionEntry x, FunctionResult yb -> Lt
    | FunctionResult x, Statement y -> Gt
    | FunctionResult x, FunctionEntry ya -> Gt
    | FunctionResult x, FunctionResult yb ->
        comparator_of (equal_literal, linorder_literal) x yb;;

let rec less_eq_cfg_node x = le_of_comp comparator_cfg_node x;;

let rec less_cfg_node x = lt_of_comp comparator_cfg_node x;;

let ord_cfg_node =
  ({less_eq = less_eq_cfg_node; less = less_cfg_node} : cfg_node ord);;

let preorder_cfg_node = ({ord_preorder = ord_cfg_node} : cfg_node preorder);;

let order_cfg_node = ({preorder_order = preorder_cfg_node} : cfg_node order);;

let linorder_cfg_node =
  ({order_linorder = order_cfg_node} : cfg_node linorder);;

type 'a toplift = TTop | TL of 'a;;

let rec equal_toplifta _A x0 x1 = match x0, x1 with TTop, TL x2 -> false
                            | TL x2, TTop -> false
                            | TL x2, TL y2 -> eq _A x2 y2
                            | TTop, TTop -> true;;

let rec equal_toplift _A = ({equal = equal_toplifta _A} : 'a toplift equal);;

let rec sup_toplifta _A
  uu uv = match uu, uv with TL a, TL b -> TL (sup _A.sup_semilattice_sup a b)
    | TTop, uv -> TTop
    | uu, TTop -> TTop;;

let rec sup_toplift _A = ({sup = sup_toplifta _A} : 'a toplift sup);;

let rec bot_toplifta _A = TL (bot _A.bot_order_bot);;

let rec bot_toplift _A = ({bot = bot_toplifta _A} : 'a toplift bot);;

let rec less_eq_toplift _A
  uu x1 = match uu, x1 with uu, TTop -> true
    | TTop, TL b -> false
    | TL a, TL b -> less_eq _A.preorder_order.ord_preorder a b;;

let rec less_toplift _A
  a b = less_eq_toplift _A a b && not (less_eq_toplift _A b a);;

let rec ord_toplift _A =
  ({less_eq = less_eq_toplift _A; less = less_toplift _A} : 'a toplift ord);;

let rec preorder_toplift _A =
  ({ord_preorder = (ord_toplift _A)} : 'a toplift preorder);;

let rec order_toplift _A =
  ({preorder_order = (preorder_toplift _A)} : 'a toplift order);;

let rec widen_toplift _A
  uu uv = match uu, uv with TL a, TL b -> TL (widen _A.widening_warrowing a b)
    | TTop, uv -> TTop
    | uu, TTop -> TTop;;

let rec widening_toplift _A =
  ({order_widening = (order_toplift _A.widening_warrowing.order_widening);
     widen = widen_toplift _A}
    : 'a toplift widening);;

let rec order_bot_toplift _A =
  ({bot_order_bot = (bot_toplift _A);
     order_order_bot = (order_toplift _A.order_order_bot)}
    : 'a toplift order_bot);;

let rec narrow_toplift _A
  x0 b = match x0, b with TTop, b -> b
    | TL a, TL b -> TL (narrow _A.narrowing_warrowing a b)
    | TL a, TTop -> TL a;;

let rec narrowing_toplift _A =
  ({order_narrowing = (order_toplift _A.widening_warrowing.order_widening);
     narrow = narrow_toplift _A}
    : 'a toplift narrowing);;

let rec warrowing_toplift _A =
  ({narrowing_warrowing = (narrowing_toplift _A);
     widening_warrowing = (widening_toplift _A)}
    : 'a toplift warrowing);;

let rec semilattice_sup_toplift _A =
  ({sup_semilattice_sup = (sup_toplift _A);
     order_semilattice_sup = (order_toplift _A.order_semilattice_sup)}
    : 'a toplift semilattice_sup);;

let rec bounded_semilattice_sup_bot_toplift _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_toplift _A.semilattice_sup_bounded_semilattice_sup_bot);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_toplift _A.order_bot_bounded_semilattice_sup_bot)}
    : 'a toplift bounded_semilattice_sup_bot);;

type ('a, 'b) dg_state = DG of 'a * 'b;;

let rec equal_dg_statea _A _B
  (DG (x1, x2)) (DG (y1, y2)) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_dg_state _A _B =
  ({equal = equal_dg_statea _A _B} : ('a, 'b) dg_state equal);;

let rec dg_global (DG (x1, x2)) = x2;;

let rec dg_local (DG (x1, x2)) = x1;;

let rec sup_dg_statea _A _B
  d1 d2 =
    DG (sup _A.sup_semilattice_sup (dg_local d1) (dg_local d2),
         sup _B.sup_semilattice_sup (dg_global d1) (dg_global d2));;

let rec sup_dg_state _A _B =
  ({sup = sup_dg_statea _A _B} : ('a, 'b) dg_state sup);;

let rec bot_dg_statea _A _B = DG (bot _A.bot_order_bot, bot _B.bot_order_bot);;

let rec bot_dg_state _A _B =
  ({bot = bot_dg_statea _A _B} : ('a, 'b) dg_state bot);;

let rec less_eq_dg_state _A _B
  d1 d2 =
    less_eq _A (dg_local d1) (dg_local d2) &&
      less_eq _B (dg_global d1) (dg_global d2);;

let rec less_dg_state _A _B
  d1 d2 = less_eq_dg_state _A _B d1 d2 && not (less_eq_dg_state _A _B d2 d1);;

let rec ord_dg_state _A _B =
  ({less_eq = less_eq_dg_state _A _B; less = less_dg_state _A _B} :
    ('a, 'b) dg_state ord);;

let rec preorder_dg_state _A _B =
  ({ord_preorder =
      (ord_dg_state _A.preorder_order.ord_preorder
        _B.preorder_order.ord_preorder)}
    : ('a, 'b) dg_state preorder);;

let rec order_dg_state _A _B =
  ({preorder_order = (preorder_dg_state _A _B)} : ('a, 'b) dg_state order);;

let rec widen_dg_state (_A1, _A2) (_B1, _B2)
  a b = DG (widen _A2.widening_warrowing (dg_local a) (dg_local b),
             widen _B2.widening_warrowing (dg_global a) (dg_global b));;

let rec widening_dg_state (_A1, _A2) (_B1, _B2) =
  ({order_widening =
      (order_dg_state _A1.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B1.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     widen = widen_dg_state (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) dg_state widening);;

let rec order_bot_dg_state _A _B =
  ({bot_order_bot = (bot_dg_state _A _B);
     order_order_bot = (order_dg_state _A.order_order_bot _B.order_order_bot)}
    : ('a, 'b) dg_state order_bot);;

let rec narrow_dg_state (_A1, _A2) (_B1, _B2)
  a b = DG (narrow _A2.narrowing_warrowing (dg_local a) (dg_local b),
             narrow _B2.narrowing_warrowing (dg_global a) (dg_global b));;

let rec narrowing_dg_state (_A1, _A2) (_B1, _B2) =
  ({order_narrowing =
      (order_dg_state _A1.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B1.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     narrow = narrow_dg_state (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) dg_state narrowing);;

let rec warrowing_dg_state (_A1, _A2) (_B1, _B2) =
  ({narrowing_warrowing = (narrowing_dg_state (_A1, _A2) (_B1, _B2));
     widening_warrowing = (widening_dg_state (_A1, _A2) (_B1, _B2))}
    : ('a, 'b) dg_state warrowing);;

let rec semilattice_sup_dg_state _A _B =
  ({sup_semilattice_sup = (sup_dg_state _A _B);
     order_semilattice_sup =
       (order_dg_state _A.order_semilattice_sup _B.order_semilattice_sup)}
    : ('a, 'b) dg_state semilattice_sup);;

let rec bounded_semilattice_sup_bot_dg_state _A _B =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_dg_state _A.semilattice_sup_bounded_semilattice_sup_bot
        _B.semilattice_sup_bounded_semilattice_sup_bot);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_dg_state _A.order_bot_bounded_semilattice_sup_bot
         _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) dg_state bounded_semilattice_sup_bot);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec less_eq_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less_eq _B y1 y2;;

let rec less_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less _B y1 y2;;

let rec ord_prod _A _B =
  ({less_eq = less_eq_prod _A _B; less = less_prod _A _B} : ('a * 'b) ord);;

let rec preorder_prod _A _B =
  ({ord_preorder = (ord_prod _A.ord_preorder _B.ord_preorder)} :
    ('a * 'b) preorder);;

let rec order_prod _A _B =
  ({preorder_order = (preorder_prod _A.preorder_order _B.preorder_order)} :
    ('a * 'b) order);;

let rec linorder_prod _A _B =
  ({order_linorder = (order_prod _A.order_linorder _B.order_linorder)} :
    ('a * 'b) linorder);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec inf_unita uu uv = ();;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_unit = ({inf = inf_unita} : unit inf);;

let rec sup_unita uu uv = ();;

let sup_unit = ({sup = sup_unita} : unit sup);;

let bot_unita : unit = ();;

let bot_unit = ({bot = bot_unita} : unit bot);;

let rec less_eq_unit uu uv = true;;

let rec less_unit uu uv = false;;

let ord_unit = ({less_eq = less_eq_unit; less = less_unit} : unit ord);;

let top_unita : unit = ();;

let top_unit = ({top = top_unita} : unit top);;

let preorder_unit = ({ord_preorder = ord_unit} : unit preorder);;

let order_unit = ({preorder_order = preorder_unit} : unit order);;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf; order_semilattice_inf : 'a order};;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf;
    semilattice_sup_lattice : 'a semilattice_sup};;

let semilattice_sup_unit =
  ({sup_semilattice_sup = sup_unit; order_semilattice_sup = order_unit} :
    unit semilattice_sup);;

let semilattice_inf_unit =
  ({inf_semilattice_inf = inf_unit; order_semilattice_inf = order_unit} :
    unit semilattice_inf);;

let lattice_unit =
  ({semilattice_inf_lattice = semilattice_inf_unit;
     semilattice_sup_lattice = semilattice_sup_unit}
    : unit lattice);;

let rec widen_unit a b = ();;

let widening_unit =
  ({order_widening = order_unit; widen = widen_unit} : unit widening);;

let order_bot_unit =
  ({bot_order_bot = bot_unit; order_order_bot = order_unit} : unit order_bot);;

let order_top_unit =
  ({order_order_top = order_unit; top_order_top = top_unit} : unit order_top);;

let rec narrow_unit a b = ();;

let narrowing_unit =
  ({order_narrowing = order_unit; narrow = narrow_unit} : unit narrowing);;

let warrowing_unit =
  ({narrowing_warrowing = narrowing_unit; widening_warrowing = widening_unit} :
    unit warrowing);;

type 'a bounded_semilattice_inf_top =
  {semilattice_inf_bounded_semilattice_inf_top : 'a semilattice_inf;
    order_top_bounded_semilattice_inf_top : 'a order_top};;

type 'a bounded_lattice_top =
  {bounded_semilattice_inf_top_bounded_lattice_top :
     'a bounded_semilattice_inf_top;
    lattice_bounded_lattice_top : 'a lattice};;

type 'a bounded_lattice_bot =
  {bounded_semilattice_sup_bot_bounded_lattice_bot :
     'a bounded_semilattice_sup_bot;
    lattice_bounded_lattice_bot : 'a lattice};;

type 'a bounded_lattice =
  {bounded_lattice_bot_bounded_lattice : 'a bounded_lattice_bot;
    bounded_lattice_top_bounded_lattice : 'a bounded_lattice_top};;

let bounded_semilattice_inf_top_unit =
  ({semilattice_inf_bounded_semilattice_inf_top = semilattice_inf_unit;
     order_top_bounded_semilattice_inf_top = order_top_unit}
    : unit bounded_semilattice_inf_top);;

let bounded_lattice_top_unit =
  ({bounded_semilattice_inf_top_bounded_lattice_top =
      bounded_semilattice_inf_top_unit;
     lattice_bounded_lattice_top = lattice_unit}
    : unit bounded_lattice_top);;

let bounded_semilattice_sup_bot_unit =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_unit;
     order_bot_bounded_semilattice_sup_bot = order_bot_unit}
    : unit bounded_semilattice_sup_bot);;

let bounded_lattice_bot_unit =
  ({bounded_semilattice_sup_bot_bounded_lattice_bot =
      bounded_semilattice_sup_bot_unit;
     lattice_bounded_lattice_bot = lattice_unit}
    : unit bounded_lattice_bot);;

let bounded_lattice_unit =
  ({bounded_lattice_bot_bounded_lattice = bounded_lattice_bot_unit;
     bounded_lattice_top_bounded_lattice = bounded_lattice_top_unit}
    : unit bounded_lattice);;

type sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop;;

let rec equal_signa x0 x1 = match x0, x1 with SPos, STop -> false
                      | STop, SPos -> false
                      | SNonNeg, STop -> false
                      | STop, SNonNeg -> false
                      | SNonNeg, SPos -> false
                      | SPos, SNonNeg -> false
                      | SZero, STop -> false
                      | STop, SZero -> false
                      | SZero, SPos -> false
                      | SPos, SZero -> false
                      | SZero, SNonNeg -> false
                      | SNonNeg, SZero -> false
                      | SNonPos, STop -> false
                      | STop, SNonPos -> false
                      | SNonPos, SPos -> false
                      | SPos, SNonPos -> false
                      | SNonPos, SNonNeg -> false
                      | SNonNeg, SNonPos -> false
                      | SNonPos, SZero -> false
                      | SZero, SNonPos -> false
                      | SNeg, STop -> false
                      | STop, SNeg -> false
                      | SNeg, SPos -> false
                      | SPos, SNeg -> false
                      | SNeg, SNonNeg -> false
                      | SNonNeg, SNeg -> false
                      | SNeg, SZero -> false
                      | SZero, SNeg -> false
                      | SNeg, SNonPos -> false
                      | SNonPos, SNeg -> false
                      | SBot, STop -> false
                      | STop, SBot -> false
                      | SBot, SPos -> false
                      | SPos, SBot -> false
                      | SBot, SNonNeg -> false
                      | SNonNeg, SBot -> false
                      | SBot, SZero -> false
                      | SZero, SBot -> false
                      | SBot, SNonPos -> false
                      | SNonPos, SBot -> false
                      | SBot, SNeg -> false
                      | SNeg, SBot -> false
                      | STop, STop -> true
                      | SPos, SPos -> true
                      | SNonNeg, SNonNeg -> true
                      | SZero, SZero -> true
                      | SNonPos, SNonPos -> true
                      | SNeg, SNeg -> true
                      | SBot, SBot -> true;;

let equal_sign = ({equal = equal_signa} : sign equal);;

let rec join_sign x0 b = match x0, b with SBot, b -> b
                    | SNeg, SBot -> SNeg
                    | SNonPos, SBot -> SNonPos
                    | SZero, SBot -> SZero
                    | SNonNeg, SBot -> SNonNeg
                    | SPos, SBot -> SPos
                    | STop, SBot -> STop
                    | STop, SNeg -> STop
                    | STop, SNonPos -> STop
                    | STop, SZero -> STop
                    | STop, SNonNeg -> STop
                    | STop, SPos -> STop
                    | STop, STop -> STop
                    | SNeg, STop -> STop
                    | SNonPos, STop -> STop
                    | SZero, STop -> STop
                    | SNonNeg, STop -> STop
                    | SPos, STop -> STop
                    | SNeg, SNeg -> SNeg
                    | SNeg, SZero -> SNonPos
                    | SNeg, SNonPos -> SNonPos
                    | SZero, SNeg -> SNonPos
                    | SZero, SZero -> SZero
                    | SZero, SPos -> SNonNeg
                    | SZero, SNonPos -> SNonPos
                    | SZero, SNonNeg -> SNonNeg
                    | SNonPos, SNeg -> SNonPos
                    | SNonPos, SZero -> SNonPos
                    | SNonPos, SNonPos -> SNonPos
                    | SNonNeg, SZero -> SNonNeg
                    | SNonNeg, SPos -> SNonNeg
                    | SNonNeg, SNonNeg -> SNonNeg
                    | SPos, SZero -> SNonNeg
                    | SPos, SNonNeg -> SNonNeg
                    | SPos, SPos -> SPos
                    | SNeg, SNonNeg -> STop
                    | SNeg, SPos -> STop
                    | SNonPos, SNonNeg -> STop
                    | SNonPos, SPos -> STop
                    | SNonNeg, SNeg -> STop
                    | SNonNeg, SNonPos -> STop
                    | SPos, SNeg -> STop
                    | SPos, SNonPos -> STop;;

let rec sup_signa x = join_sign x;;

let sup_sign = ({sup = sup_signa} : sign sup);;

let bot_signa : sign = SBot;;

let bot_sign = ({bot = bot_signa} : sign bot);;

let rec sign_le x0 uu = match x0, uu with SBot, uu -> true
                  | SNeg, STop -> true
                  | SNonPos, STop -> true
                  | SZero, STop -> true
                  | SNonNeg, STop -> true
                  | SPos, STop -> true
                  | STop, STop -> true
                  | SNeg, SNeg -> true
                  | SNeg, SNonPos -> true
                  | SNonPos, SNonPos -> true
                  | SZero, SZero -> true
                  | SZero, SNonPos -> true
                  | SZero, SNonNeg -> true
                  | SNonNeg, SNonNeg -> true
                  | SPos, SPos -> true
                  | SPos, SNonNeg -> true
                  | SNeg, SBot -> false
                  | SNeg, SZero -> false
                  | SNeg, SNonNeg -> false
                  | SNeg, SPos -> false
                  | SNonPos, SBot -> false
                  | SNonPos, SNeg -> false
                  | SNonPos, SZero -> false
                  | SNonPos, SNonNeg -> false
                  | SNonPos, SPos -> false
                  | SZero, SBot -> false
                  | SZero, SNeg -> false
                  | SZero, SPos -> false
                  | SNonNeg, SBot -> false
                  | SNonNeg, SNeg -> false
                  | SNonNeg, SNonPos -> false
                  | SNonNeg, SZero -> false
                  | SNonNeg, SPos -> false
                  | SPos, SBot -> false
                  | SPos, SNeg -> false
                  | SPos, SNonPos -> false
                  | SPos, SZero -> false
                  | STop, SBot -> false
                  | STop, SNeg -> false
                  | STop, SNonPos -> false
                  | STop, SZero -> false
                  | STop, SNonNeg -> false
                  | STop, SPos -> false;;

let rec less_eq_sign a b = sign_le a b;;

let rec less_sign a b = sign_le a b && not (sign_le b a);;

let ord_sign = ({less_eq = less_eq_sign; less = less_sign} : sign ord);;

let top_signa : sign = STop;;

let top_sign = ({top = top_signa} : sign top);;

let preorder_sign = ({ord_preorder = ord_sign} : sign preorder);;

let order_sign = ({preorder_order = preorder_sign} : sign order);;

let rec widen_sign a b = join_sign a b;;

let widening_sign =
  ({order_widening = order_sign; widen = widen_sign} : sign widening);;

let order_bot_sign =
  ({bot_order_bot = bot_sign; order_order_bot = order_sign} : sign order_bot);;

let order_top_sign =
  ({order_order_top = order_sign; top_order_top = top_sign} : sign order_top);;

let rec narrow_sign_td a b = a;;

let rec narrow_sign a b = narrow_sign_td a b;;

let narrowing_sign =
  ({order_narrowing = order_sign; narrow = narrow_sign} : sign narrowing);;

let warrowing_sign =
  ({narrowing_warrowing = narrowing_sign; widening_warrowing = widening_sign} :
    sign warrowing);;

let rec string_of_sign = function SBot -> "<bottom>"
                         | SNeg -> "-"
                         | SNonPos -> "<le>" ^ "0"
                         | SZero -> "0"
                         | SNonNeg -> "<ge>" ^ "0"
                         | SPos -> "+"
                         | STop -> "<top>";;

let rec to_string_sign a = string_of_sign a;;

let rec is_bottom_sign s = equal_signa s SBot;;

let rec is_empty_sign a = is_bottom_sign a;;

let gamma_sign _ = failwith "Sign_Lattice.gamma_sign";;

let rec gamma_signa a = gamma_sign a;;

let rec inf_sign x0 uu = match x0, uu with SBot, uu -> SBot
                   | SNeg, SBot -> SBot
                   | SNonPos, SBot -> SBot
                   | SZero, SBot -> SBot
                   | SNonNeg, SBot -> SBot
                   | SPos, SBot -> SBot
                   | STop, SBot -> SBot
                   | STop, SNeg -> SNeg
                   | STop, SNonPos -> SNonPos
                   | STop, SZero -> SZero
                   | STop, SNonNeg -> SNonNeg
                   | STop, SPos -> SPos
                   | STop, STop -> STop
                   | SNeg, STop -> SNeg
                   | SNonPos, STop -> SNonPos
                   | SZero, STop -> SZero
                   | SNonNeg, STop -> SNonNeg
                   | SPos, STop -> SPos
                   | SNeg, SNeg -> SNeg
                   | SNeg, SNonPos -> SNeg
                   | SNonPos, SNeg -> SNeg
                   | SNonPos, SNonPos -> SNonPos
                   | SNonPos, SZero -> SZero
                   | SZero, SNonPos -> SZero
                   | SNonPos, SNonNeg -> SZero
                   | SNonNeg, SNonPos -> SZero
                   | SZero, SZero -> SZero
                   | SZero, SNonNeg -> SZero
                   | SNonNeg, SZero -> SZero
                   | SNonNeg, SNonNeg -> SNonNeg
                   | SNonNeg, SPos -> SPos
                   | SPos, SNonNeg -> SPos
                   | SPos, SPos -> SPos
                   | SNeg, SZero -> SBot
                   | SNeg, SNonNeg -> SBot
                   | SNeg, SPos -> SBot
                   | SNonPos, SPos -> SBot
                   | SZero, SNeg -> SBot
                   | SZero, SPos -> SBot
                   | SNonNeg, SNeg -> SBot
                   | SPos, SNeg -> SBot
                   | SPos, SNonPos -> SBot
                   | SPos, SZero -> SBot;;

let rec narrow_ik_sign k a b = inf_sign a b;;

let rec widen_ik_sign k a b = sup_signa a b;;

let rec ik_signed = function I8 -> true
                    | U8 -> false
                    | I16 -> true
                    | U16 -> false
                    | I32 -> true
                    | U32 -> false
                    | I64 -> true
                    | U64 -> false;;

let rec empty_ik_sign
  k a = equal_signa a SBot || not (ik_signed k) && equal_signa a SNeg;;

let semilattice_sup_sign =
  ({sup_semilattice_sup = sup_sign; order_semilattice_sup = order_sign} :
    sign semilattice_sup);;

let bounded_semilattice_sup_bot_sign =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_sign;
     order_bot_bounded_semilattice_sup_bot = order_bot_sign}
    : sign bounded_semilattice_sup_bot);;

let executable_domain_sign =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_sign;
     order_top_executable_domain = order_top_sign;
     warrowing_executable_domain = warrowing_sign; is_empty = is_empty_sign;
     to_string = to_string_sign}
    : sign executable_domain);;

let numeric_domain_sign =
  ({executable_domain_numeric_domain = executable_domain_sign;
     gamma = gamma_signa}
    : sign numeric_domain);;

let ik_domain_sign =
  ({numeric_domain_ik_domain = numeric_domain_sign; widen_ik = widen_ik_sign;
     narrow_ik = narrow_ik_sign; empty_ik = empty_ik_sign}
    : sign ik_domain);;

let rec times_sign x0 uu = match x0, uu with SBot, uu -> SBot
                     | SNeg, SBot -> SBot
                     | SNonPos, SBot -> SBot
                     | SZero, SBot -> SBot
                     | SNonNeg, SBot -> SBot
                     | SPos, SBot -> SBot
                     | STop, SBot -> SBot
                     | SZero, SNeg -> SZero
                     | SZero, SNonPos -> SZero
                     | SZero, SZero -> SZero
                     | SZero, SNonNeg -> SZero
                     | SZero, SPos -> SZero
                     | SZero, STop -> SZero
                     | SNeg, SZero -> SZero
                     | SNonPos, SZero -> SZero
                     | SNonNeg, SZero -> SZero
                     | SPos, SZero -> SZero
                     | STop, SZero -> SZero
                     | SNeg, SNeg -> SPos
                     | SPos, SPos -> SPos
                     | SNeg, SPos -> SNeg
                     | SPos, SNeg -> SNeg
                     | SNeg, SNonPos -> SNonNeg
                     | SNonPos, SNeg -> SNonNeg
                     | SNeg, SNonNeg -> SNonPos
                     | SNonNeg, SNeg -> SNonPos
                     | SPos, SNonNeg -> SNonNeg
                     | SNonNeg, SPos -> SNonNeg
                     | SPos, SNonPos -> SNonPos
                     | SNonPos, SPos -> SNonPos
                     | SNonNeg, SNonNeg -> SNonNeg
                     | SNonNeg, SNonPos -> SNonPos
                     | SNonPos, SNonNeg -> SNonPos
                     | SNonPos, SNonPos -> SNonNeg
                     | SNeg, STop -> STop
                     | SNonPos, STop -> STop
                     | SNonNeg, STop -> STop
                     | SPos, STop -> STop
                     | STop, SNeg -> STop
                     | STop, SNonPos -> STop
                     | STop, SNonNeg -> STop
                     | STop, SPos -> STop
                     | STop, STop -> STop;;

let rec minus_sign x0 uu = match x0, uu with SBot, uu -> SBot
                     | SNeg, SBot -> SBot
                     | SNonPos, SBot -> SBot
                     | SZero, SBot -> SBot
                     | SNonNeg, SBot -> SBot
                     | SPos, SBot -> SBot
                     | STop, SBot -> SBot
                     | SNeg, SPos -> SNeg
                     | SNeg, SNonNeg -> SNeg
                     | SPos, SNeg -> SPos
                     | SPos, SNonPos -> SPos
                     | SNeg, SZero -> SNeg
                     | SPos, SZero -> SPos
                     | SZero, SZero -> SZero
                     | SZero, SNeg -> SPos
                     | SZero, SPos -> SNeg
                     | SZero, SNonNeg -> SNonPos
                     | SZero, SNonPos -> SNonNeg
                     | SNonNeg, SZero -> SNonNeg
                     | SNonNeg, SNeg -> SPos
                     | SNonNeg, SNonPos -> SNonNeg
                     | SNonPos, SZero -> SNonPos
                     | SNonPos, SPos -> SNeg
                     | SNonPos, SNonNeg -> SNonPos
                     | SNeg, SNeg -> STop
                     | SNeg, SNonPos -> STop
                     | SNeg, STop -> STop
                     | SNonPos, SNeg -> STop
                     | SNonPos, SNonPos -> STop
                     | SNonPos, STop -> STop
                     | SZero, STop -> STop
                     | SNonNeg, SNonNeg -> STop
                     | SNonNeg, SPos -> STop
                     | SNonNeg, STop -> STop
                     | SPos, SNonNeg -> STop
                     | SPos, SPos -> STop
                     | SPos, STop -> STop
                     | STop, SNeg -> STop
                     | STop, SNonPos -> STop
                     | STop, SZero -> STop
                     | STop, SNonNeg -> STop
                     | STop, SPos -> STop
                     | STop, STop -> STop;;

let rec plus_sign x0 uu = match x0, uu with SBot, uu -> SBot
                    | SNeg, SBot -> SBot
                    | SNonPos, SBot -> SBot
                    | SZero, SBot -> SBot
                    | SNonNeg, SBot -> SBot
                    | SPos, SBot -> SBot
                    | STop, SBot -> SBot
                    | SNeg, SNeg -> SNeg
                    | SNeg, SNonPos -> SNeg
                    | SNonPos, SNeg -> SNeg
                    | SNonPos, SNonPos -> SNonPos
                    | SPos, SPos -> SPos
                    | SPos, SNonNeg -> SPos
                    | SNonNeg, SPos -> SPos
                    | SNonNeg, SNonNeg -> SNonNeg
                    | SZero, SNeg -> SNeg
                    | SZero, SNonPos -> SNonPos
                    | SZero, SZero -> SZero
                    | SZero, SNonNeg -> SNonNeg
                    | SZero, SPos -> SPos
                    | SZero, STop -> STop
                    | SNeg, SZero -> SNeg
                    | SNonPos, SZero -> SNonPos
                    | SNonNeg, SZero -> SNonNeg
                    | SPos, SZero -> SPos
                    | STop, SZero -> STop
                    | SNeg, SNonNeg -> STop
                    | SNeg, SPos -> STop
                    | SNeg, STop -> STop
                    | SNonPos, SNonNeg -> STop
                    | SNonPos, SPos -> STop
                    | SNonPos, STop -> STop
                    | SNonNeg, SNeg -> STop
                    | SNonNeg, SNonPos -> STop
                    | SNonNeg, STop -> STop
                    | SPos, SNeg -> STop
                    | SPos, SNonPos -> STop
                    | SPos, STop -> STop
                    | STop, SNeg -> STop
                    | STop, SNonPos -> STop
                    | STop, SNonNeg -> STop
                    | STop, SPos -> STop
                    | STop, STop -> STop;;

let rec sign_mod
  a b = (if equal_signa a SBot || equal_signa b SBot then SBot
          else (if equal_signa b SZero then a else sup_signa a SZero));;

let rec sign_div
  a b = (if equal_signa a SBot || equal_signa b SBot then SBot
          else sup_signa (times_sign a b) SZero);;

let rec sign_aop x0 a b = match x0, a, b with AAdd, a, b -> plus_sign a b
                   | ASub, a, b -> minus_sign a b
                   | AMul, a, b -> times_sign a b
                   | ADiv, a, b -> sign_div a b
                   | AMod, a, b -> sign_mod a b;;

let rec raw_aop_ik_sign x = sign_aop x;;

let rec refine_ik_sign
  c a b = (if equal_cop c CEq then (inf_sign a b, inf_sign a b) else (a, b));;

let rec sign_of_int
  n = (if less_int n zero_inta then SNeg
        else (if equal_inta n zero_inta then SZero else SPos));;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec signed_take_bit _A
  n a = (let l =
           take_bit _A.semiring_bit_operations_ring_bit_operations (suc n) a in
          (if bit _A.semiring_bit_operations_ring_bit_operations.semiring_bits_semiring_bit_operations
                l n
            then plus _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.semigroup_add_numeral.plus_semigroup_add
                   l (push_bit _A.semiring_bit_operations_ring_bit_operations
                       (suc n)
                       (uminus
                         _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.uminus_group_add
                         (one _A.ring_parity_ring_bit_operations.comm_ring_1_ring_parity.ring_1_comm_ring_1.neg_numeral_ring_1.numeral_neg_numeral.one_numeral)))
            else l));;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec ik_bits = function I8 -> nat_of_integer (Z.of_int 8)
                  | U8 -> nat_of_integer (Z.of_int 8)
                  | I16 -> nat_of_integer (Z.of_int 16)
                  | U16 -> nat_of_integer (Z.of_int 16)
                  | I32 -> nat_of_integer (Z.of_int 32)
                  | U32 -> nat_of_integer (Z.of_int 32)
                  | I64 -> nat_of_integer (Z.of_int 64)
                  | U64 -> nat_of_integer (Z.of_int 64);;

let rec ik_norm
  ik n =
    (if ik_signed ik
      then signed_take_bit ring_bit_operations_int
             (minus_nat (ik_bits ik) one_nat) n
      else take_bit_int (ik_bits ik) n);;

let rec of_int_ik_sign k n = sign_of_int (ik_norm k n);;

let rec sign_cast
  ik a =
    (if equal_signa a SBot then SBot
      else (if equal_signa a SZero then SZero
             else (if ik_signed ik then STop else SNonNeg)));;

let rec arith_ik_sign k op a b = sign_cast k (sign_aop op a b);;

let rec meet_ik_sign a b = inf_sign a b;;

let rec fits_ik_sign k a = equal_signa a SBot || equal_signa a SZero;;

let zero_nat : nat = Nat Z.zero;;

let rec power _A
  a n = (if equal_nata n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nat)));;

let rec ik_half
  ik = power power_int (Int_of_integer (Z.of_int 2))
         (minus_nat (ik_bits ik) one_nat);;

let rec ik_min
  ik = (if ik_signed ik then uminus_inta (ik_half ik) else zero_inta);;

let rec ik_mod ik = power power_int (Int_of_integer (Z.of_int 2)) (ik_bits ik);;

let rec ik_max
  ik = (if ik_signed ik then minus_inta (ik_half ik) one_inta
         else minus_inta (ik_mod ik) one_inta);;

let rec cast_ik_sign
  sk k a =
    (match sk with None -> sign_cast k a
      | Some s ->
        (if less_eq_int (ik_min k) (ik_min s) &&
              less_eq_int (ik_max s) (ik_max k)
          then a else sign_cast k a));;

let rec top_ik_sign k = (if ik_signed k then STop else SNonNeg);;

let rec sign_eqb
  a b = (if equal_signa a SZero && equal_signa b SZero then Some true
          else (if sign_le a SNeg && sign_le b SNonNeg ||
                     (sign_le b SNeg && sign_le a SNonNeg ||
                       (sign_le a SPos && sign_le b SNonPos ||
                         sign_le b SPos && sign_le a SNonPos))
                 then Some false else None));;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec sign_lt
  a b = (if sign_le a SNeg && sign_le b SNonNeg then Some true
          else (if sign_le a SNonPos && sign_le b SPos then Some true
                 else (if sign_le b SNonPos && sign_le a SNonNeg then Some false
                        else (if sign_le b SNeg && sign_le a SPos
                               then Some false else None))));;

let rec sign_cop x0 a b = match x0, a, b with CLt, a, b -> sign_lt a b
                   | CGt, a, b -> sign_lt b a
                   | CLe, a, b -> map_option not (sign_lt b a)
                   | CGe, a, b -> map_option not (sign_lt a b)
                   | CEq, a, b -> sign_eqb a b
                   | CNe, a, b -> map_option not (sign_eqb a b);;

let rec cmp_ik_sign x = sign_cop x;;

type 'a kind_int_domain =
  {ik_domain_kind_int_domain : 'a ik_domain; top_ik : ikind -> 'a;
    of_int_ik : ikind -> int -> 'a; cast_ik : ikind option -> ikind -> 'a -> 'a;
    arith_ik : ikind -> aop -> 'a -> 'a -> 'a;
    cmp_ik : cop -> 'a -> 'a -> bool option; meet_ik : 'a -> 'a -> 'a;
    refine_ik : cop -> 'a -> 'a -> 'a * 'a; raw_aop_ik : aop -> 'a -> 'a -> 'a;
    fits_ik : ikind -> 'a -> bool};;
let top_ik _A = _A.top_ik;;
let of_int_ik _A = _A.of_int_ik;;
let cast_ik _A = _A.cast_ik;;
let arith_ik _A = _A.arith_ik;;
let cmp_ik _A = _A.cmp_ik;;
let meet_ik _A = _A.meet_ik;;
let refine_ik _A = _A.refine_ik;;
let raw_aop_ik _A = _A.raw_aop_ik;;
let fits_ik _A = _A.fits_ik;;

let kind_int_domain_sign =
  ({ik_domain_kind_int_domain = ik_domain_sign; top_ik = top_ik_sign;
     of_int_ik = of_int_ik_sign; cast_ik = cast_ik_sign;
     arith_ik = arith_ik_sign; cmp_ik = cmp_ik_sign; meet_ik = meet_ik_sign;
     refine_ik = refine_ik_sign; raw_aop_ik = raw_aop_ik_sign;
     fits_ik = fits_ik_sign}
    : sign kind_int_domain);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A x xa1 = match x, xa1 with x, Set xs -> membera _A xs x
                    | x, Coset xs -> not (membera _A xs x);;

let rec less_eq_set _A
  a b = match a, b with Set xs, b -> list_all (fun x -> member _A x b) xs
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Coset [], Set [] -> false;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

type relc = RelBot | RelC of (string * string) set;;

let rec equal_relca
  x0 x1 = match x0, x1 with RelBot, RelC x2 -> false
    | RelC x2, RelBot -> false
    | RelC x2, RelC y2 ->
        equal_set (equal_prod equal_literal equal_literal) x2 y2
    | RelBot, RelBot -> true;;

let equal_relc = ({equal = equal_relca} : relc equal);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec insertb _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec remove _A
  x xa1 = match x, xa1 with x, Set xs -> Set (removeAll _A x xs)
    | x, Coset xs -> Coset (insertb _A x xs);;

let rec inf_set _A
  a x1 = match a, x1 with a, Set xs -> Set (filtera (fun x -> member _A x a) xs)
    | a, Coset xs -> fold (remove _A) xs a;;

let rec sup_relca
  x0 b = match x0, b with RelBot, b -> b
    | RelC v, RelBot -> RelC v
    | RelC a, RelC b ->
        RelC (inf_set (equal_prod equal_literal equal_literal) a b);;

let sup_relc = ({sup = sup_relca} : relc sup);;

let bot_relca : relc = RelBot;;

let bot_relc = ({bot = bot_relca} : relc bot);;

let rec less_eq_relc
  x0 uu = match x0, uu with RelBot, uu -> true
    | RelC uv, RelBot -> false
    | RelC a, RelC b ->
        less_eq_set (equal_prod equal_literal equal_literal) b a;;

let rec less_relc a b = less_eq_relc a b && not (less_eq_relc b a);;

let ord_relc = ({less_eq = less_eq_relc; less = less_relc} : relc ord);;

let preorder_relc = ({ord_preorder = ord_relc} : relc preorder);;

let order_relc = ({preorder_order = preorder_relc} : relc order);;

let rec widen_relc a b = sup_relca a b;;

let widening_relc =
  ({order_widening = order_relc; widen = widen_relc} : relc widening);;

let order_bot_relc =
  ({bot_order_bot = bot_relc; order_order_bot = order_relc} : relc order_bot);;

let rec narrow_relc a b = b;;

let narrowing_relc =
  ({order_narrowing = order_relc; narrow = narrow_relc} : relc narrowing);;

let warrowing_relc =
  ({narrowing_warrowing = narrowing_relc; widening_warrowing = widening_relc} :
    relc warrowing);;

let rec vjoin_relc x = sup_relca x;;

let join_val_relc = ({vjoin = vjoin_relc} : relc join_val);;

let semilattice_sup_relc =
  ({sup_semilattice_sup = sup_relc; order_semilattice_sup = order_relc} :
    relc semilattice_sup);;

let rec split_global_at_relc x d = bot_relca;;

let rec split_free_relc r = bot_relca;;

let rec split_cmb_relc d g = d;;

let rec split_rl_relc d = d;;

let rec split_rg_relc d = bot_relca;;

type 'a ownership_split =
  {order_bot_ownership_split : 'a order_bot; split_cmb : 'a -> 'a -> 'a;
    split_rl : 'a -> 'a; split_global_at : string -> 'a -> 'a;
    split_rg : 'a -> 'a; split_free : string list -> 'a};;
let split_cmb _A = _A.split_cmb;;
let split_rl _A = _A.split_rl;;
let split_global_at _A = _A.split_global_at;;
let split_rg _A = _A.split_rg;;
let split_free _A = _A.split_free;;

let ownership_split_relc =
  ({order_bot_ownership_split = order_bot_relc; split_cmb = split_cmb_relc;
     split_rl = split_rl_relc; split_global_at = split_global_at_relc;
     split_rg = split_rg_relc; split_free = split_free_relc}
    : relc ownership_split);;

let bounded_semilattice_sup_bot_relc =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_relc;
     order_bot_bounded_semilattice_sup_bot = order_bot_relc}
    : relc bounded_semilattice_sup_bot);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

type ('a, 'b) gcall_action = CallEdge of 'a option * 'a list * 'b list;;

let rec equal_gcall_actiona _A _B
  (CallEdge (x1, x2, x3)) (CallEdge (y1, y2, y3)) =
    equal_option _A x1 y1 && (equal_lista _A x2 y2 && equal_lista _B x3 y3);;

let rec equal_gcall_action _A _B =
  ({equal = equal_gcall_actiona _A _B} : ('a, 'b) gcall_action equal);;

let rec comparator_option
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, None, None -> Eqa
    | comp_a, None, Some y -> Lt
    | comp_a, Some x, None -> Gt
    | comp_a, Some x, Some y -> comp_a x y;;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, [], [] -> Eqa
    | comp_a, [], y :: ya -> Lt
    | comp_a, x :: xa, [] -> Gt
    | comp_a, x :: xa, y :: ya ->
        (match comp_a x y with Eqa -> comparator_list comp_a xa ya | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_gcall_action
  comp_v comp_e (CallEdge (x, xa, xb)) (CallEdge (y, ya, yb)) =
    (match comparator_option comp_v x y
      with Eqa ->
        (match comparator_list comp_v xa ya
          with Eqa -> comparator_list comp_e xb yb | Lt -> Lt | Gt -> Gt)
      | Lt -> Lt | Gt -> Gt);;

let rec less_eq_gcall_action (_A1, _A2) (_B1, _B2)
  = le_of_comp
      (comparator_gcall_action (comparator_of (_A1, _A2))
        (comparator_of (_B1, _B2)));;

let rec less_gcall_action (_A1, _A2) (_B1, _B2)
  = lt_of_comp
      (comparator_gcall_action (comparator_of (_A1, _A2))
        (comparator_of (_B1, _B2)));;

let rec ord_gcall_action (_A1, _A2) (_B1, _B2) =
  ({less_eq = less_eq_gcall_action (_A1, _A2) (_B1, _B2);
     less = less_gcall_action (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) gcall_action ord);;

let rec preorder_gcall_action (_A1, _A2) (_B1, _B2) =
  ({ord_preorder = (ord_gcall_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gcall_action preorder);;

let rec order_gcall_action (_A1, _A2) (_B1, _B2) =
  ({preorder_order = (preorder_gcall_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gcall_action order);;

let rec linorder_gcall_action (_A1, _A2) (_B1, _B2) =
  ({order_linorder = (order_gcall_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gcall_action linorder);;

type 'a gspecial_call = Nondet_Int | Min of 'a * 'a | Max of 'a * 'a;;

let rec equal_gspecial_call _A
  x0 x1 = match x0, x1 with Min (x21, x22), Max (x31, x32) -> false
    | Max (x31, x32), Min (x21, x22) -> false
    | Nondet_Int, Max (x31, x32) -> false
    | Max (x31, x32), Nondet_Int -> false
    | Nondet_Int, Min (x21, x22) -> false
    | Min (x21, x22), Nondet_Int -> false
    | Max (x31, x32), Max (y31, y32) -> eq _A x31 y31 && eq _A x32 y32
    | Min (x21, x22), Min (y21, y22) -> eq _A x21 y21 && eq _A x22 y22
    | Nondet_Int, Nondet_Int -> true;;

type ('a, 'b) gedge_action = EA_Nop | EA_Assign of 'a * 'b |
  EA_Special of 'b gspecial_call * 'a | EA_Assume of 'b | EA_AssumeNot of 'b |
  EA_Body of string | EA_Ret of 'b option * string |
  EA_Check of (nat * nat) * 'b;;

let rec equal_gedge_actiona _A _B
  x0 x1 = match x0, x1 with EA_Ret (x71, x72), EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Ret (x71, x72) -> false
    | EA_Body x6, EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Body x6 -> false
    | EA_Body x6, EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_Body x6 -> false
    | EA_AssumeNot x5, EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Body x6 -> false
    | EA_Body x6, EA_AssumeNot x5 -> false
    | EA_Assume x4, EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Assume x4 -> false
    | EA_Assume x4, EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_Assume x4 -> false
    | EA_Assume x4, EA_Body x6 -> false
    | EA_Body x6, EA_Assume x4 -> false
    | EA_Assume x4, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assume x4 -> false
    | EA_Special (x31, x32), EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Body x6 -> false
    | EA_Body x6, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assume x4 -> false
    | EA_Assume x4, EA_Special (x31, x32) -> false
    | EA_Assign (x21, x22), EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Body x6 -> false
    | EA_Body x6, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Assume x4 -> false
    | EA_Assume x4, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assign (x21, x22) -> false
    | EA_Nop, EA_Check (x81, x82) -> false
    | EA_Check (x81, x82), EA_Nop -> false
    | EA_Nop, EA_Ret (x71, x72) -> false
    | EA_Ret (x71, x72), EA_Nop -> false
    | EA_Nop, EA_Body x6 -> false
    | EA_Body x6, EA_Nop -> false
    | EA_Nop, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Nop -> false
    | EA_Nop, EA_Assume x4 -> false
    | EA_Assume x4, EA_Nop -> false
    | EA_Nop, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Nop -> false
    | EA_Nop, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Nop -> false
    | EA_Check (x81, x82), EA_Check (y81, y82) ->
        equal_proda equal_nat equal_nat x81 y81 && eq _B x82 y82
    | EA_Ret (x71, x72), EA_Ret (y71, y72) ->
        equal_option _B x71 y71 && ((x72 : string) = y72)
    | EA_Body x6, EA_Body y6 -> ((x6 : string) = y6)
    | EA_AssumeNot x5, EA_AssumeNot y5 -> eq _B x5 y5
    | EA_Assume x4, EA_Assume y4 -> eq _B x4 y4
    | EA_Special (x31, x32), EA_Special (y31, y32) ->
        equal_gspecial_call _B x31 y31 && eq _A x32 y32
    | EA_Assign (x21, x22), EA_Assign (y21, y22) ->
        eq _A x21 y21 && eq _B x22 y22
    | EA_Nop, EA_Nop -> true;;

let rec equal_gedge_action _A _B =
  ({equal = equal_gedge_actiona _A _B} : ('a, 'b) gedge_action equal);;

let rec comparator_prod
  comp_a comp_b (x, xa) (y, ya) =
    (match comp_a x y with Eqa -> comp_b xa ya | Lt -> Lt | Gt -> Gt);;

let rec comparator_gspecial_call
  comp_e x1 x2 = match comp_e, x1, x2 with comp_e, Nondet_Int, Nondet_Int -> Eqa
    | comp_e, Nondet_Int, Min (y, ya) -> Lt
    | comp_e, Nondet_Int, Max (yb, yc) -> Lt
    | comp_e, Min (x, xa), Nondet_Int -> Gt
    | comp_e, Min (x, xa), Min (y, ya) ->
        (match comp_e x y with Eqa -> comp_e xa ya | Lt -> Lt | Gt -> Gt)
    | comp_e, Min (x, xa), Max (yb, yc) -> Lt
    | comp_e, Max (x, xa), Nondet_Int -> Gt
    | comp_e, Max (x, xa), Min (y, ya) -> Gt
    | comp_e, Max (x, xa), Max (yb, yc) ->
        (match comp_e x yb with Eqa -> comp_e xa yc | Lt -> Lt | Gt -> Gt);;

let rec comparator_gedge_action
  comp_v comp_e x2 x3 = match comp_v, comp_e, x2, x3 with
    comp_v, comp_e, EA_Nop, EA_Nop -> Eqa
    | comp_v, comp_e, EA_Nop, EA_Assign (y, ya) -> Lt
    | comp_v, comp_e, EA_Nop, EA_Special (yb, yc) -> Lt
    | comp_v, comp_e, EA_Nop, EA_Assume yd -> Lt
    | comp_v, comp_e, EA_Nop, EA_AssumeNot ye -> Lt
    | comp_v, comp_e, EA_Nop, EA_Body yf -> Lt
    | comp_v, comp_e, EA_Nop, EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_Nop, EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Nop -> Gt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Assign (y, ya) ->
        (match comp_v x y with Eqa -> comp_e xa ya | Lt -> Lt | Gt -> Gt)
    | comp_v, comp_e, EA_Assign (x, xa), EA_Special (yb, yc) -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Assume yd -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_AssumeNot ye -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Body yf -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_Assign (x, xa), EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Special (x, xa), EA_Nop -> Gt
    | comp_v, comp_e, EA_Special (x, xa), EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_Special (x, xa), EA_Special (yb, yc) ->
        (match comparator_gspecial_call comp_e x yb with Eqa -> comp_v xa yc
          | Lt -> Lt | Gt -> Gt)
    | comp_v, comp_e, EA_Special (x, xa), EA_Assume yd -> Lt
    | comp_v, comp_e, EA_Special (x, xa), EA_AssumeNot ye -> Lt
    | comp_v, comp_e, EA_Special (x, xa), EA_Body yf -> Lt
    | comp_v, comp_e, EA_Special (x, xa), EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_Special (x, xa), EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Assume x, EA_Nop -> Gt
    | comp_v, comp_e, EA_Assume x, EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_Assume x, EA_Special (yb, yc) -> Gt
    | comp_v, comp_e, EA_Assume x, EA_Assume yd -> comp_e x yd
    | comp_v, comp_e, EA_Assume x, EA_AssumeNot ye -> Lt
    | comp_v, comp_e, EA_Assume x, EA_Body yf -> Lt
    | comp_v, comp_e, EA_Assume x, EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_Assume x, EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_AssumeNot x, EA_Nop -> Gt
    | comp_v, comp_e, EA_AssumeNot x, EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_AssumeNot x, EA_Special (yb, yc) -> Gt
    | comp_v, comp_e, EA_AssumeNot x, EA_Assume yd -> Gt
    | comp_v, comp_e, EA_AssumeNot x, EA_AssumeNot ye -> comp_e x ye
    | comp_v, comp_e, EA_AssumeNot x, EA_Body yf -> Lt
    | comp_v, comp_e, EA_AssumeNot x, EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_AssumeNot x, EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Body x, EA_Nop -> Gt
    | comp_v, comp_e, EA_Body x, EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_Body x, EA_Special (yb, yc) -> Gt
    | comp_v, comp_e, EA_Body x, EA_Assume yd -> Gt
    | comp_v, comp_e, EA_Body x, EA_AssumeNot ye -> Gt
    | comp_v, comp_e, EA_Body x, EA_Body yf ->
        comparator_of (equal_literal, linorder_literal) x yf
    | comp_v, comp_e, EA_Body x, EA_Ret (yg, yh) -> Lt
    | comp_v, comp_e, EA_Body x, EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Nop -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Special (yb, yc) -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Assume yd -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_AssumeNot ye -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Body yf -> Gt
    | comp_v, comp_e, EA_Ret (x, xa), EA_Ret (yg, yh) ->
        (match comparator_option comp_e x yg
          with Eqa -> comparator_of (equal_literal, linorder_literal) xa yh
          | Lt -> Lt | Gt -> Gt)
    | comp_v, comp_e, EA_Ret (x, xa), EA_Check (yi, yj) -> Lt
    | comp_v, comp_e, EA_Check (x, xa), EA_Nop -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Assign (y, ya) -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Special (yb, yc) -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Assume yd -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_AssumeNot ye -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Body yf -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Ret (yg, yh) -> Gt
    | comp_v, comp_e, EA_Check (x, xa), EA_Check (yi, yj) ->
        (match
          comparator_prod (comparator_of (equal_nat, linorder_nat))
            (comparator_of (equal_nat, linorder_nat)) x yi
          with Eqa -> comp_e xa yj | Lt -> Lt | Gt -> Gt);;

let rec less_eq_gedge_action (_A1, _A2) (_B1, _B2)
  = le_of_comp
      (comparator_gedge_action (comparator_of (_A1, _A2))
        (comparator_of (_B1, _B2)));;

let rec less_gedge_action (_A1, _A2) (_B1, _B2)
  = lt_of_comp
      (comparator_gedge_action (comparator_of (_A1, _A2))
        (comparator_of (_B1, _B2)));;

let rec ord_gedge_action (_A1, _A2) (_B1, _B2) =
  ({less_eq = less_eq_gedge_action (_A1, _A2) (_B1, _B2);
     less = less_gedge_action (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) gedge_action ord);;

let rec preorder_gedge_action (_A1, _A2) (_B1, _B2) =
  ({ord_preorder = (ord_gedge_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gedge_action preorder);;

let rec order_gedge_action (_A1, _A2) (_B1, _B2) =
  ({preorder_order = (preorder_gedge_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gedge_action order);;

let rec linorder_gedge_action (_A1, _A2) (_B1, _B2) =
  ({order_linorder = (order_gedge_action (_A1, _A2) (_B1, _B2))} :
    ('a, 'b) gedge_action linorder);;

type eint = MinInf | Fin of int | PlusInf;;

let rec equal_eint x0 x1 = match x0, x1 with Fin x2, PlusInf -> false
                     | PlusInf, Fin x2 -> false
                     | MinInf, PlusInf -> false
                     | PlusInf, MinInf -> false
                     | MinInf, Fin x2 -> false
                     | Fin x2, MinInf -> false
                     | Fin x2, Fin y2 -> equal_inta x2 y2
                     | PlusInf, PlusInf -> true
                     | MinInf, MinInf -> true;;

type ivl = Ivl of eint * eint;;

let rec equal_ivla
  (Ivl (x1, x2)) (Ivl (y1, y2)) = equal_eint x1 y1 && equal_eint x2 y2;;

let equal_ivl = ({equal = equal_ivla} : ivl equal);;

let rec eint_le x0 uu = match x0, uu with MinInf, uu -> true
                  | Fin v, PlusInf -> true
                  | PlusInf, PlusInf -> true
                  | Fin n, Fin m -> less_eq_int n m
                  | Fin v, MinInf -> false
                  | PlusInf, MinInf -> false
                  | PlusInf, Fin v -> false;;

let rec less_eq_eint x = eint_le x;;

let rec join_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l1 l2 then l1 else l2),
          (if less_eq_eint u2 u1 then u1 else u2));;

let rec sup_ivla x = join_ivl x;;

let sup_ivl = ({sup = sup_ivla} : ivl sup);;

let bot_ivla : ivl = Ivl (PlusInf, MinInf);;

let bot_ivl = ({bot = bot_ivla} : ivl bot);;

let rec less_eq_ivl
  a b = (let (Ivl (l1, u1), Ivl (l2, u2)) = (a, b) in
          less_eq_eint l2 l1 && less_eq_eint u1 u2);;

let rec less_ivl a b = less_eq_ivl a b && not (less_eq_ivl b a);;

let ord_ivl = ({less_eq = less_eq_ivl; less = less_ivl} : ivl ord);;

let ivl_top : ivl = Ivl (MinInf, PlusInf);;

let top_ivla : ivl = ivl_top;;

let top_ivl = ({top = top_ivla} : ivl top);;

let preorder_ivl = ({ord_preorder = ord_ivl} : ivl preorder);;

let order_ivl = ({preorder_order = preorder_ivl} : ivl order);;

let rec widen_ivl_core
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l1 l2 then l1 else MinInf),
          (if less_eq_eint u2 u1 then u1 else PlusInf));;

let rec widen_ivl
  a b = (if equal_ivla a bot_ivla then b
          else (if equal_ivla b bot_ivla then a else widen_ivl_core a b));;

let widening_ivl =
  ({order_widening = order_ivl; widen = widen_ivl} : ivl widening);;

let order_bot_ivl =
  ({bot_order_bot = bot_ivl; order_order_bot = order_ivl} : ivl order_bot);;

let order_top_ivl =
  ({order_order_top = order_ivl; top_order_top = top_ivl} : ivl order_top);;

let rec narrow_ivl_td
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if equal_eint l1 MinInf then l2 else l1),
          (if equal_eint u1 PlusInf then u2 else u1));;

let rec narrow_ivl a b = narrow_ivl_td a b;;

let narrowing_ivl =
  ({order_narrowing = order_ivl; narrow = narrow_ivl} : ivl narrowing);;

let warrowing_ivl =
  ({narrowing_warrowing = narrowing_ivl; widening_warrowing = widening_ivl} :
    ivl warrowing);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

type char = Chr of Z.t;;

let rec char_of_integer
  k = Chr (if Z.leq Z.zero k && Z.lt k (Z.of_int 256) then k
            else modulo_integer k (Z.of_int 256));;

let rec char_of_nat x = comp char_of_integer integer_of_nat x;;

let rec integer_of_char (Chr x) = x;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);;

let rec string_of_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then implode [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else string_of_nat (divide_nat n (nat_of_integer (Z.of_int 10))) ^
               implode
                 [char_of_nat
                    (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                      (nat_of_integer (Z.of_int 48)))]);;

let rec string_of_int
  i = (if less_int i zero_inta then "-" ^ string_of_nat (nat (uminus_inta i))
        else string_of_nat (nat i));;

let rec string_of_eint = function MinInf -> "-" ^ "<infinity>"
                         | PlusInf -> "+" ^ "<infinity>"
                         | Fin n -> string_of_int n;;

let rec is_bottom_ivl
  i = (let Ivl (l, u) = i in
        equal_eint l PlusInf ||
          (equal_eint u MinInf || not (less_eq_eint l u)));;

let rec string_of_ivl
  (Ivl (l, u)) =
    (if is_bottom_ivl (Ivl (l, u)) then "<bottom>"
      else ((("[" ^ string_of_eint l) ^ ",") ^ string_of_eint u) ^ "]");;

let rec is_top_ivl i = equal_ivla i ivl_top;;

let rec to_string_ivl a = (if is_top_ivl a then "<top>" else string_of_ivl a);;

let rec is_empty_ivl a = is_bottom_ivl a;;

let gamma_ivl _ = failwith "Interval_Lattice.gamma_ivl";;

let rec gamma_ivla a = gamma_ivl a;;

let rec ik_lo k = Fin (ik_min k);;

let rec ik_hi k = Fin (ik_max k);;

let rec narrow_ivl_ik
  k (Ivl (l0, u0)) (Ivl (l1, u1)) =
    Ivl ((if equal_eint l0 (ik_lo k) then l1 else l0),
          (if equal_eint u0 (ik_hi k) then u1 else u0));;

let rec narrow_ik_ivl x = narrow_ivl_ik x;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eint a b = eint_le a b && not (eint_le b a);;

let ord_eint = ({less_eq = less_eq_eint; less = less_eint} : eint ord);;

let rec widen_ivl_ik
  k (Ivl (l0, u0)) (Ivl (l1, u1)) =
    Ivl ((if less_eq_eint l0 l1 then l0 else min ord_eint (ik_lo k) l1),
          (if less_eq_eint u1 u0 then u0 else max ord_eint (ik_hi k) u1));;

let rec widen_ik_ivl
  k a b =
    (if equal_ivla a bot_ivla then b
      else (if equal_ivla b bot_ivla then a else widen_ivl_ik k a b));;

let rec inf_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l2 l1 then l1 else l2),
          (if less_eq_eint u1 u2 then u1 else u2));;

let rec empty_ik_ivl k a = is_bottom_ivl (inf_ivl a (Ivl (ik_lo k, ik_hi k)));;

let semilattice_sup_ivl =
  ({sup_semilattice_sup = sup_ivl; order_semilattice_sup = order_ivl} :
    ivl semilattice_sup);;

let bounded_semilattice_sup_bot_ivl =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_ivl;
     order_bot_bounded_semilattice_sup_bot = order_bot_ivl}
    : ivl bounded_semilattice_sup_bot);;

let executable_domain_ivl =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_ivl;
     order_top_executable_domain = order_top_ivl;
     warrowing_executable_domain = warrowing_ivl; is_empty = is_empty_ivl;
     to_string = to_string_ivl}
    : ivl executable_domain);;

let numeric_domain_ivl =
  ({executable_domain_numeric_domain = executable_domain_ivl;
     gamma = gamma_ivla}
    : ivl numeric_domain);;

let ik_domain_ivl =
  ({numeric_domain_ik_domain = numeric_domain_ivl; widen_ik = widen_ik_ivl;
     narrow_ik = narrow_ik_ivl; empty_ik = empty_ik_ivl}
    : ivl ik_domain);;

let rec ivl_times_core
  uu uv = match uu, uv with
    Ivl (Fin l1, Fin u1), Ivl (Fin l2, Fin u2) ->
      Ivl (Fin (min ord_int (times_inta l1 l2)
                 (min ord_int (times_inta l1 u2)
                   (min ord_int (times_inta u1 l2) (times_inta u1 u2)))),
            Fin (max ord_int (times_inta l1 l2)
                  (max ord_int (times_inta l1 u2)
                    (max ord_int (times_inta u1 l2) (times_inta u1 u2)))))
    | Ivl (MinInf, va), uv -> ivl_top
    | Ivl (PlusInf, va), uv -> ivl_top
    | Ivl (v, MinInf), uv -> ivl_top
    | Ivl (v, PlusInf), uv -> ivl_top
    | uu, Ivl (MinInf, va) -> ivl_top
    | uu, Ivl (PlusInf, va) -> ivl_top
    | uu, Ivl (v, MinInf) -> ivl_top
    | uu, Ivl (v, PlusInf) -> ivl_top;;

let rec ivl_nonempty
  (Ivl (l, u)) =
    less_eq_eint l u &&
      (not (equal_eint l PlusInf) && not (equal_eint u MinInf));;

let rec times_ivl
  a b = (if ivl_nonempty a && ivl_nonempty b then ivl_times_core a b
          else bot_ivla);;

let rec minus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (minus_inta n m)
    | Fin uu, MinInf -> PlusInf
    | Fin uv, PlusInf -> MinInf
    | MinInf, MinInf -> MinInf
    | MinInf, Fin uw -> MinInf
    | MinInf, PlusInf -> MinInf
    | PlusInf, MinInf -> PlusInf
    | PlusInf, Fin ux -> PlusInf
    | PlusInf, PlusInf -> PlusInf;;

let rec normalize_ivl
  v = (let Ivl (l, u) = v in
        (if less_eq_eint l u &&
              (not (equal_eint l PlusInf) && not (equal_eint u MinInf))
          then v else bot_ivla));;

let rec minus_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    (let (Ivl (a, b), Ivl (c, d)) =
       (normalize_ivl (Ivl (l1, u1)), normalize_ivl (Ivl (l2, u2))) in
      normalize_ivl (Ivl (minus_eint a d, minus_eint b c)));;

let rec plus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (plus_inta n m)
    | Fin uu, MinInf -> MinInf
    | Fin uv, PlusInf -> PlusInf
    | MinInf, MinInf -> MinInf
    | MinInf, Fin uw -> MinInf
    | MinInf, PlusInf -> MinInf
    | PlusInf, MinInf -> PlusInf
    | PlusInf, Fin ux -> PlusInf
    | PlusInf, PlusInf -> PlusInf;;

let rec plus_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    (let (Ivl (a, b), Ivl (c, d)) =
       (normalize_ivl (Ivl (l1, u1)), normalize_ivl (Ivl (l2, u2))) in
      normalize_ivl (Ivl (plus_eint a c, plus_eint b d)));;

let rec ivl_mod_bound
  = function
    Ivl (Fin l, Fin u) ->
      (if less_int zero_inta l || less_int u zero_inta
        then Ivl (Fin (minus_inta one_inta
                        (max ord_int (abs_int l) (abs_int u))),
                   Fin (minus_inta (max ord_int (abs_int l) (abs_int u))
                         one_inta))
        else ivl_top)
    | Ivl (MinInf, va) -> ivl_top
    | Ivl (PlusInf, va) -> ivl_top
    | Ivl (v, MinInf) -> ivl_top
    | Ivl (v, PlusInf) -> ivl_top;;

let rec intersect_ivl a b = normalize_ivl (inf_ivl a b);;

let rec ivl_positive_part a = intersect_ivl a (Ivl (Fin one_inta, PlusInf));;

let rec c_div
  a b = (if equal_inta b zero_inta then zero_inta
          else times_inta (times_inta (sgn_int a) (sgn_int b))
                 (divide_inta (abs_int a) (abs_int b)));;

let rec ivl_div_positive_core
  a b = match a, b with
    Ivl (Fin l, Fin u), Ivl (Fin c, Fin d) ->
      (if less_int zero_inta c
        then Ivl (Fin (min ord_int (c_div l c) (c_div l d)),
                   Fin (max ord_int (c_div u c) (c_div u d)))
        else ivl_top)
    | Ivl (MinInf, va), b ->
        (if equal_ivla b (Ivl (Fin one_inta, Fin one_inta))
          then Ivl (MinInf, va) else ivl_top)
    | Ivl (PlusInf, va), b ->
        (if equal_ivla b (Ivl (Fin one_inta, Fin one_inta))
          then Ivl (PlusInf, va) else ivl_top)
    | Ivl (v, MinInf), b ->
        (if equal_ivla b (Ivl (Fin one_inta, Fin one_inta)) then Ivl (v, MinInf)
          else ivl_top)
    | Ivl (v, PlusInf), b ->
        (if equal_ivla b (Ivl (Fin one_inta, Fin one_inta))
          then Ivl (v, PlusInf) else ivl_top)
    | a, Ivl (MinInf, va) ->
        (if equal_ivla (Ivl (MinInf, va)) (Ivl (Fin one_inta, Fin one_inta))
          then a else ivl_top)
    | a, Ivl (PlusInf, va) ->
        (if equal_ivla (Ivl (PlusInf, va)) (Ivl (Fin one_inta, Fin one_inta))
          then a else ivl_top)
    | a, Ivl (v, MinInf) ->
        (if equal_ivla (Ivl (v, MinInf)) (Ivl (Fin one_inta, Fin one_inta))
          then a else ivl_top)
    | a, Ivl (v, PlusInf) ->
        (if equal_ivla (Ivl (v, PlusInf)) (Ivl (Fin one_inta, Fin one_inta))
          then a else ivl_top);;

let rec ivl_div_positive
  a b = (if ivl_nonempty a && ivl_nonempty b
          then normalize_ivl (ivl_div_positive_core a b) else bot_ivla);;

let rec ivl_zero_part a = intersect_ivl a (Ivl (Fin zero_inta, Fin zero_inta));;

let rec ivl_div
  a b = (if ivl_nonempty a && ivl_nonempty b
          then sup_ivla
                 (sup_ivla (ivl_div_positive a (ivl_positive_part b))
                   (ivl_div_positive
                     (minus_ivl (Ivl (Fin zero_inta, Fin zero_inta)) a)
                     (ivl_positive_part
                       (minus_ivl (Ivl (Fin zero_inta, Fin zero_inta)) b))))
                 (ivl_zero_part b)
          else bot_ivla);;

let rec ivl_mod
  a b = (if ivl_nonempty a && ivl_nonempty b
          then intersect_ivl (minus_ivl a (times_ivl (ivl_div a b) b))
                 (intersect_ivl
                   (sup_ivla a (Ivl (Fin zero_inta, Fin zero_inta)))
                   (ivl_mod_bound b))
          else bot_ivla);;

let rec ivl_aop x0 a b = match x0, a, b with AAdd, a, b -> plus_ivl a b
                  | ASub, a, b -> minus_ivl a b
                  | AMul, a, b -> times_ivl a b
                  | ADiv, a, b -> ivl_div a b
                  | AMod, a, b -> ivl_mod a b;;

let rec raw_aop_ik_ivl x = ivl_aop x;;

let rec ivl_lo (Ivl (l, u)) = l;;

let rec ivl_hi (Ivl (l, u)) = u;;

let rec ivl_lt_bounds
  a b = (inf_ivl a (Ivl (MinInf, minus_eint (ivl_hi b) (Fin one_inta))),
          inf_ivl b (Ivl (plus_eint (ivl_lo a) (Fin one_inta), PlusInf)));;

let rec ivl_le_bounds
  a b = (inf_ivl a (Ivl (MinInf, ivl_hi b)),
          inf_ivl b (Ivl (ivl_lo a, PlusInf)));;

let rec swap p = (snd p, fst p);;

let rec ivl_refine x0 a b = match x0, a, b with CLt, a, b -> ivl_lt_bounds a b
                     | CLe, a, b -> ivl_le_bounds a b
                     | CGt, a, b -> swap (ivl_lt_bounds b a)
                     | CGe, a, b -> swap (ivl_le_bounds b a)
                     | CEq, a, b -> (inf_ivl a b, inf_ivl a b)
                     | CNe, a, b -> (a, b);;

let rec refine_ik_ivl x = ivl_refine x;;

let rec of_int_ik_ivl k n = Ivl (Fin (ik_norm k n), Fin (ik_norm k n));;

let rec ik_ivl k = Ivl (ik_lo k, ik_hi k);;

let rec wrap_ivl_ik
  k x y =
    (if less_int (minus_inta y x) (ik_mod k) &&
          less_eq_int (ik_norm k x) (ik_norm k y)
      then Ivl (Fin (ik_norm k x), Fin (ik_norm k y)) else ik_ivl k);;

let rec norm_ivl_ik
  k a = (if less_eq_ivl a (ik_ivl k) then a
          else (match a with Ivl (MinInf, _) -> ik_ivl k
                 | Ivl (Fin _, MinInf) -> ik_ivl k
                 | Ivl (Fin x, Fin y) ->
                   (if ik_signed k then ik_ivl k else wrap_ivl_ik k x y)
                 | Ivl (Fin _, PlusInf) -> ik_ivl k
                 | Ivl (PlusInf, _) -> ik_ivl k));;

let rec arith_ik_ivl k op a b = norm_ivl_ik k (ivl_aop op a b);;

let rec meet_ik_ivl a b = inf_ivl a b;;

let rec fits_ik_ivl k a = less_eq_ivl a (ik_ivl k);;

let rec cast_ik_ivl sk = norm_ivl_ik;;

let rec top_ik_ivl x = ik_ivl x;;

let rec interval_less_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || less_eq_eint u2 l1);;

let rec interval_less_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u1 l2);;

let rec ivl_lt
  a b = (if interval_less_true a b then Some true
          else (if interval_less_false a b then Some false else None));;

let rec interval_eq_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || (less_eint u1 l2 || less_eint u2 l1));;

let rec interval_eq_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) ||
        equal_eint l1 u1 && (equal_eint l2 u2 && equal_eint l1 l2));;

let rec ivl_eq
  a b = (if interval_eq_true a b then Some true
          else (if interval_eq_false a b then Some false else None));;

let rec ivl_cop x0 a b = match x0, a, b with CLt, a, b -> ivl_lt a b
                  | CGt, a, b -> ivl_lt b a
                  | CLe, a, b -> map_option not (ivl_lt b a)
                  | CGe, a, b -> map_option not (ivl_lt a b)
                  | CEq, a, b -> ivl_eq a b
                  | CNe, a, b -> map_option not (ivl_eq a b);;

let rec cmp_ik_ivl x = ivl_cop x;;

let kind_int_domain_ivl =
  ({ik_domain_kind_int_domain = ik_domain_ivl; top_ik = top_ik_ivl;
     of_int_ik = of_int_ik_ivl; cast_ik = cast_ik_ivl; arith_ik = arith_ik_ivl;
     cmp_ik = cmp_ik_ivl; meet_ik = meet_ik_ivl; refine_ik = refine_ik_ivl;
     raw_aop_ik = raw_aop_ik_ivl; fits_ik = fits_ik_ivl}
    : ivl kind_int_domain);;

type 'a gquery = EvalInt of 'a;;

let rec equal_gquerya _A (EvalInt x) (EvalInt ya) = eq _A x ya;;

let rec equal_gquery _A = ({equal = equal_gquerya _A} : 'a gquery equal);;

type parity = PBot | PEven | POdd | PTop;;

let rec equal_paritya x0 x1 = match x0, x1 with POdd, PTop -> false
                        | PTop, POdd -> false
                        | PEven, PTop -> false
                        | PTop, PEven -> false
                        | PEven, POdd -> false
                        | POdd, PEven -> false
                        | PBot, PTop -> false
                        | PTop, PBot -> false
                        | PBot, POdd -> false
                        | POdd, PBot -> false
                        | PBot, PEven -> false
                        | PEven, PBot -> false
                        | PTop, PTop -> true
                        | POdd, POdd -> true
                        | PEven, PEven -> true
                        | PBot, PBot -> true;;

let equal_parity = ({equal = equal_paritya} : parity equal);;

let rec join_parity x0 b = match x0, b with PBot, b -> b
                      | PEven, PBot -> PEven
                      | POdd, PBot -> POdd
                      | PTop, PBot -> PTop
                      | PTop, PEven -> PTop
                      | PTop, POdd -> PTop
                      | PTop, PTop -> PTop
                      | PEven, PTop -> PTop
                      | POdd, PTop -> PTop
                      | PEven, PEven -> PEven
                      | POdd, POdd -> POdd
                      | PEven, POdd -> PTop
                      | POdd, PEven -> PTop;;

let rec sup_paritya x = join_parity x;;

let sup_parity = ({sup = sup_paritya} : parity sup);;

let bot_paritya : parity = PBot;;

let bot_parity = ({bot = bot_paritya} : parity bot);;

let rec parity_le x0 uu = match x0, uu with PBot, uu -> true
                    | PEven, PTop -> true
                    | POdd, PTop -> true
                    | PTop, PTop -> true
                    | PEven, PEven -> true
                    | POdd, POdd -> true
                    | PEven, PBot -> false
                    | PEven, POdd -> false
                    | POdd, PBot -> false
                    | POdd, PEven -> false
                    | PTop, PBot -> false
                    | PTop, PEven -> false
                    | PTop, POdd -> false;;

let rec less_eq_parity a b = parity_le a b;;

let rec less_parity a b = parity_le a b && not (parity_le b a);;

let ord_parity = ({less_eq = less_eq_parity; less = less_parity} : parity ord);;

let top_paritya : parity = PTop;;

let top_parity = ({top = top_paritya} : parity top);;

let preorder_parity = ({ord_preorder = ord_parity} : parity preorder);;

let order_parity = ({preorder_order = preorder_parity} : parity order);;

let rec widen_parity a b = join_parity a b;;

let widening_parity =
  ({order_widening = order_parity; widen = widen_parity} : parity widening);;

let order_bot_parity =
  ({bot_order_bot = bot_parity; order_order_bot = order_parity} :
    parity order_bot);;

let order_top_parity =
  ({order_order_top = order_parity; top_order_top = top_parity} :
    parity order_top);;

let rec narrow_parity a b = a;;

let narrowing_parity =
  ({order_narrowing = order_parity; narrow = narrow_parity} :
    parity narrowing);;

let warrowing_parity =
  ({narrowing_warrowing = narrowing_parity;
     widening_warrowing = widening_parity}
    : parity warrowing);;

let rec string_of_parity = function PBot -> "<bottom>"
                           | PEven -> "2" ^ "<int>"
                           | POdd -> "1+2" ^ "<int>"
                           | PTop -> "<int>";;

let rec is_top_parity p = equal_paritya p PTop;;

let rec to_string_parity
  a = (if is_top_parity a then "<top>" else string_of_parity a);;

let rec is_bottom_parity p = equal_paritya p PBot;;

let rec is_empty_parity a = is_bottom_parity a;;

let gamma_parity _ = failwith "Parity_Lattice.gamma_parity";;

let rec gamma_paritya a = gamma_parity a;;

let rec inf_parity
  x0 b = match x0, b with PTop, b -> b
    | PBot, PTop -> PBot
    | PEven, PTop -> PEven
    | POdd, PTop -> POdd
    | PBot, PBot -> (if equal_paritya PBot PBot then PBot else PBot)
    | PBot, PEven -> (if equal_paritya PBot PEven then PBot else PBot)
    | PBot, POdd -> (if equal_paritya PBot POdd then PBot else PBot)
    | PEven, PBot -> (if equal_paritya PEven PBot then PEven else PBot)
    | PEven, PEven -> (if equal_paritya PEven PEven then PEven else PBot)
    | PEven, POdd -> (if equal_paritya PEven POdd then PEven else PBot)
    | POdd, PBot -> (if equal_paritya POdd PBot then POdd else PBot)
    | POdd, PEven -> (if equal_paritya POdd PEven then POdd else PBot)
    | POdd, POdd -> (if equal_paritya POdd POdd then POdd else PBot);;

let rec narrow_ik_parity k a b = inf_parity a b;;

let rec widen_ik_parity k a b = sup_paritya a b;;

let rec empty_ik_parity k a = equal_paritya a PBot;;

let semilattice_sup_parity =
  ({sup_semilattice_sup = sup_parity; order_semilattice_sup = order_parity} :
    parity semilattice_sup);;

let bounded_semilattice_sup_bot_parity =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_parity;
     order_bot_bounded_semilattice_sup_bot = order_bot_parity}
    : parity bounded_semilattice_sup_bot);;

let executable_domain_parity =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_parity;
     order_top_executable_domain = order_top_parity;
     warrowing_executable_domain = warrowing_parity; is_empty = is_empty_parity;
     to_string = to_string_parity}
    : parity executable_domain);;

let numeric_domain_parity =
  ({executable_domain_numeric_domain = executable_domain_parity;
     gamma = gamma_paritya}
    : parity numeric_domain);;

let ik_domain_parity =
  ({numeric_domain_ik_domain = numeric_domain_parity;
     widen_ik = widen_ik_parity; narrow_ik = narrow_ik_parity;
     empty_ik = empty_ik_parity}
    : parity ik_domain);;

let rec times_parity x0 uu = match x0, uu with PBot, uu -> PBot
                       | PEven, PBot -> PBot
                       | POdd, PBot -> PBot
                       | PTop, PBot -> PBot
                       | PEven, PEven -> PEven
                       | PEven, POdd -> PEven
                       | PEven, PTop -> PEven
                       | POdd, PEven -> PEven
                       | PTop, PEven -> PEven
                       | POdd, POdd -> POdd
                       | POdd, PTop -> PTop
                       | PTop, POdd -> PTop
                       | PTop, PTop -> PTop;;

let rec minus_parity x0 uu = match x0, uu with PBot, uu -> PBot
                       | PEven, PBot -> PBot
                       | POdd, PBot -> PBot
                       | PTop, PBot -> PBot
                       | PEven, PEven -> PEven
                       | POdd, POdd -> PEven
                       | PEven, POdd -> POdd
                       | POdd, PEven -> POdd
                       | PEven, PTop -> PTop
                       | POdd, PTop -> PTop
                       | PTop, PEven -> PTop
                       | PTop, POdd -> PTop
                       | PTop, PTop -> PTop;;

let rec plus_parity x0 uu = match x0, uu with PBot, uu -> PBot
                      | PEven, PBot -> PBot
                      | POdd, PBot -> PBot
                      | PTop, PBot -> PBot
                      | PEven, PEven -> PEven
                      | POdd, POdd -> PEven
                      | PEven, POdd -> POdd
                      | POdd, PEven -> POdd
                      | PEven, PTop -> PTop
                      | POdd, PTop -> PTop
                      | PTop, PEven -> PTop
                      | PTop, POdd -> PTop
                      | PTop, PTop -> PTop;;

let rec parity_mod
  a b = (if equal_paritya a PBot || equal_paritya b PBot then PBot
          else (if equal_paritya b PEven then a else PTop));;

let rec parity_div
  a b = (if equal_paritya a PBot || equal_paritya b PBot then PBot else PTop);;

let rec parity_aop x0 a b = match x0, a, b with AAdd, a, b -> plus_parity a b
                     | ASub, a, b -> minus_parity a b
                     | AMul, a, b -> times_parity a b
                     | ADiv, a, b -> parity_div a b
                     | AMod, a, b -> parity_mod a b;;

let rec raw_aop_ik_parity x = parity_aop x;;

let rec refine_ik_parity
  c a b =
    (if equal_cop c CEq then (inf_parity a b, inf_parity a b) else (a, b));;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo
            _A2.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
            b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec parity_of_int
  n = (if dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2)) n
        then PEven else POdd);;

let rec of_int_ik_parity k n = parity_of_int (ik_norm k n);;

let rec arith_ik_parity k = parity_aop;;

let rec meet_ik_parity a b = inf_parity a b;;

let rec fits_ik_parity k a = equal_paritya a PBot;;

let rec cast_ik_parity sk k a = a;;

let rec top_ik_parity k = PTop;;

let rec parity_eqb uu uv = match uu, uv with PEven, POdd -> Some false
                     | POdd, PEven -> Some false
                     | PBot, uv -> None
                     | POdd, PBot -> None
                     | POdd, POdd -> None
                     | POdd, PTop -> None
                     | PTop, uv -> None
                     | uu, PBot -> None
                     | PEven, PEven -> None
                     | uu, PTop -> None;;

let rec parity_cop x0 a b = match x0, a, b with CEq, a, b -> parity_eqb a b
                     | CNe, a, b -> map_option not (parity_eqb a b)
                     | CLt, a, b -> None
                     | CLe, a, b -> None
                     | CGt, a, b -> None
                     | CGe, a, b -> None;;

let rec cmp_ik_parity x = parity_cop x;;

let kind_int_domain_parity =
  ({ik_domain_kind_int_domain = ik_domain_parity; top_ik = top_ik_parity;
     of_int_ik = of_int_ik_parity; cast_ik = cast_ik_parity;
     arith_ik = arith_ik_parity; cmp_ik = cmp_ik_parity;
     meet_ik = meet_ik_parity; refine_ik = refine_ik_parity;
     raw_aop_ik = raw_aop_ik_parity; fits_ik = fits_ik_parity}
    : parity kind_int_domain);;

type 'a query_lift = QBot | QLifted of 'a | QTop;;

let rec top_query_lifta _A = QTop;;

let rec top_query_lift _A = ({top = top_query_lifta _A} : 'a query_lift top);;

type congruence = Abs_congruence of (int * int) option;;

let rec rep_congruence (Abs_congruence x) = x;;

let rec equal_congruencea
  a b = equal_option (equal_prod equal_int equal_int) (rep_congruence a)
          (rep_congruence b);;

type int_tuple = IT of ivl * congruence;;

let rec equal_int_tuplea
  (IT (x1, x2)) (IT (y1, y2)) = equal_ivla x1 y1 && equal_congruencea x2 y2;;

let equal_int_tuple = ({equal = equal_int_tuplea} : int_tuple equal);;

let rec normalize_congruence_rep
  = function None -> None
    | Some (c, m) ->
        (if equal_inta m zero_inta then Some (c, zero_inta)
          else (let p = abs_int m in
                let r = modulo_inta c p in
                 Some (r, p)));;

let rec join_congruence_rep
  x0 y = match x0, y with None, y -> y
    | Some v, None -> Some v
    | Some (c1, m1), Some (c2, m2) ->
        Some (c1, gcd_intc m1 (gcd_intc m2 (minus_inta c1 c2)));;

let rec join_congruence
  xb xc =
    Abs_congruence
      (normalize_congruence_rep
        (join_congruence_rep (rep_congruence xb) (rep_congruence xc)));;

let rec sup_congruencea x = join_congruence x;;

let rec it_cong (IT (x1, x2)) = x2;;

let rec it_ivl (IT (x1, x2)) = x1;;

let rec sup_int_tuplea
  a b = IT (sup_ivla (it_ivl a) (it_ivl b),
             sup_congruencea (it_cong a) (it_cong b));;

let sup_int_tuple = ({sup = sup_int_tuplea} : int_tuple sup);;

let bottom_congruence : congruence = Abs_congruence None;;

let bot_congruencea : congruence = bottom_congruence;;

let bot_int_tuplea : int_tuple = IT (bot_ivla, bot_congruencea);;

let bot_int_tuple = ({bot = bot_int_tuplea} : int_tuple bot);;

let rec congruence_le_rep
  x0 uu = match x0, uu with None, uu -> true
    | Some uv, None -> false
    | Some (c1, m1), Some (c2, m2) ->
        dvd (equal_int, semidom_modulo_int) m2 m1 &&
          dvd (equal_int, semidom_modulo_int) m2 (minus_inta c1 c2);;

let rec congruence_le
  a b = congruence_le_rep (rep_congruence a) (rep_congruence b);;

let rec less_eq_congruence a b = congruence_le a b;;

let rec less_eq_int_tuple
  a b = less_eq_ivl (it_ivl a) (it_ivl b) &&
          less_eq_congruence (it_cong a) (it_cong b);;

let rec less_int_tuple
  a b = less_eq_int_tuple a b && not (less_eq_int_tuple b a);;

let ord_int_tuple =
  ({less_eq = less_eq_int_tuple; less = less_int_tuple} : int_tuple ord);;

let rec mk_congruence
  xb xc = Abs_congruence (normalize_congruence_rep (Some (xb, xc)));;

let top_congruencea : congruence = mk_congruence zero_inta one_inta;;

let top_int_tuplea : int_tuple = IT (top_ivla, top_congruencea);;

let top_int_tuple = ({top = top_int_tuplea} : int_tuple top);;

let preorder_int_tuple = ({ord_preorder = ord_int_tuple} : int_tuple preorder);;

let order_int_tuple =
  ({preorder_order = preorder_int_tuple} : int_tuple order);;

let rec widen_congruence a b = join_congruence a b;;

let rec widen_int_tuple
  a b = IT (widen_ivl (it_ivl a) (it_ivl b),
             widen_congruence (it_cong a) (it_cong b));;

let widening_int_tuple =
  ({order_widening = order_int_tuple; widen = widen_int_tuple} :
    int_tuple widening);;

let order_bot_int_tuple =
  ({bot_order_bot = bot_int_tuple; order_order_bot = order_int_tuple} :
    int_tuple order_bot);;

let order_top_int_tuple =
  ({order_order_top = order_int_tuple; top_order_top = top_int_tuple} :
    int_tuple order_top);;

let rec narrow_congruence_td a b = a;;

let rec narrow_congruence a b = narrow_congruence_td a b;;

let rec narrow_int_tuple
  a b = IT (narrow_ivl (it_ivl a) (it_ivl b),
             narrow_congruence (it_cong a) (it_cong b));;

let narrowing_int_tuple =
  ({order_narrowing = order_int_tuple; narrow = narrow_int_tuple} :
    int_tuple narrowing);;

let warrowing_int_tuple =
  ({narrowing_warrowing = narrowing_int_tuple;
     widening_warrowing = widening_int_tuple}
    : int_tuple warrowing);;

let rec string_of_congruence
  c = (match rep_congruence c with None -> "<bottom>"
        | Some (r, m) ->
          (if equal_inta m zero_inta then string_of_int r
            else ((if equal_inta r zero_inta then ""
                    else string_of_int r ^ "+") ^
                   (if equal_inta m one_inta then "" else string_of_int m)) ^
                   "<int>"));;

let rec is_top_congruence a = equal_congruencea a top_congruencea;;

let rec to_string_congruence
  a = (if is_top_congruence a then "<top>" else string_of_congruence a);;

let rec to_string_int_tuple
  a = (("intervals:" ^ to_string_ivl (it_ivl a)) ^ "; congruences:") ^
        to_string_congruence (it_cong a);;

let rec ivl_upper (Ivl (x1, x2)) = x2;;

let rec ivl_lower (Ivl (x1, x2)) = x1;;

let rec cong_meets
  (c, m) l u =
    (if equal_inta m zero_inta
      then less_eq_eint l (Fin c) && less_eq_eint (Fin c) u
      else (match (l, u) with (MinInf, MinInf) -> false
             | (MinInf, Fin _) -> true | (MinInf, PlusInf) -> true
             | (Fin _, MinInf) -> false
             | (Fin x, Fin a) ->
               less_eq_int (plus_inta x (modulo_inta (minus_inta c x) m)) a
             | (Fin _, PlusInf) -> true | (PlusInf, _) -> false));;

let rec it_empty
  i c = (match rep_congruence c with None -> true
          | Some cm -> not (cong_meets cm (ivl_lower i) (ivl_upper i)));;

let rec is_empty_int_tuple a = it_empty (it_ivl a) (it_cong a);;

let gamma_congruence _ = failwith "Congruence_Lattice.gamma_congruence";;

let rec gamma_it
  a = inf_set equal_int (gamma_ivl (it_ivl a)) (gamma_congruence (it_cong a));;

let rec gamma_int_tuple x = gamma_it x;;

let rec euclid_ext_aux (_A1, _A2)
  sa s ta t ra r =
    (if eq _A2 r
          (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
      then (let c =
              divide
                _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo.divide_modulo
                (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
                (unit_factor
                  _A1.factorial_ring_gcd_euclidean_ring_gcd.ring_gcd_factorial_ring_gcd.semiring_gcd_ring_gcd.normalization_semidom_semiring_gcd.semidom_divide_unit_factor_normalization_semidom.unit_factor_semidom_divide_unit_factor
                  ra)
              in
             ((times _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                 sa c,
                times _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                  ta c),
               normalize
                 _A1.factorial_ring_gcd_euclidean_ring_gcd.ring_gcd_factorial_ring_gcd.semiring_gcd_ring_gcd.normalization_semidom_semiring_gcd
                 ra))
      else (let q =
              divide
                _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo.divide_modulo
                ra r
              in
             euclid_ext_aux (_A1, _A2) s
               (minus
                 _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.idom_divide_idom_modulo.idom_idom_divide.comm_ring_1_idom.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.minus_group_add
                 sa (times
                      _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                      q s))
               t (minus
                   _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.idom_divide_idom_modulo.idom_idom_divide.comm_ring_1_idom.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.minus_group_add
                   ta (times
                        _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                        q t))
               r (modulo
                   _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
                   ra r)));;

let rec bezout_coefficients (_A1, _A2)
  a b = fst (euclid_ext_aux (_A1, _A2)
              (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
              (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
              (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
              (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
              a b);;

let rec intersect_congruence_rep
  x0 y = match x0, y with None, y -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep
          (if equal_inta m1 zero_inta
            then (if dvd (equal_int, semidom_modulo_int) m2 (minus_inta c1 c2)
                   then Some (c1, zero_inta) else None)
            else (if equal_inta m2 zero_inta
                   then (if dvd (equal_int, semidom_modulo_int) m1
                              (minus_inta c2 c1)
                          then Some (c2, zero_inta) else None)
                   else (let g = gcd_intc m1 m2 in
                          (if dvd (equal_int, semidom_modulo_int) g
                                (minus_inta c2 c1)
                            then (let s =
                                    fst (bezout_coefficients
  (euclidean_ring_gcd_int, equal_int) m1 m2)
                                    in
                                  let q = divide_inta (minus_inta c2 c1) g in
                                   Some (plus_inta c1
   (times_inta m1 (times_inta q s)),
  lcm_inta m1 m2))
                            else None))));;

let rec inf_congruence
  xb xc =
    Abs_congruence
      (intersect_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec narrow_ik_congruence k a b = inf_congruence a b;;

let rec narrow_ik_int_tuple
  k a b =
    IT (narrow_ik_ivl k (it_ivl a) (it_ivl b),
         narrow_ik_congruence k (it_cong a) (it_cong b));;

let rec widen_ik_congruence k a b = sup_congruencea a b;;

let rec widen_ik_int_tuple
  k a b =
    IT (widen_ik_ivl k (it_ivl a) (it_ivl b),
         widen_ik_congruence k (it_cong a) (it_cong b));;

let rec empty_ik_int_tuple
  k a = it_empty (inf_ivl (it_ivl a) (ik_ivl k)) (it_cong a);;

let semilattice_sup_int_tuple =
  ({sup_semilattice_sup = sup_int_tuple;
     order_semilattice_sup = order_int_tuple}
    : int_tuple semilattice_sup);;

let bounded_semilattice_sup_bot_int_tuple =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_int_tuple;
     order_bot_bounded_semilattice_sup_bot = order_bot_int_tuple}
    : int_tuple bounded_semilattice_sup_bot);;

let executable_domain_int_tuple =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_int_tuple;
     order_top_executable_domain = order_top_int_tuple;
     warrowing_executable_domain = warrowing_int_tuple;
     is_empty = is_empty_int_tuple; to_string = to_string_int_tuple}
    : int_tuple executable_domain);;

let numeric_domain_int_tuple =
  ({executable_domain_numeric_domain = executable_domain_int_tuple;
     gamma = gamma_int_tuple}
    : int_tuple numeric_domain);;

let ik_domain_int_tuple =
  ({numeric_domain_ik_domain = numeric_domain_int_tuple;
     widen_ik = widen_ik_int_tuple; narrow_ik = narrow_ik_int_tuple;
     empty_ik = empty_ik_int_tuple}
    : int_tuple ik_domain);;

let rec times_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep
          (Some (times_inta c1 c2,
                  gcd_intc (times_inta c1 m2)
                    (gcd_intc (times_inta m1 c2) (times_inta m1 m2))));;

let rec times_congruence
  xb xc =
    Abs_congruence
      (times_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec minus_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep (Some (minus_inta c1 c2, gcd_intc m1 m2));;

let rec minus_congruence
  xb xc =
    Abs_congruence
      (minus_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec plus_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep (Some (plus_inta c1 c2, gcd_intc m1 m2));;

let rec plus_congruence
  xb xc =
    Abs_congruence
      (plus_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec is_bottom_congruence a = equal_congruencea a bot_congruencea;;

let rec is_empty_congruence a = is_bottom_congruence a;;

let rec congruence_singleton
  a = (match rep_congruence a with None -> None
        | Some (c, m) -> (if equal_inta m zero_inta then Some c else None));;

let rec congruence_of_int n = mk_congruence n zero_inta;;

let rec congruence_exact_binop
  f fallback a b =
    (if is_empty_congruence a || is_empty_congruence b then bot_congruencea
      else (match (congruence_singleton a, congruence_singleton b)
             with (None, _) -> fallback a b | (Some _, None) -> fallback a b
             | (Some x, Some y) -> congruence_of_int (f x y)));;

let rec c_mod
  a b = (if equal_inta b zero_inta then a
          else minus_inta a (times_inta (c_div a b) b));;

let rec congruence_mod
  x = congruence_exact_binop c_mod
        (fun a b -> minus_congruence a (times_congruence top_congruencea b)) x;;

let rec congruence_divides
  d a = (match rep_congruence a with None -> true
          | Some (c, m) ->
            dvd (equal_int, semidom_modulo_int) d c &&
              dvd (equal_int, semidom_modulo_int) d m);;

let rec congruence_div_const
  a d = (match rep_congruence a with None -> bot_congruencea
          | Some (c, m) ->
            (if equal_inta d zero_inta then congruence_of_int zero_inta
              else (if congruence_divides d a
                     then mk_congruence (divide_inta c d) (divide_inta m d)
                     else top_congruencea)));;

let rec congruence_div_fallback
  a b = (if is_empty_congruence a || is_empty_congruence b then bot_congruencea
          else (match congruence_singleton b with None -> top_congruencea
                 | Some ba -> congruence_div_const a ba));;

let rec congruence_div
  x = congruence_exact_binop c_div congruence_div_fallback x;;

let rec cong_aop
  x0 a b = match x0, a, b with AAdd, a, b -> plus_congruence a b
    | ASub, a, b -> minus_congruence a b
    | AMul, a, b -> times_congruence a b
    | ADiv, a, b -> congruence_div a b
    | AMod, a, b -> congruence_mod a b;;

let rec raw_aop_ik_congruence x = cong_aop x;;

let rec raw_aop_ik_int_tuple
  op a b =
    IT (raw_aop_ik_ivl op (it_ivl a) (it_ivl b),
         raw_aop_ik_congruence op (it_cong a) (it_cong b));;

let rec cong_refine
  x0 a b = match x0, a, b with
    CEq, a, b -> (inf_congruence a b, inf_congruence a b)
    | CLt, a, b -> (a, b)
    | CLe, a, b -> (a, b)
    | CGt, a, b -> (a, b)
    | CGe, a, b -> (a, b)
    | CNe, a, b -> (a, b);;

let rec refine_ik_congruence x = cong_refine x;;

let rec congruence_upper_bound
  c m x2 = match c, m, x2 with c, m, MinInf -> MinInf
    | c, m, Fin u -> Fin (minus_inta u (modulo_inta (minus_inta u c) m))
    | c, m, PlusInf -> PlusInf;;

let rec congruence_lower_bound
  c m x2 = match c, m, x2 with c, m, MinInf -> MinInf
    | c, m, Fin l -> Fin (plus_inta l (modulo_inta (minus_inta c l) m))
    | c, m, PlusInf -> PlusInf;;

let rec mk_ivl l u = normalize_ivl (Ivl (l, u));;

let rec refine_ivl_with_congruence_rep
  x0 i = match x0, i with None, i -> bot_ivla
    | Some (c, m), Ivl (l, u) ->
        (if equal_inta m zero_inta
          then intersect_ivl (Ivl (Fin c, Fin c)) (Ivl (l, u))
          else intersect_ivl
                 (mk_ivl (congruence_lower_bound c m l)
                   (congruence_upper_bound c m u))
                 (Ivl (l, u)));;

let rec refine_ivl_with_congruence
  fct i = refine_ivl_with_congruence_rep (rep_congruence fct) i;;

let rec cong_refine_with_ivl
  i c = (match (i, rep_congruence c) with (Ivl (MinInf, _), _) -> c
          | (Ivl (Fin _, MinInf), _) -> c | (Ivl (Fin _, Fin _), None) -> c
          | (Ivl (Fin x, Fin y), Some (r, m)) ->
            (if equal_inta m zero_inta
              then (if less_eq_int x r && less_eq_int r y then c
                     else bot_congruencea)
              else (let lo = plus_inta x (modulo_inta (minus_inta r x) m) in
                    let hi = minus_inta y (modulo_inta (minus_inta y r) m) in
                     (if less_int hi lo then bot_congruencea
                       else (if equal_inta lo hi then congruence_of_int lo
                              else c))))
          | (Ivl (Fin _, PlusInf), _) -> c | (Ivl (PlusInf, _), _) -> c);;

let rec it_refine
  a = (let c = cong_refine_with_ivl (it_ivl a) (it_cong a) in
        IT (refine_ivl_with_congruence c (it_ivl a), c));;

let rec refine_ik_int_tuple
  c a b =
    (let (i1, i2) = refine_ik_ivl c (it_ivl a) (it_ivl b) in
     let (c1, c2) = refine_ik_congruence c (it_cong a) (it_cong b) in
      (it_refine (IT (i1, c1)), it_refine (IT (i2, c2))));;

let rec of_int_ik_congruence k n = congruence_of_int (ik_norm k n);;

let rec of_int_ik_int_tuple
  k n = IT (of_int_ik_ivl k n, of_int_ik_congruence k n);;

let rec norm_cong_ik
  k a = (match rep_congruence a with None -> bot_congruencea
          | Some (c, m) ->
            (let g = gcd_intc m (ik_mod k) in
              (if equal_inta g (ik_mod k) then congruence_of_int (ik_norm k c)
                else mk_congruence c g)));;

let rec arith_ik_congruence k op a b = norm_cong_ik k (cong_aop op a b);;

let rec arith_ik_int_tuple
  k op a b =
    (let r = raw_aop_ik_ivl op (it_ivl a) (it_ivl b) in
      it_refine
        (IT (cast_ik_ivl None k r,
              (if fits_ik_ivl k r
                then raw_aop_ik_congruence op (it_cong a) (it_cong b)
                else arith_ik_congruence k op (it_cong a) (it_cong b)))));;

let rec meet_ik_congruence a b = inf_congruence a b;;

let rec meet_ik_int_tuple
  a b = it_refine
          (IT (meet_ik_ivl (it_ivl a) (it_ivl b),
                meet_ik_congruence (it_cong a) (it_cong b)));;

let rec fits_ik_congruence
  k a = (match rep_congruence a with None -> true
          | Some (c, m) ->
            equal_inta m zero_inta &&
              (less_eq_int (ik_min k) c && less_eq_int c (ik_max k)));;

let rec fits_ik_int_tuple
  k a = fits_ik_ivl k (it_ivl a) || fits_ik_congruence k (it_cong a);;

let rec sub_kind
  s k = less_eq_int (ik_min k) (ik_min s) && less_eq_int (ik_max s) (ik_max k);;

let rec cast_ik_congruence
  sk k a =
    (match sk with None -> norm_cong_ik k a
      | Some s -> (if sub_kind s k then a else norm_cong_ik k a));;

let rec cast_ik_int_tuple
  sk k a =
    it_refine
      (IT (cast_ik_ivl sk k (it_ivl a),
            (if fits_ik_ivl k (it_ivl a) then it_cong a
              else cast_ik_congruence sk k (it_cong a))));;

let rec top_ik_congruence k = top_congruencea;;

let rec top_ik_int_tuple k = IT (top_ik_ivl k, top_ik_congruence k);;

let rec congruence_lt
  a b = (match (congruence_singleton a, congruence_singleton b)
          with (None, _) -> None | (Some _, None) -> None
          | (Some c1, Some c2) -> Some (less_int c1 c2));;

let rec congruence_eqb
  a b = (match (congruence_singleton a, congruence_singleton b)
          with (None, _) -> None | (Some _, None) -> None
          | (Some c1, Some c2) -> Some (equal_inta c1 c2));;

let rec cong_eq
  a b = (match congruence_eqb a b
          with None ->
            (if is_bottom_congruence (inf_congruence a b) then Some false
              else None)
          | Some aa -> Some aa);;

let rec cong_cop x0 a b = match x0, a, b with CLt, a, b -> congruence_lt a b
                   | CGt, a, b -> congruence_lt b a
                   | CLe, a, b -> map_option not (congruence_lt b a)
                   | CGe, a, b -> map_option not (congruence_lt a b)
                   | CEq, a, b -> cong_eq a b
                   | CNe, a, b -> map_option not (cong_eq a b);;

let rec cmp_ik_congruence x = cong_cop x;;

let rec cmp_ik_int_tuple
  c a b =
    (match cmp_ik_ivl c (it_ivl a) (it_ivl b)
      with None -> cmp_ik_congruence c (it_cong a) (it_cong b)
      | Some aa -> Some aa);;

let kind_int_domain_int_tuple =
  ({ik_domain_kind_int_domain = ik_domain_int_tuple; top_ik = top_ik_int_tuple;
     of_int_ik = of_int_ik_int_tuple; cast_ik = cast_ik_int_tuple;
     arith_ik = arith_ik_int_tuple; cmp_ik = cmp_ik_int_tuple;
     meet_ik = meet_ik_int_tuple; refine_ik = refine_ik_int_tuple;
     raw_aop_ik = raw_aop_ik_int_tuple; fits_ik = fits_ik_int_tuple}
    : int_tuple kind_int_domain);;

type 'a lifted = Bot | Lifted of 'a;;

let rec equal_lifteda _A x0 x1 = match x0, x1 with Bot, Lifted x2 -> false
                           | Lifted x2, Bot -> false
                           | Lifted x2, Lifted y2 -> eq _A x2 y2
                           | Bot, Bot -> true;;

let rec equal_lifted _A = ({equal = equal_lifteda _A} : 'a lifted equal);;

let rec sup_lifteda _A
  x0 y = match x0, y with Bot, y -> y
    | Lifted v, Bot -> Lifted v
    | Lifted a, Lifted b -> Lifted (sup _A.sup_semilattice_sup a b);;

let rec sup_lifted _A = ({sup = sup_lifteda _A} : 'a lifted sup);;

let rec bot_lifteda _A = Bot;;

let rec bot_lifted _A = ({bot = bot_lifteda _A} : 'a lifted bot);;

let rec less_eq_lifted _A
  x0 uu = match x0, uu with Bot, uu -> true
    | Lifted uv, Bot -> false
    | Lifted a, Lifted b ->
        less_eq _A.order_semilattice_sup.preorder_order.ord_preorder a b;;

let rec less_lifted _A
  x y = less_eq_lifted _A x y && not (less_eq_lifted _A y x);;

let rec ord_lifted _A =
  ({less_eq = less_eq_lifted _A; less = less_lifted _A} : 'a lifted ord);;

let rec preorder_lifted _A =
  ({ord_preorder = (ord_lifted _A)} : 'a lifted preorder);;

let rec order_lifted _A =
  ({preorder_order = (preorder_lifted _A)} : 'a lifted order);;

let rec widen_lifted (_A1, _A2)
  x0 y = match x0, y with Bot, y -> y
    | Lifted v, Bot -> Lifted v
    | Lifted a, Lifted b -> Lifted (widen _A2 a b);;

let rec widening_lifted (_A1, _A2) =
  ({order_widening = (order_lifted _A1); widen = widen_lifted (_A1, _A2)} :
    'a lifted widening);;

let rec order_bot_lifted _A =
  ({bot_order_bot = (bot_lifted _A); order_order_bot = (order_lifted _A)} :
    'a lifted order_bot);;

let rec narrow_lifted (_A1, _A2)
  x0 y = match x0, y with Bot, y -> Bot
    | Lifted a, Bot -> Bot
    | Lifted a, Lifted b -> Lifted (narrow _A2 a b);;

let rec narrowing_lifted (_A1, _A2) =
  ({order_narrowing = (order_lifted _A1); narrow = narrow_lifted (_A1, _A2)} :
    'a lifted narrowing);;

let rec warrowing_lifted (_A1, _A2) =
  ({narrowing_warrowing =
      (narrowing_lifted
        (_A1.semilattice_sup_bounded_semilattice_sup_bot,
          _A2.narrowing_warrowing));
     widening_warrowing =
       (widening_lifted
         (_A1.semilattice_sup_bounded_semilattice_sup_bot,
           _A2.widening_warrowing))}
    : 'a lifted warrowing);;

let rec vjoin_lifted _A x0 y = match x0, y with Bot, y -> y
                          | Lifted x, Bot -> Lifted x
                          | Lifted x, Lifted y -> Lifted (vjoin _A x y);;

let rec join_val_lifted _A = ({vjoin = vjoin_lifted _A} : 'a lifted join_val);;

let rec semilattice_sup_lifted _A =
  ({sup_semilattice_sup = (sup_lifted _A);
     order_semilattice_sup = (order_lifted _A)}
    : 'a lifted semilattice_sup);;

let rec bind_lift x0 f = match x0, f with Bot, f -> Bot
                    | Lifted a, f -> f a;;

let rec map_lift f x = bind_lift x (fun a -> Lifted (f a));;

let rec split_global_at_lifted (_A1, _A2) x = map_lift (split_global_at _A2 x);;

let rec split_free_lifted (_A1, _A2) r = Lifted (split_free _A2 r);;

let rec split_cmb_lifted (_A1, _A2)
  d g = (match d with Bot -> Bot
          | Lifted a ->
            Lifted
              (split_cmb _A2 a
                (match g
                  with Bot -> bot _A2.order_bot_ownership_split.bot_order_bot
                  | Lifted b -> b)));;

let rec split_rl_lifted (_A1, _A2) = map_lift (split_rl _A2);;

let rec split_rg_lifted (_A1, _A2) = map_lift (split_rg _A2);;

let rec ownership_split_lifted (_A1, _A2) =
  ({order_bot_ownership_split = (order_bot_lifted _A1);
     split_cmb = split_cmb_lifted (_A1, _A2);
     split_rl = split_rl_lifted (_A1, _A2);
     split_global_at = split_global_at_lifted (_A1, _A2);
     split_rg = split_rg_lifted (_A1, _A2);
     split_free = split_free_lifted (_A1, _A2)}
    : 'a lifted ownership_split);;

let rec bounded_semilattice_sup_bot_lifted _A =
  ({semilattice_sup_bounded_semilattice_sup_bot = (semilattice_sup_lifted _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_lifted _A)}
    : 'a lifted bounded_semilattice_sup_bot);;

type check_result = Check_Proved | Check_Refuted | Check_Unknown;;

let rec equal_check_result
  x0 x1 = match x0, x1 with Check_Refuted, Check_Unknown -> false
    | Check_Unknown, Check_Refuted -> false
    | Check_Proved, Check_Unknown -> false
    | Check_Unknown, Check_Proved -> false
    | Check_Proved, Check_Refuted -> false
    | Check_Refuted, Check_Proved -> false
    | Check_Unknown, Check_Unknown -> true
    | Check_Refuted, Check_Refuted -> true
    | Check_Proved, Check_Proved -> true;;

let rec sup_check_resulta
  x y = (if equal_check_result x y then x else Check_Unknown);;

let sup_check_result = ({sup = sup_check_resulta} : check_result sup);;

let rec less_eq_check_result
  x y = equal_check_result x y || equal_check_result y Check_Unknown;;

let rec less_check_result
  x y = less_eq_check_result x y && not (less_eq_check_result y x);;

let ord_check_result =
  ({less_eq = less_eq_check_result; less = less_check_result} :
    check_result ord);;

let preorder_check_result =
  ({ord_preorder = ord_check_result} : check_result preorder);;

let order_check_result =
  ({preorder_order = preorder_check_result} : check_result order);;

let semilattice_sup_check_result =
  ({sup_semilattice_sup = sup_check_result;
     order_semilattice_sup = order_check_result}
    : check_result semilattice_sup);;

type order_key = Key_Int of int | Key_Node of cfg_node |
  Key_List of order_key list;;

let rec equal_order_key () = ({equal = equal_order_keya} : order_key equal)
and equal_order_keya
  x0 x1 = match x0, x1 with Key_Node x2, Key_List x3 -> false
    | Key_List x3, Key_Node x2 -> false
    | Key_Int x1, Key_List x3 -> false
    | Key_List x3, Key_Int x1 -> false
    | Key_Int x1, Key_Node x2 -> false
    | Key_Node x2, Key_Int x1 -> false
    | Key_List x3, Key_List y3 -> equal_lista (equal_order_key ()) x3 y3
    | Key_Node x2, Key_Node y2 -> equal_cfg_nodea x2 y2
    | Key_Int x1, Key_Int y1 -> equal_inta x1 y1;;
let equal_order_key = equal_order_key ();;

let rec comparator_order_key
  x0 x1 = match x0, x1 with
    Key_Int x, Key_Int y -> comparator_of (equal_int, linorder_int) x y
    | Key_Int x, Key_Node ya -> Lt
    | Key_Int x, Key_List yb -> Lt
    | Key_Node x, Key_Int y -> Gt
    | Key_Node x, Key_Node ya -> comparator_cfg_node x ya
    | Key_Node x, Key_List yb -> Lt
    | Key_List x, Key_Int y -> Gt
    | Key_List x, Key_Node ya -> Gt
    | Key_List x, Key_List yb -> comparator_list comparator_order_key x yb;;

let rec less_eq_order_key x = le_of_comp comparator_order_key x;;

let rec less_order_key x = lt_of_comp comparator_order_key x;;

let ord_order_key =
  ({less_eq = less_eq_order_key; less = less_order_key} : order_key ord);;

let preorder_order_key = ({ord_preorder = ord_order_key} : order_key preorder);;

let order_order_key =
  ({preorder_order = preorder_order_key} : order_key order);;

let linorder_order_key =
  ({order_linorder = order_order_key} : order_key linorder);;

let rec map_of _A
  x0 k = match x0, k with [], k -> None
    | (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k);;

let rec default_dict_get _B
  (d, ps) x = (match map_of _B ps x with None -> d | Some a -> a);;

let rec le_default_dict _A _B
  (d, ps) (e, qs) =
    less_eq _A.preorder_order.ord_preorder d e &&
      list_all
        (fun x ->
          less_eq _A.preorder_order.ord_preorder (default_dict_get _B (d, ps) x)
            (default_dict_get _B (e, qs) x))
        (map fst ps @ map fst qs);;

let rec le_default_st_rep_code _A _B
  (l1, g1) (l2, g2) =
    le_default_dict _A.order_order_bot _B l1 l2 &&
      le_default_dict _A.order_order_bot _B g1 g2;;

type ('a, 'b) gdefault_st =
  Abs_default_st of (('b * ('a * 'b) list) * ('b * ('a * 'b) list));;

let rec less_eq_gdefault_st (_A1, _A2) _B
  (Abs_default_st xb) (Abs_default_st x) = le_default_st_rep_code _B _A2 xb x;;

let rec equal_gdefault_sta (_A1, _A2) (_B1, _B2)
  s t = less_eq_gdefault_st (_A1, _A2) _B2 s t &&
          less_eq_gdefault_st (_A1, _A2) _B2 t s;;

let rec equal_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({equal = equal_gdefault_sta (_A1, _A2) (_B1, _B2)} :
    ('a, 'b) gdefault_st equal);;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec map2_default_dict _B
  f (d1, ps1) (d2, ps2) =
    (f d1 d2,
      map (fun x ->
            (x, f (default_dict_get _B (d1, ps1) x)
                  (default_dict_get _B (d2, ps2) x)))
        (remdups _B (map fst ps1 @ map fst ps2)));;

let rec map2_default_st_rep _A _B
  f (l1, g1) (l2, g2) =
    (map2_default_dict _B f l1 l2, map2_default_dict _B f g1 g2);;

let rec merge_default_st_rep _A _B
  s t = map2_default_st_rep
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot _B
          (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup)
          s t;;

let rec sup_gdefault_sta (_A1, _A2) _B
  (Abs_default_st xa) (Abs_default_st x) =
    Abs_default_st (merge_default_st_rep _B _A2 xa x);;

let rec sup_gdefault_st (_A1, _A2) _B =
  ({sup = sup_gdefault_sta (_A1, _A2) _B} : ('a, 'b) gdefault_st sup);;

let rec bot_gdefault_sta _B = Abs_default_st ((bot _B, []), (bot _B, []));;

let rec bot_gdefault_st _B =
  ({bot = bot_gdefault_sta _B} : ('a, 'b) gdefault_st bot);;

let rec less_gdefault_st (_A1, _A2) _B
  s t = less_eq_gdefault_st (_A1, _A2) _B s t &&
          not (less_eq_gdefault_st (_A1, _A2) _B t s);;

let rec ord_gdefault_st (_A1, _A2) _B =
  ({less_eq = less_eq_gdefault_st (_A1, _A2) _B;
     less = less_gdefault_st (_A1, _A2) _B}
    : ('a, 'b) gdefault_st ord);;

let rec preorder_gdefault_st (_A1, _A2) _B =
  ({ord_preorder = (ord_gdefault_st (_A1, _A2) _B)} :
    ('a, 'b) gdefault_st preorder);;

let rec order_gdefault_st (_A1, _A2) _B =
  ({preorder_order = (preorder_gdefault_st (_A1, _A2) _B)} :
    ('a, 'b) gdefault_st order);;

let rec widen_default_st_rep (_A1, _A2) _B
  s t = map2_default_st_rep
          _A1.order_bot_bounded_semilattice_sup_bot.bot_order_bot _B
          (widen _A2.widening_warrowing) s t;;

let rec widen_on_default_st (_A1, _A2) (_B1, _B2)
  (Abs_default_st xa) (Abs_default_st x) =
    Abs_default_st (widen_default_st_rep (_B1, _B2) _A2 xa x);;

let rec widen_gdefault_st (_A1, _A2) (_B1, _B2)
  s t = widen_on_default_st (_A1, _A2) (_B1, _B2) s t;;

let rec widening_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({order_widening =
      (order_gdefault_st (_A1, _A2) _B1.order_bot_bounded_semilattice_sup_bot);
     widen = widen_gdefault_st (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) gdefault_st widening);;

let rec order_bot_gdefault_st (_A1, _A2) _B =
  ({bot_order_bot = (bot_gdefault_st _B.bot_order_bot);
     order_order_bot = (order_gdefault_st (_A1, _A2) _B)}
    : ('a, 'b) gdefault_st order_bot);;

let rec narrow_default_st_rep (_A1, _A2) _B
  s t = map2_default_st_rep
          _A1.order_bot_bounded_semilattice_sup_bot.bot_order_bot _B
          (narrow _A2.narrowing_warrowing) s t;;

let rec narrow_on_default_st (_A1, _A2) (_B1, _B2)
  (Abs_default_st xa) (Abs_default_st x) =
    Abs_default_st (narrow_default_st_rep (_B1, _B2) _A2 xa x);;

let rec narrow_gdefault_st (_A1, _A2) (_B1, _B2)
  s t = narrow_on_default_st (_A1, _A2) (_B1, _B2) s t;;

let rec narrowing_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({order_narrowing =
      (order_gdefault_st (_A1, _A2) _B1.order_bot_bounded_semilattice_sup_bot);
     narrow = narrow_gdefault_st (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) gdefault_st narrowing);;

let rec warrowing_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({narrowing_warrowing = (narrowing_gdefault_st (_A1, _A2) (_B1, _B2));
     widening_warrowing = (widening_gdefault_st (_A1, _A2) (_B1, _B2))}
    : ('a, 'b) gdefault_st warrowing);;

let rec semilattice_sup_gdefault_st (_A1, _A2) _B =
  ({sup_semilattice_sup = (sup_gdefault_st (_A1, _A2) _B);
     order_semilattice_sup =
       (order_gdefault_st (_A1, _A2) _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) gdefault_st semilattice_sup);;

type 'a glocation = Local_Location of 'a | Global_Location of 'a;;

let rec delete _A k = filtera (fun (ka, _) -> not (eq _A k ka));;

let rec default_dict_set _B (d, ps) x a = (d, (x, a) :: delete _B x ps);;

let rec default_st_rep_set _A _B
  x0 x1 a = match x0, x1, a with
    (l, g), Local_Location x, a -> (default_dict_set _B l x a, g)
    | (l, g), Global_Location x, a -> (l, default_dict_set _B g x a);;

let rec default_st_set _A _B
  (Abs_default_st xb) xa x = Abs_default_st (default_st_rep_set _B _A xb xa x);;

let rec default_st_rep_get _A _B
  x0 x1 = match x0, x1 with (l, g), Local_Location x -> default_dict_get _B l x
    | (l, g), Global_Location x -> default_dict_get _B g x;;

let rec default_st_get _A _B (Abs_default_st x) = default_st_rep_get _B _A x;;

let rec split_global_at_gdefault_st (_A1, _A2) (_B1, _B2)
  x d = default_st_set _A2 _B1.bot_order_bot
          (bot_gdefault_sta _B1.bot_order_bot)
          (Global_Location (global_name _A1 x))
          (default_st_get _A2 _B1.bot_order_bot d
            (Global_Location (global_name _A1 x)));;

let rec split_free_gdefault_st _A (_B1, _B2)
  r = Abs_default_st
        ((bot _B1.bot_order_bot, []),
          (top _B2.top_order_top,
            map (fun x -> (global_name _A x, bot _B1.bot_order_bot)) r));;

let rec combine_default_st_rep _A sc se = (fst sc, snd se);;

let rec combine_default_st _B
  (Abs_default_st xa) (Abs_default_st x) =
    Abs_default_st (combine_default_st_rep _B xa x);;

let rec split_cmb_gdefault_st _A (_B1, _B2)
  = combine_default_st _B1.bot_order_bot;;

let rec restrict_local_default_st_rep _A s = (fst s, (bot _A, []));;

let rec restrict_local_default_st _B
  (Abs_default_st x) = Abs_default_st (restrict_local_default_st_rep _B x);;

let rec split_rl_gdefault_st _A (_B1, _B2)
  = restrict_local_default_st _B1.bot_order_bot;;

let rec restrict_global_default_st_rep _A s = ((bot _A, []), snd s);;

let rec restrict_global_default_st _B
  (Abs_default_st x) = Abs_default_st (restrict_global_default_st_rep _B x);;

let rec split_rg_gdefault_st _A (_B1, _B2)
  = restrict_global_default_st _B1.bot_order_bot;;

let rec ownership_split_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({order_bot_ownership_split =
      (order_bot_gdefault_st (_A1.infinite_key_global_name, _A2) _B1);
     split_cmb = split_cmb_gdefault_st _A1 (_B1, _B2);
     split_rl = split_rl_gdefault_st _A1 (_B1, _B2);
     split_global_at = split_global_at_gdefault_st (_A1, _A2) (_B1, _B2);
     split_rg = split_rg_gdefault_st _A1 (_B1, _B2);
     split_free = split_free_gdefault_st _A1 (_B1, _B2)}
    : ('a, 'b) gdefault_st ownership_split);;

let rec bounded_semilattice_sup_bot_gdefault_st (_A1, _A2) _B =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_gdefault_st (_A1, _A2) _B);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_gdefault_st (_A1, _A2)
         _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) gdefault_st bounded_semilattice_sup_bot);;

type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint;;

let rec equal_refine_mode
  x0 x1 = match x0, x1 with Refine_Once, Refine_Fixpoint -> false
    | Refine_Fixpoint, Refine_Once -> false
    | Refine_Never, Refine_Fixpoint -> false
    | Refine_Fixpoint, Refine_Never -> false
    | Refine_Never, Refine_Once -> false
    | Refine_Once, Refine_Never -> false
    | Refine_Fixpoint, Refine_Fixpoint -> true
    | Refine_Once, Refine_Once -> true
    | Refine_Never, Refine_Never -> true;;

type analysis_domain = Sign_Analysis | Interval_Analysis | Parity_Analysis |
  Int_Analysis of refine_mode | Congruence_Analysis | Order_Analysis;;

let rec equal_analysis_domaina
  x0 x1 = match x0, x1 with Congruence_Analysis, Order_Analysis -> false
    | Order_Analysis, Congruence_Analysis -> false
    | Int_Analysis x4, Order_Analysis -> false
    | Order_Analysis, Int_Analysis x4 -> false
    | Int_Analysis x4, Congruence_Analysis -> false
    | Congruence_Analysis, Int_Analysis x4 -> false
    | Parity_Analysis, Order_Analysis -> false
    | Order_Analysis, Parity_Analysis -> false
    | Parity_Analysis, Congruence_Analysis -> false
    | Congruence_Analysis, Parity_Analysis -> false
    | Parity_Analysis, Int_Analysis x4 -> false
    | Int_Analysis x4, Parity_Analysis -> false
    | Interval_Analysis, Order_Analysis -> false
    | Order_Analysis, Interval_Analysis -> false
    | Interval_Analysis, Congruence_Analysis -> false
    | Congruence_Analysis, Interval_Analysis -> false
    | Interval_Analysis, Int_Analysis x4 -> false
    | Int_Analysis x4, Interval_Analysis -> false
    | Interval_Analysis, Parity_Analysis -> false
    | Parity_Analysis, Interval_Analysis -> false
    | Sign_Analysis, Order_Analysis -> false
    | Order_Analysis, Sign_Analysis -> false
    | Sign_Analysis, Congruence_Analysis -> false
    | Congruence_Analysis, Sign_Analysis -> false
    | Sign_Analysis, Int_Analysis x4 -> false
    | Int_Analysis x4, Sign_Analysis -> false
    | Sign_Analysis, Parity_Analysis -> false
    | Parity_Analysis, Sign_Analysis -> false
    | Sign_Analysis, Interval_Analysis -> false
    | Interval_Analysis, Sign_Analysis -> false
    | Int_Analysis x4, Int_Analysis y4 -> equal_refine_mode x4 y4
    | Order_Analysis, Order_Analysis -> true
    | Congruence_Analysis, Congruence_Analysis -> true
    | Parity_Analysis, Parity_Analysis -> true
    | Interval_Analysis, Interval_Analysis -> true
    | Sign_Analysis, Sign_Analysis -> true;;

let equal_analysis_domain =
  ({equal = equal_analysis_domaina} : analysis_domain equal);;

let equal_congruence = ({equal = equal_congruencea} : congruence equal);;

let sup_congruence = ({sup = sup_congruencea} : congruence sup);;

let bot_congruence = ({bot = bot_congruencea} : congruence bot);;

let rec less_congruence
  a b = less_eq_congruence a b && not (less_eq_congruence b a);;

let ord_congruence =
  ({less_eq = less_eq_congruence; less = less_congruence} : congruence ord);;

let top_congruence = ({top = top_congruencea} : congruence top);;

let preorder_congruence =
  ({ord_preorder = ord_congruence} : congruence preorder);;

let order_congruence =
  ({preorder_order = preorder_congruence} : congruence order);;

let widening_congruence =
  ({order_widening = order_congruence; widen = widen_congruence} :
    congruence widening);;

let order_bot_congruence =
  ({bot_order_bot = bot_congruence; order_order_bot = order_congruence} :
    congruence order_bot);;

let order_top_congruence =
  ({order_order_top = order_congruence; top_order_top = top_congruence} :
    congruence order_top);;

let narrowing_congruence =
  ({order_narrowing = order_congruence; narrow = narrow_congruence} :
    congruence narrowing);;

let warrowing_congruence =
  ({narrowing_warrowing = narrowing_congruence;
     widening_warrowing = widening_congruence}
    : congruence warrowing);;

let rec gamma_congruencea a = gamma_congruence a;;

let rec empty_ik_congruence
  k a = (match rep_congruence a with None -> true
          | Some (c, m) ->
            (if equal_inta m zero_inta
              then not (less_eq_int (ik_min k) c && less_eq_int c (ik_max k))
              else less_int (ik_max k)
                     (plus_inta (ik_min k)
                       (modulo_inta (minus_inta c (ik_min k)) m))));;

let semilattice_sup_congruence =
  ({sup_semilattice_sup = sup_congruence;
     order_semilattice_sup = order_congruence}
    : congruence semilattice_sup);;

let bounded_semilattice_sup_bot_congruence =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_congruence;
     order_bot_bounded_semilattice_sup_bot = order_bot_congruence}
    : congruence bounded_semilattice_sup_bot);;

let executable_domain_congruence =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_congruence;
     order_top_executable_domain = order_top_congruence;
     warrowing_executable_domain = warrowing_congruence;
     is_empty = is_empty_congruence; to_string = to_string_congruence}
    : congruence executable_domain);;

let numeric_domain_congruence =
  ({executable_domain_numeric_domain = executable_domain_congruence;
     gamma = gamma_congruencea}
    : congruence numeric_domain);;

let ik_domain_congruence =
  ({numeric_domain_ik_domain = numeric_domain_congruence;
     widen_ik = widen_ik_congruence; narrow_ik = narrow_ik_congruence;
     empty_ik = empty_ik_congruence}
    : congruence ik_domain);;

let kind_int_domain_congruence =
  ({ik_domain_kind_int_domain = ik_domain_congruence;
     top_ik = top_ik_congruence; of_int_ik = of_int_ik_congruence;
     cast_ik = cast_ik_congruence; arith_ik = arith_ik_congruence;
     cmp_ik = cmp_ik_congruence; meet_ik = meet_ik_congruence;
     refine_ik = refine_ik_congruence; raw_aop_ik = raw_aop_ik_congruence;
     fits_ik = fits_ik_congruence}
    : congruence kind_int_domain);;

type 'a order_rel = OBot | OFacts of ('a * 'a) set;;

let rec equal_order_rela _A
  x0 x1 = match x0, x1 with OBot, OFacts x2 -> false
    | OFacts x2, OBot -> false
    | OFacts x2, OFacts y2 -> equal_set (equal_prod _A _A) x2 y2
    | OBot, OBot -> true;;

let rec equal_order_rel _A =
  ({equal = equal_order_rela _A} : 'a order_rel equal);;

let rec sup_order_rela _A
  x0 b = match x0, b with OBot, b -> b
    | OFacts v, OBot -> OFacts v
    | OFacts a, OFacts b -> OFacts (inf_set (equal_prod _A _A) a b);;

let rec sup_order_rel _A = ({sup = sup_order_rela _A} : 'a order_rel sup);;

let bot_order_rela : 'a order_rel = OBot;;

let bot_order_rel = ({bot = bot_order_rela} : 'a order_rel bot);;

let rec less_eq_order_rel _A
  x0 uu = match x0, uu with OBot, uu -> true
    | OFacts uv, OBot -> false
    | OFacts a, OFacts b -> less_eq_set (equal_prod _A _A) b a;;

let rec less_order_rel _A
  a b = less_eq_order_rel _A a b && not (less_eq_order_rel _A b a);;

let rec ord_order_rel _A =
  ({less_eq = less_eq_order_rel _A; less = less_order_rel _A} :
    'a order_rel ord);;

let rec preorder_order_rel _A =
  ({ord_preorder = (ord_order_rel _A)} : 'a order_rel preorder);;

let rec order_order_rel _A =
  ({preorder_order = (preorder_order_rel _A)} : 'a order_rel order);;

let rec widen_order_rel _A a b = sup_order_rela _A a b;;

let rec widening_order_rel _A =
  ({order_widening = (order_order_rel _A); widen = widen_order_rel _A} :
    'a order_rel widening);;

let rec order_bot_order_rel _A =
  ({bot_order_bot = bot_order_rel; order_order_bot = (order_order_rel _A)} :
    'a order_rel order_bot);;

let rec narrow_order_rel a b = b;;

let rec narrowing_order_rel _A =
  ({order_narrowing = (order_order_rel _A); narrow = narrow_order_rel} :
    'a order_rel narrowing);;

let rec warrowing_order_rel _A =
  ({narrowing_warrowing = (narrowing_order_rel _A);
     widening_warrowing = (widening_order_rel _A)}
    : 'a order_rel warrowing);;

let rec semilattice_sup_order_rel _A =
  ({sup_semilattice_sup = (sup_order_rel _A);
     order_semilattice_sup = (order_order_rel _A)}
    : 'a order_rel semilattice_sup);;

let rec bounded_semilattice_sup_bot_order_rel _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_order_rel _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_order_rel _A)}
    : 'a order_rel bounded_semilattice_sup_bot);;

type 'a int_dom_ext = Int_dom_ext of sign * ivl * parity * congruence * 'a;;

let rec equal_int_dom_exta _A
  (Int_dom_ext (int_signa, int_ivla, int_paritya, int_congruencea, morea))
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    equal_signa int_signa int_sign &&
      (equal_ivla int_ivla int_ivl &&
        (equal_paritya int_paritya int_parity &&
          (equal_congruencea int_congruencea int_congruence &&
            eq _A morea more)));;

let rec equal_int_dom_ext _A =
  ({equal = equal_int_dom_exta _A} : 'a int_dom_ext equal);;

let rec int_congruence
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_congruence;;

let rec int_parity
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_parity;;

let rec int_sign
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_sign;;

let rec int_ivl
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_ivl;;

let rec more
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) = more;;

let rec inf_int_dom_exta _A
  a b = Int_dom_ext
          (inf_sign (int_sign a) (int_sign b), inf_ivl (int_ivl a) (int_ivl b),
            inf_parity (int_parity a) (int_parity b),
            inf_congruence (int_congruence a) (int_congruence b),
            inf _A.bounded_lattice_bot_bounded_lattice.lattice_bounded_lattice_bot.semilattice_inf_lattice.inf_semilattice_inf
              (more a) (more b));;

let rec inf_int_dom_ext _A =
  ({inf = inf_int_dom_exta _A} : 'a int_dom_ext inf);;

let rec sup_int_dom_exta _A
  a b = Int_dom_ext
          (sup_signa (int_sign a) (int_sign b),
            sup_ivla (int_ivl a) (int_ivl b),
            sup_paritya (int_parity a) (int_parity b),
            sup_congruencea (int_congruence a) (int_congruence b),
            sup _A.bounded_lattice_bot_bounded_lattice.lattice_bounded_lattice_bot.semilattice_sup_lattice.sup_semilattice_sup
              (more a) (more b));;

let rec sup_int_dom_ext _A =
  ({sup = sup_int_dom_exta _A} : 'a int_dom_ext sup);;

let rec bot_int_dom_exta _A
  = Int_dom_ext
      (bot_signa, bot_ivla, bot_paritya, bot_congruencea,
        bot _A.bounded_lattice_bot_bounded_lattice.bounded_semilattice_sup_bot_bounded_lattice_bot.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec bot_int_dom_ext _A =
  ({bot = bot_int_dom_exta _A} : 'a int_dom_ext bot);;

let rec less_eq_int_dom_ext _A
  a b = less_eq_sign (int_sign a) (int_sign b) &&
          (less_eq_ivl (int_ivl a) (int_ivl b) &&
            (less_eq_parity (int_parity a) (int_parity b) &&
              (less_eq_congruence (int_congruence a) (int_congruence b) &&
                less_eq
                  _A.bounded_lattice_bot_bounded_lattice.bounded_semilattice_sup_bot_bounded_lattice_bot.order_bot_bounded_semilattice_sup_bot.order_order_bot.preorder_order.ord_preorder
                  (more a) (more b))));;

let rec less_int_dom_ext _A
  a b = less_eq_int_dom_ext _A a b && not (less_eq_int_dom_ext _A b a);;

let rec ord_int_dom_ext _A =
  ({less_eq = less_eq_int_dom_ext _A; less = less_int_dom_ext _A} :
    'a int_dom_ext ord);;

let rec top_int_dom_exta _A
  = Int_dom_ext
      (top_signa, top_ivla, top_paritya, top_congruencea,
        top _A.bounded_lattice_top_bounded_lattice.bounded_semilattice_inf_top_bounded_lattice_top.order_top_bounded_semilattice_inf_top.top_order_top);;

let rec top_int_dom_ext _A =
  ({top = top_int_dom_exta _A} : 'a int_dom_ext top);;

let rec preorder_int_dom_ext _A =
  ({ord_preorder = (ord_int_dom_ext _A)} : 'a int_dom_ext preorder);;

let rec order_int_dom_ext _A =
  ({preorder_order = (preorder_int_dom_ext _A)} : 'a int_dom_ext order);;

let rec int_congruence_update
  int_congruencea
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_parity, int_congruencea int_congruence, more);;

let rec int_parity_update
  int_paritya
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_paritya int_parity, int_congruence, more);;

let rec int_sign_update
  int_signa (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more))
    = Int_dom_ext
        (int_signa int_sign, int_ivl, int_parity, int_congruence, more);;

let rec int_ivl_update
  int_ivla (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext (int_sign, int_ivla int_ivl, int_parity, int_congruence, more);;

let rec truncate
  r = Int_dom_ext (int_sign r, int_ivl r, int_parity r, int_congruence r, ());;

let rec extend
  r more =
    Int_dom_ext (int_sign r, int_ivl r, int_parity r, int_congruence r, more);;

let rec widen_int_dom_ext (_A1, _A2)
  a b = extend
          (truncate
            (int_congruence_update
              (fun _ -> widen_congruence (int_congruence a) (int_congruence b))
              (int_parity_update
                (fun _ -> widen_parity (int_parity a) (int_parity b))
                (int_ivl_update (fun _ -> widen_ivl (int_ivl a) (int_ivl b))
                  (int_sign_update
                    (fun _ -> widen_sign (int_sign a) (int_sign b)) a)))))
          (widen _A2.widening_warrowing (more a) (more b));;

let rec widening_int_dom_ext (_A1, _A2) =
  ({order_widening = (order_int_dom_ext _A1);
     widen = widen_int_dom_ext (_A1, _A2)}
    : 'a int_dom_ext widening);;

let rec order_bot_int_dom_ext _A =
  ({bot_order_bot = (bot_int_dom_ext _A);
     order_order_bot = (order_int_dom_ext _A)}
    : 'a int_dom_ext order_bot);;

let rec order_top_int_dom_ext _A =
  ({order_order_top = (order_int_dom_ext _A);
     top_order_top = (top_int_dom_ext _A)}
    : 'a int_dom_ext order_top);;

let rec narrow_int_dom_ext (_A1, _A2)
  a b = extend
          (truncate
            (int_congruence_update
              (fun _ -> narrow_congruence (int_congruence a) (int_congruence b))
              (int_parity_update
                (fun _ -> narrow_parity (int_parity a) (int_parity b))
                (int_ivl_update (fun _ -> narrow_ivl (int_ivl a) (int_ivl b))
                  (int_sign_update
                    (fun _ -> narrow_sign (int_sign a) (int_sign b)) a)))))
          (narrow _A2.narrowing_warrowing (more a) (more b));;

let rec narrowing_int_dom_ext (_A1, _A2) =
  ({order_narrowing = (order_int_dom_ext _A1);
     narrow = narrow_int_dom_ext (_A1, _A2)}
    : 'a int_dom_ext narrowing);;

let rec warrowing_int_dom_ext (_A1, _A2) =
  ({narrowing_warrowing = (narrowing_int_dom_ext (_A1, _A2));
     widening_warrowing = (widening_int_dom_ext (_A1, _A2))}
    : 'a int_dom_ext warrowing);;

let rec semilattice_sup_int_dom_ext _A =
  ({sup_semilattice_sup = (sup_int_dom_ext _A);
     order_semilattice_sup = (order_int_dom_ext _A)}
    : 'a int_dom_ext semilattice_sup);;

let rec parity_accepts
  x0 n = match x0, n with PBot, n -> false
    | PEven, n ->
        dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2)) n
    | POdd, n ->
        not (dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2))
              n)
    | PTop, n -> true;;

let rec restrict_congruence_rep_by_parity
  x0 r = match x0, r with PBot, r -> None
    | PTop, r -> r
    | PEven, None -> None
    | POdd, None -> None
    | PEven, Some (c, m) ->
        (if equal_inta m zero_inta
          then (if parity_accepts PEven c then Some (c, zero_inta) else None)
          else (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) m &&
                     not (parity_accepts PEven c)
                 then None
                 else normalize_congruence_rep
                        (Some (plus_inta c
                                 (if parity_accepts PEven c then zero_inta
                                   else m),
                                lcm_inta m (Int_of_integer (Z.of_int 2))))))
    | POdd, Some (c, m) ->
        (if equal_inta m zero_inta
          then (if parity_accepts POdd c then Some (c, zero_inta) else None)
          else (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) m &&
                     not (parity_accepts POdd c)
                 then None
                 else normalize_congruence_rep
                        (Some (plus_inta c
                                 (if parity_accepts POdd c then zero_inta
                                   else m),
                                lcm_inta m (Int_of_integer (Z.of_int 2))))));;

let rec restrict_congruence_by_parity
  xb xc =
    Abs_congruence (restrict_congruence_rep_by_parity xb (rep_congruence xc));;

let rec ivl_congruence_rep_nonempty
  i x1 = match i, x1 with i, None -> false
    | Ivl (MinInf, MinInf), Some cm -> false
    | Ivl (MinInf, Fin u), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int c u else true)
    | Ivl (MinInf, PlusInf), Some cm -> true
    | Ivl (Fin l, MinInf), Some cm -> false
    | Ivl (Fin l, Fin u), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int l c && less_eq_int c u
          else less_eq_int l u &&
                 less_eq_int (plus_inta l (modulo_inta (minus_inta c l) m)) u)
    | Ivl (Fin l, PlusInf), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int l c else true)
    | Ivl (PlusInf, u), Some cm -> false;;

let rec ivl_congruence_nonempty
  i c = ivl_congruence_rep_nonempty i (rep_congruence c);;

let rec interval_fact_of_sign
  = function SBot -> bot_ivla
    | SNeg -> Ivl (MinInf, Fin (uminus_inta one_inta))
    | SNonPos -> Ivl (MinInf, Fin zero_inta)
    | SZero -> Ivl (Fin zero_inta, Fin zero_inta)
    | SNonNeg -> Ivl (Fin zero_inta, PlusInf)
    | SPos -> Ivl (Fin one_inta, PlusInf)
    | STop -> top_ivla;;

let rec is_bottom_int_dom
  d = not (ivl_congruence_nonempty
            (intersect_ivl (interval_fact_of_sign (int_sign d)) (int_ivl d))
            (restrict_congruence_by_parity (int_parity d) (int_congruence d)));;

let rec congruence_constant
  c = (match rep_congruence c with None -> None
        | Some (r, m) -> (if equal_inta m zero_inta then Some r else None));;

let rec ivl_constant
  = function Ivl (Fin l, Fin u) -> (if equal_inta l u then Some l else None)
    | Ivl (MinInf, va) -> None
    | Ivl (PlusInf, va) -> None
    | Ivl (v, MinInf) -> None
    | Ivl (v, PlusInf) -> None;;

let rec int_dom_constant
  d = (if equal_signa (int_sign d) SZero then Some zero_inta
        else (match ivl_constant (int_ivl d)
               with None -> congruence_constant (int_congruence d)
               | Some a -> Some a));;

let rec is_top_sign s = equal_signa s STop;;

let rec is_top_int_dom
  d = is_top_sign (int_sign d) &&
        (is_top_ivl (int_ivl d) &&
          (is_top_parity (int_parity d) &&
            is_top_congruence (int_congruence d)));;

let rec string_of_int_dom
  d = (if is_bottom_int_dom d then "<bottom>"
        else (if is_top_int_dom d then "<top>"
               else (match int_dom_constant d
                      with None ->
                        (((((("signs:" ^ string_of_sign (int_sign d)) ^
                              "; intervals:") ^
                             string_of_ivl (int_ivl d)) ^
                            "; parities:") ^
                           string_of_parity (int_parity d)) ^
                          "; congruences:") ^
                          string_of_congruence (int_congruence d)
                      | Some a -> string_of_int a)));;

let rec to_string_int_dom_ext (_A1, _A2) d = string_of_int_dom d;;

let rec is_empty_int_dom_ext (_A1, _A2) d = is_bottom_int_dom d;;

let rec bounded_semilattice_sup_bot_int_dom_ext _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_int_dom_ext _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_int_dom_ext _A)}
    : 'a int_dom_ext bounded_semilattice_sup_bot);;

let rec executable_domain_int_dom_ext (_A1, _A2) =
  ({bounded_semilattice_sup_bot_executable_domain =
      (bounded_semilattice_sup_bot_int_dom_ext _A1);
     order_top_executable_domain = (order_top_int_dom_ext _A1);
     warrowing_executable_domain = (warrowing_int_dom_ext (_A1, _A2));
     is_empty = is_empty_int_dom_ext (_A1, _A2);
     to_string = to_string_int_dom_ext (_A1, _A2)}
    : 'a int_dom_ext executable_domain);;

type ('a, 'b) analysis_product = Product of 'a * 'b;;

let rec equal_analysis_producta _A _B
  (Product (x1, x2)) (Product (y1, y2)) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_analysis_product _A _B =
  ({equal = equal_analysis_producta _A _B} : ('a, 'b) analysis_product equal);;

let rec pright (Product (x1, x2)) = x2;;

let rec pleft (Product (x1, x2)) = x1;;

let rec sup_analysis_producta _A _B
  p q = Product
          (sup _A.sup_semilattice_sup (pleft p) (pleft q),
            sup _B.sup_semilattice_sup (pright p) (pright q));;

let rec sup_analysis_product _A _B =
  ({sup = sup_analysis_producta _A _B} : ('a, 'b) analysis_product sup);;

let rec bot_analysis_producta _A _B
  = Product (bot _A.bot_order_bot, bot _B.bot_order_bot);;

let rec bot_analysis_product _A _B =
  ({bot = bot_analysis_producta _A _B} : ('a, 'b) analysis_product bot);;

let rec less_eq_analysis_product _A _B
  p q = less_eq _A (pleft p) (pleft q) && less_eq _B (pright p) (pright q);;

let rec less_analysis_product _A _B
  p q = less_eq_analysis_product _A _B p q &&
          not (less_eq_analysis_product _A _B q p);;

let rec ord_analysis_product _A _B =
  ({less_eq = less_eq_analysis_product _A _B;
     less = less_analysis_product _A _B}
    : ('a, 'b) analysis_product ord);;

let rec preorder_analysis_product _A _B =
  ({ord_preorder =
      (ord_analysis_product _A.preorder_order.ord_preorder
        _B.preorder_order.ord_preorder)}
    : ('a, 'b) analysis_product preorder);;

let rec order_analysis_product _A _B =
  ({preorder_order = (preorder_analysis_product _A _B)} :
    ('a, 'b) analysis_product order);;

let rec widen_analysis_product (_A1, _A2) (_B1, _B2)
  p q = Product
          (widen _A2.widening_warrowing (pleft p) (pleft q),
            widen _B2.widening_warrowing (pright p) (pright q));;

let rec widening_analysis_product (_A1, _A2) (_B1, _B2) =
  ({order_widening =
      (order_analysis_product
        _A1.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B1.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     widen = widen_analysis_product (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) analysis_product widening);;

let rec order_bot_analysis_product _A _B =
  ({bot_order_bot = (bot_analysis_product _A _B);
     order_order_bot =
       (order_analysis_product _A.order_order_bot _B.order_order_bot)}
    : ('a, 'b) analysis_product order_bot);;

let rec narrow_analysis_product (_A1, _A2) (_B1, _B2)
  p q = Product
          (narrow _A2.narrowing_warrowing (pleft p) (pleft q),
            narrow _B2.narrowing_warrowing (pright p) (pright q));;

let rec narrowing_analysis_product (_A1, _A2) (_B1, _B2) =
  ({order_narrowing =
      (order_analysis_product
        _A1.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B1.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     narrow = narrow_analysis_product (_A1, _A2) (_B1, _B2)}
    : ('a, 'b) analysis_product narrowing);;

let rec warrowing_analysis_product (_A1, _A2) (_B1, _B2) =
  ({narrowing_warrowing = (narrowing_analysis_product (_A1, _A2) (_B1, _B2));
     widening_warrowing = (widening_analysis_product (_A1, _A2) (_B1, _B2))}
    : ('a, 'b) analysis_product warrowing);;

let rec vjoin_analysis_product _A _B
  p q = Product (vjoin _A (pleft p) (pleft q), vjoin _B (pright p) (pright q));;

let rec join_val_analysis_product _A _B =
  ({vjoin = vjoin_analysis_product _A _B} :
    ('a, 'b) analysis_product join_val);;

let rec semilattice_sup_analysis_product _A _B =
  ({sup_semilattice_sup = (sup_analysis_product _A _B);
     order_semilattice_sup =
       (order_analysis_product _A.order_semilattice_sup
         _B.order_semilattice_sup)}
    : ('a, 'b) analysis_product semilattice_sup);;

let rec split_global_at_analysis_product _A _B
  x d = Product
          (split_global_at _A x (pleft d), split_global_at _B x (pright d));;

let rec split_free_analysis_product _A _B
  r = Product (split_free _A r, split_free _B r);;

let rec split_cmb_analysis_product _A _B
  d g = Product
          (split_cmb _A (pleft d) (pleft g),
            split_cmb _B (pright d) (pright g));;

let rec split_rl_analysis_product _A _B
  d = Product (split_rl _A (pleft d), split_rl _B (pright d));;

let rec split_rg_analysis_product _A _B
  d = Product (split_rg _A (pleft d), split_rg _B (pright d));;

let rec ownership_split_analysis_product _A _B =
  ({order_bot_ownership_split =
      (order_bot_analysis_product _A.order_bot_ownership_split
        _B.order_bot_ownership_split);
     split_cmb = split_cmb_analysis_product _A _B;
     split_rl = split_rl_analysis_product _A _B;
     split_global_at = split_global_at_analysis_product _A _B;
     split_rg = split_rg_analysis_product _A _B;
     split_free = split_free_analysis_product _A _B}
    : ('a, 'b) analysis_product ownership_split);;

let rec bounded_semilattice_sup_bot_analysis_product _A _B =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_analysis_product
        _A.semilattice_sup_bounded_semilattice_sup_bot
        _B.semilattice_sup_bounded_semilattice_sup_bot);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_analysis_product _A.order_bot_bounded_semilattice_sup_bot
         _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) analysis_product bounded_semilattice_sup_bot);;

type ('a, 'b) global_unknown = Analysis_Buffer | Analysis_Global of 'a |
  Activation_Seed of cfg_node * 'b;;

let rec equal_global_unknowna _A _B
  x0 x1 = match x0, x1 with
    Analysis_Global x2, Activation_Seed (x31, x32) -> false
    | Activation_Seed (x31, x32), Analysis_Global x2 -> false
    | Analysis_Buffer, Activation_Seed (x31, x32) -> false
    | Activation_Seed (x31, x32), Analysis_Buffer -> false
    | Analysis_Buffer, Analysis_Global x2 -> false
    | Analysis_Global x2, Analysis_Buffer -> false
    | Activation_Seed (x31, x32), Activation_Seed (y31, y32) ->
        equal_cfg_nodea x31 y31 && eq _B x32 y32
    | Analysis_Global x2, Analysis_Global y2 -> eq _A x2 y2
    | Analysis_Buffer, Analysis_Buffer -> true;;

let rec equal_global_unknown _A _B =
  ({equal = equal_global_unknowna _A _B} : ('a, 'b) global_unknown equal);;

type ('a, 'b, 'c) gcom = SKIP of 'a | Assign of 'a * 'b * 'c |
  Check of 'a * (nat * nat) * 'c | Seq of ('a, 'b, 'c) gcom * ('a, 'b, 'c) gcom
  | If of 'a * 'c * ('a, 'b, 'c) gcom * ('a, 'b, 'c) gcom |
  While of 'a * 'c * ('a, 'b, 'c) gcom |
  Call of 'a * 'b option * string * 'c list | Return of 'a * 'c option |
  Restore of 'a | Unwind of 'a;;

let rec equal_gcom _A _B _C
  x0 x1 = match x0, x1 with Restore x9, Unwind x10 -> false
    | Unwind x10, Restore x9 -> false
    | Return (x81, x82), Unwind x10 -> false
    | Unwind x10, Return (x81, x82) -> false
    | Return (x81, x82), Restore x9 -> false
    | Restore x9, Return (x81, x82) -> false
    | Call (x71, x72, x73, x74), Unwind x10 -> false
    | Unwind x10, Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), Restore x9 -> false
    | Restore x9, Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), Return (x81, x82) -> false
    | Return (x81, x82), Call (x71, x72, x73, x74) -> false
    | While (x61, x62, x63), Unwind x10 -> false
    | Unwind x10, While (x61, x62, x63) -> false
    | While (x61, x62, x63), Restore x9 -> false
    | Restore x9, While (x61, x62, x63) -> false
    | While (x61, x62, x63), Return (x81, x82) -> false
    | Return (x81, x82), While (x61, x62, x63) -> false
    | While (x61, x62, x63), Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), While (x61, x62, x63) -> false
    | If (x51, x52, x53, x54), Unwind x10 -> false
    | Unwind x10, If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Restore x9 -> false
    | Restore x9, If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Return (x81, x82) -> false
    | Return (x81, x82), If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), While (x61, x62, x63) -> false
    | While (x61, x62, x63), If (x51, x52, x53, x54) -> false
    | Seq (x41, x42), Unwind x10 -> false
    | Unwind x10, Seq (x41, x42) -> false
    | Seq (x41, x42), Restore x9 -> false
    | Restore x9, Seq (x41, x42) -> false
    | Seq (x41, x42), Return (x81, x82) -> false
    | Return (x81, x82), Seq (x41, x42) -> false
    | Seq (x41, x42), Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), Seq (x41, x42) -> false
    | Seq (x41, x42), While (x61, x62, x63) -> false
    | While (x61, x62, x63), Seq (x41, x42) -> false
    | Seq (x41, x42), If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Seq (x41, x42) -> false
    | Check (x31, x32, x33), Unwind x10 -> false
    | Unwind x10, Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), Restore x9 -> false
    | Restore x9, Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), Return (x81, x82) -> false
    | Return (x81, x82), Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), While (x61, x62, x63) -> false
    | While (x61, x62, x63), Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), Seq (x41, x42) -> false
    | Seq (x41, x42), Check (x31, x32, x33) -> false
    | Assign (x21, x22, x23), Unwind x10 -> false
    | Unwind x10, Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), Restore x9 -> false
    | Restore x9, Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), Return (x81, x82) -> false
    | Return (x81, x82), Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), While (x61, x62, x63) -> false
    | While (x61, x62, x63), Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), Seq (x41, x42) -> false
    | Seq (x41, x42), Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), Assign (x21, x22, x23) -> false
    | SKIP x1, Unwind x10 -> false
    | Unwind x10, SKIP x1 -> false
    | SKIP x1, Restore x9 -> false
    | Restore x9, SKIP x1 -> false
    | SKIP x1, Return (x81, x82) -> false
    | Return (x81, x82), SKIP x1 -> false
    | SKIP x1, Call (x71, x72, x73, x74) -> false
    | Call (x71, x72, x73, x74), SKIP x1 -> false
    | SKIP x1, While (x61, x62, x63) -> false
    | While (x61, x62, x63), SKIP x1 -> false
    | SKIP x1, If (x51, x52, x53, x54) -> false
    | If (x51, x52, x53, x54), SKIP x1 -> false
    | SKIP x1, Seq (x41, x42) -> false
    | Seq (x41, x42), SKIP x1 -> false
    | SKIP x1, Check (x31, x32, x33) -> false
    | Check (x31, x32, x33), SKIP x1 -> false
    | SKIP x1, Assign (x21, x22, x23) -> false
    | Assign (x21, x22, x23), SKIP x1 -> false
    | Unwind x10, Unwind y10 -> eq _A x10 y10
    | Restore x9, Restore y9 -> eq _A x9 y9
    | Return (x81, x82), Return (y81, y82) ->
        eq _A x81 y81 && equal_option _C x82 y82
    | Call (x71, x72, x73, x74), Call (y71, y72, y73, y74) ->
        eq _A x71 y71 &&
          (equal_option _B x72 y72 &&
            (((x73 : string) = y73) && equal_lista _C x74 y74))
    | While (x61, x62, x63), While (y61, y62, y63) ->
        eq _A x61 y61 && (eq _C x62 y62 && equal_gcom _A _B _C x63 y63)
    | If (x51, x52, x53, x54), If (y51, y52, y53, y54) ->
        eq _A x51 y51 &&
          (eq _C x52 y52 &&
            (equal_gcom _A _B _C x53 y53 && equal_gcom _A _B _C x54 y54))
    | Seq (x41, x42), Seq (y41, y42) ->
        equal_gcom _A _B _C x41 y41 && equal_gcom _A _B _C x42 y42
    | Check (x31, x32, x33), Check (y31, y32, y33) ->
        eq _A x31 y31 &&
          (equal_proda equal_nat equal_nat x32 y32 && eq _C x33 y33)
    | Assign (x21, x22, x23), Assign (y21, y22, y23) ->
        eq _A x21 y21 && (eq _B x22 y22 && eq _C x23 y23)
    | SKIP x1, SKIP y1 -> eq _A x1 y1;;

type ('a, 'b, 'c, 'd) gproc_decl_ext =
  Gproc_decl_ext of 'b list * ('a, 'b, 'c) gcom * 'd;;

let rec equal_gproc_decl_exta _A _B _C _D
  (Gproc_decl_ext (formalsa, bodya, morea))
    (Gproc_decl_ext (formals, body, more)) =
    equal_lista _B formalsa formals &&
      (equal_gcom _A _B _C bodya body && eq _D morea more);;

let rec equal_gproc_decl_ext _A _B _C _D =
  ({equal = equal_gproc_decl_exta _A _B _C _D} :
    ('a, 'b, 'c, 'd) gproc_decl_ext equal);;

type 'a itself = Type;;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type ('b, 'a) rbt = RBT of ('b, 'a) rbta;;

type 'a fset = Abs_fset of 'a set;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

type phase = Widening | Narrowing;;

type 'a trace_key = Trace_Buffer | Trace_Global of string |
  Trace_Seed of cfg_node * 'a;;

type ('a, 'b, 'c) gcfg_ext =
  Gcfg_ext of
    (cfg_node * (('a, 'b) gedge_action * cfg_node)) set *
      (cfg_node * (('a, 'b) gcall_action * (cfg_node * cfg_node))) set *
      cfg_node * (cfg_node * 'b) set * 'c;;

type ('a, 'b, 'c) route_event = Ev_Route of 'a * 'b * 'c;;

type typed_answer = Typed_Malformed | Typed_No_Answer |
  Typed_Analysed of (cfg_node * (texp * check_result)) list;;

type typed_domain = Typed_Interval | Typed_Congruence | Typed_Int | Typed_Order
  | Typed_Sign | Typed_Parity;;

type 'a ganalysis_event = Check_Event of (nat * nat) * 'a;;

type ('a, 'b, 'c, 'd) state_ext =
  State_ext of
    'a set * (('a, 'b) sum, ('a list)) fmap * 'a set * (('a, 'b) sum -> 'c) *
      'd;;

type ('a, 'b, 'c) strategy_tree = Answer of 'c |
  QueryL of 'a * ('c -> ('a, 'b, 'c) strategy_tree) |
  QueryG of 'b * ('c -> ('a, 'b, 'c) strategy_tree) |
  Side of 'b * 'c * ('a, 'b, 'c) strategy_tree;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) gman_ext =
  Gman_ext of
    'e * ('d ->
           ('f -> ('b, 'c, ('e, 'f) dg_state) strategy_tree) ->
             ('b, 'c, ('e, 'f) dg_state) strategy_tree) *
      ('d ->
        'f -> (unit -> ('b, 'c, ('e, 'f) dg_state) strategy_tree) ->
                ('b, 'c, ('e, 'f) dg_state) strategy_tree) *
      ('a gquery ->
        (unit int_dom_ext query_lift ->
          ('b, 'c, ('e, 'f) dg_state) strategy_tree) ->
          ('b, 'c, ('e, 'f) dg_state) strategy_tree) *
      'g;;

type 'a analysis_context = Context_Unit | Context_Entry of 'a list |
  Context_Call_String of cfg_node list;;

type 'a field_state = Field_Store of (string * 'a) list | Field_Whole of 'a;;

type abstract_value = SignValue of sign | IntervalValue of ivl |
  ParityValue of parity | IntDomValue of unit int_dom_ext |
  IntDomOnceValue of unit int_dom_ext | IntDomNeverValue of unit int_dom_ext |
  CongruenceValue of congruence |
  OrderValue of ((string * string) list) option;;

type ('a, 'b, 'c, 'd) trace_printers =
  Trace_Printers of
    ('a -> abstract_value analysis_context) * ('b -> 'a trace_key) *
      ('c -> ((analysis_domain * abstract_value field_state) list) lifted) *
      (string option ->
        'c -> ((analysis_domain * abstract_value field_state) list) lifted) *
      ('d -> ((analysis_domain * abstract_value field_state) list) lifted);;

type globals_rule = Globals_Join | Globals_Per_Origin | Globals_Warrow |
  Globals_Warrow_Per_Origin | Globals_Bounded_Narrowing of nat;;

type ('a, 'b) solved_table =
  Solved_Table of (cfg_node * 'a) set * (cfg_node -> 'a -> 'b lifted);;

type ('a, 'b, 'c) solver_event = Ev_Start of 'a | Ev_Stop |
  Ev_Query of 'a * 'a * bool * bool | Ev_Query_Wpoint of 'a * bool |
  Ev_Iterate_From_Query of 'a | Ev_Add_Infl of ('a, 'b) sum * 'a |
  Ev_Answer of 'a * 'a * 'c | Ev_Query_Global of 'a * 'b |
  Ev_Answer_Global of 'a * 'b * 'c | Ev_Iterate of 'a * bool * bool * bool |
  Ev_Eq of 'a | Ev_Rhs of 'a * 'c | Ev_Still_Unstable of 'a |
  Ev_Widen of 'a * bool | Ev_Sol of 'a * bool * 'c * 'c * 'c |
  Ev_Wpoint_Remove of 'a * bool | Ev_Wpoint_Clear of 'a * bool |
  Ev_Update of 'a * bool * bool * 'c * 'c | Ev_Iterate_Changed of 'a |
  Ev_Side of 'a * 'b * 'c | Ev_Update_Global of 'a * 'b * bool * 'c * 'c |
  Ev_Destabilize of ('a, 'b) sum | Ev_Stable_Remove of 'a;;

type special_desc = SD_Nondet_Int | SD_Min | SD_Max;;

type report_context = Report_Unit |
  Report_Entry of
    ((sign list),
      ((ivl list),
        ((parity list),
          ((unit int_dom_ext list),
            ((unit int_dom_ext list),
              ((unit int_dom_ext list),
                ((congruence list), (unit list)) analysis_product)
                analysis_product)
              analysis_product)
            analysis_product)
          analysis_product)
        analysis_product)
      analysis_product
  | Report_Call_String of cfg_node list;;

type context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString of nat;;

type unknown_node = Local_Node of cfg_node * nat | Global_Node of string;;

type 'a analysis_answer = Invalid_Activation | Malformed_Program | No_Answer |
  Analysed of 'a;;

type program_globals = Program_Globals_Flow_Sensitive |
  Program_Globals_Flow_Insensitive;;

type analysis_config =
  Analysis_Config of
    analysis_domain list * globals_rule * context_mode * program_globals;;

type analysis_edge = Intra_Dep of (string, exp) gedge_action |
  Enter_Dep of (string, exp) gcall_action |
  Combine_Dep of (string, exp) gcall_action |
  Continue_Dep of (string, exp) gcall_action | Global_Read | Global_Write;;

type ('a, 'b, 'c) gcall_info_ext =
  Gcall_info_ext of 'a option * string * 'a list * 'b list * 'c;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) gdg_spec_ext =
  Gdg_spec_ext of
    (('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
      ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
        ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      ('a ->
        'b -> ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
                ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
                  ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      ('b gspecial_call ->
        'a -> ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
                ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
                  ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      ('b ->
        bool ->
          ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
            ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
              ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      (string ->
        ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
          ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
            ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      ('b option ->
        string ->
          ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
            ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
              ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      (('a, 'b, unit) gcall_info_ext ->
        ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
          (('f * 'f) list -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
            ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      ('b ganalysis_event ->
        ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
          ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
            ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      (('a, 'b, unit) gcall_info_ext ->
        ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
          'f -> ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
                  ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      (('a, 'b, unit) gcall_info_ext ->
        ('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
          'f -> ('f -> ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
                  ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      (('b, 'c, 'd, 'e, 'f, 'g, unit) gman_ext ->
        'b gquery ->
          (unit int_dom_ext query_lift ->
            ('c, 'd, ('f, 'g) dg_state) strategy_tree) ->
            ('c, 'd, ('f, 'g) dg_state) strategy_tree) *
      'h;;

type ('a, 'b) state_exta = State_exta of 'a set * 'b;;

type result_global_unknown = Global_Named of string |
  Global_Seed of string * nat option;;

type ('a, 'b, 'c, 'd) ug_state_ext =
  Ug_state_ext of ('b -> ('a, 'c) fmap) * 'd;;

type 'a imp_prog_ext =
  Imp_prog_ext of
    (string * (unit, string, exp, unit) gproc_decl_ext) list * string list *
      'a;;

type ('a, 'b, 'c, 'd) glocal_spec_ext =
  Glocal_spec_ext of
    (('b gquery -> unit int_dom_ext query_lift) ->
      'c -> 'b gquery -> unit int_dom_ext query_lift) *
      (('b gquery -> unit int_dom_ext query_lift) -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) -> 'a -> 'b -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        'b gspecial_call -> 'a -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) -> 'b -> bool -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) -> string -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        'b option -> string -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        'b ganalysis_event -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        ('a, 'b, unit) gcall_info_ext -> 'c * 'c -> ('c * 'c) list) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        ('b gquery -> unit int_dom_ext query_lift) ->
          ('a, 'b, unit) gcall_info_ext -> 'c -> 'c -> 'c) *
      (('b gquery -> unit int_dom_ext query_lift) ->
        ('a, 'b, unit) gcall_info_ext -> 'c -> 'c -> 'c) *
      'd;;

type 'a call_route_ext =
  Call_route_ext of cfg_node * nat * string * nat list * 'a;;

type ('a, 'b, 'c, 'd, 'e, 'f) gsolved_run_ext =
  Gsolved_run_ext of
    ('c, 'e) solved_table * ('d -> 'e lifted) * (string -> 'c -> 'e lifted) *
      (cfg_node -> 'c -> ('a, 'b) gedge_action -> 'e lifted) *
      (cfg_node -> 'c -> ('a, 'b) gcall_action -> string -> 'c option) * 'f;;

type ('a, 'b) refine_ops_ext =
  Refine_ops_ext of
    ('a -> bool option) * (bool -> 'a -> 'a -> 'a * 'a) *
      (bool -> 'a -> 'a -> 'a * 'a) * ('a -> 'a -> 'a -> 'a * 'a) *
      ('a -> 'a -> 'a -> 'a * 'a) * ('a -> 'a -> 'a -> 'a * 'a) *
      ('a -> 'a -> 'a) * 'b;;

type ('a, 'b) special_ops_ext =
  Special_ops_ext of ('a -> 'a -> 'a) * ('a -> 'a -> 'a) * 'b;;

type 'a analysis_graph_ext =
  Analysis_graph_ext of
    unknown_node list * (unknown_node * (analysis_edge * unknown_node)) list *
      'a;;

type arithmetic_obligation = Arithmetic_Obligation of exp * exp;;

type arithmetic_diagnostic =
  Arithmetic_Diagnostic of
    cfg_node * nat * arithmetic_obligation * check_result;;

type ('a, 'b) result_global_ext =
  Result_global_ext of result_global_unknown * 'a lifted * 'b;;

type ('a, 'b) result_state_ext =
  Result_state_ext of
    cfg_node * nat * 'a lifted * (exp * check_result lifted) list *
      (arithmetic_obligation * check_result lifted) list *
      (cfg_node * 'a lifted) list * 'b;;

type 'a result_check_ext =
  Result_check_ext of cfg_node * (nat * nat) * exp * check_result lifted * 'a;;

type ('a, 'b) run_result_ext =
  Run_result_ext of
    (string, exp, unit) gcfg_ext * 'a analysis_context list *
      (((analysis_domain * 'a field_state) list), unit) result_state_ext list *
      (cfg_node *
        (((analysis_domain * 'a field_state) list) lifted *
          (cfg_node *
            ((analysis_domain * 'a field_state) list) lifted) list)) list *
      unit call_route_ext list * unit result_check_ext list *
      (((analysis_domain * 'a field_state) list), unit) result_global_ext list *
      arithmetic_diagnostic list * unit analysis_graph_ext * 'b;;

type ('a, 'b) query_ops_ext =
  Query_ops_ext of ('a -> 'a -> bool option) * ('a -> 'a -> bool option) * 'b;;

type ('a, 'b, 'c, 'd) func_state =
  Q of ('a * ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext)))
  | I of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                 ('a, 'b, 'c, 'd) ug_state_ext))
  | Ra of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                  ('a, 'b, 'c, 'd) ug_state_ext))
  | E of ('a * (('a, 'b, 'c) strategy_tree *
                 (('b -> 'c) *
                   (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext))));;

type 'a analysis_report_ext =
  Analysis_report_ext of
    analysis_config * string list * (string, exp, unit) gcfg_ext *
      report_context list *
      (((string -> sign) lifted,
         ((string -> ivl) lifted,
           ((string -> parity) lifted,
             ((string -> unit int_dom_ext) lifted,
               ((string -> unit int_dom_ext) lifted,
                 ((string -> unit int_dom_ext) lifted,
                   ((string -> congruence) lifted, relc) analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product,
        unit)
        result_state_ext list *
      unit call_route_ext list * unit result_check_ext list *
      (((string -> sign) lifted,
         ((string -> ivl) lifted,
           ((string -> parity) lifted,
             ((string -> unit int_dom_ext) lifted,
               ((string -> unit int_dom_ext) lifted,
                 ((string -> unit int_dom_ext) lifted,
                   ((string -> congruence) lifted, relc) analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product,
        unit)
        result_global_ext list *
      arithmetic_diagnostic list * 'a;;

type ('a, 'b, 'c) ug_state_with_gas_ext =
  Ug_state_with_gas_ext of ('b -> 'a -> phase * nat) * 'c;;

type ('a, 'b) nonrelational_ops_ext =
  Nonrelational_ops_ext of
    (exp -> (string -> 'a) -> 'a) * ('a, unit) query_ops_ext *
      ('a, unit) refine_ops_ext * ('a, unit) special_ops_ext * 'b;;

type 'a analysis_registration_ext =
  Analysis_registration_ext of
    ((string -> bool) ->
      unit imp_prog_ext ->
        (string, exp,
          ((string, sign) gdefault_st lifted,
            ((string, ivl) gdefault_st lifted,
              ((string, parity) gdefault_st lifted,
                ((string, unit int_dom_ext) gdefault_st lifted,
                  ((string, unit int_dom_ext) gdefault_st lifted,
                    ((string, unit int_dom_ext) gdefault_st lifted,
                      ((string, congruence) gdefault_st lifted, relc)
                        analysis_product)
                      analysis_product)
                    analysis_product)
                  analysis_product)
                analysis_product)
              analysis_product)
            analysis_product
            lifted,
          unit)
          glocal_spec_ext) *
      (((string, sign) gdefault_st lifted,
         ((string, ivl) gdefault_st lifted,
           ((string, parity) gdefault_st lifted,
             ((string, unit int_dom_ext) gdefault_st lifted,
               ((string, unit int_dom_ext) gdefault_st lifted,
                 ((string, unit int_dom_ext) gdefault_st lifted,
                   ((string, congruence) gdefault_st lifted, relc)
                     analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product ->
        bool) *
      (string list ->
        ((string, sign) gdefault_st lifted,
          ((string, ivl) gdefault_st lifted,
            ((string, parity) gdefault_st lifted,
              ((string, unit int_dom_ext) gdefault_st lifted,
                ((string, unit int_dom_ext) gdefault_st lifted,
                  ((string, unit int_dom_ext) gdefault_st lifted,
                    ((string, congruence) gdefault_st lifted, relc)
                      analysis_product)
                    analysis_product)
                  analysis_product)
                analysis_product)
              analysis_product)
            analysis_product)
          analysis_product ->
          bool) *
      (((string -> sign) lifted,
         ((string -> ivl) lifted,
           ((string -> parity) lifted,
             ((string -> unit int_dom_ext) lifted,
               ((string -> unit int_dom_ext) lifted,
                 ((string -> unit int_dom_ext) lifted,
                   ((string -> congruence) lifted, relc) analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product ->
        exp gquery -> unit int_dom_ext query_lift) *
      (((string -> sign) lifted,
         ((string -> ivl) lifted,
           ((string -> parity) lifted,
             ((string -> unit int_dom_ext) lifted,
               ((string -> unit int_dom_ext) lifted,
                 ((string -> unit int_dom_ext) lifted,
                   ((string -> congruence) lifted, relc) analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product ->
        string list -> abstract_value field_state) *
      (((sign list),
         ((ivl list),
           ((parity list),
             ((unit int_dom_ext list),
               ((unit int_dom_ext list),
                 ((unit int_dom_ext list),
                   ((congruence list), (unit list)) analysis_product)
                   analysis_product)
                 analysis_product)
               analysis_product)
             analysis_product)
           analysis_product)
         analysis_product ->
        abstract_value list) *
      'a;;

let rec id x = (fun xa -> xa) x;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then []
          else x :: take (minus_nat n one_nat) xs);;

let rec empty _A = RBT Empty;;

let rec image f (Set xs) = Set (map f xs);;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if less _A x k then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec impl_of _B (RBT x) = x;;

let rec insert _A
  xc xd xe =
    RBT (rbt_insert _A.order_linorder.preorder_order.ord_preorder xc xd
          (impl_of _A xe));;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if less _A k x then rbt_lookup _A l k
          else (if less _A x k then rbt_lookup _A r k else Some y));;

let rec lookup _A
  x = rbt_lookup _A.order_linorder.preorder_order.ord_preorder (impl_of _A x);;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec inserta _A
  x xa1 = match x, xa1 with x, Set xs -> Set (insertb _A x xs)
    | x, Coset xs -> Coset (removeAll _A x xs);;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fset (Abs_fset x) = x;;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec hd (x21 :: x22) = x21;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec the_elem _A
  (Set xs) =
    (match remdups _A xs
      with [] ->
        failwith "the_elem: not a singleton" (fun _ -> the_elem _A (Set xs))
      | [x] -> x
      | _ :: _ :: _ ->
        failwith "the_elem: not a singleton" (fun _ -> the_elem _A (Set xs)));;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec enumerate n x1 = match n, x1 with n, [] -> []
                    | n, x :: xs -> (n, x) :: enumerate (suc n) xs;;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec ik_unsigned_of = function I8 -> U8
                         | U8 -> U8
                         | I16 -> U16
                         | U16 -> U16
                         | I32 -> U32
                         | U32 -> U32
                         | I64 -> U64
                         | U64 -> U64;;

let rec ik_promote
  ik = (if less_nat (ik_bits ik) (ik_bits I32) then I32 else ik);;

let rec usual_kind
  a0 b0 =
    (let a = ik_promote a0 in
     let b = ik_promote b0 in
      (if equal_ikind a b then a
        else (if equal_boola (ik_signed a) (ik_signed b)
               then (if less_nat (ik_bits a) (ik_bits b) then b else a)
               else (let s = (if ik_signed a then a else b) in
                     let u = (if ik_signed a then b else a) in
                      (if less_eq_nat (ik_bits s) (ik_bits u) then u
                        else (if less_eq_int (ik_max u) (ik_max s) then s
                               else ik_unsigned_of s))))));;

let rec ik_of_lit
  n = (if less_eq_int (abs_int n) (ik_max I32) then I32 else I64);;

let rec esyn
  gamma x1 = match gamma, x1 with gamma, N n -> ik_of_lit n
    | gamma, V x -> gamma x
    | gamma, Plus (a, b) -> usual_kind (esyn gamma a) (esyn gamma b)
    | gamma, Minus (a, b) -> usual_kind (esyn gamma a) (esyn gamma b)
    | gamma, Times (a, b) -> usual_kind (esyn gamma a) (esyn gamma b)
    | gamma, Div (a, b) -> usual_kind (esyn gamma a) (esyn gamma b)
    | gamma, Mod (a, b) -> usual_kind (esyn gamma a) (esyn gamma b)
    | gamma, Less (a, b) -> I32
    | gamma, LessEq (a, b) -> I32
    | gamma, Greater (a, b) -> I32
    | gamma, GreaterEq (a, b) -> I32
    | gamma, NotEq (a, b) -> I32
    | gamma, Eq (a, b) -> I32
    | gamma, Not a -> I32
    | gamma, And (a, b) -> I32
    | gamma, Or (a, b) -> I32
    | gamma, Cast (ik, a) -> ik;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let ret_var : string = "#ret";;

let rec var_name = function GlobalId x -> x
                   | ScopedId (uu, x) -> x
                   | ReturnId uv -> ret_var
                   | ReturnVar -> ret_var;;

let rec cfg_entry
  (Gcfg_ext (intra, calls, cfg_entry, checks, more)) = cfg_entry;;

let rec cfg_exit
  g = (match cfg_entry g
        with Statement nat ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> Statement nat)
        | FunctionEntry a -> FunctionResult a
        | FunctionResult literal ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> FunctionResult literal));;

let rec sp_return a k = k a;;

let rec man_ask_update
  man_aska (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) =
    Gman_ext (man_local, man_global, man_sideg, man_aska man_ask, more);;

let rec ask_with _A
  qa n asked m q =
    (if equal_nata n zero_nat
      then failwith "query recursion exceeded query_depth"
             (fun _ ->
               sp_return
                 (top_query_lifta (order_int_dom_ext bounded_lattice_unit)))
      else (if member (equal_gquery _A) q asked
             then sp_return
                    (top_query_lifta (order_int_dom_ext bounded_lattice_unit))
             else qa (man_ask_update
                       (fun _ ->
                         ask_with _A qa (minus_nat n one_nat)
                           (inserta (equal_gquery _A) q asked) m)
                       m)
                    q));;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec ask_rec _A
  h n asked x q =
    (if equal_nata n zero_nat
      then failwith "query recursion exceeded query_depth"
             (fun _ -> top_query_lifta (order_int_dom_ext bounded_lattice_unit))
      else (if member (equal_gquery _A) q asked
             then top_query_lifta (order_int_dom_ext bounded_lattice_unit)
             else h (ask_rec _A h (minus_nat n one_nat)
                      (inserta (equal_gquery _A) q asked) x)
                    x
                    q));;

let rec ls_combine_assign
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_combine_assign;;

let rec ls_combine_env
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_combine_env;;

let rec ls_query
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_query;;

let rec ls_enter
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_enter;;

let rec event_action (Check_Event (l, cnd)) = EA_Check (l, cnd);;

let rec make_local_spec
  qry st en ce ca =
    Glocal_spec_ext
      (qry, (fun ch -> st ch EA_Nop), (fun ch x e -> st ch (EA_Assign (x, e))),
        (fun ch sc x -> st ch (EA_Special (sc, x))),
        (fun ch b pol -> st ch (if pol then EA_Assume b else EA_AssumeNot b)),
        (fun ch p -> st ch (EA_Body p)), (fun ch r p -> st ch (EA_Ret (r, p))),
        (fun ch ev -> st ch (event_action ev)), en, ce, ca, ());;

let rec ls_special
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_special;;

let rec ls_return
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_return;;

let rec ls_branch
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_branch;;

let rec ls_assign
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_assign;;

let rec ls_event
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_event;;

let rec ls_skip
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_skip;;

let rec ls_body
  (Glocal_spec_ext
    (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
      ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = ls_body;;

let rec local_spec_step
  sk asn sp br bd rt ev x7 = match sk, asn, sp, br, bd, rt, ev, x7 with
    sk, asn, sp, br, bd, rt, ev, EA_Nop -> sk
    | sk, asn, sp, br, bd, rt, ev, EA_Assign (x, e) -> asn x e
    | sk, asn, sp, br, bd, rt, ev, EA_Special (sc, x) -> sp sc x
    | sk, asn, sp, br, bd, rt, ev, EA_Assume b -> br b true
    | sk, asn, sp, br, bd, rt, ev, EA_AssumeNot b -> br b false
    | sk, asn, sp, br, bd, rt, ev, EA_Body p -> bd p
    | sk, asn, sp, br, bd, rt, ev, EA_Ret (e, p) -> rt e p
    | sk, asn, sp, br, bd, rt, ev, EA_Check (l, cnd) ->
        ev (Check_Event (l, cnd));;

let rec ls_step
  c ch =
    local_spec_step (ls_skip c ch) (ls_assign c ch) (ls_special c ch)
      (ls_branch c ch) (ls_body c ch) (ls_return c ch) (ls_event c ch);;

let rec lens_of
  get put c =
    make_local_spec (fun ch x -> ls_query c ch (get x))
      (fun ch a x -> put x (ls_step c ch a (get x)))
      (fun ch ci p ->
        map (fun (q, e) -> (put (fst p) q, put (snd p) e))
          (ls_enter c ch ci (get (fst p), get (snd p))))
      (fun ch cha ci x de ->
        put x (ls_combine_env c ch cha ci (get x) (get de)))
      (fun ch ci x de -> put x (ls_combine_assign c ch ci (get x) (get de)));;

let rec inf_query_lift _A x0 uu = match x0, uu with QBot, uu -> QBot
                            | QLifted v, QBot -> QBot
                            | QTop, QBot -> QBot
                            | QTop, QLifted v -> QLifted v
                            | QTop, QTop -> QTop
                            | QLifted v, QTop -> QLifted v
                            | QLifted a, QLifted b -> QLifted (inf _A a b);;

let rec mcp_qry
  cs ch x q =
    fold (fun c r ->
           inf_query_lift (inf_int_dom_ext bounded_lattice_unit) r
             (ls_query c ch x q))
      cs (top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let bot_set : 'a set = Set [];;

let query_depth : nat = nat_of_integer (Z.of_int 1024);;

let rec outer_man _A
  q m = man_ask_update (fun _ -> ask_with _A q query_depth bot_set m) m;;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filtera (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (eq _A aa a));;

let rec slot1 r = pleft r;;

let rec slot2 r = pleft (pright r);;

let rec slot3 r = pleft (pright (pright r));;

let rec slot4 r = pleft (pright (pright (pright r)));;

let rec slot5 r = pleft (pright (pright (pright (pright r))));;

let rec slot6 r = pleft (pright (pright (pright (pright (pright r)))));;

let rec slot7
  r = pleft (pright (pright (pright (pright (pright (pright r))))));;

let rec slot8
  r = pright (pright (pright (pright (pright (pright (pright r))))));;

let rec lift_get _B f x = (match x with Bot -> bot _B | Lifted a -> f a);;

let rec lift_put _A (_B1, _B2)
  u x v =
    (match x
      with Bot -> (if eq _B1 v (bot _B2) then Bot else Lifted (u (bot _A) v))
      | Lifted r -> Lifted (u r v));;

let rec mcp_comb
  cs cha ch ci x de =
    fold (fun c y ->
           ls_combine_assign c ch ci (ls_combine_env c cha ch ci y de) de)
      cs x;;

let rec mcp_step cs ch a x = fold (fun c -> ls_step c ch a) cs x;;

let rec ls_query_update
  ls_querya
    (Glocal_spec_ext
      (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
        ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = Glocal_spec_ext
        (ls_querya ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body,
          ls_return, ls_event, ls_enter, ls_combine_env, ls_combine_assign,
          more);;

let rec with_qry h c = ls_query_update (fun _ -> h) c;;

let rec aop_exp = function AAdd -> (fun a b -> Plus (a, b))
                  | ASub -> (fun a b -> Minus (a, b))
                  | AMul -> (fun a b -> Times (a, b))
                  | ADiv -> (fun a b -> Div (a, b))
                  | AMod -> (fun a b -> Mod (a, b));;

let rec cop_exp = function CLt -> (fun a b -> Less (a, b))
                  | CLe -> (fun a b -> LessEq (a, b))
                  | CGt -> (fun a b -> Greater (a, b))
                  | CGe -> (fun a b -> GreaterEq (a, b))
                  | CEq -> (fun a b -> Eq (a, b))
                  | CNe -> (fun a b -> NotEq (a, b));;

let rec ik_widens
  k ik =
    less_eq_int (ik_min ik) (ik_min k) && less_eq_int (ik_max k) (ik_max ik);;

let rec texp_kind = function TN (ik, uu) -> ik
                    | TVar (ik, uv) -> ik
                    | TArith (ik, uw, ux, uy) -> ik
                    | TCast (ik, uz) -> ik
                    | TCmp (va, vb, vc) -> I32
                    | TNot vd -> I32
                    | TAnd (ve, vf) -> I32
                    | TOr (vg, vh) -> I32;;

let rec lower
  = function TN (ik, n) -> N (ik_norm ik n)
    | TVar (ik, v) -> Cast (ik, V (var_name v))
    | TArith (ik, op, a, b) -> Cast (ik, aop_exp op (lower a) (lower b))
    | TCast (ik, a) ->
        (if ik_widens (texp_kind a) ik then lower a else Cast (ik, lower a))
    | TCmp (op, a, b) -> cop_exp op (lower a) (lower b)
    | TNot a -> Not (lower a)
    | TAnd (a, b) -> And (lower a, lower b)
    | TOr (a, b) -> Or (lower a, lower b);;

let rec calls (Gcfg_ext (intra, calls, cfg_entry, checks, more)) = calls;;

let rec intra (Gcfg_ext (intra, calls, cfg_entry, checks, more)) = intra;;

let rec genv key tau v = dg_global (tau (Inr (key v)));;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec location_of
  g x = (if g x then Global_Location x else Local_Location x);;

let rec default_st_to_fun _A _B
  g s x = default_st_get _A _B s (location_of g x);;

let rec mcp_rd
  g r = Product
          (map_lift (default_st_to_fun equal_literal bot_sign g) (slot1 r),
            Product
              (map_lift (default_st_to_fun equal_literal bot_ivl g) (slot2 r),
                Product
                  (map_lift (default_st_to_fun equal_literal bot_parity g)
                     (slot3 r),
                    Product
                      (map_lift
                         (default_st_to_fun equal_literal
                           (bot_int_dom_ext bounded_lattice_unit) g)
                         (slot4 r),
                        Product
                          (map_lift
                             (default_st_to_fun equal_literal
                               (bot_int_dom_ext bounded_lattice_unit) g)
                             (slot5 r),
                            Product
                              (map_lift
                                 (default_st_to_fun equal_literal
                                   (bot_int_dom_ext bounded_lattice_unit) g)
                                 (slot6 r),
                                Product
                                  (map_lift
                                     (default_st_to_fun equal_literal
                                       bot_congruence g)
                                     (slot7 r),
                                    slot8 r)))))));;

let rec infl (State_ext (called, infl, stabl, sigma, more)) = infl;;

let rec tcast_to ik k a = (if equal_ikind ik k then a else TCast (ik, a));;

let rec elaborate
  rho kappa ik x3 = match rho, kappa, ik, x3 with
    rho, kappa, ik, N n -> TN (ik, n)
    | rho, kappa, ik, V x ->
        tcast_to ik (kappa (rho x)) (TVar (kappa (rho x), rho x))
    | rho, kappa, ik, Plus (a, b) ->
        (let k = esyn (comp kappa rho) (Plus (a, b)) in
          tcast_to ik k
            (TArith
              (k, AAdd, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Minus (a, b) ->
        (let k = esyn (comp kappa rho) (Minus (a, b)) in
          tcast_to ik k
            (TArith
              (k, ASub, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Times (a, b) ->
        (let k = esyn (comp kappa rho) (Times (a, b)) in
          tcast_to ik k
            (TArith
              (k, AMul, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Div (a, b) ->
        (let k = esyn (comp kappa rho) (Div (a, b)) in
          tcast_to ik k
            (TArith
              (k, ADiv, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Mod (a, b) ->
        (let k = esyn (comp kappa rho) (Mod (a, b)) in
          tcast_to ik k
            (TArith
              (k, AMod, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Less (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CLt, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, LessEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CLe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Greater (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CGt, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, GreaterEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CGe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, NotEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CNe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Eq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          tcast_to ik I32
            (TCmp (CEq, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Not a ->
        tcast_to ik I32 (TNot (elaborate rho kappa (esyn (comp kappa rho) a) a))
    | rho, kappa, ik, And (a, b) ->
        tcast_to ik I32
          (TAnd (elaborate rho kappa (esyn (comp kappa rho) a) a,
                  elaborate rho kappa (esyn (comp kappa rho) b) b))
    | rho, kappa, ik, Or (a, b) ->
        tcast_to ik I32
          (TOr (elaborate rho kappa (esyn (comp kappa rho) a) a,
                 elaborate rho kappa (esyn (comp kappa rho) b) b))
    | rho, kappa, ik, Cast (k, a) ->
        tcast_to ik k
          (TCast (k, elaborate rho kappa (esyn (comp kappa rho) a) a));;

let rec elaborate_syn
  rho kappa e = elaborate rho kappa (esyn (comp kappa rho) e) e;;

let rec elab_args
  rho kappa x2 es = match rho, kappa, x2, es with
    rho, kappa, f :: fs, e :: es ->
      elaborate rho kappa (kappa f) e :: elab_args rho kappa fs es
    | rho, kappa, [], es -> map (elaborate_syn rho kappa) es
    | rho, kappa, v :: va, [] -> [];;

let rec resolve_var g q x = (if g x then GlobalId x else ScopedId (q, x));;

let rec elab_com
  g fm kappa q x4 = match g, fm, kappa, q, x4 with
    g, fm, kappa, q, SKIP i -> SKIP i
    | g, fm, kappa, q, Assign (i, x, e) ->
        Assign
          (i, resolve_var g q x,
            elaborate (resolve_var g q) kappa (kappa (resolve_var g q x)) e)
    | g, fm, kappa, q, Check (i, l, c) ->
        Check (i, l, elaborate_syn (resolve_var g q) kappa c)
    | g, fm, kappa, q, Seq (c1, c2) ->
        Seq (elab_com g fm kappa q c1, elab_com g fm kappa q c2)
    | g, fm, kappa, q, If (i, b, c1, c2) ->
        If (i, elaborate_syn (resolve_var g q) kappa b,
             elab_com g fm kappa q c1, elab_com g fm kappa q c2)
    | g, fm, kappa, q, While (i, b, c) ->
        While (i, elaborate_syn (resolve_var g q) kappa b,
                elab_com g fm kappa q c)
    | g, fm, kappa, q, Call (i, dst, p, es) ->
        Call (i, map_option (resolve_var g q) dst, p,
               elab_args (resolve_var g q) kappa (map (resolve_var g p) (fm p))
                 es)
    | g, fm, kappa, q, Return (i, e) ->
        Return
          (i, map_option
                (elaborate (resolve_var g q) kappa (kappa (ReturnId q))) e)
    | g, fm, kappa, q, Restore i -> Restore i
    | g, fm, kappa, q, Unwind i -> Unwind i;;

let rec sp_publish g d k = Side (g, d, k ());;

let rec dg_sideg _D gk gd = sp_publish gk (DG (bot _D, gd));;

let rec man_local
  (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) = man_local;;

let rec local_query h m q = sp_return (h (man_local m) q);;

let rec parity_eq_false
  a b = match a, b with PEven, POdd -> true
    | POdd, PEven -> true
    | PBot, b -> equal_paritya PBot PBot || equal_paritya b PBot
    | POdd, PBot -> equal_paritya POdd PBot || equal_paritya PBot PBot
    | POdd, POdd -> equal_paritya POdd PBot || equal_paritya POdd PBot
    | POdd, PTop -> equal_paritya POdd PBot || equal_paritya PTop PBot
    | PTop, b -> equal_paritya PTop PBot || equal_paritya b PBot
    | a, PBot -> equal_paritya a PBot || equal_paritya PBot PBot
    | PEven, PEven -> equal_paritya PEven PBot || equal_paritya PEven PBot
    | a, PTop -> equal_paritya a PBot || equal_paritya PTop PBot;;

let rec sign_eq_false a b = equal_signa (inf_sign a b) SBot;;

let rec int_eq_false
  a b = sign_eq_false (int_sign a) (int_sign b) ||
          (interval_eq_false (int_ivl a) (int_ivl b) ||
            (parity_eq_false (int_parity a) (int_parity b) ||
              equal_option equal_bool
                (congruence_eqb (int_congruence a) (int_congruence b))
                (Some false)));;

let rec parity_vacuous a b = equal_paritya a PBot || equal_paritya b PBot;;

let rec parity_eq_true x = parity_vacuous x;;

let rec inv_less_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 ->
      (let a1a = (if sign_le a2 SNonPos then inf_sign a1 SNeg else a1) in
       let a = (if sign_le a1 SNonNeg then inf_sign a2 SPos else a2) in
        (a1a, a))
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a2 SPos then inf_sign a1 SPos
             else (if sign_le a2 SNonNeg then inf_sign a1 SNonNeg else a1))
           in
         let a =
           (if sign_le a1 SNeg then inf_sign a2 SNeg
             else (if sign_le a1 SNonPos then inf_sign a2 SNonPos else a2))
           in
          (a1a, a));;

let rec sign_less_false
  a b = equal_signa (fst (inv_less_sign true a b)) SBot ||
          equal_signa (snd (inv_less_sign true a b)) SBot;;

let rec sign_eq_true a b = sign_less_false a b && sign_less_false b a;;

let rec int_eq_true
  a b = sign_eq_true (int_sign a) (int_sign b) ||
          (interval_eq_true (int_ivl a) (int_ivl b) ||
            (parity_eq_true (int_parity a) (int_parity b) ||
              equal_option equal_bool
                (congruence_eqb (int_congruence a) (int_congruence b))
                (Some true)));;

let rec int_eq
  a b = (if int_eq_true a b then Some true
          else (if int_eq_false a b then Some false else None));;

let rec length_tailrec x0 n = match x0, n with [], n -> n
                         | x :: xs, n -> length_tailrec xs (suc n);;

let rec dgs_combine_assign_update
  dgs_combine_assigna
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
          dgs_enter, dgs_event, dgs_combine_env,
          dgs_combine_assigna dgs_combine_assign, dgs_query, more);;

let rec dgs_combine_env_update
  dgs_combine_enva
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
          dgs_enter, dgs_event, dgs_combine_enva dgs_combine_env,
          dgs_combine_assign, dgs_query, more);;

let rec dgs_special_update
  dgs_speciala
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_speciala dgs_special, dgs_branch, dgs_body,
          dgs_return, dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_return_update
  dgs_returna
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body,
          dgs_returna dgs_return, dgs_enter, dgs_event, dgs_combine_env,
          dgs_combine_assign, dgs_query, more);;

let rec dgs_branch_update
  dgs_brancha
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_brancha dgs_branch, dgs_body,
          dgs_return, dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_assign_update
  dgs_assigna
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assigna dgs_assign, dgs_special, dgs_branch, dgs_body,
          dgs_return, dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_query_update
  dgs_querya
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
          dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_querya dgs_query, more);;

let rec dgs_event_update
  dgs_eventa
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
          dgs_enter, dgs_eventa dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_enter_update
  dgs_entera
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
          dgs_entera dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_skip_update
  dgs_skipa
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skipa dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body,
          dgs_return, dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec dgs_body_update
  dgs_bodya
    (Gdg_spec_ext
      (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
        dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
        more))
    = Gdg_spec_ext
        (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_bodya dgs_body,
          dgs_return, dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign,
          dgs_query, more);;

let rec local_combine_transfer f m exit = sp_return (f (man_local m) exit);;

let rec local_enter_transfer f m = sp_return (f (man_local m));;

let local_dg_spec_template : ('a, 'b, 'c, 'd, 'e, 'f, 'g, unit) gdg_spec_ext
  = Gdg_spec_ext
      ((fun m -> sp_return (id (man_local m))),
        (fun _ _ m -> sp_return (id (man_local m))),
        (fun _ _ m -> sp_return (id (man_local m))),
        (fun _ _ m -> sp_return (id (man_local m))),
        (fun _ m -> sp_return (id (man_local m))),
        (fun _ _ m -> sp_return (id (man_local m))),
        (fun _ -> local_enter_transfer (fun d -> [(d, d)])),
        (fun _ m -> sp_return (id (man_local m))),
        (fun _ -> local_combine_transfer (fun d _ -> d)),
        (fun _ -> local_combine_transfer (fun d _ -> d)),
        (fun _ _ ->
          sp_return (top_query_lifta (order_int_dom_ext bounded_lattice_unit))),
        ());;

let rec local_transfer f m = sp_return (f (man_local m));;

let rec ls_channel _B c x = ask_rec _B (ls_query c) query_depth bot_set x;;

let rec closed_step _B c a d = ls_step c (ls_channel _B c d) a d;;

let rec dg_spec_of _B _C
  c = dgs_query_update (fun _ -> local_query (ls_channel _B c))
        (dgs_combine_assign_update
          (fun _ ci ->
            local_combine_transfer
              (fun dc de -> ls_combine_assign c (ls_channel _B c de) ci dc de))
          (dgs_combine_env_update
            (fun _ ci ->
              local_combine_transfer
                (fun dc de ->
                  ls_combine_env c (ls_channel _B c dc) (ls_channel _B c de) ci
                    dc de))
            (dgs_event_update
              (fun _ ev -> local_transfer (closed_step _B c (event_action ev)))
              (dgs_enter_update
                (fun _ ci ->
                  local_enter_transfer
                    (fun d -> ls_enter c (ls_channel _B c d) ci (d, d)))
                (dgs_return_update
                  (fun _ e p ->
                    local_transfer (closed_step _B c (EA_Ret (e, p))))
                  (dgs_body_update
                    (fun _ p -> local_transfer (closed_step _B c (EA_Body p)))
                    (dgs_branch_update
                      (fun _ b pol ->
                        local_transfer
                          (closed_step _B c
                            (if pol then EA_Assume b else EA_AssumeNot b)))
                      (dgs_special_update
                        (fun _ sc x ->
                          local_transfer
                            (closed_step _B c (EA_Special (sc, x))))
                        (dgs_assign_update
                          (fun _ x e ->
                            local_transfer
                              (closed_step _B c (EA_Assign (x, e))))
                          (dgs_skip_update
                            (fun _ -> local_transfer (closed_step _B c EA_Nop))
                            local_dg_spec_template))))))))));;

let rec stabl (State_ext (called, infl, stabl, sigma, more)) = stabl;;

let rec ea_check_cond (EA_Check (x81, x82)) = x82;;

let rec is_EA_Check = function EA_Nop -> false
                      | EA_Assign (x21, x22) -> false
                      | EA_Special (x31, x32) -> false
                      | EA_Assume x4 -> false
                      | EA_AssumeNot x5 -> false
                      | EA_Body x6 -> false
                      | EA_Ret (x71, x72) -> false
                      | EA_Check (x81, x82) -> true;;

let rec body (Gproc_decl_ext (formals, body, more)) = body;;

let rec classify_special
  uu x1 = match uu, x1 with SD_Nondet_Int, [] -> Some Nondet_Int
    | SD_Min, [a; b] -> Some (Min (a, b))
    | SD_Max, [a; b] -> Some (Max (a, b))
    | SD_Min, [] -> None
    | SD_Min, [v] -> None
    | SD_Min, v :: vb :: vd :: ve -> None
    | SD_Max, [] -> None
    | SD_Max, [v] -> None
    | SD_Max, v :: vb :: vd :: ve -> None
    | SD_Nondet_Int, v :: va -> None
    | uu, [v] -> None
    | uu, v :: vb :: vd :: ve -> None;;

let rec formals (Gproc_decl_ext (formals, body, more)) = formals;;

let rec call_formals
  pi q =
    (match pi q
      with None ->
        failwith "call_formals: call to an undeclared procedure" (fun _ -> [])
      | Some a -> formals a);;

let special_pname_nondet_int : string = "__voblint_nondet_int";;

let special_pname_min : string = "min";;

let special_pname_max : string = "max";;

let rec special_table
  p = (if ((p : string) = special_pname_nondet_int) then Some SD_Nondet_Int
        else (if ((p : string) = special_pname_min) then Some SD_Min
               else (if ((p : string) = special_pname_max) then Some SD_Max
                      else None)));;

let rec sup_set _A
  x0 a = match x0, a with Set xs, a -> fold (inserta _A) xs a
    | Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs);;

let rec csize
  = function SKIP i -> one_nat
    | Assign (i, x, a) -> one_nat
    | Check (i, l, c) -> one_nat
    | Seq (c1, c2) -> plus_nat (csize c1) (csize c2)
    | If (i, b, c1, c2) -> plus_nat (plus_nat one_nat (csize c1)) (csize c2)
    | While (i, b, c) -> plus_nat one_nat (csize c)
    | Call (i, dst, q, actuals) -> one_nat
    | Return (i, e) -> one_nat
    | Restore i -> one_nat
    | Unwind i -> one_nat;;

let rec is_SKIP = function SKIP x1 -> true
                  | Assign (x21, x22, x23) -> false
                  | Check (x31, x32, x33) -> false
                  | Seq (x41, x42) -> false
                  | If (x51, x52, x53, x54) -> false
                  | While (x61, x62, x63) -> false
                  | Call (x71, x72, x73, x74) -> false
                  | Return (x81, x82) -> false
                  | Restore x9 -> false
                  | Unwind x10 -> false;;

let rec compile _B _C
  pi p x2 k n = match pi, p, x2, k, n with
    pi, p, SKIP i, k, n ->
      (suc n,
        (Statement n,
          (inserta
             (equal_prod equal_cfg_node
               (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
             (Statement n, (EA_Nop, k)) bot_set,
            bot_set)))
    | pi, p, Assign (i, x, a), k, n ->
        (suc n,
          (Statement n,
            (inserta
               (equal_prod equal_cfg_node
                 (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
               (Statement n, (EA_Assign (x, a), k)) bot_set,
              bot_set)))
    | pi, p, Check (i, l, c), k, n ->
        (suc n,
          (Statement n,
            (inserta
               (equal_prod equal_cfg_node
                 (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
               (Statement n, (EA_Check (l, c), k)) bot_set,
              bot_set)))
    | pi, p, Seq (c1, c2), k, n ->
        (let (_, (en1, (e1, k1))) =
           compile _B _C pi p c1 (Statement (plus_nat n (csize c1))) n in
         let (n2, (_, (e2, k2))) =
           compile _B _C pi p c2 k (plus_nat n (csize c1)) in
          (n2, (en1, (sup_set
                        (equal_prod equal_cfg_node
                          (equal_prod (equal_gedge_action _B _C)
                            equal_cfg_node))
                        e1 e2,
                       sup_set
                         (equal_prod equal_cfg_node
                           (equal_prod (equal_gcall_action _B _C)
                             (equal_prod equal_cfg_node equal_cfg_node)))
                         k1 k2))))
    | pi, p, If (i, b, c1, c2), k, n ->
        (let (n1, (en1, (e1, k1))) = compile _B _C pi p c1 k (suc n) in
         let (n2, (en2, (e2, k2))) = compile _B _C pi p c2 k n1 in
          (n2, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                    (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                      (inserta
                        (equal_prod equal_cfg_node
                          (equal_prod (equal_gedge_action _B _C)
                            equal_cfg_node))
                        (Statement n,
                          (EA_Assume b, (if is_SKIP c1 then k else en1)))
                        (inserta
                          (equal_prod equal_cfg_node
                            (equal_prod (equal_gedge_action _B _C)
                              equal_cfg_node))
                          (Statement n,
                            (EA_AssumeNot b, (if is_SKIP c2 then k else en2)))
                          bot_set))
                      (if is_SKIP c1 then bot_set else e1))
                    (if is_SKIP c2 then bot_set else e2),
                   sup_set
                     (equal_prod equal_cfg_node
                       (equal_prod (equal_gcall_action _B _C)
                         (equal_prod equal_cfg_node equal_cfg_node)))
                     k1 k2))))
    | pi, p, While (i, b, c), k, n ->
        (let (n1, (en1, (e1, k1))) = compile _B _C pi p c (Statement n) (suc n)
           in
          (n1, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                    (inserta
                      (equal_prod equal_cfg_node
                        (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                      (Statement n, (EA_Assume b, en1))
                      (inserta
                        (equal_prod equal_cfg_node
                          (equal_prod (equal_gedge_action _B _C)
                            equal_cfg_node))
                        (Statement n, (EA_AssumeNot b, k)) bot_set))
                    e1,
                   k1))))
    | pi, p, Call (i, dst, q, actuals), k, n ->
        (match special_table q
          with None ->
            (suc n,
              (Statement n,
                (bot_set,
                  inserta
                    (equal_prod equal_cfg_node
                      (equal_prod (equal_gcall_action _B _C)
                        (equal_prod equal_cfg_node equal_cfg_node)))
                    (Statement n,
                      (CallEdge (dst, call_formals pi q, actuals),
                        (FunctionEntry q, k)))
                    bot_set)))
          | Some desc ->
            (match classify_special desc actuals
              with None ->
                (suc n,
                  (Statement n,
                    (inserta
                       (equal_prod equal_cfg_node
                         (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                       (Statement n, (EA_Nop, k)) bot_set,
                      bot_set)))
              | Some sc ->
                (match dst
                  with None ->
                    (suc n,
                      (Statement n,
                        (inserta
                           (equal_prod equal_cfg_node
                             (equal_prod (equal_gedge_action _B _C)
                               equal_cfg_node))
                           (Statement n, (EA_Nop, k)) bot_set,
                          bot_set)))
                  | Some x ->
                    (suc n,
                      (Statement n,
                        (inserta
                           (equal_prod equal_cfg_node
                             (equal_prod (equal_gedge_action _B _C)
                               equal_cfg_node))
                           (Statement n, (EA_Special (sc, x), k)) bot_set,
                          bot_set))))))
    | pi, p, Return (i, e), k, n ->
        (suc n,
          (Statement n,
            (inserta
               (equal_prod equal_cfg_node
                 (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
               (Statement n, (EA_Ret (e, p), FunctionResult p)) bot_set,
              bot_set)))
    | pi, p, Restore i, k, n ->
        (suc n,
          (Statement n,
            (inserta
               (equal_prod equal_cfg_node
                 (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)))
    | pi, p, Unwind i, k, n ->
        (suc n,
          (Statement n,
            (inserta
               (equal_prod equal_cfg_node
                 (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)));;

let rec compile_proc _B _C
  pi p decl n =
    (let r = plus_nat n (csize (body decl)) in
     let (_, (ben, (e, k))) = compile _B _C pi p (body decl) (Statement r) n in
      (suc r,
        (inserta
           (equal_prod equal_cfg_node
             (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
           (FunctionEntry p, (EA_Body p, ben))
           (inserta
             (equal_prod equal_cfg_node
               (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
             (Statement r, (EA_Ret (None, p), FunctionResult p)) e),
          k)));;

let rec compile_procs _B _C
  pi x1 n = match pi, x1, n with pi, [], n -> (n, (bot_set, bot_set))
    | pi, p :: ps, n ->
        (match pi p with None -> compile_procs _B _C pi ps n
          | Some decl ->
            (let (n1, (e, k)) = compile_proc _B _C pi p decl n in
             let (n2, (ea, ka)) = compile_procs _B _C pi ps n1 in
              (n2, (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                      e ea,
                     sup_set
                       (equal_prod equal_cfg_node
                         (equal_prod (equal_gcall_action _B _C)
                           (equal_prod equal_cfg_node equal_cfg_node)))
                       k ka))));;

let prog_main_name : string = "main";;

let rec main_body
  pi = (match pi prog_main_name
         with None ->
           failwith "main_body: entry procedure not declared"
             (fun _ -> SKIP (failwith "undefined"))
         | Some a -> body a);;

let rec compile_prog _B _C
  pi ps =
    (let (n1, (eprocs, kprocs)) = compile_procs _B _C pi ps zero_nat in
     let (_, (emain, kmain)) =
       compile_proc _B _C pi prog_main_name
         (Gproc_decl_ext ([], main_body pi, ())) n1
       in
      Gcfg_ext
        (sup_set
           (equal_prod equal_cfg_node
             (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
           eprocs emain,
          sup_set
            (equal_prod equal_cfg_node
              (equal_prod (equal_gcall_action _B _C)
                (equal_prod equal_cfg_node equal_cfg_node)))
            kprocs kmain,
          FunctionEntry prog_main_name,
          image (fun (u, (a, _)) -> (u, ea_check_cond a))
            (filter (fun (_, (a, _)) -> is_EA_Check a)
              (sup_set
                (equal_prod equal_cfg_node
                  (equal_prod (equal_gedge_action _B _C) equal_cfg_node))
                eprocs emain)),
          ()));;

let rec proc_rep
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = proc_rep;;

let rec prog_procs
  p = filtera (fun n -> not ((n : string) = prog_main_name))
        (map fst (proc_rep p));;

let rec declared_global_vars
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = declared_global_vars;;

let rec declared_global p x = membera equal_literal (declared_global_vars p) x;;

let rec prog_table p = map_of equal_literal (proc_rep p);;

let rec prog_formals
  p q = (match prog_table p q with None -> [] | Some a -> formals a);;

let rec kenv_of
  ds v = (match map_of equal_var_id ds v with None -> I32 | Some k -> k);;

let rec typed_ptable
  p ds q =
    map_option
      (fun d ->
        Gproc_decl_ext
          (map (resolve_var (declared_global p) q) (formals d),
            elab_com (declared_global p) (prog_formals p) (kenv_of ds) q
              (body d),
            ()))
      (prog_table p q);;

let rec typed_cfg
  p ds =
    compile_prog equal_var_id equal_texp (typed_ptable p ds) (prog_procs p);;

let rec kd_val _A
  = function
    KBot ->
      bot _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
    | KD (k, a) -> a
    | KTop ->
        top _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.order_top_executable_domain.top_order_top;;

let rec truth_ik _A a = cmp_ik _A CNe a (of_int_ik _A I32 zero_inta);;

let rec src_kind
  kappa e =
    (match e with TN (_, _) -> Some (texp_kind e)
      | TVar (ik, v) ->
        (if not (equal_var_ida v ReturnVar) && equal_ikind ik (kappa v)
          then Some ik else None)
      | TArith (_, _, _, _) -> Some (texp_kind e)
      | TCast (_, _) -> Some (texp_kind e)
      | TCmp (_, _, _) -> Some (texp_kind e) | TNot _ -> Some (texp_kind e)
      | TAnd (_, _) -> Some (texp_kind e) | TOr (_, _) -> Some (texp_kind e));;

let rec read_var _A
  kappa sigma v =
    (match sigma v with KBot -> kd_val _A KBot
      | KD (ikind, a) -> kd_val _A (KD (ikind, a))
      | KTop ->
        (if equal_var_ida v ReturnVar
          then top _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.order_top_executable_domain.top_order_top
          else top_ik _A (kappa v)));;

let rec bool_val _A
  r = (match r
        with None ->
          sup _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
            (of_int_ik _A I32 zero_inta) (of_int_ik _A I32 one_inta)
        | Some true -> of_int_ik _A I32 one_inta
        | Some false -> of_int_ik _A I32 zero_inta);;

let rec taeval _A
  kappa x1 sigma = match kappa, x1, sigma with
    kappa, TN (ik, n), sigma -> of_int_ik _A ik n
    | kappa, TVar (ik, v), sigma -> read_var _A kappa sigma v
    | kappa, TArith (ik, op, a, b), sigma ->
        arith_ik _A ik op (taeval _A kappa a sigma) (taeval _A kappa b sigma)
    | kappa, TCast (ik, a), sigma ->
        cast_ik _A (src_kind kappa a) ik (taeval _A kappa a sigma)
    | kappa, TCmp (op, a, b), sigma ->
        bool_val _A
          (cmp_ik _A op (taeval _A kappa a sigma) (taeval _A kappa b sigma))
    | kappa, TNot a, sigma ->
        bool_val _A (map_option not (truth_ik _A (taeval _A kappa a sigma)))
    | kappa, TAnd (a, b), sigma ->
        bool_val _A
          (match
            (truth_ik _A (taeval _A kappa a sigma),
              truth_ik _A (taeval _A kappa b sigma))
            with (None, None) -> None | (None, Some true) -> None
            | (None, Some false) -> Some false | (Some true, None) -> None
            | (Some true, Some true) -> Some true
            | (Some true, Some false) -> Some false
            | (Some false, _) -> Some false)
    | kappa, TOr (a, b), sigma ->
        bool_val _A
          (match
            (truth_ik _A (taeval _A kappa a sigma),
              truth_ik _A (taeval _A kappa b sigma))
            with (None, None) -> None | (None, Some true) -> Some true
            | (None, Some false) -> None | (Some true, _) -> Some true
            | (Some false, None) -> None | (Some false, Some true) -> Some true
            | (Some false, Some false) -> Some false);;

let top_order_rel : 'a order_rel = OFacts bot_set;;

let rec init_state (_C1, _C2)
  = State_ext
      (bot_set, fmempty, bot_set,
        (fun _ -> bot _C1.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
        State_exta (bot_set, ()));;

let rec point_update
  pointa (State_ext (called, infl, stabl, sigma, State_exta (point, more))) =
    State_ext (called, infl, stabl, sigma, State_exta (pointa point, more));;

let rec warrow _A
  a b = (if less_eq
              _A.widening_warrowing.order_widening.preorder_order.ord_preorder b
              a
          then narrow _A.narrowing_warrowing a b
          else widen _A.widening_warrowing a b);;

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

let rec fmlookup_default _A
  m d x = (match fmlookup _A m x with None -> d | Some v -> v);;

let rec destab_opt _A _B
  x i s c =
    (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Destabilize x) in
      destab_iter_opt _A _B (fmlookup_default (equal_sum _A _B) i [] x)
        (fmdrop (equal_sum _A _B) x i) s c)
and destab_iter_opt _A _B
  x0 i s c = match x0, i, s, c with [], i, s, c -> (i, s)
    | y :: ys, i, s, c ->
        (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Stable_Remove y)
           in
         let (ia, sa) =
           (if member _A y c then (i, remove _A y s)
             else destab_opt _A _B (Inl y) i (remove _A y s) c)
           in
          destab_iter_opt _A _B ys ia sa c);;

let rec sigma_update
  sigmaa (State_ext (called, infl, stabl, sigma, more)) =
    State_ext (called, infl, stabl, sigmaa sigma, more);;

let rec rho_update
  rhoa (Ug_state_ext (rho, more)) = Ug_state_ext (rhoa rho, more);;

let rec rho (Ug_state_ext (rho, more)) = rho;;

let abort_empty_set _ = failwith "List.abort_empty_set";;

let rec sup_fin _A = function Set [] -> abort_empty_set (sup_fin _A)
                     | Set (x :: xs) -> fold (sup _A.sup_semilattice_sup) xs x;;

let rec sup_fset _A s = sup_fin _A (fset s);;

let rec sup_over_origins _A _C
  state g =
    sup_fset _C.semilattice_sup_bounded_semilattice_sup_bot
      (fimage
        (fmlookup_default _A (rho state g)
          (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
        (fmdom (rho state g)));;

let rec update_global_warrowing_per_origin (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if eq _A1
          (fmlookup_default _B (rho state g)
            (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
          d
      then (None, state)
      else (let warrow_per_orig =
              warrow _A3
                (fmlookup_default _B (rho state g)
                  (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                  orig)
                d
              in
            let statea =
              rho_update
                (fun _ ->
                  fun_upd _C (rho state) g
                    (fmupd _B orig warrow_per_orig (rho state g)))
                state
              in
            let join_over_origins = sup_over_origins _B _A2 statea g in
             (Some join_over_origins, statea)));;

let rec gas_update
  gasa (Ug_state_ext (rho, Ug_state_with_gas_ext (gas, more))) =
    Ug_state_ext (rho, Ug_state_with_gas_ext (gasa gas, more));;

let rec equal_phase x0 x1 = match x0, x1 with Widening, Narrowing -> false
                      | Narrowing, Widening -> false
                      | Narrowing, Narrowing -> true
                      | Widening, Widening -> true;;

let rec gas (Ug_state_ext (rho, Ug_state_with_gas_ext (gas, more))) = gas;;

let rec update_global_bounded_narrowing (_A1, _A2, _A3) _B _C
  i da orig g d state =
    (if eq _A1
          (fmlookup_default _B (rho state g)
            (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
          d
      then (None, state)
      else (let (phase, ia) = gas state g orig in
             (if less_eq
                   _A2.order_bot_bounded_semilattice_sup_bot.order_order_bot.preorder_order.ord_preorder
                   d (fmlookup_default _B (rho state g)
                       (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                       orig) &&
                   (equal_phase phase Narrowing && less_eq_nat i ia)
               then (None, state)
               else (let (db, (phasea, ib)) =
                       (if not (less_eq
                                 _A2.order_bot_bounded_semilattice_sup_bot.order_order_bot.preorder_order.ord_preorder
                                 d (fmlookup_default _B (rho state g)
                                     (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                                     orig))
                         then (widen _A3.widening_warrowing
                                 (fmlookup_default _B (rho state g)
                                   (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                                   orig)
                                 d,
                                (Widening, ia))
                         else (if equal_phase phase Narrowing
                                then (narrow _A3.narrowing_warrowing
(fmlookup_default _B (rho state g)
  (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
d,
                                       (phase, ia))
                                else (narrow _A3.narrowing_warrowing
(fmlookup_default _B (rho state g)
  (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
d,
                                       (Narrowing, plus_nat ia one_nat))))
                       in
                     let statea =
                       gas_update
                         (fun _ ->
                           fun_upd _C (gas state) g
                             (fun_upd _B (gas state g) orig (phasea, ib)))
                         (rho_update
                           (fun _ ->
                             fun_upd _C (rho state) g
                               (fmupd _B orig db (rho state g)))
                           state)
                       in
                     let join_over_origins = sup_over_origins _B _A2 statea g in
                      (if eq _A1 join_over_origins da then (None, statea)
                        else (Some join_over_origins, statea))))));;

let rec update_global_warrowing_apinis (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if eq _A1
          (fmlookup_default _B (rho state g)
            (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
          d
      then (None, state)
      else (let statea =
              rho_update
                (fun _ ->
                  fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
                state
              in
            let db = warrow _A3 da (sup_over_origins _B _A2 statea g) in
             (Some db, statea)));;

let rec update_global_always_join (_A1, _A2) _B _C
  da orig g d state =
    (let statea =
       rho_update
         (fun _ -> fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
         state
       in
     let db =
       sup _A2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
         da d
       in
      (if eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec update_global_per_origin (_A1, _A2) _B _C
  da orig g d state =
    (let statea =
       rho_update
         (fun _ -> fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
         state
       in
     let db = sup_over_origins _B _A2 statea g in
      (if eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec truncatea r = Ug_state_ext (rho r, ());;

let rec changed _A
  d res =
    (match res with None -> None
      | Some da -> (if eq _A da d then None else Some da));;

let rec lift_basic_rule _A
  f da orig g d state =
    (let (res, st) = f da orig g d (truncatea state) in
      (changed _A da res, rho_update (fun _ -> rho st) state));;

let rec update_global_of (_A1, _A2, _A3) _B _C
  r = (match r
        with Globals_Join ->
          lift_basic_rule _A1 (update_global_always_join (_A1, _A2) _B _C)
        | Globals_Per_Origin ->
          lift_basic_rule _A1 (update_global_per_origin (_A1, _A2) _B _C)
        | Globals_Warrow ->
          lift_basic_rule _A1
            (update_global_warrowing_apinis (_A1, _A2, _A3) _B _C)
        | Globals_Warrow_Per_Origin ->
          lift_basic_rule _A1
            (update_global_warrowing_per_origin (_A1, _A2, _A3) _B _C)
        | Globals_Bounded_Narrowing a ->
          update_global_bounded_narrowing (_A1, _A2, _A3) _B _C a);;

let rec point
  (State_ext (called, infl, stabl, sigma, State_exta (point, more))) = point;;

let rec called_update
  calleda (State_ext (called, infl, stabl, sigma, more)) =
    State_ext (calleda called, infl, stabl, sigma, more);;

let rec stabl_update
  stabla (State_ext (called, infl, stabl, sigma, more)) =
    State_ext (called, infl, stabla stabl, sigma, more);;

let rec infl_update
  infla (State_ext (called, infl, stabl, sigma, more)) =
    State_ext (called, infla infl, stabl, sigma, more);;

let rec sigma (State_ext (called, infl, stabl, sigma, more)) = sigma;;

let rec called (State_ext (called, infl, stabl, sigma, more)) = called;;

let rec fminsert _A
  infl x y = fmupd _A x (y :: fmlookup_default _A infl [] x) infl;;

let rec tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  r t s =
    (match s
      with Q (y, (x, (state, ug_state))) ->
        (let _ =
           Solver_trace_hook.emit "solver"
             (fun _ ->
               Ev_Query
                 (y, x, member _A x (stabl state), member _A x (called state)))
           in
          bind (if member _A x (called state)
                 then (let _ =
                         Solver_trace_hook.emit "solver"
                           (fun _ ->
                             Ev_Query_Wpoint (x, member _A x (point state)))
                         in
                        Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> inserta _A x (point state)) state,
                                 ug_state)))
                 else (let _ =
                         Solver_trace_hook.emit "solver"
                           (fun _ -> Ev_Iterate_From_Query x)
                         in
                        tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r
                          t (I (x, (called_update
                                      (fun _ -> inserta _A x (called state))
                                      state,
                                     ug_state)))))
            (fun (xd, (statea, ug_statea)) ->
              (let _ =
                 Solver_trace_hook.emit "solver"
                   (fun _ -> Ev_Add_Infl (Inl x, y))
                 in
               let _ =
                 Solver_trace_hook.emit "solver" (fun _ -> Ev_Answer (y, x, xd))
                 in
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))))
      | I (x, (state, ug_state)) ->
        (let _ =
           Solver_trace_hook.emit "solver"
             (fun _ ->
               Ev_Iterate
                 (x, member _A x (called state), member _A x (stabl state),
                   member _A x (point state)))
           in
          (if not (member _A x (stabl state))
            then bind (tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
                        (Ra (x, (state, ug_state))))
                   (fun (d_new, (state1, ug_state1)) ->
                     (let _ =
                        Solver_trace_hook.emit "solver"
                          (fun _ -> Ev_Widen (x, member _A x (point state)))
                        in
                      let d_newa =
                        (if member _A x (point state)
                          then warrow _C3 (sigma state1 (Inl x)) d_new
                          else d_new)
                        in
                      let _ =
                        Solver_trace_hook.emit "solver"
                          (fun _ ->
                            Ev_Sol
                              (x, member _A x (point state),
                                sigma state1 (Inl x), d_new, d_newa))
                        in
                       (if eq _C1 (sigma state1 (Inl x)) d_newa
                         then (let _ =
                                 Solver_trace_hook.emit "solver"
                                   (fun _ ->
                                     Ev_Wpoint_Remove
                                       (x, member _A x (point state1)))
                                 in
                                Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (called_update (fun _ -> remove _A x (called state1)) state1),
 ug_state1)))
                         else (let _ =
                                 Solver_trace_hook.emit "solver"
                                   (fun _ ->
                                     Ev_Update
                                       (x, member _A x (point state1),
 eq _C1 (sigma state1 (Inl x))
   (bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
 sigma state1 (Inl x), d_newa))
                                 in
                               let (infl1, stabl1) =
                                 destab_opt _A _B (Inl x) (infl state1)
                                   (stabl state1) (called state1)
                                 in
                               let _ =
                                 Solver_trace_hook.emit "solver"
                                   (fun _ -> Ev_Iterate_Changed x)
                                 in
                                tD_side_rule_Interp_solve_rec_c _A _B
                                  (_C1, _C2, _C3) r t
                                  (I (x, (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
            else (let _ =
                    Solver_trace_hook.emit "solver"
                      (fun _ -> Ev_Wpoint_Clear (x, member _A x (point state)))
                    in
                   Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (called_update
                               (fun _ -> remove _A x (called state)) state),
                            ug_state)))))
      | Ra (x, (state, ug_state)) ->
        (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Eq x) in
          bind (tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
                 (E (x, (t x, ((fun _ ->
                                 bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                (stabl_update
                                   (fun _ -> inserta _A x (stabl state)) state,
                                  ug_state))))))
            (fun (xd, (statea, ug_statea)) ->
              (if member _A x (stabl statea) then Some (xd, (statea, ug_statea))
                else (let _ =
                        Solver_trace_hook.emit "solver"
                          (fun _ -> Ev_Still_Unstable x)
                        in
                       tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
                         (Ra (x, (statea, ug_statea)))))))
      | E (x, (Answer d, (_, (state, ug_state)))) ->
        (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Rhs (x, d)) in
          Some (d, (state, ug_state)))
      | E (x, (QueryL (y, g), (sides, (state, ug_state)))) ->
        bind (tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
               (Q (x, (y, (state, ug_state)))))
          (fun (yd, (statea, ug_statea)) ->
            tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
              (E (x, (g yd, (sides, (statea, ug_statea))))))
      | E (x, (QueryG (y, g), (sides, (state, ug_state)))) ->
        (let _ =
           Solver_trace_hook.emit "solver" (fun _ -> Ev_Query_Global (x, y)) in
         let _ =
           Solver_trace_hook.emit "solver" (fun _ -> Ev_Add_Infl (Inr y, x)) in
         let _ =
           Solver_trace_hook.emit "solver"
             (fun _ -> Ev_Answer_Global (x, y, sigma state (Inr y)))
           in
          tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
            (E (x, (g (sigma state (Inr y)),
                     (sides,
                       (infl_update
                          (fun _ ->
                            fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                          state,
                         ug_state))))))
      | E (x, (Side (y, d, ta), (sides, (state, ug_state)))) ->
        (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Side (x, y, d)) in
         let da =
           sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
             (sides y) d
           in
         let sidesa = fun_upd _B sides y da in
          (match
            update_global_of (_C1, _C2, _C3) _A _B r (sigma state (Inr y)) x y
              da ug_state
            with (None, ug_statea) ->
              tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
                (E (x, (ta, (sidesa, (state, ug_statea)))))
            | (Some db, ug_statea) ->
              (let _ =
                 Solver_trace_hook.emit "solver"
                   (fun _ ->
                     Ev_Update_Global
                       (x, y,
                         eq _C1 (sigma state (Inr y))
                           (bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                         sigma state (Inr y), db))
                 in
               let (infla, stabla) =
                 destab_opt _A _B (Inr y) (infl state) (stabl state)
                   (called state)
                 in
                tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
                  (E (x, (ta, (sidesa,
                                (sigma_update
                                   (fun _ ->
                                     fun_upd (equal_sum _A _B) (sigma state)
                                       (Inr y) db)
                                   (stabl_update (fun _ -> stabla)
                                     (infl_update (fun _ -> infla) state)),
                                  ug_statea)))))))));;

let rec init_ug_state_with_gas _C
  = Ug_state_ext
      ((fun _ -> fmempty),
        Ug_state_with_gas_ext ((fun _ _ -> (Widening, zero_nat)), ()));;

let rec tD_side_rule_Interp_solve_c _A _B (_C1, _C2, _C3)
  r t x =
    bind (tD_side_rule_Interp_solve_rec_c _A _B (_C1, _C2, _C3) r t
           (I (x, (called_update
                     (fun _ -> inserta _A x (called (init_state (_C2, _C3))))
                     (init_state (_C2, _C3)),
                    init_ug_state_with_gas
                      _C2.order_bot_bounded_semilattice_sup_bot))))
      (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_rule_Interp_solve _A _B (_C1, _C2, _C3)
  r t x =
    (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Start x) in
     let res = tD_side_rule_Interp_solve_c _A _B (_C1, _C2, _C3) r t x in
     let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Stop) in
      (match res
        with None ->
          failwith "Input not in domain"
            (fun _ -> tD_side_rule_Interp_solve _A _B (_C1, _C2, _C3) r t x)
        | Some v -> v));;

let rec ord_le
  d x y =
    (match d with OBot -> false
      | OFacts ps ->
        equal_var_ida x y ||
          member (equal_prod equal_var_id equal_var_id) (x, y) ps);;

let rec ord_decide
  xa0 d x y = match xa0, d, x, y with
    CLe, d, x, y -> (if ord_le d x y then Some true else None)
    | CGe, d, x, y -> (if ord_le d y x then Some true else None)
    | CLt, d, x, y -> (if ord_le d y x then Some false else None)
    | CGt, d, x, y -> (if ord_le d x y then Some false else None)
    | CEq, d, x, y -> (if ord_le d x y && ord_le d y x then Some true else None)
    | CNe, d, x, y ->
        (if ord_le d x y && ord_le d y x then Some false else None);;

let rec ord_classify
  x0 d = match x0, d with
    TCmp (c, TVar (ka, x), TVar (k, y)), d ->
      (match ord_decide c d x y with None -> Check_Unknown
        | Some true -> Check_Proved | Some false -> Check_Refuted)
    | TN (v, va), d -> Check_Unknown
    | TVar (v, va), d -> Check_Unknown
    | TArith (v, va, vb, vc), d -> Check_Unknown
    | TCast (v, va), d -> Check_Unknown
    | TCmp (v, TN (vc, vd), vb), d -> Check_Unknown
    | TCmp (v, TArith (vc, vd, ve, vf), vb), d -> Check_Unknown
    | TCmp (v, TCast (vc, vd), vb), d -> Check_Unknown
    | TCmp (v, TCmp (vc, vd, ve), vb), d -> Check_Unknown
    | TCmp (v, TNot vc, vb), d -> Check_Unknown
    | TCmp (v, TAnd (vc, vd), vb), d -> Check_Unknown
    | TCmp (v, TOr (vc, vd), vb), d -> Check_Unknown
    | TCmp (v, va, TN (vc, vd)), d -> Check_Unknown
    | TCmp (v, va, TArith (vc, vd, ve, vf)), d -> Check_Unknown
    | TCmp (v, va, TCast (vc, vd)), d -> Check_Unknown
    | TCmp (v, va, TCmp (vc, vd, ve)), d -> Check_Unknown
    | TCmp (v, va, TNot vc), d -> Check_Unknown
    | TCmp (v, va, TAnd (vc, vd)), d -> Check_Unknown
    | TCmp (v, va, TOr (vc, vd)), d -> Check_Unknown
    | TNot v, d -> Check_Unknown
    | TAnd (v, va), d -> Check_Unknown
    | TOr (v, va), d -> Check_Unknown;;

let rec group_lookup _A
  m k = (match lookup _A m k with None -> [] | Some ys -> ys);;

let rec group_by_key _B
  key_of f xs =
    foldr (fun x m ->
            (match f x with None -> m
              | Some y ->
                insert _B (key_of x) (y :: group_lookup _B m (key_of x)) m))
      xs (empty _B);;

let rec size_list xs = length_tailrec xs zero_nat;;

let rec part _B
  f pivot x2 = match f, pivot, x2 with f, pivot, [] -> ([], ([], []))
    | f, pivot, x :: xs ->
        (let (lts, (eqs, gts)) = part _B f pivot xs in
         let xa = f x in
          (if less _B.order_linorder.preorder_order.ord_preorder xa pivot
            then (x :: lts, (eqs, gts))
            else (if less _B.order_linorder.preorder_order.ord_preorder pivot xa
                   then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts)))));;

let rec sort_key _B
  f xs =
    (match xs with [] -> [] | [_] -> xs
      | [x; y] ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then xs else [y; x])
      | _ :: _ :: _ :: _ ->
        (let (lts, (eqs, gts)) =
           part _B f
             (f (nth xs
                  (divide_nat (size_list xs) (nat_of_integer (Z.of_int 2)))))
             xs
           in
          sort_key _B f lts @ eqs @ sort_key _B f gts));;

let rec sorted_list_of_set (_A1, _A2)
  (Set xs) = sort_key _A2 (fun x -> x) (remdups _A1 xs);;

let rec cfg_intra_list (_A1, _A2) (_B1, _B2)
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod (equal_gedge_action _A1 _B1) equal_cfg_node)),
          (linorder_prod linorder_cfg_node
            (linorder_prod (linorder_gedge_action (_A1, _A2) (_B1, _B2))
              linorder_cfg_node)))
        (intra g);;

let rec intra_predecessor_index (_A1, _A2) (_B1, _B2)
  g = group_by_key linorder_cfg_node (fun (_, (_, w)) -> w)
        (fun (u, (a, _)) -> Some (u, a))
        (cfg_intra_list (_A1, _A2) (_B1, _B2) g);;

let rec sp_read_global g k = QueryG (g, k);;

let rec sp_bind m f k = m (fun v -> f v k);;

let rec routed_entry_seed_programs _C _D _E _F
  seed route ctx v =
    (match v with Statement _ -> []
      | FunctionEntry _ ->
        [sp_bind (sp_read_global (seed v ctx))
           (fun seed_state ->
             sp_return
               (DG (dg_local seed_state,
                     bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))]
      | FunctionResult _ -> []);;

let rec routed_contribution_programs _A _B _E _F
  pred_sel site_sel route it cmb extra g ctx v =
    map (fun (a, b) -> it ctx a b) (pred_sel g v ctx) @
      map (fun (cc, ca) -> cmb route ctx ca cc v) (site_sel g v) @
        extra route ctx v;;

let rec flush_sides _B
  x0 t = match x0, t with [], t -> t
    | kv :: kvs, t ->
        (if less_eq
              _B.order_bot_bounded_semilattice_sup_bot.order_order_bot.preorder_order.ord_preorder
              (snd kv)
              (bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          then flush_sides _B kvs t
          else Side (fst kv, snd kv, flush_sides _B kvs t));;

let rec acc_add _A _B
  k d x2 = match k, d, x2 with k, d, [] -> [(k, d)]
    | ka, da, (k, d) :: kvs ->
        (if eq _A k ka
          then (k, sup _B.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                     d da) ::
                 kvs
          else (k, d) :: acc_add _A _B ka da kvs);;

let rec buffer_aux _B _C
  publish_before acc x2 = match publish_before, acc, x2 with
    publish_before, acc, Answer d -> flush_sides _C acc (Answer d)
    | publish_before, acc, QueryL (y, g) ->
        (if publish_before y
          then flush_sides _C acc
                 (QueryL
                   (y, (fun v -> buffer_aux _B _C publish_before [] (g v))))
          else QueryL (y, (fun v -> buffer_aux _B _C publish_before acc (g v))))
    | publish_before, acc, QueryG (y, g) ->
        QueryG (y, (fun v -> buffer_aux _B _C publish_before acc (g v)))
    | publish_before, acc, Side (y, d, t) ->
        buffer_aux _B _C publish_before (acc_add _B _C y d acc) t;;

let rec buffer_sides _B _C
  publish_before t = buffer_aux _B _C publish_before [] t;;

let rec fold_rhs_program _A
  acc x1 = match acc, x1 with acc, [] -> sp_return acc
    | acc, p :: ps ->
        sp_bind p
          (fun res ->
            fold_rhs_program _A (sup _A.sup_semilattice_sup acc res) ps);;

let rec sp_lift_tree
  x0 k = match x0, k with Answer d, k -> k d
    | QueryL (x, f), k -> QueryL (x, (fun d -> sp_lift_tree (f d) k))
    | QueryG (g, f), k -> QueryG (g, (fun d -> sp_lift_tree (f d) k))
    | Side (g, d, t), k -> Side (g, d, sp_lift_tree t k);;

let rec sp_compile_with encode p = p (comp (fun a -> Answer a) encode);;

let rec sp_compile p = sp_compile_with id p;;

let rec routed_node_rhs_buffered _A _B _D _E _F
  pred_sel site_sel buffer_key_at route it_c cmb_c extra g bot0 d_0 g_0 =
    (fun (v, c) ->
      (let acc0 =
         DG ((if equal_cfg_nodea v (cfg_entry g)
               then sup _E.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                      bot0 d_0
               else bot0),
              (if equal_cfg_nodea v (cfg_entry g) then g_0
                else bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
         in
       let t =
         sp_compile
           (fold_rhs_program
             (semilattice_sup_dg_state
               _E.semilattice_sup_bounded_semilattice_sup_bot
               _F.semilattice_sup_bounded_semilattice_sup_bot)
             acc0
             (routed_contribution_programs _A _B _E _F pred_sel site_sel route
               it_c cmb_c extra g c v))
         in
        buffer_sides _D (bounded_semilattice_sup_bot_dg_state _E _F)
          (fun _ -> less_eq_nat (size_list (site_sel g v)) one_nat)
          (sp_lift_tree t
            (fun res ->
              Side (buffer_key_at c,
                     DG (bot _E.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                          dg_global res),
                     Answer
                       (DG (dg_local res,
                             bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))))));;

let rec call_target_at _A _B
  v x1 = match v, x1 with
    v, (c, (ca, (FunctionEntry p, k))) ->
      (if equal_cfg_nodea k v then Some (c, (ca, p)) else None)
    | v, (va, (vc, (Statement vg, vf))) -> None
    | v, (va, (vc, (FunctionResult vg, vf))) -> None;;

let rec cfg_calls_list (_A1, _A2) (_B1, _B2)
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod (equal_gcall_action _A1 _B1)
             (equal_prod equal_cfg_node equal_cfg_node))),
          (linorder_prod linorder_cfg_node
            (linorder_prod (linorder_gcall_action (_A1, _A2) (_B1, _B2))
              (linorder_prod linorder_cfg_node linorder_cfg_node))))
        (calls g);;

let rec call_target_index (_A1, _A2) (_B1, _B2)
  g = group_by_key linorder_cfg_node (fun (_, (_, (_, k))) -> k)
        (fun (c, (ca, (ce, k))) -> call_target_at _A2 _B2 k (c, (ca, (ce, k))))
        (cfg_calls_list (_A1, _A2) (_B1, _B2) g);;

let rec sp_read_local x k = QueryL (x, k);;

let rec dgs_combine_assign
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_combine_assign;;

let rec dgs_combine_env
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_combine_env;;

let rec man_local_update
  man_locala (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) =
    Gman_ext (man_locala man_local, man_global, man_sideg, man_ask, more);;

let rec dg_spec_combine_transfer
  s ci m exit =
    sp_bind (dgs_combine_env s ci m exit)
      (fun d_env ->
        dgs_combine_assign s ci (man_local_update (fun _ -> d_env) m) exit);;

let rec sp_map e p = (fun k -> p (fun v -> k (e v)));;

let rec dg_read_global
  gk = sp_bind (sp_read_global gk) (comp sp_return dg_global);;

let rec mk_dg_man _A
  d unknown_of =
    Gman_ext
      (d, (fun v -> dg_read_global (unknown_of v)),
        (fun v -> dg_sideg _A (unknown_of v)),
        (fun _ ->
          sp_return (top_query_lifta (order_int_dom_ext bounded_lattice_unit))),
        ());;

let rec ce_formals (CallEdge (x1, x2, x3)) = x2;;

let rec ce_args (CallEdge (x1, x2, x3)) = x3;;

let rec ce_dst (CallEdge (x1, x2, x3)) = x1;;

let rec call_info_of
  ca p = Gcall_info_ext (ce_dst ca, p, ce_formals ca, ce_args ca, ());;

let rec routed_call_alternative_program _A _B _F _G
  s global_of seed route is_bot ctx ca cc p alt =
    (let (cont, entry) = alt in
      (if is_bot entry
        then sp_map
               (fun d ->
                 DG (d, bot _G.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
               (dg_spec_combine_transfer s (call_info_of ca p)
                 (mk_dg_man
                   _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot cont
                   global_of)
                 (bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
        else (let ctxa = route cc ctx entry ca in
               sp_bind
                 (sp_publish (seed (FunctionEntry p) ctxa)
                   (DG (entry,
                         bot _G.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))
                 (fun _ ->
                   sp_bind (sp_read_local (FunctionResult p, ctxa))
                     (fun callee_state ->
                       sp_map
                         (fun d ->
                           DG (d, bot _G.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
                         (dg_spec_combine_transfer s (call_info_of ca p)
                           (mk_dg_man
                             _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                             cont global_of)
                           (dg_local callee_state)))))));;

let rec side_rhs_fold_dg _A _B
  acc x1 = match acc, x1 with
    acc, [] ->
      sp_return
        (DG (acc, bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
    | acc, p :: ps ->
        sp_bind p
          (fun res ->
            side_rhs_fold_dg _A _B
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc (dg_local res))
              ps);;

let rec dgs_enter
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_enter;;

let rec routed_callee_call_program _A _B _F _G
  s global_of seed route is_bot ctx ca cc caller p =
    sp_bind
      (dgs_enter s (call_info_of ca p)
        (mk_dg_man _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot caller
          global_of))
      (fun pairs ->
        side_rhs_fold_dg _F _G
          (bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          (map (routed_call_alternative_program _A _B _F _G s global_of seed
                 route is_bot ctx ca cc p)
            pairs));;

let rec routed_call_program _A _B _F _G
  s global_of seed resolve is_bot route ctx ca cc v =
    sp_bind (sp_read_local (cc, ctx))
      (fun caller_state ->
        side_rhs_fold_dg _F _G
          (bot _F.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          (map (routed_callee_call_program _A _B _F _G s global_of seed route
                 is_bot ctx ca cc (dg_local caller_state))
            (resolve v cc ca (dg_local caller_state))));;

let rec dgs_query
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_query;;

let rec sp_read_at = function Inl x -> sp_read_local x
                     | Inr g -> sp_read_global g;;

let rec dg_read_at src = sp_bind (sp_read_at src) (comp sp_return dg_local);;

let rec transfer_program_at _E
  transfer src unknown_of =
    sp_bind (dg_read_at src) (fun d -> transfer (mk_dg_man _E d unknown_of));;

let rec transfer_program _E _F
  t src unknown_of =
    sp_map (fun d -> DG (d, bot _F)) (transfer_program_at _E t src unknown_of);;

let rec dgs_special
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_special;;

let rec dgs_return
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_return;;

let rec dgs_branch
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_branch;;

let rec dgs_assign
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_assign;;

let rec dgs_event
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_event;;

let rec dgs_skip
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_skip;;

let rec dgs_body
  (Gdg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, dgs_query,
      more))
    = dgs_body;;

let rec dg_spec_step
  s x1 = match s, x1 with s, EA_Nop -> dgs_skip s
    | s, EA_Assign (x, e) -> dgs_assign s x e
    | s, EA_Special (sc, x) -> dgs_special s sc x
    | s, EA_Assume b -> dgs_branch s b true
    | s, EA_AssumeNot b -> dgs_branch s b false
    | s, EA_Body p -> dgs_body s p
    | s, EA_Ret (e, p) -> dgs_return s e p
    | s, EA_Check (l, cnd) -> dgs_event s (Check_Event (l, cnd));;

let rec dg_spec_edge_program _B _F _G
  s a src unknown_of =
    transfer_program _F _G
      (fun m -> dg_spec_step s a (outer_man _B (dgs_query s) m)) src
      unknown_of;;

let rec compiled_routed_eqs_for _A (_D1, _D2) (_E1, _E2) (_F1, _F2) _G
  global global_of seed route s g initial initial_global =
    (let preds = intra_predecessor_index (_E1, _E2) (_F1, _F2) g in
     let targets = call_target_index (_E1, _E2) (_F1, _F2) g in
      routed_node_rhs_buffered _E2 _F2 _A _D2 _G
        (fun _ v ctx ->
          map (fun (u, a) -> (Inl (u, ctx), a))
            (group_lookup linorder_cfg_node preds v))
        (fun _ v ->
          remdups (equal_prod equal_cfg_node (equal_gcall_action _E1 _F1))
            (map (fun (c, (ca, _)) -> (c, ca))
              (group_lookup linorder_cfg_node targets v)))
        (fun _ -> global) route
        (fun _ src a ->
          dg_spec_edge_program _F1
            _D2.order_bot_bounded_semilattice_sup_bot.bot_order_bot
            _G.order_bot_bounded_semilattice_sup_bot.bot_order_bot s a src
            global_of)
        (routed_call_program _E2 _F2 _D2 _G s global_of seed
          (fun v cc ca _ ->
            map_filter
              (fun x ->
                (if (let (c, (a, _)) = x in
                      equal_cfg_nodea c cc && equal_gcall_actiona _E1 _F1 a ca)
                  then Some (let (_, (_, p)) = x in p) else None))
              (group_lookup linorder_cfg_node targets v))
          (fun d ->
            eq _D1 d
              (bot _D2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))
        (routed_entry_seed_programs _D2 _E2 _F2 _G seed) g
        (bot _D2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) initial
        initial_global);;

let rec init_publications _C _D _F
  global_of root_ctx place_inits pentry g p x =
    (if equal_proda equal_cfg_node _C x (pentry p, root_ctx)
      then map (fun (n, d) -> (global_of n, DG (Bot, d))) (place_inits g p)
      else []);;

let rec analysis_spec _A _C _D comp place_spec g p = place_spec p (comp g p);;

let rec init_sides xs t = foldr (fun (a, b) -> (fun c -> Side (a, b, c))) xs t;;

let rec with_init init t = (fun x -> init_sides (init x) (t x));;

let rec equations (_A1, _A2) (_C1, _C2) (_D1, _D2) _E _G
  comp init_st buffer_key global_of seed route root_ctx place_spec place_rg
    place_inits pcfg pentry g p =
    with_init
      (init_publications _G _A2 _D2 global_of root_ctx place_inits pentry g p)
      (compiled_routed_eqs_for _E
        ((equal_lifted _D1), (bounded_semilattice_sup_bot_lifted _D2))
        (_A1, _A2) (_C1, _C2) (bounded_semilattice_sup_bot_lifted _D2)
        buffer_key global_of seed (route g)
        (analysis_spec _A2 _C2 _D2 comp place_spec g p) (pcfg p)
        (Lifted init_st) (place_rg g (Lifted init_st)));;

let rec covered_keys (Solved_Table (x1, x2)) = x1;;

let rec table_at (Solved_Table (x1, x2)) = x2;;

let rec lookup_table _A
  r v ctx =
    (if member (equal_prod equal_cfg_node _A) (v, ctx) (covered_keys r)
      then table_at r v ctx else Bot);;

let rec state_at _B
  table bot_state p ctx v =
    (match lookup_table _B (table p) v ctx with Bot -> bot_state
      | Lifted st -> st);;

let rec classify_checks (_A1, _A2) (_B1, _B2)
  g env classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      (u, (ea_check_cond a,
                            classify (ea_check_cond a) (env u))))
          else None))
      (cfg_intra_list (_A1, _A2) (_B1, _B2) g);;

let rec reporta _B (_D1, _D2) (_E1, _E2)
  table bot_state classify pcfg p ctx =
    classify_checks (_E1, _E2) (_D1, _D2) (pcfg p)
      (state_at _B table bot_state p ctx) classify;;

let rec normalize_lift empty_pred a = (if empty_pred a then Bot else Lifted a);;

let rec transfer_lift
  empty_pred f x = bind_lift x (fun a -> normalize_lift empty_pred (f a));;

let rec canonicalize_lift empty_pred = transfer_lift empty_pred id;;

let rec dg_result_for
  rd emp rc gk sol =
    Solved_Table
      (fst sol,
        (fun v ctx ->
          map_lift rd
            (canonicalize_lift emp
              (rc (dg_local (snd sol (Inl (v, ctx)))) (genv gk (snd sol))))));;

let rec solution (_A1, _A2) (_C1, _C2) (_D1, _D2) _E _G
  comp init_st buffer_key global_of seed route root_ctx solve place_spec
    place_rg place_inits pcfg pentry g p =
    solve (equations (_A1, _A2) (_C1, _C2) (_D1, _D2) _E _G comp init_st
            buffer_key global_of seed route root_ctx place_spec place_rg
            place_inits pcfg pentry g p)
      (cfg_exit (pcfg p), root_ctx);;

let rec result (_A1, _A2) (_C1, _C2) (_D1, _D2) _F _H
  comp emp rd init_st buffer_key global_of seed route root_ctx solve place_spec
    place_cmb place_rg place_inits pcfg pentry g p =
    dg_result_for (rd g) (emp p) (place_cmb p) global_of
      (solution (_A1, _A2) (_C1, _C2) (_D1, _D2) _F _H comp init_st buffer_key
        global_of seed route root_ctx solve place_spec place_rg place_inits pcfg
        pentry g p);;

let rec report (_A1, _A2) (_C1, _C2) (_D1, _D2) _F _H
  comp emp rd init_st buffer_key global_of seed route root_ctx solve bot_state
    classify place_spec place_cmb place_rg place_inits pcfg pentry g =
    reporta _H (_C1, _C2) (_A1, _A2)
      (result (_A1, _A2) (_C1, _C2) (_D1, _D2) _F _H comp emp rd init_st
        buffer_key global_of seed route root_ctx solve place_spec place_cmb
        place_rg place_inits pcfg pentry g)
      bot_state classify pcfg;;

let rec ord_forget _A
  x xa1 = match x, xa1 with x, OBot -> OBot
    | x, OFacts ps ->
        OFacts (filter (fun (a, b) -> not (eq _A a x) && not (eq _A b x)) ps);;

let rec cmp_facts _A
  xa0 xa1 x y = match xa0, xa1, x, y with
    CLt, true, x, y -> inserta (equal_prod _A _A) (x, y) bot_set
    | CLe, true, x, y -> inserta (equal_prod _A _A) (x, y) bot_set
    | CGt, true, x, y -> inserta (equal_prod _A _A) (y, x) bot_set
    | CGe, true, x, y -> inserta (equal_prod _A _A) (y, x) bot_set
    | CEq, true, x, y ->
        inserta (equal_prod _A _A) (x, y)
          (inserta (equal_prod _A _A) (y, x) bot_set)
    | CNe, true, x, y -> bot_set
    | CLt, false, x, y -> inserta (equal_prod _A _A) (y, x) bot_set
    | CLe, false, x, y -> inserta (equal_prod _A _A) (y, x) bot_set
    | CGt, false, x, y -> inserta (equal_prod _A _A) (x, y) bot_set
    | CGe, false, x, y -> inserta (equal_prod _A _A) (x, y) bot_set
    | CEq, false, x, y -> bot_set
    | CNe, false, x, y ->
        inserta (equal_prod _A _A) (x, y)
          (inserta (equal_prod _A _A) (y, x) bot_set);;

let rec ord_branch
  x0 pol d = match x0, pol, d with
    TCmp (c, TVar (ka, x), TVar (k, y)), pol, OFacts ps ->
      OFacts
        (sup_set (equal_prod equal_var_id equal_var_id) ps
          (cmp_facts equal_var_id c pol x y))
    | TNot b, pol, d -> ord_branch b (not pol) d
    | TN (v, va), uv, d -> d
    | TVar (v, va), uv, d -> d
    | TArith (v, va, vb, vc), uv, d -> d
    | TCast (v, va), uv, d -> d
    | TCmp (v, TN (vc, vd), vb), uv, d -> d
    | TCmp (v, TArith (vc, vd, ve, vf), vb), uv, d -> d
    | TCmp (v, TCast (vc, vd), vb), uv, d -> d
    | TCmp (v, TCmp (vc, vd, ve), vb), uv, d -> d
    | TCmp (v, TNot vc, vb), uv, d -> d
    | TCmp (v, TAnd (vc, vd), vb), uv, d -> d
    | TCmp (v, TOr (vc, vd), vb), uv, d -> d
    | TCmp (v, va, TN (vc, vd)), uv, d -> d
    | TCmp (v, va, TArith (vc, vd, ve, vf)), uv, d -> d
    | TCmp (v, va, TCast (vc, vd)), uv, d -> d
    | TCmp (v, va, TCmp (vc, vd, ve)), uv, d -> d
    | TCmp (v, va, TNot vc), uv, d -> d
    | TCmp (v, va, TAnd (vc, vd)), uv, d -> d
    | TCmp (v, va, TOr (vc, vd)), uv, d -> d
    | TAnd (v, va), uv, d -> d
    | TOr (v, va), uv, d -> d
    | TCmp (v, va, vb), uv, OBot -> OBot;;

let rec combine_env_identity cha ch ci x de = x;;

let rec top_fun _B x = top _B;;

let rec query_unknown
  ch x = top_fun (top_query_lift (order_int_dom_ext bounded_lattice_unit));;

let ord_spec : (var_id, texp, var_id order_rel lifted, unit) glocal_spec_ext
  = Glocal_spec_ext
      (query_unknown, (fun _ d -> d),
        (fun _ x _ -> map_lift (ord_forget equal_var_id x)),
        (fun _ _ x -> map_lift (ord_forget equal_var_id x)),
        (fun _ b pol -> map_lift (ord_branch b pol)), (fun _ _ d -> d),
        (fun _ r _ d ->
          (match r with None -> d
            | Some _ -> map_lift (ord_forget equal_var_id ReturnVar) d)),
        (fun _ _ d -> d), (fun _ _ p -> [(fst p, Lifted top_order_rel)]),
        combine_env_identity, (fun _ _ _ _ -> Lifted top_order_rel), ());;

let rec tglobal = function GlobalId uu -> true
                  | ScopedId (v, va) -> false
                  | ReturnId v -> false
                  | ReturnVar -> false;;

let rec order_run
  r ds p =
    (if is_none
          (tD_side_rule_Interp_solve_c (equal_prod equal_cfg_node equal_unit)
            (equal_global_unknown equal_unit equal_unit)
            ((equal_dg_state (equal_lifted (equal_order_rel equal_var_id))
               (equal_lifted (equal_order_rel equal_var_id))),
              (bounded_semilattice_sup_bot_dg_state
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_order_rel
                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_order_rel
                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
              (warrowing_dg_state
                ((bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_order_rel
                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
                  (warrowing_lifted
                    ((bounded_semilattice_sup_bot_order_rel equal_var_id),
                      (warrowing_order_rel equal_var_id))))
                ((bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_order_rel
                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
                  (warrowing_lifted
                    ((bounded_semilattice_sup_bot_order_rel equal_var_id),
                      (warrowing_order_rel equal_var_id))))))
            r (equations (equal_var_id, linorder_var_id)
                (equal_texp, linorder_texp)
                ((equal_order_rel equal_var_id),
                  (semilattice_sup_order_rel equal_var_id))
                (equal_global_unknown equal_unit equal_unit) equal_unit
                (fun _ _ -> ord_spec) top_order_rel (Analysis_Global ())
                (fun a -> Analysis_Global a) (fun a b -> Activation_Seed (a, b))
                (fun _ _ _ _ _ -> ()) ()
                (fun _ ->
                  dg_spec_of equal_texp
                    (bot_lifted (semilattice_sup_order_rel equal_var_id)))
                (fun _ _ -> Bot) (fun _ _ -> []) (fun pa -> typed_cfg pa ds)
                (fun _ -> FunctionEntry prog_main_name) tglobal p)
            (cfg_exit (typed_cfg p ds), ()))
      then Typed_No_Answer
      else Typed_Analysed
             (report (equal_var_id, linorder_var_id) (equal_texp, linorder_texp)
               ((equal_order_rel equal_var_id),
                 (semilattice_sup_order_rel equal_var_id))
               (equal_global_unknown equal_unit equal_unit) equal_unit
               (fun _ _ -> ord_spec)
               (fun _ d -> equal_order_rela equal_var_id d OBot) (fun _ d -> d)
               top_order_rel (Analysis_Global ()) (fun a -> Analysis_Global a)
               (fun a b -> Activation_Seed (a, b)) (fun _ _ _ _ _ -> ()) ()
               (tD_side_rule_Interp_solve (equal_prod equal_cfg_node equal_unit)
                 (equal_global_unknown equal_unit equal_unit)
                 ((equal_dg_state (equal_lifted (equal_order_rel equal_var_id))
                    (equal_lifted (equal_order_rel equal_var_id))),
                   (bounded_semilattice_sup_bot_dg_state
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_order_rel
                         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_order_rel
                         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
                   (warrowing_dg_state
                     ((bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_order_rel
                          equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
                       (warrowing_lifted
                         ((bounded_semilattice_sup_bot_order_rel equal_var_id),
                           (warrowing_order_rel equal_var_id))))
                     ((bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_order_rel
                          equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
                       (warrowing_lifted
                         ((bounded_semilattice_sup_bot_order_rel equal_var_id),
                           (warrowing_order_rel equal_var_id))))))
                 r)
               OBot ord_classify
               (fun _ ->
                 dg_spec_of equal_texp
                   (bot_lifted (semilattice_sup_order_rel equal_var_id)))
               (fun _ d _ -> d) (fun _ _ -> Bot) (fun _ _ -> [])
               (fun pa -> typed_cfg pa ds)
               (fun _ -> FunctionEntry prog_main_name) tglobal p ()));;

let rec greserved_ret_var rv g = not (g rv);;

let rec may_fallthrough
  = function SKIP uu -> true
    | Assign (uv, uw, ux) -> true
    | Check (uy, uz, va) -> true
    | Seq (c1, c2) -> may_fallthrough c1 && may_fallthrough c2
    | If (vb, vc, c1, c2) -> may_fallthrough c1 || may_fallthrough c2
    | While (vd, ve, vf) -> true
    | Call (vg, vh, vi, vj) -> true
    | Return (vk, vl) -> false
    | Restore vm -> false
    | Unwind vn -> false;;

let rec may_return_value
  = function
    Seq (c1, c2) ->
      may_return_value c1 || may_fallthrough c1 && may_return_value c2
    | If (uu, uv, c1, c2) -> may_return_value c1 || may_return_value c2
    | While (uw, ux, c) -> may_return_value c
    | Return (uy, e) -> not (is_none e)
    | SKIP v -> false
    | Assign (v, va, vb) -> false
    | Check (v, va, vb) -> false
    | Call (v, va, vb, vc) -> false
    | Restore v -> false
    | Unwind v -> false;;

let rec may_return_none
  = function
    Seq (c1, c2) ->
      may_return_none c1 || may_fallthrough c1 && may_return_none c2
    | If (uu, uv, c1, c2) -> may_return_none c1 || may_return_none c2
    | While (uw, ux, c) -> may_return_none c
    | Return (uy, e) -> is_none e
    | SKIP v -> false
    | Assign (v, va, vb) -> false
    | Check (v, va, vb) -> false
    | Call (v, va, vb, vc) -> false
    | Restore v -> false
    | Unwind v -> false;;

let rec source_com = function SKIP uu -> true
                     | Assign (uv, x, a) -> true
                     | Check (uw, l, c) -> true
                     | Seq (c1, c2) -> source_com c1 && source_com c2
                     | If (ux, b, c1, c2) -> source_com c1 && source_com c2
                     | While (uy, b, c) -> source_com c
                     | Call (uz, dst, p, actuals) -> true
                     | Return (va, e) -> true
                     | Restore vb -> false
                     | Unwind vc -> false;;

let rec value_providing
  c = source_com c &&
        (not (may_fallthrough c) &&
          (not (may_return_none c) && may_return_value c));;

let rec gsource_exp _B vars rv a = not (member _B rv (vars a));;

let rec gwf_source_com _B
  vars rv pi x3 = match vars, rv, pi, x3 with vars, rv, pi, SKIP uu -> true
    | vars, rv, pi, Assign (uv, x, a) ->
        not (eq _B x rv) && gsource_exp _B vars rv a
    | vars, rv, pi, Check (uw, l, c) -> gsource_exp _B vars rv c
    | vars, rv, pi, Seq (c1, c2) ->
        gwf_source_com _B vars rv pi c1 && gwf_source_com _B vars rv pi c2
    | vars, rv, pi, If (ux, b, c1, c2) ->
        gsource_exp _B vars rv b &&
          (gwf_source_com _B vars rv pi c1 && gwf_source_com _B vars rv pi c2)
    | vars, rv, pi, While (uy, b, c) ->
        gsource_exp _B vars rv b && gwf_source_com _B vars rv pi c
    | vars, rv, pi, Call (uz, dst, p, actuals) ->
        (match special_table p
          with None ->
            (match pi p with None -> false
              | Some decl ->
                equal_nata (size_list actuals) (size_list (formals decl)) &&
                  (list_all (gsource_exp _B vars rv) actuals &&
                    (match dst with None -> true
                      | Some x ->
                        not (eq _B x rv) && value_providing (body decl))))
          | Some desc ->
            not (is_none (classify_special desc actuals)) &&
              (list_all (gsource_exp _B vars rv) actuals &&
                (match dst with None -> false | Some x -> not (eq _B x rv))))
    | vars, rv, pi, Return (va, e) ->
        (match e with None -> true | Some a -> gsource_exp _B vars rv a)
    | vars, rv, pi, Restore vb -> false
    | vars, rv, pi, Unwind vc -> false;;

let rec gvalid_formal _A rv g x = not (g x) && not (eq _A x rv);;

let rec gwf_proc_decl _B
  vars rv g pi decl =
    distinct _B (formals decl) &&
      (list_all (gvalid_formal _B rv g) (formals decl) &&
        gwf_source_com _B vars rv pi (body decl));;

let rec prog_main p = main_body (prog_table p);;

let rec exp_vnames
  = function N uu -> bot_set
    | V x -> inserta equal_literal x bot_set
    | Plus (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Minus (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Times (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Div (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Mod (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Less (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | LessEq (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Greater (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | GreaterEq (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | NotEq (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Eq (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Not b -> exp_vnames b
    | And (b1, b2) -> sup_set equal_literal (exp_vnames b1) (exp_vnames b2)
    | Or (b1, b2) -> sup_set equal_literal (exp_vnames b1) (exp_vnames b2)
    | Cast (uv, a) -> exp_vnames a;;

let rec no_return = function Seq (c1, c2) -> no_return c1 && no_return c2
                    | If (uu, uv, c1, c2) -> no_return c1 && no_return c2
                    | While (uw, ux, c) -> no_return c
                    | Return (uy, uz) -> false
                    | SKIP v -> true
                    | Assign (v, vb, vc) -> true
                    | Check (v, vb, vc) -> true
                    | Call (v, vb, vc, vd) -> true
                    | Restore v -> true
                    | Unwind v -> true;;

let rec wf_program_compile_input_exec
  p = (let procs = proc_rep p in
       let g = declared_global p in
       let pi = map_of equal_literal procs in
        greserved_ret_var ret_var g &&
          (distinct equal_literal (prog_procs p) &&
            (equal_set equal_literal (Set (prog_procs p))
               (remove equal_literal prog_main_name (Set (map fst procs))) &&
              (not (membera equal_literal (prog_procs p) prog_main_name) &&
                (equal_option
                   (equal_gproc_decl_ext equal_unit equal_literal equal_exp
                     equal_unit)
                   (pi prog_main_name)
                   (Some (Gproc_decl_ext ([], prog_main p, ()))) &&
                  (gwf_source_com equal_literal exp_vnames ret_var pi
                     (prog_main p) &&
                    (no_return (prog_main p) &&
                      (list_all
                         (fun (_, a) ->
                           gwf_proc_decl equal_literal exp_vnames ret_var g pi
                             a)
                         procs &&
                        list_all (fun (q, _) -> is_none (special_table q))
                          procs))))))));;

let rec tclassify _A
  kappa c d =
    (match d with TTop -> Check_Unknown
      | TL sigma ->
        (match truth_ik _A (taeval _A kappa c sigma) with None -> Check_Unknown
          | Some true -> Check_Proved | Some false -> Check_Refuted));;

let rec tinit_st _A
  ds = TL (Abs_default_st
            ((KTop, []),
              (KD (I32, of_int_ik _A I32 zero_inta),
                map (fun (v, k) -> (v, KD (k, of_int_ik _A k zero_inta)))
                  ds)));;

let rec bot_fun _B x = bot _B;;

let rec map_toplift f x1 = match f, x1 with f, TTop -> TTop
                      | f, TL x2 -> TL (f x2);;

let rec transfer_lift2
  empty_pred f x y =
    bind_lift x
      (fun a -> bind_lift y (fun b -> normalize_lift empty_pred (f a b)));;

let rec tcombine_assign_st _A
  kappa dst st ste =
    (match dst with None -> st
      | Some x ->
        default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
          (location_of tglobal x)
          (KD (kappa x,
                cast_ik _A None (kappa x)
                  (kd_val _A
                    (default_st_to_fun equal_var_id
                      (bot_kd _A.ik_domain_kind_int_domain) tglobal ste
                      ReturnVar)))));;

let rec ci_formals
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_formals;;

let rec ci_args
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_args;;

let rec ci_dst
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_dst;;

let rec tl_map2 f uu uv = match f, uu, uv with f, TL a, TL b -> TL (f a b)
                  | f, TTop, uv -> TTop
                  | f, uu, TTop -> TTop;;

let rec tl_bind f x1 = match f, x1 with f, TTop -> TTop
                  | f, TL a -> f a;;

let rec special_val _A
  kappa sc x sigma =
    (match sc with Nondet_Int -> top_ik _A (kappa x)
      | Min (a, b) ->
        cast_ik _A None (kappa x)
          (sup _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
            (taeval _A kappa a sigma) (taeval _A kappa b sigma))
      | Max (a, b) ->
        cast_ik _A None (kappa x)
          (sup _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
            (taeval _A kappa a sigma) (taeval _A kappa b sigma)));;

let rec tspecial_st _A
  kappa sc x st =
    default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
      (location_of tglobal x)
      (KD (kappa x,
            special_val _A kappa sc x
              (default_st_to_fun equal_var_id
                (bot_kd _A.ik_domain_kind_int_domain) tglobal st)));;

let rec tl_map f x1 = match f, x1 with f, TTop -> TTop
                 | f, TL a -> TL (f a);;

let rec ret_kd _A
  kappa e sigma =
    (match e with TN (_, _) -> KD (texp_kind e, taeval _A kappa e sigma)
      | TVar (_, v) ->
        (if equal_var_ida v ReturnVar then KTop
          else KD (kappa v, read_var _A kappa sigma v))
      | TArith (_, _, _, _) -> KD (texp_kind e, taeval _A kappa e sigma)
      | TCast (_, _) -> KD (texp_kind e, taeval _A kappa e sigma)
      | TCmp (_, _, _) -> KD (texp_kind e, taeval _A kappa e sigma)
      | TNot _ -> KD (texp_kind e, taeval _A kappa e sigma)
      | TAnd (_, _) -> KD (texp_kind e, taeval _A kappa e sigma)
      | TOr (_, _) -> KD (texp_kind e, taeval _A kappa e sigma));;

let rec treturn_st _A
  kappa r st =
    (match r with None -> st
      | Some e ->
        default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
          (location_of tglobal ReturnVar)
          (ret_kd _A kappa e
            (default_st_to_fun equal_var_id
              (bot_kd _A.ik_domain_kind_int_domain) tglobal st)));;

let rec narrow_var _A
  kappa v a sigma =
    (if equal_var_ida v ReturnVar then sigma
      else fun_upd equal_var_id sigma v
             (KD (kappa v, meet_ik _A a (read_var _A kappa sigma v))));;

let rec refine_var _A
  kappa x1 a sigma = match kappa, x1, a, sigma with
    kappa, TVar (ik, v), a, sigma -> narrow_var _A kappa v a sigma
    | kappa, TCast (ik, e), a, sigma ->
        (if fits_ik _A ik (taeval _A kappa e sigma)
          then refine_var _A kappa e a sigma else sigma)
    | kappa, TArith (ik, op, e_1, e_2), a, sigma ->
        (let a_1 = taeval _A kappa e_1 sigma in
         let a_2 = taeval _A kappa e_2 sigma in
          (if not (fits_ik _A ik (raw_aop_ik _A op a_1 a_2)) then sigma
            else (match op
                   with AAdd ->
                     refine_var _A kappa e_2 (raw_aop_ik _A ASub a a_1)
                       (refine_var _A kappa e_1 (raw_aop_ik _A ASub a a_2)
                         sigma)
                   | ASub ->
                     refine_var _A kappa e_2 (raw_aop_ik _A ASub a_1 a)
                       (refine_var _A kappa e_1 (raw_aop_ik _A AAdd a a_2)
                         sigma)
                   | AMul -> sigma | ADiv -> sigma | AMod -> sigma)))
    | kappa, TN (v, va), a, sigma -> sigma
    | kappa, TCmp (v, va, vb), a, sigma -> sigma
    | kappa, TNot v, a, sigma -> sigma
    | kappa, TAnd (v, va), a, sigma -> sigma
    | kappa, TOr (v, va), a, sigma -> sigma;;

let rec neg_cop = function CLt -> CGe
                  | CLe -> CGt
                  | CGt -> CLe
                  | CGe -> CLt
                  | CEq -> CNe
                  | CNe -> CEq;;

let rec trefine _A
  kappa x1 pol sigma = match kappa, x1, pol, sigma with
    kappa, TCmp (c, l, r), pol, sigma ->
      (let (al, ar) =
         refine_ik _A (if pol then c else neg_cop c) (taeval _A kappa l sigma)
           (taeval _A kappa r sigma)
         in
        refine_var _A kappa l al (refine_var _A kappa r ar sigma))
    | kappa, TNot e, pol, sigma -> trefine _A kappa e (not pol) sigma
    | kappa, TAnd (a, b), true, sigma ->
        trefine _A kappa b true (trefine _A kappa a true sigma)
    | kappa, TOr (a, b), false, sigma ->
        trefine _A kappa b false (trefine _A kappa a false sigma)
    | kappa, TN (v, va), pol, sigma -> sigma
    | kappa, TVar (v, va), pol, sigma -> sigma
    | kappa, TArith (v, va, vb, vc), pol, sigma -> sigma
    | kappa, TCast (v, va), pol, sigma -> sigma
    | kappa, TAnd (v, va), false, sigma -> sigma
    | kappa, TOr (v, va), true, sigma -> sigma;;

let rec write_back _A
  vs sigma st =
    fold (fun v sta ->
           default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) sta
             (location_of tglobal v) (sigma v))
      vs st;;

let rec tvar_list = function TN (uu, uv) -> []
                    | TVar (uw, v) -> [v]
                    | TArith (ux, uy, a, b) -> tvar_list a @ tvar_list b
                    | TCast (uz, a) -> tvar_list a
                    | TCmp (va, a, b) -> tvar_list a @ tvar_list b
                    | TNot a -> tvar_list a
                    | TAnd (a, b) -> tvar_list a @ tvar_list b
                    | TOr (a, b) -> tvar_list a @ tvar_list b;;

let rec tbranch_st _A
  kappa b pol st =
    (let refined =
       write_back _A (tvar_list b)
         (trefine _A kappa b pol
           (default_st_to_fun equal_var_id (bot_kd _A.ik_domain_kind_int_domain)
             tglobal st))
         st
       in
      (match
        truth_ik _A
          (taeval _A kappa b
            (default_st_to_fun equal_var_id
              (bot_kd _A.ik_domain_kind_int_domain) tglobal st))
        with None -> refined
        | Some r ->
          (if equal_boola r pol then refined
            else bot_gdefault_sta (bot_kd _A.ik_domain_kind_int_domain))));;

let rec tassign_st _A
  kappa x e st =
    default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
      (location_of tglobal x)
      (KD (kappa x,
            cast_ik _A None (kappa x)
              (taeval _A kappa e
                (default_st_to_fun equal_var_id
                  (bot_kd _A.ik_domain_kind_int_domain) tglobal st))));;

let rec is_empty_kd _A = function KBot -> true
                         | KD (k, a) -> empty_ik _A k a
                         | KTop -> false;;

let rec tst_rep_is_bot _A
  ((dl, ls), (dg, gs)) =
    is_empty_kd _A.ik_domain_kind_int_domain dl ||
      (is_empty_kd _A.ik_domain_kind_int_domain dg ||
        (list_ex
           (fun x ->
             not (tglobal x) &&
               is_empty_kd _A.ik_domain_kind_int_domain
                 (default_dict_get equal_var_id (dl, ls) x))
           (map fst ls) ||
          list_ex
            (fun x ->
              tglobal x &&
                is_empty_kd _A.ik_domain_kind_int_domain
                  (default_dict_get equal_var_id (dg, gs) x))
            (map fst gs)));;

let rec tst_is_bot _A (Abs_default_st x) = tst_rep_is_bot _A x;;

let rec tst_empty _A = function TTop -> false
                       | TL st -> tst_is_bot _A st;;

let rec enter_frame_D_default_st_rep _A top_val s = ((top_val, []), snd s);;

let rec enter_frame_D_default_st _A
  xa (Abs_default_st x) =
    Abs_default_st (enter_frame_D_default_st_rep _A xa x);;

let rec bind_formals_default_st_rep _A _B
  g xs avs s =
    fold (fun (x, a) t -> default_st_rep_set _B _A t (location_of g x) a)
      (zip xs avs) s;;

let rec bind_formals_default_st _A _B
  xc xb xa (Abs_default_st x) =
    Abs_default_st (bind_formals_default_st_rep _A _B xc xb xa x);;

let rec arg_fits
  kappa p e =
    not (equal_var_ida p ReturnVar) &&
      (match e with TN (_, _) -> equal_ikind (texp_kind e) (kappa p)
        | TVar (_, v) ->
          not (equal_var_ida v ReturnVar) && equal_ikind (kappa v) (kappa p)
        | TArith (_, _, _, _) -> equal_ikind (texp_kind e) (kappa p)
        | TCast (_, _) -> equal_ikind (texp_kind e) (kappa p)
        | TCmp (_, _, _) -> equal_ikind (texp_kind e) (kappa p)
        | TNot _ -> equal_ikind (texp_kind e) (kappa p)
        | TAnd (_, _) -> equal_ikind (texp_kind e) (kappa p)
        | TOr (_, _) -> equal_ikind (texp_kind e) (kappa p));;

let rec tenter_st _A
  kappa ps es st =
    (if list_all (fun (a, b) -> arg_fits kappa a b) (zip ps es)
      then TL (bind_formals_default_st equal_var_id
                (bot_kd _A.ik_domain_kind_int_domain) tglobal ps
                (map (fun (x, y) ->
                       KD (kappa x,
                            cast_ik _A None (kappa x)
                              (taeval _A kappa y
                                (default_st_to_fun equal_var_id
                                  (bot_kd _A.ik_domain_kind_int_domain) tglobal
                                  st))))
                  (zip ps es))
                (enter_frame_D_default_st (bot_kd _A.ik_domain_kind_int_domain)
                  KTop st))
      else TTop);;

let rec typed_exec_spec _A
  kappa =
    Glocal_spec_ext
      (query_unknown, (fun _ d -> d),
        (fun _ x e ->
          transfer_lift (tst_empty _A) (tl_map (tassign_st _A kappa x e))),
        (fun _ sc x ->
          transfer_lift (tst_empty _A) (tl_map (tspecial_st _A kappa sc x))),
        (fun _ b pol ->
          transfer_lift (tst_empty _A) (tl_map (tbranch_st _A kappa b pol))),
        (fun _ _ d -> d),
        (fun _ r _ ->
          transfer_lift (tst_empty _A) (tl_map (treturn_st _A kappa r))),
        (fun _ _ d -> d),
        (fun _ ci p ->
          [(fst p,
             transfer_lift (tst_empty _A)
               (tl_bind (tenter_st _A kappa (ci_formals ci) (ci_args ci)))
               (fst p))]),
        (fun _ _ _ x y ->
          bind_lift x
            (fun a ->
              bind_lift y
                (fun b ->
                  Lifted
                    (tl_map2
                      (combine_default_st (bot_kd _A.ik_domain_kind_int_domain))
                      a b)))),
        (fun _ ci ->
          transfer_lift2 (tst_empty _A)
            (tl_map2 (tcombine_assign_st _A kappa (ci_dst ci)))),
        ());;

let rec nonrel_run (_A1, _A2)
  t r ds p =
    (if is_none
          (tD_side_rule_Interp_solve_c (equal_prod equal_cfg_node equal_unit)
            (equal_global_unknown equal_unit equal_unit)
            ((equal_dg_state
               (equal_lifted
                 (equal_toplift
                   (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                     ((equal_kd _A1),
                       (bounded_semilattice_sup_bot_kd
                         _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))))
               (equal_lifted
                 (equal_toplift
                   (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                     ((equal_kd _A1),
                       (bounded_semilattice_sup_bot_kd
                         _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))))),
              (bounded_semilattice_sup_bot_dg_state
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_toplift
                    (bounded_semilattice_sup_bot_gdefault_st
                      (infinite_key_var_id, equal_var_id)
                      (bounded_semilattice_sup_bot_kd
                        _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot)
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_toplift
                    (bounded_semilattice_sup_bot_gdefault_st
                      (infinite_key_var_id, equal_var_id)
                      (bounded_semilattice_sup_bot_kd
                        _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot)),
              (warrowing_dg_state
                ((bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_toplift
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_var_id, equal_var_id)
                       (bounded_semilattice_sup_bot_kd
                         _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot),
                  (warrowing_lifted
                    ((bounded_semilattice_sup_bot_toplift
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_var_id, equal_var_id)
                         (bounded_semilattice_sup_bot_kd
                           _A2.ik_domain_kind_int_domain))),
                      (warrowing_toplift
                        (warrowing_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          ((bounded_semilattice_sup_bot_kd
                             _A2.ik_domain_kind_int_domain),
                            (warrowing_kd _A2.ik_domain_kind_int_domain)))))))
                ((bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_toplift
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_var_id, equal_var_id)
                       (bounded_semilattice_sup_bot_kd
                         _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot),
                  (warrowing_lifted
                    ((bounded_semilattice_sup_bot_toplift
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_var_id, equal_var_id)
                         (bounded_semilattice_sup_bot_kd
                           _A2.ik_domain_kind_int_domain))),
                      (warrowing_toplift
                        (warrowing_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          ((bounded_semilattice_sup_bot_kd
                             _A2.ik_domain_kind_int_domain),
                            (warrowing_kd _A2.ik_domain_kind_int_domain)))))))))
            r (equations (equal_var_id, linorder_var_id)
                (equal_texp, linorder_texp)
                ((equal_toplift
                   (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                     ((equal_kd _A1),
                       (bounded_semilattice_sup_bot_kd
                         _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))),
                  (semilattice_sup_toplift
                    (semilattice_sup_gdefault_st
                      (infinite_key_var_id, equal_var_id)
                      (bounded_semilattice_sup_bot_kd
                        _A2.ik_domain_kind_int_domain))))
                (equal_global_unknown equal_unit equal_unit) equal_unit
                (fun _ _ -> typed_exec_spec _A2 (kenv_of ds)) (tinit_st _A2 ds)
                (Analysis_Global ()) (fun a -> Analysis_Global a)
                (fun a b -> Activation_Seed (a, b)) (fun _ _ _ _ _ -> ()) ()
                (fun _ ->
                  dg_spec_of equal_texp
                    (bot_lifted
                      (semilattice_sup_toplift
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            _A2.ik_domain_kind_int_domain)))))
                (fun _ _ -> Bot) (fun _ _ -> []) (fun pa -> typed_cfg pa ds)
                (fun _ -> FunctionEntry prog_main_name) tglobal p)
            (cfg_exit (typed_cfg p ds), ()))
      then Typed_No_Answer
      else Typed_Analysed
             (report (equal_var_id, linorder_var_id) (equal_texp, linorder_texp)
               ((equal_toplift
                  (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                    ((equal_kd _A1),
                      (bounded_semilattice_sup_bot_kd
                        _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))),
                 (semilattice_sup_toplift
                   (semilattice_sup_gdefault_st
                     (infinite_key_var_id, equal_var_id)
                     (bounded_semilattice_sup_bot_kd
                       _A2.ik_domain_kind_int_domain))))
               (equal_global_unknown equal_unit equal_unit) equal_unit
               (fun _ _ -> typed_exec_spec _A2 (kenv_of ds))
               (fun _ -> tst_empty _A2)
               (fun g ->
                 map_toplift
                   (default_st_to_fun equal_var_id
                     (bot_kd _A2.ik_domain_kind_int_domain) g))
               (tinit_st _A2 ds) (Analysis_Global ())
               (fun a -> Analysis_Global a) (fun a b -> Activation_Seed (a, b))
               (fun _ _ _ _ _ -> ()) ()
               (tD_side_rule_Interp_solve (equal_prod equal_cfg_node equal_unit)
                 (equal_global_unknown equal_unit equal_unit)
                 ((equal_dg_state
                    (equal_lifted
                      (equal_toplift
                        (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                          ((equal_kd _A1),
                            (bounded_semilattice_sup_bot_kd
                              _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))))
                    (equal_lifted
                      (equal_toplift
                        (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                          ((equal_kd _A1),
                            (bounded_semilattice_sup_bot_kd
                              _A2.ik_domain_kind_int_domain).order_bot_bounded_semilattice_sup_bot))))),
                   (bounded_semilattice_sup_bot_dg_state
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_toplift
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_toplift
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot)),
                   (warrowing_dg_state
                     ((bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_toplift
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot),
                       (warrowing_lifted
                         ((bounded_semilattice_sup_bot_toplift
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                _A2.ik_domain_kind_int_domain))),
                           (warrowing_toplift
                             (warrowing_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((bounded_semilattice_sup_bot_kd
                                  _A2.ik_domain_kind_int_domain),
                                 (warrowing_kd
                                   _A2.ik_domain_kind_int_domain)))))))
                     ((bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_toplift
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              _A2.ik_domain_kind_int_domain))).semilattice_sup_bounded_semilattice_sup_bot),
                       (warrowing_lifted
                         ((bounded_semilattice_sup_bot_toplift
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                _A2.ik_domain_kind_int_domain))),
                           (warrowing_toplift
                             (warrowing_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((bounded_semilattice_sup_bot_kd
                                  _A2.ik_domain_kind_int_domain),
                                 (warrowing_kd
                                   _A2.ik_domain_kind_int_domain)))))))))
                 r)
               (TL (bot_fun (bot_kd _A2.ik_domain_kind_int_domain)))
               (tclassify _A2 (kenv_of ds))
               (fun _ ->
                 dg_spec_of equal_texp
                   (bot_lifted
                     (semilattice_sup_toplift
                       (semilattice_sup_gdefault_st
                         (infinite_key_var_id, equal_var_id)
                         (bounded_semilattice_sup_bot_kd
                           _A2.ik_domain_kind_int_domain)))))
               (fun _ d _ -> d) (fun _ _ -> Bot) (fun _ _ -> [])
               (fun pa -> typed_cfg pa ds)
               (fun _ -> FunctionEntry prog_main_name) tglobal p ()));;

let rec run_typed
  d r ds p =
    (if not (wf_program_compile_input_exec p) then Typed_Malformed
      else (match d
             with Typed_Interval ->
               nonrel_run (equal_ivl, kind_int_domain_ivl) Type r ds p
             | Typed_Congruence ->
               nonrel_run (equal_congruence, kind_int_domain_congruence) Type r
                 ds p
             | Typed_Int ->
               nonrel_run (equal_int_tuple, kind_int_domain_int_tuple) Type r ds
                 p
             | Typed_Order -> order_run r ds p
             | Typed_Sign ->
               nonrel_run (equal_sign, kind_int_domain_sign) Type r ds p
             | Typed_Parity ->
               nonrel_run (equal_parity, kind_int_domain_parity) Type r ds p));;

let rec field_empty
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = field_empty;;

let rec default_st_rep_is_bot _A
  g ((dl, ls), (dg, gs)) =
    is_empty _A dl ||
      (list_ex
         (fun x ->
           not (g x) && is_empty _A (default_dict_get equal_literal (dl, ls) x))
         (map fst ls) ||
        list_ex
          (fun x ->
            g x && is_empty _A (default_dict_get equal_literal (dg, gs) x))
          (map fst gs));;

let rec default_st_rep_is_bot_for _A
  globals g s =
    list_ex
      (fun x ->
        is_empty _A
          (default_st_rep_get
            _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
            equal_literal s (location_of g x)))
      globals ||
      default_st_rep_is_bot _A g s;;

let rec default_st_is_bot_for _A
  xb (Abs_default_st xa) =
    default_st_rep_is_bot_for _A xb (membera equal_literal xb) xa;;

let rec n_query (_A1, _A2)
  (Nonrelational_ops_ext (n_aval, n_query, n_refine, n_special, more)) =
    n_query;;

let rec n_aval (_A1, _A2)
  (Nonrelational_ops_ext (n_aval, n_query, n_refine, n_special, more)) =
    n_aval;;

let rec congruence_min a b = sup_congruencea a b;;

let rec congruence_max a b = sup_congruencea a b;;

let congruence_special_ops : (congruence, unit) special_ops_ext
  = Special_ops_ext (congruence_min, congruence_max, ());;

let rec preimage_times_const_rep
  x0 k = match x0, k with None, k -> None
    | Some (c, m), k ->
        normalize_congruence_rep
          (if equal_inta m zero_inta
            then (if equal_inta k zero_inta
                   then (if equal_inta c zero_inta
                          then Some (zero_inta, one_inta) else None)
                   else (if dvd (equal_int, semidom_modulo_int) k c
                          then Some (divide_inta c k, zero_inta) else None))
            else (let g = gcd_intc k m in
                   (if dvd (equal_int, semidom_modulo_int) g c
                     then (let s =
                             fst (bezout_coefficients
                                   (euclidean_ring_gcd_int, equal_int) k m)
                             in
                            Some (times_inta (divide_inta c g) s,
                                   divide_inta m g))
                     else None)));;

let rec inverse_times_candidate_rep
  x0 factor = match x0, factor with None, factor -> None
    | Some v, None -> None
    | Some (c, m), Some (k, n) ->
        (if equal_inta n zero_inta then preimage_times_const_rep (Some (c, m)) k
          else Some (zero_inta, one_inta));;

let rec inverse_times_candidate
  xb xc =
    Abs_congruence
      (inverse_times_candidate_rep (rep_congruence xb) (rep_congruence xc));;

let rec inv_times_congruence
  r a b =
    (inf_congruence a (inverse_times_candidate r b),
      inf_congruence b (inverse_times_candidate r a));;

let rec inv_minus_congruence
  r a b =
    (inf_congruence a (plus_congruence r b),
      inf_congruence b (minus_congruence a r));;

let rec inv_plus_congruence
  r a b =
    (inf_congruence a (minus_congruence r b),
      inf_congruence b (minus_congruence r a));;

let rec inv_less_congruence result a b = (a, b);;

let rec congruence_tobool
  a = (match congruence_singleton a with None -> None
        | Some c -> Some (not (equal_inta c zero_inta)));;

let rec inv_eq_congruence
  x0 a b = match x0, a, b with
    true, a, b -> (inf_congruence a b, inf_congruence a b)
    | false, a, b -> (a, b);;

let congruence_refine_ops : (congruence, unit) refine_ops_ext
  = Refine_ops_ext
      (congruence_tobool, inv_less_congruence, inv_eq_congruence,
        inv_plus_congruence, inv_minus_congruence, inv_times_congruence,
        inf_congruence, ());;

let rec congruence_cast
  ik a =
    (if is_empty_congruence a then bot_congruencea
      else (match congruence_singleton a with None -> top_congruencea
             | Some c -> congruence_of_int (ik_norm ik c)));;

let rec of_bool_option _A
  lit x1 = match lit, x1 with
    lit, Some b -> lit (if b then one_inta else zero_inta)
    | lit, None -> sup _A (lit zero_inta) (lit one_inta);;

let rec bin_log
  f ann x y =
    (if equal_option equal_bool x (Some ann) ||
          equal_option equal_bool y (Some ann)
      then Some ann
      else (match (x, y) with (None, _) -> None | (Some _, None) -> None
             | (Some a, Some b) -> Some (f a b)));;

let rec aval_congruence
  x0 sigma = match x0, sigma with N n, sigma -> congruence_of_int n
    | V x, sigma -> sigma x
    | Plus (e1, e2), sigma ->
        plus_congruence (aval_congruence e1 sigma) (aval_congruence e2 sigma)
    | Minus (e1, e2), sigma ->
        minus_congruence (aval_congruence e1 sigma) (aval_congruence e2 sigma)
    | Times (e1, e2), sigma ->
        times_congruence (aval_congruence e1 sigma) (aval_congruence e2 sigma)
    | Div (e1, e2), sigma ->
        congruence_div (aval_congruence e1 sigma) (aval_congruence e2 sigma)
    | Mod (e1, e2), sigma ->
        congruence_mod (aval_congruence e1 sigma) (aval_congruence e2 sigma)
    | Less (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (congruence_lt (aval_congruence e1 sigma)
                   (aval_congruence e2 sigma)))
    | LessEq (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (map_option not
                   (congruence_lt (aval_congruence e2 sigma)
                     (aval_congruence e1 sigma))))
    | Greater (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (congruence_lt (aval_congruence e2 sigma)
                   (aval_congruence e1 sigma)))
    | GreaterEq (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (map_option not
                   (congruence_lt (aval_congruence e1 sigma)
                     (aval_congruence e2 sigma))))
    | NotEq (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (map_option not
                   (congruence_eqb (aval_congruence e1 sigma)
                     (aval_congruence e2 sigma))))
    | Eq (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (congruence_eqb (aval_congruence e1 sigma)
                   (aval_congruence e2 sigma)))
    | Not e, sigma ->
        (if is_empty_congruence (aval_congruence e sigma) then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (map_option not (congruence_tobool (aval_congruence e sigma))))
    | And (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (bin_log (fun a b -> a && b) false
                   (congruence_tobool (aval_congruence e1 sigma))
                   (congruence_tobool (aval_congruence e2 sigma))))
    | Or (e1, e2), sigma ->
        (if is_empty_congruence (aval_congruence e1 sigma) ||
              is_empty_congruence (aval_congruence e2 sigma)
          then bot_congruencea
          else of_bool_option sup_congruence congruence_of_int
                 (bin_log (fun a b -> a || b) true
                   (congruence_tobool (aval_congruence e1 sigma))
                   (congruence_tobool (aval_congruence e2 sigma))))
    | Cast (ik, e), sigma -> congruence_cast ik (aval_congruence e sigma);;

let congruence_ops : (congruence, unit) nonrelational_ops_ext
  = Nonrelational_ops_ext
      (aval_congruence, Query_ops_ext (congruence_lt, congruence_eqb, ()),
        congruence_refine_ops, congruence_special_ops, ());;

let rec q_eq (Query_ops_ext (q_less, q_eq, more)) = q_eq;;

let rec congruence_truthy_query
  e d = map_option not
          (q_eq (n_query (bot_congruence, top_congruence) congruence_ops)
            (n_aval (bot_congruence, top_congruence) congruence_ops e d)
            (n_aval (bot_congruence, top_congruence) congruence_ops
              (N zero_inta) d));;

let rec q_less (Query_ops_ext (q_less, q_eq, more)) = q_less;;

let rec congruence_check_query
  x0 d = match x0, d with
    Not b, d -> map_option not (congruence_check_query b d)
    | And (b1, b2), d ->
        bin_log (fun a b -> a && b) false (congruence_check_query b1 d)
          (congruence_check_query b2 d)
    | Or (b1, b2), d ->
        bin_log (fun a b -> a || b) true (congruence_check_query b1 d)
          (congruence_check_query b2 d)
    | Less (a, b), d ->
        q_less (n_query (bot_congruence, top_congruence) congruence_ops)
          (n_aval (bot_congruence, top_congruence) congruence_ops a d)
          (n_aval (bot_congruence, top_congruence) congruence_ops b d)
    | LessEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_congruence, top_congruence) congruence_ops)
            (n_aval (bot_congruence, top_congruence) congruence_ops b d)
            (n_aval (bot_congruence, top_congruence) congruence_ops a d))
    | Greater (a, b), d ->
        q_less (n_query (bot_congruence, top_congruence) congruence_ops)
          (n_aval (bot_congruence, top_congruence) congruence_ops b d)
          (n_aval (bot_congruence, top_congruence) congruence_ops a d)
    | GreaterEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_congruence, top_congruence) congruence_ops)
            (n_aval (bot_congruence, top_congruence) congruence_ops a d)
            (n_aval (bot_congruence, top_congruence) congruence_ops b d))
    | Eq (a, b), d ->
        q_eq (n_query (bot_congruence, top_congruence) congruence_ops)
          (n_aval (bot_congruence, top_congruence) congruence_ops a d)
          (n_aval (bot_congruence, top_congruence) congruence_ops b d)
    | NotEq (a, b), d ->
        map_option not
          (q_eq (n_query (bot_congruence, top_congruence) congruence_ops)
            (n_aval (bot_congruence, top_congruence) congruence_ops a d)
            (n_aval (bot_congruence, top_congruence) congruence_ops b d))
    | N v, d -> congruence_truthy_query (N v) d
    | V v, d -> congruence_truthy_query (V v) d
    | Plus (v, va), d -> congruence_truthy_query (Plus (v, va)) d
    | Minus (v, va), d -> congruence_truthy_query (Minus (v, va)) d
    | Times (v, va), d -> congruence_truthy_query (Times (v, va)) d
    | Div (v, va), d -> congruence_truthy_query (Div (v, va)) d
    | Mod (v, va), d -> congruence_truthy_query (Mod (v, va)) d
    | Cast (v, va), d -> congruence_truthy_query (Cast (v, va)) d;;

let rec bool_valued = function Not uu -> true
                      | And (uv, uw) -> true
                      | Or (ux, uy) -> true
                      | Less (uz, va) -> true
                      | LessEq (vb, vc) -> true
                      | Greater (vd, ve) -> true
                      | GreaterEq (vf, vg) -> true
                      | Eq (vh, vi) -> true
                      | NotEq (vj, vk) -> true
                      | N v -> false
                      | V v -> false
                      | Plus (v, va) -> false
                      | Minus (v, va) -> false
                      | Times (v, va) -> false
                      | Div (v, va) -> false
                      | Mod (v, va) -> false
                      | Cast (v, va) -> false;;

let rec answer_of_ivl
  i = QLifted
        (int_ivl_update (fun _ -> i) (top_int_dom_exta bounded_lattice_unit));;

let rec int_dom_of_int
  n = int_congruence_update (fun _ -> congruence_of_int n)
        (int_parity_update (fun _ -> parity_of_int n)
          (int_ivl_update (fun _ -> Ivl (Fin n, Fin n))
            (int_sign_update (fun _ -> sign_of_int n)
              (top_int_dom_exta bounded_lattice_unit))));;

let rec answer_of_int n = QLifted (int_dom_of_int n);;

let rec bool_answer
  r = (match r with None -> answer_of_ivl (Ivl (Fin zero_inta, Fin one_inta))
        | Some b -> answer_of_int (if b then one_inta else zero_inta));;

let rec congruence_eval_answer
  d (EvalInt e) =
    (if bool_valued e then bool_answer (congruence_check_query e d)
      else top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec generic_enter_st_for (_A1, _A2)
  ops g ci s =
    bind_formals_default_st equal_literal _A1 g (ci_formals ci)
      (map (fun e ->
             n_aval (_A1, _A2) ops e (default_st_to_fun equal_literal _A1 g s))
        (ci_args ci))
      (enter_frame_D_default_st _A1 (top _A2) s);;

let rec interval_less
  a b = (if interval_less_true a b then Some true
          else (if interval_less_false a b then Some false else None));;

let rec interval_eq
  a b = (if interval_eq_true a b then Some true
          else (if interval_eq_false a b then Some false else None));;

let rec ivl_min
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (min ord_eint l1 l2, min ord_eint u1 u2));;

let rec ivl_max
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (max ord_eint l1 l2, max ord_eint u1 u2));;

let ivl_special_ops : (ivl, unit) special_ops_ext
  = Special_ops_ext (ivl_min, ivl_max, ());;

let rec interval_tobool
  a = (if interval_eq_false a (Ivl (Fin zero_inta, Fin zero_inta))
        then Some true
        else (if interval_eq_true a (Ivl (Fin zero_inta, Fin zero_inta))
               then Some false else None));;

let rec inv_conservative r a1 a2 = (a1, a2);;

let rec inv_less_ivl
  x0 x1 x2 = match x0, x1, x2 with
    true, Ivl (l1, u1), Ivl (l2, u2) ->
      (inf_ivl (Ivl (l1, u1)) (Ivl (MinInf, minus_eint u2 (Fin one_inta))),
        inf_ivl (Ivl (l2, u2)) (Ivl (plus_eint l1 (Fin one_inta), PlusInf)))
    | false, Ivl (l1, u1), Ivl (l2, u2) ->
        (inf_ivl (Ivl (l1, u1)) (Ivl (l2, PlusInf)),
          inf_ivl (Ivl (l2, u2)) (Ivl (MinInf, u1)));;

let rec inv_eq_ivl
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (inf_ivl a1 a2, inf_ivl a1 a2)
    | false, a1, a2 -> (a1, a2);;

let ivl_refine_ops : (ivl, unit) refine_ops_ext
  = Refine_ops_ext
      (interval_tobool, inv_less_ivl, inv_eq_ivl, inv_conservative,
        inv_conservative, inv_conservative, intersect_ivl, ());;

let rec ivl_of_int n = Ivl (Fin n, Fin n);;

let rec ivl_wrap
  ik uu uv = match ik, uu, uv with
    ik, Fin x, Fin y ->
      (if less_eq_int (minus_inta y x) (minus_inta (ik_max ik) (ik_min ik)) &&
            less_eq_int (ik_norm ik x) (ik_norm ik y)
        then Ivl (Fin (ik_norm ik x), Fin (ik_norm ik y))
        else Ivl (Fin (ik_min ik), Fin (ik_max ik)))
    | ik, MinInf, uv -> Ivl (Fin (ik_min ik), Fin (ik_max ik))
    | ik, PlusInf, uv -> Ivl (Fin (ik_min ik), Fin (ik_max ik))
    | ik, uu, MinInf -> Ivl (Fin (ik_min ik), Fin (ik_max ik))
    | ik, uu, PlusInf -> Ivl (Fin (ik_min ik), Fin (ik_max ik));;

let rec ivl_cast
  ik a =
    (let Ivl (l, u) = a in
      (if not (eint_le l u) then bot_ivla
        else (if eint_le (Fin (ik_min ik)) l && eint_le u (Fin (ik_max ik))
               then a else ivl_wrap ik l u)));;

let rec aval_ivl
  x0 d = match x0, d with N n, d -> ivl_of_int n
    | V x, d -> d x
    | Plus (a, b), d -> plus_ivl (aval_ivl a d) (aval_ivl b d)
    | Minus (a, b), d -> minus_ivl (aval_ivl a d) (aval_ivl b d)
    | Times (a, b), d -> times_ivl (aval_ivl a d) (aval_ivl b d)
    | Div (a, b), d -> ivl_div (aval_ivl a d) (aval_ivl b d)
    | Mod (a, b), d -> ivl_mod (aval_ivl a d) (aval_ivl b d)
    | Less (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (interval_less (aval_ivl a d) (aval_ivl b d)))
    | LessEq (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (map_option not (interval_less (aval_ivl b d) (aval_ivl a d))))
    | Greater (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (interval_less (aval_ivl b d) (aval_ivl a d)))
    | GreaterEq (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (map_option not (interval_less (aval_ivl a d) (aval_ivl b d))))
    | NotEq (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (map_option not (interval_eq (aval_ivl a d) (aval_ivl b d))))
    | Eq (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (interval_eq (aval_ivl a d) (aval_ivl b d)))
    | Not a, d ->
        (if is_empty_ivl (aval_ivl a d) then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (map_option not (interval_tobool (aval_ivl a d))))
    | And (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (bin_log (fun aa ba -> aa && ba) false
                   (interval_tobool (aval_ivl a d))
                   (interval_tobool (aval_ivl b d))))
    | Or (a, b), d ->
        (if is_empty_ivl (aval_ivl a d) || is_empty_ivl (aval_ivl b d)
          then bot_ivla
          else of_bool_option sup_ivl ivl_of_int
                 (bin_log (fun aa ba -> aa || ba) true
                   (interval_tobool (aval_ivl a d))
                   (interval_tobool (aval_ivl b d))))
    | Cast (ik, a), d -> ivl_cast ik (aval_ivl a d);;

let ivl_ops : (ivl, unit) nonrelational_ops_ext
  = Nonrelational_ops_ext
      (aval_ivl, Query_ops_ext (interval_less, interval_eq, ()), ivl_refine_ops,
        ivl_special_ops, ());;

let rec interval_truthy_query
  e d = map_option not
          (q_eq (n_query (bot_ivl, top_ivl) ivl_ops)
            (n_aval (bot_ivl, top_ivl) ivl_ops e d)
            (n_aval (bot_ivl, top_ivl) ivl_ops (N zero_inta) d));;

let rec interval_check_query
  x0 d = match x0, d with Not b, d -> map_option not (interval_check_query b d)
    | And (b1, b2), d ->
        bin_log (fun a b -> a && b) false (interval_check_query b1 d)
          (interval_check_query b2 d)
    | Or (b1, b2), d ->
        bin_log (fun a b -> a || b) true (interval_check_query b1 d)
          (interval_check_query b2 d)
    | Less (a, b), d ->
        q_less (n_query (bot_ivl, top_ivl) ivl_ops)
          (n_aval (bot_ivl, top_ivl) ivl_ops a d)
          (n_aval (bot_ivl, top_ivl) ivl_ops b d)
    | LessEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_ivl, top_ivl) ivl_ops)
            (n_aval (bot_ivl, top_ivl) ivl_ops b d)
            (n_aval (bot_ivl, top_ivl) ivl_ops a d))
    | Greater (a, b), d ->
        q_less (n_query (bot_ivl, top_ivl) ivl_ops)
          (n_aval (bot_ivl, top_ivl) ivl_ops b d)
          (n_aval (bot_ivl, top_ivl) ivl_ops a d)
    | GreaterEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_ivl, top_ivl) ivl_ops)
            (n_aval (bot_ivl, top_ivl) ivl_ops a d)
            (n_aval (bot_ivl, top_ivl) ivl_ops b d))
    | Eq (a, b), d ->
        q_eq (n_query (bot_ivl, top_ivl) ivl_ops)
          (n_aval (bot_ivl, top_ivl) ivl_ops a d)
          (n_aval (bot_ivl, top_ivl) ivl_ops b d)
    | NotEq (a, b), d ->
        map_option not
          (q_eq (n_query (bot_ivl, top_ivl) ivl_ops)
            (n_aval (bot_ivl, top_ivl) ivl_ops a d)
            (n_aval (bot_ivl, top_ivl) ivl_ops b d))
    | N v, d -> interval_truthy_query (N v) d
    | V v, d -> interval_truthy_query (V v) d
    | Plus (v, va), d -> interval_truthy_query (Plus (v, va)) d
    | Minus (v, va), d -> interval_truthy_query (Minus (v, va)) d
    | Times (v, va), d -> interval_truthy_query (Times (v, va)) d
    | Div (v, va), d -> interval_truthy_query (Div (v, va)) d
    | Mod (v, va), d -> interval_truthy_query (Mod (v, va)) d
    | Cast (v, va), d -> interval_truthy_query (Cast (v, va)) d;;

let rec interval_eval_answer
  d (EvalInt e) =
    (if bool_valued e then bool_answer (interval_check_query e d)
      else top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec n_special (_A1, _A2)
  (Nonrelational_ops_ext (n_aval, n_query, n_refine, n_special, more)) =
    n_special;;

let rec n_refine (_A1, _A2)
  (Nonrelational_ops_ext (n_aval, n_query, n_refine, n_special, more)) =
    n_refine;;

let rec special_min
  (Special_ops_ext (special_min, special_max, more)) = special_min;;

let rec special_max
  (Special_ops_ext (special_min, special_max, more)) = special_max;;

let rec r_inv_less
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_inv_less;;

let rec default_st_set_lift _A
  x loc a =
    bind_lift x
      (fun s ->
        (if is_empty _A a then Bot
          else Lifted
                 (default_st_set equal_literal
                   _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                   s loc a)));;

let rec r_inv_times
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_inv_times;;

let rec r_inv_minus
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_inv_minus;;

let rec r_intersect
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_intersect;;

let rec r_inv_plus
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_inv_plus;;

let rec afilter_st_lift_with _A
  ev ops g x3 a x_lift = match ev, ops, g, x3, a, x_lift with
    ev, ops, g, V x, a, x_lift ->
      bind_lift x_lift
        (fun s ->
          default_st_set_lift _A (Lifted s) (location_of g x)
            (r_intersect ops a
              (default_st_to_fun equal_literal
                _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                g s x)))
    | ev, ops, g, Plus (e1, e2), a, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_plus ops a
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, Minus (e1, e2), a, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_minus ops a
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, Times (e1, e2), a, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_times ops a
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, N v, a, x_lift -> x_lift
    | ev, ops, g, Div (v, va), a, x_lift -> x_lift
    | ev, ops, g, Mod (v, va), a, x_lift -> x_lift
    | ev, ops, g, Less (v, va), a, x_lift -> x_lift
    | ev, ops, g, LessEq (v, va), a, x_lift -> x_lift
    | ev, ops, g, Greater (v, va), a, x_lift -> x_lift
    | ev, ops, g, GreaterEq (v, va), a, x_lift -> x_lift
    | ev, ops, g, NotEq (v, va), a, x_lift -> x_lift
    | ev, ops, g, Eq (v, va), a, x_lift -> x_lift
    | ev, ops, g, Not v, a, x_lift -> x_lift
    | ev, ops, g, And (v, va), a, x_lift -> x_lift
    | ev, ops, g, Or (v, va), a, x_lift -> x_lift
    | ev, ops, g, Cast (v, va), a, x_lift -> x_lift;;

let rec r_inv_eq
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_inv_eq;;

let rec r_tobool
  (Refine_ops_ext
    (r_tobool, r_inv_less, r_inv_eq, r_inv_plus, r_inv_minus, r_inv_times,
      r_intersect, more))
    = r_tobool;;

let rec feasible_with _A
  ev ops e pol sigma =
    not (is_empty _A (ev e sigma)) &&
      not (equal_option equal_bool (r_tobool ops (ev e sigma))
            (Some (not pol)));;

let rec bfilter_st_lift_with _A
  ev ops g x3 res x_lift = match ev, ops, g, x3, res, x_lift with
    ev, ops, g, Less (e1, e2), res, x_lift ->
      bind_lift x_lift
        (fun s ->
          (let (a1, a2) =
             r_inv_less ops res
               (ev e1
                 (default_st_to_fun equal_literal
                   _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                   g s))
               (ev e2
                 (default_st_to_fun equal_literal
                   _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                   g s))
             in
            afilter_st_lift_with _A ev ops g e1 a1
              (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, GreaterEq (e1, e2), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_less ops (not res)
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, Greater (e1, e2), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_less ops res
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e2 a1
                (afilter_st_lift_with _A ev ops g e1 a2 (Lifted s))))
    | ev, ops, g, LessEq (e1, e2), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_less ops (not res)
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e2 a1
                (afilter_st_lift_with _A ev ops g e1 a2 (Lifted s))))
    | ev, ops, g, Not b, res, x_lift ->
        bfilter_st_lift_with _A ev ops g b (not res) x_lift
    | ev, ops, g, And (b1, b2), true, x_lift ->
        bfilter_st_lift_with _A ev ops g b1 true
          (bfilter_st_lift_with _A ev ops g b2 true x_lift)
    | ev, ops, g, And (b1, b2), false, x_lift ->
        bind_lift x_lift
          (fun s ->
            sup_lifteda
              (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
                _A.bounded_semilattice_sup_bot_executable_domain)
              (if feasible_with _A ev ops b1 false
                    (default_st_to_fun equal_literal
                      _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                      g s)
                then bfilter_st_lift_with _A ev ops g b1 false (Lifted s)
                else Bot)
              (if feasible_with _A ev ops b2 false
                    (default_st_to_fun equal_literal
                      _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                      g s)
                then bfilter_st_lift_with _A ev ops g b2 false (Lifted s)
                else Bot))
    | ev, ops, g, Or (b1, b2), true, x_lift ->
        bind_lift x_lift
          (fun s ->
            sup_lifteda
              (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
                _A.bounded_semilattice_sup_bot_executable_domain)
              (if feasible_with _A ev ops b1 true
                    (default_st_to_fun equal_literal
                      _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                      g s)
                then bfilter_st_lift_with _A ev ops g b1 true (Lifted s)
                else Bot)
              (if feasible_with _A ev ops b2 true
                    (default_st_to_fun equal_literal
                      _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                      g s)
                then bfilter_st_lift_with _A ev ops g b2 true (Lifted s)
                else Bot))
    | ev, ops, g, Or (b1, b2), false, x_lift ->
        bfilter_st_lift_with _A ev ops g b1 false
          (bfilter_st_lift_with _A ev ops g b2 false x_lift)
    | ev, ops, g, Eq (e1, e2), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_eq ops res
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, NotEq (e1, e2), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, a2) =
               r_inv_eq ops (not res)
                 (ev e1
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev e2
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g e1 a1
                (afilter_st_lift_with _A ev ops g e2 a2 (Lifted s))))
    | ev, ops, g, N v, res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (N v)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (N v) a1 (Lifted s)))
    | ev, ops, g, V v, res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (V v)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (V v) a1 (Lifted s)))
    | ev, ops, g, Plus (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Plus (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Plus (v, va)) a1 (Lifted s)))
    | ev, ops, g, Minus (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Minus (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Minus (v, va)) a1 (Lifted s)))
    | ev, ops, g, Times (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Times (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Times (v, va)) a1 (Lifted s)))
    | ev, ops, g, Div (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Div (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Div (v, va)) a1 (Lifted s)))
    | ev, ops, g, Mod (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Mod (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Mod (v, va)) a1 (Lifted s)))
    | ev, ops, g, Cast (v, va), res, x_lift ->
        bind_lift x_lift
          (fun s ->
            (let (a1, _) =
               r_inv_eq ops (not res)
                 (ev (Cast (v, va))
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
                 (ev (N zero_inta)
                   (default_st_to_fun equal_literal
                     _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                     g s))
               in
              afilter_st_lift_with _A ev ops g (Cast (v, va)) a1 (Lifted s)));;

let rec collapse_lift _A = function Bot -> bot _A
                           | Lifted a -> a;;

let rec branch_st_with _A
  ev ops g e pol s =
    (if feasible_with _A ev ops e pol
          (default_st_to_fun equal_literal
            _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
            g s)
      then collapse_lift
             (bot_gdefault_st
               _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
             (bfilter_st_lift_with _A ev ops g e pol (Lifted s))
      else bot_gdefault_sta
             _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec generic_tf_st_for _A
  ops g x2 s = match ops, g, x2, s with ops, g, EA_Nop, s -> s
    | ops, g, EA_Assign (x, a), s ->
        default_st_set equal_literal
          _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
          s (location_of g x)
          (n_aval
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops a
            (default_st_to_fun equal_literal
              _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              g s))
    | ops, g, EA_Special (sc, x), s ->
        default_st_set equal_literal
          _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
          s (location_of g x)
          (match sc
            with Nondet_Int -> top _A.order_top_executable_domain.top_order_top
            | Min (a, b) ->
              special_min
                (n_special
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops)
                (n_aval
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops a
                  (default_st_to_fun equal_literal
                    _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                    g s))
                (n_aval
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops b
                  (default_st_to_fun equal_literal
                    _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                    g s))
            | Max (a, b) ->
              special_max
                (n_special
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops)
                (n_aval
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops a
                  (default_st_to_fun equal_literal
                    _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                    g s))
                (n_aval
                  (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                    _A.order_top_executable_domain.top_order_top)
                  ops b
                  (default_st_to_fun equal_literal
                    _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                    g s)))
    | ops, g, EA_Assume b, s ->
        branch_st_with _A
          (n_aval
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops)
          (n_refine
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops)
          g b true s
    | ops, g, EA_AssumeNot b, s ->
        branch_st_with _A
          (n_aval
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops)
          (n_refine
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops)
          g b false s
    | ops, g, EA_Body p, s -> s
    | ops, g, EA_Ret (None, p), s -> s
    | ops, g, EA_Ret (Some a, p), s ->
        default_st_set equal_literal
          _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
          s (location_of g ret_var)
          (n_aval
            (_A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
              _A.order_top_executable_domain.top_order_top)
            ops a
            (default_st_to_fun equal_literal
              _A.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              g s))
    | ops, g, EA_Check (l, cnd), s -> s;;

let rec combine_assign_default_st_rep _A _B
  g dst v s =
    (match dst with None -> s
      | Some x -> default_st_rep_set _B _A s (location_of g x) v);;

let rec combine_assign_default_st _A _B
  xc xb xa (Abs_default_st x) =
    Abs_default_st (combine_assign_default_st_rep _A _B xc xb xa x);;

let rec combine_env_st_lifted _A
  dc de =
    (match dc with Bot -> Bot
      | Lifted x ->
        (match de with Bot -> Bot
          | Lifted y ->
            Lifted
              (combine_default_st
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot x y)));;

let rec exec_local_spec _A
  g empty_pred tf_st enter_st =
    make_local_spec
      (fun _ _ ->
        top_fun (top_query_lift (order_int_dom_ext bounded_lattice_unit)))
      (fun _ a -> transfer_lift empty_pred (tf_st a))
      (fun _ ci p -> [(fst p, transfer_lift empty_pred (enter_st ci) (fst p))])
      (fun _ _ _ -> combine_env_st_lifted _A)
      (fun _ ci ->
        transfer_lift2 empty_pred
          (fun env0 de0 ->
            combine_assign_default_st equal_literal
              _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot g
              (ci_dst ci)
              (default_st_get equal_literal
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de0
                (location_of g ret_var))
              env0));;

let rec parity_less_false x = parity_vacuous x;;

let rec parity_less_true x = parity_vacuous x;;

let rec parity_less
  a b = (if parity_less_true a b then Some true
          else (if parity_less_false a b then Some false else None));;

let rec parity_min x0 uu = match x0, uu with PBot, uu -> PBot
                     | PEven, PBot -> PBot
                     | POdd, PBot -> PBot
                     | PTop, PBot -> PBot
                     | PEven, PEven -> PEven
                     | POdd, POdd -> POdd
                     | PEven, POdd -> PTop
                     | PEven, PTop -> PTop
                     | POdd, PEven -> PTop
                     | POdd, PTop -> PTop
                     | PTop, PEven -> PTop
                     | PTop, POdd -> PTop
                     | PTop, PTop -> PTop;;

let rec parity_max x0 uu = match x0, uu with PBot, uu -> PBot
                     | PEven, PBot -> PBot
                     | POdd, PBot -> PBot
                     | PTop, PBot -> PBot
                     | PEven, PEven -> PEven
                     | POdd, POdd -> POdd
                     | PEven, POdd -> PTop
                     | PEven, PTop -> PTop
                     | POdd, PEven -> PTop
                     | POdd, PTop -> PTop
                     | PTop, PEven -> PTop
                     | PTop, POdd -> PTop
                     | PTop, PTop -> PTop;;

let parity_special_ops : (parity, unit) special_ops_ext
  = Special_ops_ext (parity_min, parity_max, ());;

let rec factor_parity = function PBot -> PBot
                        | POdd -> POdd
                        | PEven -> PTop
                        | PTop -> PTop;;

let rec inv_times_parity
  r a b = (inf_parity a (factor_parity r), inf_parity b (factor_parity r));;

let rec inv_minus_parity
  r a b = (inf_parity a (plus_parity r b), inf_parity b (minus_parity a r));;

let rec inv_plus_parity
  r a b = (inf_parity a (minus_parity r b), inf_parity b (minus_parity r a));;

let rec inv_eq_parity
  res a b = (if res then (inf_parity a b, inf_parity a b) else (a, b));;

let rec parity_tobool = function POdd -> Some true
                        | PBot -> None
                        | PEven -> None
                        | PTop -> None;;

let parity_refine_ops : (parity, unit) refine_ops_ext
  = Refine_ops_ext
      (parity_tobool, inv_conservative, inv_eq_parity, inv_plus_parity,
        inv_minus_parity, inv_times_parity, inf_parity, ());;

let rec parity_eq
  a b = (if parity_eq_true a b then Some true
          else (if parity_eq_false a b then Some false else None));;

let rec parity_lt uu uv = None;;

let rec aval_parity
  x0 d = match x0, d with N n, d -> parity_of_int n
    | V v, d -> d v
    | Plus (a, b), d -> plus_parity (aval_parity a d) (aval_parity b d)
    | Minus (a, b), d -> minus_parity (aval_parity a d) (aval_parity b d)
    | Times (a, b), d -> times_parity (aval_parity a d) (aval_parity b d)
    | Div (a, b), d -> parity_div (aval_parity a d) (aval_parity b d)
    | Mod (a, b), d -> parity_mod (aval_parity a d) (aval_parity b d)
    | Less (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (parity_lt (aval_parity a d) (aval_parity b d)))
    | LessEq (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (map_option not
                   (parity_lt (aval_parity b d) (aval_parity a d))))
    | Greater (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (parity_lt (aval_parity b d) (aval_parity a d)))
    | GreaterEq (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (map_option not
                   (parity_lt (aval_parity a d) (aval_parity b d))))
    | NotEq (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (map_option not
                   (parity_eqb (aval_parity a d) (aval_parity b d))))
    | Eq (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (parity_eqb (aval_parity a d) (aval_parity b d)))
    | Not a, d ->
        (if is_empty_parity (aval_parity a d) then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (map_option not (parity_tobool (aval_parity a d))))
    | And (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (bin_log (fun aa ba -> aa && ba) false
                   (parity_tobool (aval_parity a d))
                   (parity_tobool (aval_parity b d))))
    | Or (a, b), d ->
        (if is_empty_parity (aval_parity a d) ||
              is_empty_parity (aval_parity b d)
          then bot_paritya
          else of_bool_option sup_parity parity_of_int
                 (bin_log (fun aa ba -> aa || ba) true
                   (parity_tobool (aval_parity a d))
                   (parity_tobool (aval_parity b d))))
    | Cast (ik, a), d -> aval_parity a d;;

let parity_ops : (parity, unit) nonrelational_ops_ext
  = Nonrelational_ops_ext
      (aval_parity, Query_ops_ext (parity_less, parity_eq, ()),
        parity_refine_ops, parity_special_ops, ());;

let rec parity_truthy_query
  e d = map_option not
          (q_eq (n_query (bot_parity, top_parity) parity_ops)
            (n_aval (bot_parity, top_parity) parity_ops e d)
            (n_aval (bot_parity, top_parity) parity_ops (N zero_inta) d));;

let rec parity_check_query
  x0 d = match x0, d with Not b, d -> map_option not (parity_check_query b d)
    | And (b1, b2), d ->
        bin_log (fun a b -> a && b) false (parity_check_query b1 d)
          (parity_check_query b2 d)
    | Or (b1, b2), d ->
        bin_log (fun a b -> a || b) true (parity_check_query b1 d)
          (parity_check_query b2 d)
    | Less (a, b), d ->
        q_less (n_query (bot_parity, top_parity) parity_ops)
          (n_aval (bot_parity, top_parity) parity_ops a d)
          (n_aval (bot_parity, top_parity) parity_ops b d)
    | LessEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_parity, top_parity) parity_ops)
            (n_aval (bot_parity, top_parity) parity_ops b d)
            (n_aval (bot_parity, top_parity) parity_ops a d))
    | Greater (a, b), d ->
        q_less (n_query (bot_parity, top_parity) parity_ops)
          (n_aval (bot_parity, top_parity) parity_ops b d)
          (n_aval (bot_parity, top_parity) parity_ops a d)
    | GreaterEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_parity, top_parity) parity_ops)
            (n_aval (bot_parity, top_parity) parity_ops a d)
            (n_aval (bot_parity, top_parity) parity_ops b d))
    | Eq (a, b), d ->
        q_eq (n_query (bot_parity, top_parity) parity_ops)
          (n_aval (bot_parity, top_parity) parity_ops a d)
          (n_aval (bot_parity, top_parity) parity_ops b d)
    | NotEq (a, b), d ->
        map_option not
          (q_eq (n_query (bot_parity, top_parity) parity_ops)
            (n_aval (bot_parity, top_parity) parity_ops a d)
            (n_aval (bot_parity, top_parity) parity_ops b d))
    | N v, d -> parity_truthy_query (N v) d
    | V v, d -> parity_truthy_query (V v) d
    | Plus (v, va), d -> parity_truthy_query (Plus (v, va)) d
    | Minus (v, va), d -> parity_truthy_query (Minus (v, va)) d
    | Times (v, va), d -> parity_truthy_query (Times (v, va)) d
    | Div (v, va), d -> parity_truthy_query (Div (v, va)) d
    | Mod (v, va), d -> parity_truthy_query (Mod (v, va)) d
    | Cast (v, va), d -> parity_truthy_query (Cast (v, va)) d;;

let rec parity_eval_answer
  d (EvalInt e) =
    (if bool_valued e then bool_answer (parity_check_query e d)
      else top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec sign_less_true
  a b = equal_signa (fst (inv_less_sign false a b)) SBot ||
          equal_signa (snd (inv_less_sign false a b)) SBot;;

let rec sign_less
  a b = (if sign_less_true a b then Some true
          else (if sign_less_false a b then Some false else None));;

let rec sign_min x0 uu = match x0, uu with SBot, uu -> SBot
                   | SNeg, SBot -> SBot
                   | SNonPos, SBot -> SBot
                   | SZero, SBot -> SBot
                   | SNonNeg, SBot -> SBot
                   | SPos, SBot -> SBot
                   | STop, SBot -> SBot
                   | SNeg, SNeg -> SNeg
                   | SNonPos, SNonPos -> SNonPos
                   | SZero, SZero -> SZero
                   | SNonNeg, SNonNeg -> SNonNeg
                   | SPos, SPos -> SPos
                   | STop, STop -> STop
                   | SNeg, SNonPos -> SNeg
                   | SNonPos, SNeg -> SNeg
                   | SNeg, SZero -> SNeg
                   | SZero, SNeg -> SNeg
                   | SNeg, SNonNeg -> SNeg
                   | SNonNeg, SNeg -> SNeg
                   | SNeg, SPos -> SNeg
                   | SPos, SNeg -> SNeg
                   | SNeg, STop -> SNeg
                   | STop, SNeg -> SNeg
                   | SNonPos, SZero -> SNonPos
                   | SZero, SNonPos -> SNonPos
                   | SNonPos, SNonNeg -> SNonPos
                   | SNonNeg, SNonPos -> SNonPos
                   | SNonPos, SPos -> SNonPos
                   | SPos, SNonPos -> SNonPos
                   | SNonPos, STop -> SNonPos
                   | STop, SNonPos -> SNonPos
                   | SZero, SNonNeg -> SZero
                   | SNonNeg, SZero -> SZero
                   | SZero, SPos -> SZero
                   | SPos, SZero -> SZero
                   | SZero, STop -> SNonPos
                   | STop, SZero -> SNonPos
                   | SNonNeg, SPos -> SNonNeg
                   | SPos, SNonNeg -> SNonNeg
                   | SNonNeg, STop -> STop
                   | STop, SNonNeg -> STop
                   | SPos, STop -> STop
                   | STop, SPos -> STop;;

let rec sign_max x0 uu = match x0, uu with SBot, uu -> SBot
                   | SNeg, SBot -> SBot
                   | SNonPos, SBot -> SBot
                   | SZero, SBot -> SBot
                   | SNonNeg, SBot -> SBot
                   | SPos, SBot -> SBot
                   | STop, SBot -> SBot
                   | SNeg, SNeg -> SNeg
                   | SNonPos, SNonPos -> SNonPos
                   | SZero, SZero -> SZero
                   | SNonNeg, SNonNeg -> SNonNeg
                   | SPos, SPos -> SPos
                   | STop, STop -> STop
                   | SNeg, SNonPos -> SNonPos
                   | SNonPos, SNeg -> SNonPos
                   | SNeg, SZero -> SZero
                   | SZero, SNeg -> SZero
                   | SNeg, SNonNeg -> SNonNeg
                   | SNonNeg, SNeg -> SNonNeg
                   | SNeg, SPos -> SPos
                   | SPos, SNeg -> SPos
                   | SNeg, STop -> STop
                   | STop, SNeg -> STop
                   | SNonPos, SZero -> SZero
                   | SZero, SNonPos -> SZero
                   | SNonPos, SNonNeg -> SNonNeg
                   | SNonNeg, SNonPos -> SNonNeg
                   | SNonPos, SPos -> SPos
                   | SPos, SNonPos -> SPos
                   | SNonPos, STop -> STop
                   | STop, SNonPos -> STop
                   | SZero, SNonNeg -> SNonNeg
                   | SNonNeg, SZero -> SNonNeg
                   | SZero, SPos -> SPos
                   | SPos, SZero -> SPos
                   | SZero, STop -> SNonNeg
                   | STop, SZero -> SNonNeg
                   | SNonNeg, SPos -> SPos
                   | SPos, SNonNeg -> SPos
                   | SNonNeg, STop -> SNonNeg
                   | STop, SNonNeg -> SNonNeg
                   | SPos, STop -> SPos
                   | STop, SPos -> SPos;;

let sign_special_ops : (sign, unit) special_ops_ext
  = Special_ops_ext (sign_min, sign_max, ());;

let rec sign_tobool
  a = (if sign_le a SNeg || sign_le a SPos then Some true
        else (if sign_le a SZero then Some false else None));;

let rec inv_eq_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (inf_sign a1 a2, inf_sign a1 a2)
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a2 SZero && sign_le a1 SNonNeg
                    then inf_sign a1 SPos
                    else (if sign_le a2 SZero && sign_le a1 SNonPos
                           then inf_sign a1 SNeg else a1)))
           in
         let a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a1 SZero && sign_le a2 SNonNeg
                    then inf_sign a2 SPos
                    else (if sign_le a1 SZero && sign_le a2 SNonPos
                           then inf_sign a2 SNeg else a2)))
           in
          (a1a, a));;

let sign_refine_ops : (sign, unit) refine_ops_ext
  = Refine_ops_ext
      (sign_tobool, inv_less_sign, inv_eq_sign, inv_conservative,
        inv_conservative, inv_conservative, inf_sign, ());;

let rec sign_eq
  a b = (if sign_eq_true a b then Some true
          else (if sign_eq_false a b then Some false else None));;

let rec aval_sign
  x0 d = match x0, d with N n, d -> sign_of_int n
    | V x, d -> d x
    | Plus (a, b), d -> plus_sign (aval_sign a d) (aval_sign b d)
    | Minus (a, b), d -> minus_sign (aval_sign a d) (aval_sign b d)
    | Times (a, b), d -> times_sign (aval_sign a d) (aval_sign b d)
    | Div (a, b), d -> sign_div (aval_sign a d) (aval_sign b d)
    | Mod (a, b), d -> sign_mod (aval_sign a d) (aval_sign b d)
    | Less (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (sign_lt (aval_sign a d) (aval_sign b d)))
    | LessEq (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (map_option not (sign_lt (aval_sign b d) (aval_sign a d))))
    | Greater (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (sign_lt (aval_sign b d) (aval_sign a d)))
    | GreaterEq (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (map_option not (sign_lt (aval_sign a d) (aval_sign b d))))
    | NotEq (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (map_option not (sign_eqb (aval_sign a d) (aval_sign b d))))
    | Eq (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (sign_eqb (aval_sign a d) (aval_sign b d)))
    | Not a, d ->
        (if is_empty_sign (aval_sign a d) then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (map_option not (sign_tobool (aval_sign a d))))
    | And (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (bin_log (fun aa ba -> aa && ba) false
                   (sign_tobool (aval_sign a d)) (sign_tobool (aval_sign b d))))
    | Or (a, b), d ->
        (if is_empty_sign (aval_sign a d) || is_empty_sign (aval_sign b d)
          then bot_signa
          else of_bool_option sup_sign sign_of_int
                 (bin_log (fun aa ba -> aa || ba) true
                   (sign_tobool (aval_sign a d)) (sign_tobool (aval_sign b d))))
    | Cast (ik, a), d -> sign_cast ik (aval_sign a d);;

let sign_ops : (sign, unit) nonrelational_ops_ext
  = Nonrelational_ops_ext
      (aval_sign, Query_ops_ext (sign_less, sign_eq, ()), sign_refine_ops,
        sign_special_ops, ());;

let rec sign_truthy_query
  e d = map_option not
          (q_eq (n_query (bot_sign, top_sign) sign_ops)
            (n_aval (bot_sign, top_sign) sign_ops e d)
            (n_aval (bot_sign, top_sign) sign_ops (N zero_inta) d));;

let rec sign_check_query
  x0 d = match x0, d with Not b, d -> map_option not (sign_check_query b d)
    | And (b1, b2), d ->
        bin_log (fun a b -> a && b) false (sign_check_query b1 d)
          (sign_check_query b2 d)
    | Or (b1, b2), d ->
        bin_log (fun a b -> a || b) true (sign_check_query b1 d)
          (sign_check_query b2 d)
    | Less (a, b), d ->
        q_less (n_query (bot_sign, top_sign) sign_ops)
          (n_aval (bot_sign, top_sign) sign_ops a d)
          (n_aval (bot_sign, top_sign) sign_ops b d)
    | LessEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_sign, top_sign) sign_ops)
            (n_aval (bot_sign, top_sign) sign_ops b d)
            (n_aval (bot_sign, top_sign) sign_ops a d))
    | Greater (a, b), d ->
        q_less (n_query (bot_sign, top_sign) sign_ops)
          (n_aval (bot_sign, top_sign) sign_ops b d)
          (n_aval (bot_sign, top_sign) sign_ops a d)
    | GreaterEq (a, b), d ->
        map_option not
          (q_less (n_query (bot_sign, top_sign) sign_ops)
            (n_aval (bot_sign, top_sign) sign_ops a d)
            (n_aval (bot_sign, top_sign) sign_ops b d))
    | Eq (a, b), d ->
        q_eq (n_query (bot_sign, top_sign) sign_ops)
          (n_aval (bot_sign, top_sign) sign_ops a d)
          (n_aval (bot_sign, top_sign) sign_ops b d)
    | NotEq (a, b), d ->
        map_option not
          (q_eq (n_query (bot_sign, top_sign) sign_ops)
            (n_aval (bot_sign, top_sign) sign_ops a d)
            (n_aval (bot_sign, top_sign) sign_ops b d))
    | N v, d -> sign_truthy_query (N v) d
    | V v, d -> sign_truthy_query (V v) d
    | Plus (v, va), d -> sign_truthy_query (Plus (v, va)) d
    | Minus (v, va), d -> sign_truthy_query (Minus (v, va)) d
    | Times (v, va), d -> sign_truthy_query (Times (v, va)) d
    | Div (v, va), d -> sign_truthy_query (Div (v, va)) d
    | Mod (v, va), d -> sign_truthy_query (Mod (v, va)) d
    | Cast (v, va), d -> sign_truthy_query (Cast (v, va)) d;;

let rec sign_eval_answer
  d (EvalInt e) =
    (if bool_valued e then bool_answer (sign_check_query e d)
      else top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec apply_reduction_steps
  x0 d = match x0, d with [], d -> d
    | step :: steps, d -> apply_reduction_steps steps (step d);;

let rec refine_congruence_with_congruence fct c = fct;;

let rec parity_fact_of_congruence_rep
  = function None -> PBot
    | Some (c, m) ->
        (if equal_inta m zero_inta ||
              dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2))
                m
          then (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) c
                 then PEven else POdd)
          else PTop);;

let rec parity_fact_of_congruence
  fct = parity_fact_of_congruence_rep (rep_congruence fct);;

let rec refine_parity_with_congruence
  fct p = inf_parity (parity_fact_of_congruence fct) p;;

let rec congruence_fact_of_congruence c = c;;

let rec congruence_fact_of_int_dom
  d = restrict_congruence_by_parity (int_parity d)
        (congruence_fact_of_congruence (int_congruence d));;

let rec refine_congruence
  d = (let fct = congruence_fact_of_int_dom d in
        int_congruence_update
          (fun _ -> refine_congruence_with_congruence fct (int_congruence d))
          (int_parity_update
            (fun _ -> refine_parity_with_congruence fct (int_parity d))
            (int_ivl_update
              (fun _ -> refine_ivl_with_congruence fct (int_ivl d)) d)));;

let rec interval_parity_fact
  i = (if is_bottom_ivl i then PBot
        else (match i with Ivl (MinInf, _) -> PTop | Ivl (Fin _, MinInf) -> PTop
               | Ivl (Fin l, Fin u) ->
                 (if equal_inta l u
                   then (if dvd (equal_int, semidom_modulo_int)
                              (Int_of_integer (Z.of_int 2)) l
                          then PEven else POdd)
                   else PTop)
               | Ivl (Fin _, PlusInf) -> PTop | Ivl (PlusInf, _) -> PTop));;

let rec refine_parity_with_interval
  fct p = inf_parity (interval_parity_fact fct) p;;

let rec interval_sign_fact
  i = (if is_bottom_ivl i then SBot
        else (let Ivl (l, u) = i in
               (if less_eint u (Fin zero_inta) then SNeg
                 else (if equal_eint u (Fin zero_inta)
                        then (if equal_eint l (Fin zero_inta) then SZero
                               else SNonPos)
                        else (if less_eint (Fin zero_inta) l then SPos
                               else (if equal_eint l (Fin zero_inta)
                                      then SNonNeg else STop))))));;

let rec refine_sign_with_interval fct s = inf_sign (interval_sign_fact fct) s;;

let rec refine_ivl_with_interval fct i = intersect_ivl fct i;;

let rec interval_fact_of_ivl i = i;;

let rec interval_fact_of_int_dom
  d = intersect_ivl (interval_fact_of_sign (int_sign d))
        (interval_fact_of_ivl (int_ivl d));;

let rec refine_interval
  d = (let fct = interval_fact_of_int_dom d in
        int_parity_update
          (fun _ -> refine_parity_with_interval fct (int_parity d))
          (int_ivl_update (fun _ -> refine_ivl_with_interval fct (int_ivl d))
            (int_sign_update
              (fun _ -> refine_sign_with_interval fct (int_sign d)) d)));;

let refinement_steps : (unit int_dom_ext -> unit int_dom_ext) list
  = [refine_interval; refine_congruence];;

let rec refine_round x = apply_reduction_steps refinement_steps x;;

let rec canonical_refine_step
  d = (let da = refine_round d in
        (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) da
          then bot_int_dom_exta bounded_lattice_unit else da));;

let rec while_option b c s = (if b s then while_option b c (c s) else Some s);;

let rec refine_fix_option
  d = while_option
        (fun x ->
          not (equal_int_dom_exta equal_unit (canonical_refine_step x) x))
        canonical_refine_step d;;

let rec refine_fix
  d = (match refine_fix_option d with None -> d | Some r -> r);;

let rec refine
  mode d =
    (match mode with Refine_Never -> d | Refine_Once -> refine_round d
      | Refine_Fixpoint -> refine_fix d);;

let rec int_dom_min_raw
  a b = int_parity_update (fun _ -> parity_min (int_parity a) (int_parity b))
          (int_ivl_update (fun _ -> ivl_min (int_ivl a) (int_ivl b))
            (int_sign_update (fun _ -> sign_min (int_sign a) (int_sign b))
              (top_int_dom_exta bounded_lattice_unit)));;

let rec int_dom_min mode a b = refine mode (int_dom_min_raw a b);;

let rec int_dom_max_raw
  a b = int_parity_update (fun _ -> parity_max (int_parity a) (int_parity b))
          (int_ivl_update (fun _ -> ivl_max (int_ivl a) (int_ivl b))
            (int_sign_update (fun _ -> sign_max (int_sign a) (int_sign b))
              (top_int_dom_exta bounded_lattice_unit)));;

let rec int_dom_max mode a b = refine mode (int_dom_max_raw a b);;

let rec int_dom_special_ops
  mode = Special_ops_ext (int_dom_min mode, int_dom_max mode, ());;

let rec intersect_int_dom
  d1 d2 =
    int_congruence_update
      (fun _ -> inf_congruence (int_congruence d1) (int_congruence d2))
      (int_parity_update (fun _ -> inf_parity (int_parity d1) (int_parity d2))
        (int_ivl_update (fun _ -> intersect_ivl (int_ivl d1) (int_ivl d2))
          (int_sign_update (fun _ -> inf_sign (int_sign d1) (int_sign d2))
            d1)));;

let rec intersect_int_dom_mode mode a b = refine mode (intersect_int_dom a b);;

let rec inv_times_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_times_parity (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_times_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_times_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_times_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let rec inv_minus_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_minus_parity (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_minus_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_minus_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_minus_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let rec inv_plus_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_plus_parity (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_plus_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_plus_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_plus_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let rec inv_less_int_dom_raw
  res d1 d2 =
    (let (s1, s2) = inv_less_sign res (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_less_ivl res (int_ivl d1) (int_ivl d2) in
     let (c1, c2) =
       inv_less_congruence res (int_congruence d1) (int_congruence d2) in
      (int_congruence_update (fun _ -> c1)
         (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1)),
        int_congruence_update (fun _ -> c2)
          (int_ivl_update (fun _ -> i2) (int_sign_update (fun _ -> s2) d2))));;

let rec inv_less_int_dom
  mode res d1 d2 =
    (let (r1, r2) = inv_less_int_dom_raw res d1 d2 in
      (refine mode r1, refine mode r2));;

let rec first_deciding
  xa0 x = match xa0, x with [], x -> None
    | q :: qs, x ->
        (match q x with None -> first_deciding qs x | Some a -> Some a);;

let rec int_dom_tobool
  d = first_deciding
        [(fun a -> interval_tobool (int_ivl a));
          (fun a -> sign_tobool (int_sign a));
          (fun a -> parity_tobool (int_parity a));
          (fun a -> congruence_tobool (int_congruence a))]
        d;;

let rec inv_eq_int_dom_raw
  res d1 d2 =
    (if res then (intersect_int_dom d1 d2, intersect_int_dom d1 d2)
      else (let (s1, s2) = inv_eq_sign false (int_sign d1) (int_sign d2) in
            let (i1, i2) = inv_eq_ivl false (int_ivl d1) (int_ivl d2) in
            let (c1, c2) =
              inv_eq_congruence false (int_congruence d1) (int_congruence d2) in
             (int_congruence_update (fun _ -> c1)
                (int_ivl_update (fun _ -> i1)
                  (int_sign_update (fun _ -> s1) d1)),
               int_congruence_update (fun _ -> c2)
                 (int_ivl_update (fun _ -> i2)
                   (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_eq_int_dom
  mode res d1 d2 =
    (let (r1, r2) = inv_eq_int_dom_raw res d1 d2 in
      (refine mode r1, refine mode r2));;

let rec int_refine_ops
  mode =
    Refine_ops_ext
      (int_dom_tobool, inv_less_int_dom mode, inv_eq_int_dom mode,
        inv_plus_int_dom mode, inv_minus_int_dom mode, inv_times_int_dom mode,
        intersect_int_dom_mode mode, ());;

let rec times_int_dom_raw
  a b = int_congruence_update
          (fun _ -> times_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> times_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> times_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> times_sign (int_sign a) (int_sign b))
                (top_int_dom_exta bounded_lattice_unit))));;

let rec times_int_dom mode a b = refine mode (times_int_dom_raw a b);;

let rec minus_int_dom_raw
  a b = int_congruence_update
          (fun _ -> minus_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> minus_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> minus_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> minus_sign (int_sign a) (int_sign b))
                (top_int_dom_exta bounded_lattice_unit))));;

let rec minus_int_dom mode a b = refine mode (minus_int_dom_raw a b);;

let rec plus_int_dom_raw
  a b = int_congruence_update
          (fun _ -> plus_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> plus_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> plus_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> plus_sign (int_sign a) (int_sign b))
                (top_int_dom_exta bounded_lattice_unit))));;

let rec plus_int_dom mode a b = refine mode (plus_int_dom_raw a b);;

let rec cast_int_dom_raw
  ik a =
    int_congruence_update (fun _ -> congruence_cast ik (int_congruence a))
      (int_parity_update (fun _ -> int_parity a)
        (int_ivl_update (fun _ -> ivl_cast ik (int_ivl a))
          (int_sign_update (fun _ -> sign_cast ik (int_sign a))
            (top_int_dom_exta bounded_lattice_unit))));;

let rec cast_int_dom mode ik a = refine mode (cast_int_dom_raw ik a);;

let rec mod_int_dom_raw
  a b = int_congruence_update
          (fun _ -> congruence_mod (int_congruence a) (int_congruence b))
          (int_parity_update (fun _ -> parity_mod (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> ivl_mod (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> sign_mod (int_sign a) (int_sign b))
                (top_int_dom_exta bounded_lattice_unit))));;

let rec mod_int_dom mode a b = refine mode (mod_int_dom_raw a b);;

let rec first_deciding2
  xa0 x y = match xa0, x, y with [], x, y -> None
    | q :: qs, x, y ->
        (match q x y with None -> first_deciding2 qs x y | Some a -> Some a);;

let rec int_dom_eqb
  d1 d2 =
    first_deciding2
      [(fun a b -> interval_eq (int_ivl a) (int_ivl b));
        (fun a b -> sign_eqb (int_sign a) (int_sign b));
        (fun a b -> parity_eqb (int_parity a) (int_parity b));
        (fun a b -> congruence_eqb (int_congruence a) (int_congruence b))]
      d1 d2;;

let rec div_int_dom_raw
  a b = int_congruence_update
          (fun _ -> congruence_div (int_congruence a) (int_congruence b))
          (int_parity_update (fun _ -> parity_div (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> ivl_div (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> sign_div (int_sign a) (int_sign b))
                (top_int_dom_exta bounded_lattice_unit))));;

let rec div_int_dom mode a b = refine mode (div_int_dom_raw a b);;

let rec int_dom_lt
  d1 d2 =
    first_deciding2
      [(fun a b -> interval_less (int_ivl a) (int_ivl b));
        (fun a b -> sign_lt (int_sign a) (int_sign b));
        (fun a b -> parity_lt (int_parity a) (int_parity b));
        (fun a b -> congruence_lt (int_congruence a) (int_congruence b))]
      d1 d2;;

let rec aval_int_dom
  mode x1 sigma = match mode, x1, sigma with
    mode, N n, sigma -> int_dom_of_int n
    | mode, V x, sigma -> sigma x
    | mode, Plus (e1, e2), sigma ->
        plus_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Minus (e1, e2), sigma ->
        minus_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Times (e1, e2), sigma ->
        times_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Div (e1, e2), sigma ->
        div_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Mod (e1, e2), sigma ->
        mod_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Less (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (int_dom_lt a b)))
    | mode, LessEq (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (map_option not (int_dom_lt b a))))
    | mode, Greater (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (int_dom_lt b a)))
    | mode, GreaterEq (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (map_option not (int_dom_lt a b))))
    | mode, NotEq (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (map_option not (int_dom_eqb a b))))
    | mode, Eq (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (int_dom_eqb a b)))
    | mode, Not e, sigma ->
        (let a = aval_int_dom mode e sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int (map_option not (int_dom_tobool a))))
    | mode, And (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int
                   (bin_log (fun aa ba -> aa && ba) false (int_dom_tobool a)
                     (int_dom_tobool b))))
    | mode, Or (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) a ||
                is_empty_int_dom_ext (bounded_lattice_unit, warrowing_unit) b
            then bot_int_dom_exta bounded_lattice_unit
            else of_bool_option (sup_int_dom_ext bounded_lattice_unit)
                   int_dom_of_int
                   (bin_log (fun aa ba -> aa || ba) true (int_dom_tobool a)
                     (int_dom_tobool b))))
    | mode, Cast (ik, e), sigma ->
        cast_int_dom mode ik (aval_int_dom mode e sigma);;

let rec int_less_false
  a b = sign_less_false (int_sign a) (int_sign b) ||
          (interval_less_false (int_ivl a) (int_ivl b) ||
            (parity_less_false (int_parity a) (int_parity b) ||
              equal_option equal_bool
                (congruence_lt (int_congruence a) (int_congruence b))
                (Some false)));;

let rec int_less_true
  a b = sign_less_true (int_sign a) (int_sign b) ||
          (interval_less_true (int_ivl a) (int_ivl b) ||
            (parity_less_true (int_parity a) (int_parity b) ||
              equal_option equal_bool
                (congruence_lt (int_congruence a) (int_congruence b))
                (Some true)));;

let rec int_less
  a b = (if int_less_true a b then Some true
          else (if int_less_false a b then Some false else None));;

let rec int_dom_ops
  mode =
    Nonrelational_ops_ext
      (aval_int_dom mode, Query_ops_ext (int_less, int_eq, ()),
        int_refine_ops mode, int_dom_special_ops mode, ());;

let rec int_truthy_query
  mode e d =
    map_option not
      (q_eq (n_query
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode))
        (n_aval
          ((bot_int_dom_ext bounded_lattice_unit),
            (top_int_dom_ext bounded_lattice_unit))
          (int_dom_ops mode) e d)
        (n_aval
          ((bot_int_dom_ext bounded_lattice_unit),
            (top_int_dom_ext bounded_lattice_unit))
          (int_dom_ops mode) (N zero_inta) d));;

let rec int_check_query
  mode x1 d = match mode, x1, d with
    mode, Not b, d -> map_option not (int_check_query mode b d)
    | mode, And (b1, b2), d ->
        bin_log (fun a b -> a && b) false (int_check_query mode b1 d)
          (int_check_query mode b2 d)
    | mode, Or (b1, b2), d ->
        bin_log (fun a b -> a || b) true (int_check_query mode b1 d)
          (int_check_query mode b2 d)
    | mode, Less (a, b), d ->
        q_less
          (n_query
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode))
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) a d)
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) b d)
    | mode, LessEq (a, b), d ->
        map_option not
          (q_less
            (n_query
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode))
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) b d)
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) a d))
    | mode, Greater (a, b), d ->
        q_less
          (n_query
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode))
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) b d)
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) a d)
    | mode, GreaterEq (a, b), d ->
        map_option not
          (q_less
            (n_query
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode))
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) a d)
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) b d))
    | mode, Eq (a, b), d ->
        q_eq (n_query
               ((bot_int_dom_ext bounded_lattice_unit),
                 (top_int_dom_ext bounded_lattice_unit))
               (int_dom_ops mode))
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) a d)
          (n_aval
            ((bot_int_dom_ext bounded_lattice_unit),
              (top_int_dom_ext bounded_lattice_unit))
            (int_dom_ops mode) b d)
    | mode, NotEq (a, b), d ->
        map_option not
          (q_eq (n_query
                  ((bot_int_dom_ext bounded_lattice_unit),
                    (top_int_dom_ext bounded_lattice_unit))
                  (int_dom_ops mode))
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) a d)
            (n_aval
              ((bot_int_dom_ext bounded_lattice_unit),
                (top_int_dom_ext bounded_lattice_unit))
              (int_dom_ops mode) b d))
    | mode, N v, d -> int_truthy_query mode (N v) d
    | mode, V v, d -> int_truthy_query mode (V v) d
    | mode, Plus (v, va), d -> int_truthy_query mode (Plus (v, va)) d
    | mode, Minus (v, va), d -> int_truthy_query mode (Minus (v, va)) d
    | mode, Times (v, va), d -> int_truthy_query mode (Times (v, va)) d
    | mode, Div (v, va), d -> int_truthy_query mode (Div (v, va)) d
    | mode, Mod (v, va), d -> int_truthy_query mode (Mod (v, va)) d
    | mode, Cast (v, va), d -> int_truthy_query mode (Cast (v, va)) d;;

let rec int_eval_answer
  mode d (EvalInt e) =
    (if bool_valued e then bool_answer (int_check_query mode e d)
      else top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec order_pairs
  d = (match d with RelBot -> None
        | RelC ps ->
          Some (sorted_list_of_set
                 ((equal_prod equal_literal equal_literal),
                   (linorder_prod linorder_literal linorder_literal))
                 ps));;

let rec ls_assign_update
  ls_assigna
    (Glocal_spec_ext
      (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
        ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = Glocal_spec_ext
        (ls_query, ls_skip, ls_assigna ls_assign, ls_special, ls_branch,
          ls_body, ls_return, ls_event, ls_enter, ls_combine_env,
          ls_combine_assign, more);;

let rec answer_const = function QLifted d -> int_dom_constant d
                       | QBot -> None
                       | QTop -> None;;

let rec assign_ask
  asn ch x e d =
    (match answer_const (ch (EvalInt e)) with None -> asn ch x e d
      | Some n -> asn ch x (N n) d);;

let rec ask_assign c = ls_assign_update (fun _ -> assign_ask (ls_assign c)) c;;

let rec ls_branch_update
  ls_brancha
    (Glocal_spec_ext
      (ls_query, ls_skip, ls_assign, ls_special, ls_branch, ls_body, ls_return,
        ls_event, ls_enter, ls_combine_env, ls_combine_assign, more))
    = Glocal_spec_ext
        (ls_query, ls_skip, ls_assign, ls_special, ls_brancha ls_branch,
          ls_body, ls_return, ls_event, ls_enter, ls_combine_env,
          ls_combine_assign, more);;

let top_relc : relc = RelC bot_set;;

let rec assume_not_step
  b d = (match d with RelBot -> RelBot
          | RelC ps ->
            (match b with N _ -> RelC ps | V _ -> RelC ps
              | Plus (_, _) -> RelC ps | Minus (_, _) -> RelC ps
              | Times (_, _) -> RelC ps | Div (_, _) -> RelC ps
              | Mod (_, _) -> RelC ps | Less (N _, _) -> RelC ps
              | Less (V _, N _) -> RelC ps
              | Less (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (y, x)
                       ps)
              | Less (V _, Plus (_, _)) -> RelC ps
              | Less (V _, Minus (_, _)) -> RelC ps
              | Less (V _, Times (_, _)) -> RelC ps
              | Less (V _, Div (_, _)) -> RelC ps
              | Less (V _, Mod (_, _)) -> RelC ps
              | Less (V _, Less (_, _)) -> RelC ps
              | Less (V _, LessEq (_, _)) -> RelC ps
              | Less (V _, Greater (_, _)) -> RelC ps
              | Less (V _, GreaterEq (_, _)) -> RelC ps
              | Less (V _, NotEq (_, _)) -> RelC ps
              | Less (V _, Eq (_, _)) -> RelC ps | Less (V _, Not _) -> RelC ps
              | Less (V _, And (_, _)) -> RelC ps
              | Less (V _, Or (_, _)) -> RelC ps
              | Less (V _, Cast (_, _)) -> RelC ps
              | Less (Plus (_, _), _) -> RelC ps
              | Less (Minus (_, _), _) -> RelC ps
              | Less (Times (_, _), _) -> RelC ps
              | Less (Div (_, _), _) -> RelC ps
              | Less (Mod (_, _), _) -> RelC ps
              | Less (Less (_, _), _) -> RelC ps
              | Less (LessEq (_, _), _) -> RelC ps
              | Less (Greater (_, _), _) -> RelC ps
              | Less (GreaterEq (_, _), _) -> RelC ps
              | Less (NotEq (_, _), _) -> RelC ps
              | Less (Eq (_, _), _) -> RelC ps | Less (Not _, _) -> RelC ps
              | Less (And (_, _), _) -> RelC ps | Less (Or (_, _), _) -> RelC ps
              | Less (Cast (_, _), _) -> RelC ps | LessEq (N _, _) -> RelC ps
              | LessEq (V _, N _) -> RelC ps
              | LessEq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (y, x)
                       ps)
              | LessEq (V _, Plus (_, _)) -> RelC ps
              | LessEq (V _, Minus (_, _)) -> RelC ps
              | LessEq (V _, Times (_, _)) -> RelC ps
              | LessEq (V _, Div (_, _)) -> RelC ps
              | LessEq (V _, Mod (_, _)) -> RelC ps
              | LessEq (V _, Less (_, _)) -> RelC ps
              | LessEq (V _, LessEq (_, _)) -> RelC ps
              | LessEq (V _, Greater (_, _)) -> RelC ps
              | LessEq (V _, GreaterEq (_, _)) -> RelC ps
              | LessEq (V _, NotEq (_, _)) -> RelC ps
              | LessEq (V _, Eq (_, _)) -> RelC ps
              | LessEq (V _, Not _) -> RelC ps
              | LessEq (V _, And (_, _)) -> RelC ps
              | LessEq (V _, Or (_, _)) -> RelC ps
              | LessEq (V _, Cast (_, _)) -> RelC ps
              | LessEq (Plus (_, _), _) -> RelC ps
              | LessEq (Minus (_, _), _) -> RelC ps
              | LessEq (Times (_, _), _) -> RelC ps
              | LessEq (Div (_, _), _) -> RelC ps
              | LessEq (Mod (_, _), _) -> RelC ps
              | LessEq (Less (_, _), _) -> RelC ps
              | LessEq (LessEq (_, _), _) -> RelC ps
              | LessEq (Greater (_, _), _) -> RelC ps
              | LessEq (GreaterEq (_, _), _) -> RelC ps
              | LessEq (NotEq (_, _), _) -> RelC ps
              | LessEq (Eq (_, _), _) -> RelC ps | LessEq (Not _, _) -> RelC ps
              | LessEq (And (_, _), _) -> RelC ps
              | LessEq (Or (_, _), _) -> RelC ps
              | LessEq (Cast (_, _), _) -> RelC ps | Greater (N _, _) -> RelC ps
              | Greater (V _, N _) -> RelC ps
              | Greater (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       ps)
              | Greater (V _, Plus (_, _)) -> RelC ps
              | Greater (V _, Minus (_, _)) -> RelC ps
              | Greater (V _, Times (_, _)) -> RelC ps
              | Greater (V _, Div (_, _)) -> RelC ps
              | Greater (V _, Mod (_, _)) -> RelC ps
              | Greater (V _, Less (_, _)) -> RelC ps
              | Greater (V _, LessEq (_, _)) -> RelC ps
              | Greater (V _, Greater (_, _)) -> RelC ps
              | Greater (V _, GreaterEq (_, _)) -> RelC ps
              | Greater (V _, NotEq (_, _)) -> RelC ps
              | Greater (V _, Eq (_, _)) -> RelC ps
              | Greater (V _, Not _) -> RelC ps
              | Greater (V _, And (_, _)) -> RelC ps
              | Greater (V _, Or (_, _)) -> RelC ps
              | Greater (V _, Cast (_, _)) -> RelC ps
              | Greater (Plus (_, _), _) -> RelC ps
              | Greater (Minus (_, _), _) -> RelC ps
              | Greater (Times (_, _), _) -> RelC ps
              | Greater (Div (_, _), _) -> RelC ps
              | Greater (Mod (_, _), _) -> RelC ps
              | Greater (Less (_, _), _) -> RelC ps
              | Greater (LessEq (_, _), _) -> RelC ps
              | Greater (Greater (_, _), _) -> RelC ps
              | Greater (GreaterEq (_, _), _) -> RelC ps
              | Greater (NotEq (_, _), _) -> RelC ps
              | Greater (Eq (_, _), _) -> RelC ps
              | Greater (Not _, _) -> RelC ps
              | Greater (And (_, _), _) -> RelC ps
              | Greater (Or (_, _), _) -> RelC ps
              | Greater (Cast (_, _), _) -> RelC ps
              | GreaterEq (N _, _) -> RelC ps | GreaterEq (V _, N _) -> RelC ps
              | GreaterEq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       ps)
              | GreaterEq (V _, Plus (_, _)) -> RelC ps
              | GreaterEq (V _, Minus (_, _)) -> RelC ps
              | GreaterEq (V _, Times (_, _)) -> RelC ps
              | GreaterEq (V _, Div (_, _)) -> RelC ps
              | GreaterEq (V _, Mod (_, _)) -> RelC ps
              | GreaterEq (V _, Less (_, _)) -> RelC ps
              | GreaterEq (V _, LessEq (_, _)) -> RelC ps
              | GreaterEq (V _, Greater (_, _)) -> RelC ps
              | GreaterEq (V _, GreaterEq (_, _)) -> RelC ps
              | GreaterEq (V _, NotEq (_, _)) -> RelC ps
              | GreaterEq (V _, Eq (_, _)) -> RelC ps
              | GreaterEq (V _, Not _) -> RelC ps
              | GreaterEq (V _, And (_, _)) -> RelC ps
              | GreaterEq (V _, Or (_, _)) -> RelC ps
              | GreaterEq (V _, Cast (_, _)) -> RelC ps
              | GreaterEq (Plus (_, _), _) -> RelC ps
              | GreaterEq (Minus (_, _), _) -> RelC ps
              | GreaterEq (Times (_, _), _) -> RelC ps
              | GreaterEq (Div (_, _), _) -> RelC ps
              | GreaterEq (Mod (_, _), _) -> RelC ps
              | GreaterEq (Less (_, _), _) -> RelC ps
              | GreaterEq (LessEq (_, _), _) -> RelC ps
              | GreaterEq (Greater (_, _), _) -> RelC ps
              | GreaterEq (GreaterEq (_, _), _) -> RelC ps
              | GreaterEq (NotEq (_, _), _) -> RelC ps
              | GreaterEq (Eq (_, _), _) -> RelC ps
              | GreaterEq (Not _, _) -> RelC ps
              | GreaterEq (And (_, _), _) -> RelC ps
              | GreaterEq (Or (_, _), _) -> RelC ps
              | GreaterEq (Cast (_, _), _) -> RelC ps
              | NotEq (N _, _) -> RelC ps | NotEq (V _, N _) -> RelC ps
              | NotEq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       (inserta (equal_prod equal_literal equal_literal) (y, x)
                         ps))
              | NotEq (V _, Plus (_, _)) -> RelC ps
              | NotEq (V _, Minus (_, _)) -> RelC ps
              | NotEq (V _, Times (_, _)) -> RelC ps
              | NotEq (V _, Div (_, _)) -> RelC ps
              | NotEq (V _, Mod (_, _)) -> RelC ps
              | NotEq (V _, Less (_, _)) -> RelC ps
              | NotEq (V _, LessEq (_, _)) -> RelC ps
              | NotEq (V _, Greater (_, _)) -> RelC ps
              | NotEq (V _, GreaterEq (_, _)) -> RelC ps
              | NotEq (V _, NotEq (_, _)) -> RelC ps
              | NotEq (V _, Eq (_, _)) -> RelC ps
              | NotEq (V _, Not _) -> RelC ps
              | NotEq (V _, And (_, _)) -> RelC ps
              | NotEq (V _, Or (_, _)) -> RelC ps
              | NotEq (V _, Cast (_, _)) -> RelC ps
              | NotEq (Plus (_, _), _) -> RelC ps
              | NotEq (Minus (_, _), _) -> RelC ps
              | NotEq (Times (_, _), _) -> RelC ps
              | NotEq (Div (_, _), _) -> RelC ps
              | NotEq (Mod (_, _), _) -> RelC ps
              | NotEq (Less (_, _), _) -> RelC ps
              | NotEq (LessEq (_, _), _) -> RelC ps
              | NotEq (Greater (_, _), _) -> RelC ps
              | NotEq (GreaterEq (_, _), _) -> RelC ps
              | NotEq (NotEq (_, _), _) -> RelC ps
              | NotEq (Eq (_, _), _) -> RelC ps | NotEq (Not _, _) -> RelC ps
              | NotEq (And (_, _), _) -> RelC ps
              | NotEq (Or (_, _), _) -> RelC ps
              | NotEq (Cast (_, _), _) -> RelC ps | Eq (_, _) -> RelC ps
              | Not _ -> RelC ps | And (_, _) -> RelC ps | Or (_, _) -> RelC ps
              | Cast (_, _) -> RelC ps));;

let rec assume_step
  b d = (match d with RelBot -> RelBot
          | RelC ps ->
            (match b with N _ -> RelC ps | V _ -> RelC ps
              | Plus (_, _) -> RelC ps | Minus (_, _) -> RelC ps
              | Times (_, _) -> RelC ps | Div (_, _) -> RelC ps
              | Mod (_, _) -> RelC ps | Less (N _, _) -> RelC ps
              | Less (V _, N _) -> RelC ps
              | Less (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       ps)
              | Less (V _, Plus (_, _)) -> RelC ps
              | Less (V _, Minus (_, _)) -> RelC ps
              | Less (V _, Times (_, _)) -> RelC ps
              | Less (V _, Div (_, _)) -> RelC ps
              | Less (V _, Mod (_, _)) -> RelC ps
              | Less (V _, Less (_, _)) -> RelC ps
              | Less (V _, LessEq (_, _)) -> RelC ps
              | Less (V _, Greater (_, _)) -> RelC ps
              | Less (V _, GreaterEq (_, _)) -> RelC ps
              | Less (V _, NotEq (_, _)) -> RelC ps
              | Less (V _, Eq (_, _)) -> RelC ps | Less (V _, Not _) -> RelC ps
              | Less (V _, And (_, _)) -> RelC ps
              | Less (V _, Or (_, _)) -> RelC ps
              | Less (V _, Cast (_, _)) -> RelC ps
              | Less (Plus (_, _), _) -> RelC ps
              | Less (Minus (_, _), _) -> RelC ps
              | Less (Times (_, _), _) -> RelC ps
              | Less (Div (_, _), _) -> RelC ps
              | Less (Mod (_, _), _) -> RelC ps
              | Less (Less (_, _), _) -> RelC ps
              | Less (LessEq (_, _), _) -> RelC ps
              | Less (Greater (_, _), _) -> RelC ps
              | Less (GreaterEq (_, _), _) -> RelC ps
              | Less (NotEq (_, _), _) -> RelC ps
              | Less (Eq (_, _), _) -> RelC ps | Less (Not _, _) -> RelC ps
              | Less (And (_, _), _) -> RelC ps | Less (Or (_, _), _) -> RelC ps
              | Less (Cast (_, _), _) -> RelC ps | LessEq (N _, _) -> RelC ps
              | LessEq (V _, N _) -> RelC ps
              | LessEq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       ps)
              | LessEq (V _, Plus (_, _)) -> RelC ps
              | LessEq (V _, Minus (_, _)) -> RelC ps
              | LessEq (V _, Times (_, _)) -> RelC ps
              | LessEq (V _, Div (_, _)) -> RelC ps
              | LessEq (V _, Mod (_, _)) -> RelC ps
              | LessEq (V _, Less (_, _)) -> RelC ps
              | LessEq (V _, LessEq (_, _)) -> RelC ps
              | LessEq (V _, Greater (_, _)) -> RelC ps
              | LessEq (V _, GreaterEq (_, _)) -> RelC ps
              | LessEq (V _, NotEq (_, _)) -> RelC ps
              | LessEq (V _, Eq (_, _)) -> RelC ps
              | LessEq (V _, Not _) -> RelC ps
              | LessEq (V _, And (_, _)) -> RelC ps
              | LessEq (V _, Or (_, _)) -> RelC ps
              | LessEq (V _, Cast (_, _)) -> RelC ps
              | LessEq (Plus (_, _), _) -> RelC ps
              | LessEq (Minus (_, _), _) -> RelC ps
              | LessEq (Times (_, _), _) -> RelC ps
              | LessEq (Div (_, _), _) -> RelC ps
              | LessEq (Mod (_, _), _) -> RelC ps
              | LessEq (Less (_, _), _) -> RelC ps
              | LessEq (LessEq (_, _), _) -> RelC ps
              | LessEq (Greater (_, _), _) -> RelC ps
              | LessEq (GreaterEq (_, _), _) -> RelC ps
              | LessEq (NotEq (_, _), _) -> RelC ps
              | LessEq (Eq (_, _), _) -> RelC ps | LessEq (Not _, _) -> RelC ps
              | LessEq (And (_, _), _) -> RelC ps
              | LessEq (Or (_, _), _) -> RelC ps
              | LessEq (Cast (_, _), _) -> RelC ps | Greater (N _, _) -> RelC ps
              | Greater (V _, N _) -> RelC ps
              | Greater (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (y, x)
                       ps)
              | Greater (V _, Plus (_, _)) -> RelC ps
              | Greater (V _, Minus (_, _)) -> RelC ps
              | Greater (V _, Times (_, _)) -> RelC ps
              | Greater (V _, Div (_, _)) -> RelC ps
              | Greater (V _, Mod (_, _)) -> RelC ps
              | Greater (V _, Less (_, _)) -> RelC ps
              | Greater (V _, LessEq (_, _)) -> RelC ps
              | Greater (V _, Greater (_, _)) -> RelC ps
              | Greater (V _, GreaterEq (_, _)) -> RelC ps
              | Greater (V _, NotEq (_, _)) -> RelC ps
              | Greater (V _, Eq (_, _)) -> RelC ps
              | Greater (V _, Not _) -> RelC ps
              | Greater (V _, And (_, _)) -> RelC ps
              | Greater (V _, Or (_, _)) -> RelC ps
              | Greater (V _, Cast (_, _)) -> RelC ps
              | Greater (Plus (_, _), _) -> RelC ps
              | Greater (Minus (_, _), _) -> RelC ps
              | Greater (Times (_, _), _) -> RelC ps
              | Greater (Div (_, _), _) -> RelC ps
              | Greater (Mod (_, _), _) -> RelC ps
              | Greater (Less (_, _), _) -> RelC ps
              | Greater (LessEq (_, _), _) -> RelC ps
              | Greater (Greater (_, _), _) -> RelC ps
              | Greater (GreaterEq (_, _), _) -> RelC ps
              | Greater (NotEq (_, _), _) -> RelC ps
              | Greater (Eq (_, _), _) -> RelC ps
              | Greater (Not _, _) -> RelC ps
              | Greater (And (_, _), _) -> RelC ps
              | Greater (Or (_, _), _) -> RelC ps
              | Greater (Cast (_, _), _) -> RelC ps
              | GreaterEq (N _, _) -> RelC ps | GreaterEq (V _, N _) -> RelC ps
              | GreaterEq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (y, x)
                       ps)
              | GreaterEq (V _, Plus (_, _)) -> RelC ps
              | GreaterEq (V _, Minus (_, _)) -> RelC ps
              | GreaterEq (V _, Times (_, _)) -> RelC ps
              | GreaterEq (V _, Div (_, _)) -> RelC ps
              | GreaterEq (V _, Mod (_, _)) -> RelC ps
              | GreaterEq (V _, Less (_, _)) -> RelC ps
              | GreaterEq (V _, LessEq (_, _)) -> RelC ps
              | GreaterEq (V _, Greater (_, _)) -> RelC ps
              | GreaterEq (V _, GreaterEq (_, _)) -> RelC ps
              | GreaterEq (V _, NotEq (_, _)) -> RelC ps
              | GreaterEq (V _, Eq (_, _)) -> RelC ps
              | GreaterEq (V _, Not _) -> RelC ps
              | GreaterEq (V _, And (_, _)) -> RelC ps
              | GreaterEq (V _, Or (_, _)) -> RelC ps
              | GreaterEq (V _, Cast (_, _)) -> RelC ps
              | GreaterEq (Plus (_, _), _) -> RelC ps
              | GreaterEq (Minus (_, _), _) -> RelC ps
              | GreaterEq (Times (_, _), _) -> RelC ps
              | GreaterEq (Div (_, _), _) -> RelC ps
              | GreaterEq (Mod (_, _), _) -> RelC ps
              | GreaterEq (Less (_, _), _) -> RelC ps
              | GreaterEq (LessEq (_, _), _) -> RelC ps
              | GreaterEq (Greater (_, _), _) -> RelC ps
              | GreaterEq (GreaterEq (_, _), _) -> RelC ps
              | GreaterEq (NotEq (_, _), _) -> RelC ps
              | GreaterEq (Eq (_, _), _) -> RelC ps
              | GreaterEq (Not _, _) -> RelC ps
              | GreaterEq (And (_, _), _) -> RelC ps
              | GreaterEq (Or (_, _), _) -> RelC ps
              | GreaterEq (Cast (_, _), _) -> RelC ps | NotEq (_, _) -> RelC ps
              | Eq (N _, _) -> RelC ps | Eq (V _, N _) -> RelC ps
              | Eq (V x, V y) ->
                RelC (inserta (equal_prod equal_literal equal_literal) (x, y)
                       (inserta (equal_prod equal_literal equal_literal) (y, x)
                         ps))
              | Eq (V _, Plus (_, _)) -> RelC ps
              | Eq (V _, Minus (_, _)) -> RelC ps
              | Eq (V _, Times (_, _)) -> RelC ps
              | Eq (V _, Div (_, _)) -> RelC ps
              | Eq (V _, Mod (_, _)) -> RelC ps
              | Eq (V _, Less (_, _)) -> RelC ps
              | Eq (V _, LessEq (_, _)) -> RelC ps
              | Eq (V _, Greater (_, _)) -> RelC ps
              | Eq (V _, GreaterEq (_, _)) -> RelC ps
              | Eq (V _, NotEq (_, _)) -> RelC ps
              | Eq (V _, Eq (_, _)) -> RelC ps | Eq (V _, Not _) -> RelC ps
              | Eq (V _, And (_, _)) -> RelC ps | Eq (V _, Or (_, _)) -> RelC ps
              | Eq (V _, Cast (_, _)) -> RelC ps
              | Eq (Plus (_, _), _) -> RelC ps | Eq (Minus (_, _), _) -> RelC ps
              | Eq (Times (_, _), _) -> RelC ps | Eq (Div (_, _), _) -> RelC ps
              | Eq (Mod (_, _), _) -> RelC ps | Eq (Less (_, _), _) -> RelC ps
              | Eq (LessEq (_, _), _) -> RelC ps
              | Eq (Greater (_, _), _) -> RelC ps
              | Eq (GreaterEq (_, _), _) -> RelC ps
              | Eq (NotEq (_, _), _) -> RelC ps | Eq (Eq (_, _), _) -> RelC ps
              | Eq (Not _, _) -> RelC ps | Eq (And (_, _), _) -> RelC ps
              | Eq (Or (_, _), _) -> RelC ps | Eq (Cast (_, _), _) -> RelC ps
              | Not _ -> RelC ps | And (_, _) -> RelC ps | Or (_, _) -> RelC ps
              | Cast (_, _) -> RelC ps));;

let rec relc_branch_step
  b pol d = (if pol then assume_step b d else assume_not_step b d);;

let rec branch_identity ch b pol x = x;;

let rec event_identity ch ev x = x;;

let rec skip_identity ch x = x;;

let rec body_identity ch p x = x;;

let rec conservative_local_spec
  asn sp rt en ca =
    Glocal_spec_ext
      (query_unknown, skip_identity, asn, sp, branch_identity, body_identity,
        rt, event_identity, en, combine_env_identity, ca, ());;

let rec relc_learn
  ch ys x e d =
    (match d with RelBot -> RelBot
      | RelC ps ->
        RelC (sup_set (equal_prod equal_literal equal_literal)
               (sup_set (equal_prod equal_literal equal_literal) ps
                 (Set (map_filter
                        (fun xa ->
                          (if not ((xa : string) = x) &&
                                equal_option equal_int
                                  (answer_const
                                    (ch (EvalInt (LessEq (e, V xa)))))
                                  (Some one_inta)
                            then Some (x, xa) else None))
                        ys)))
               (Set (map_filter
                      (fun xa ->
                        (if not ((xa : string) = x) &&
                              equal_option equal_int
                                (answer_const (ch (EvalInt (LessEq (V xa, e)))))
                                (Some one_inta)
                          then Some (xa, x) else None))
                      ys))));;

let rec forget_relc
  x xa1 = match x, xa1 with x, RelBot -> RelBot
    | x, RelC ps ->
        RelC (filter
               (fun (a, b) -> not ((a : string) = x) && not ((b : string) = x))
               ps);;

let rec relc_ret
  eo d = (match eo with None -> d | Some _ -> forget_relc ret_var d);;

let rec var_of = function V x -> Some x
                 | N v -> None
                 | Plus (v, va) -> None
                 | Minus (v, va) -> None
                 | Times (v, va) -> None
                 | Div (v, va) -> None
                 | Mod (v, va) -> None
                 | Less (v, va) -> None
                 | LessEq (v, va) -> None
                 | Greater (v, va) -> None
                 | GreaterEq (v, va) -> None
                 | NotEq (v, va) -> None
                 | Eq (v, va) -> None
                 | Not v -> None
                 | And (v, va) -> None
                 | Or (v, va) -> None
                 | Cast (v, va) -> None;;

let rec relc_has
  x y xa2 = match x, y, xa2 with x, y, RelBot -> true
    | x, y, RelC ps ->
        member (equal_prod equal_literal equal_literal) (x, y) ps;;

let rec relc_le
  d a b =
    (match (var_of a, var_of b) with (None, _) -> false
      | (Some _, None) -> false
      | (Some x, Some y) -> ((x : string) = y) || relc_has x y d);;

let rec relc_eval
  d e = (match e
          with N _ -> top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | V _ -> top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Plus (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Minus (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Times (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Div (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Mod (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Less (a, b) ->
            (if relc_le d b a then answer_of_int zero_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | LessEq (a, b) ->
            (if relc_le d a b then answer_of_int one_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | Greater (a, b) ->
            (if relc_le d a b then answer_of_int zero_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | GreaterEq (a, b) ->
            (if relc_le d b a then answer_of_int one_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | NotEq (a, b) ->
            (if relc_le d a b && relc_le d b a then answer_of_int zero_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | Eq (a, b) ->
            (if relc_le d a b && relc_le d b a then answer_of_int one_inta
              else top_query_lifta (order_int_dom_ext bounded_lattice_unit))
          | Not _ -> top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | And (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Or (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit)
          | Cast (_, _) ->
            top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec relc_qry d (EvalInt e) = relc_eval d e;;

let rec order_spec
  ys = ls_branch_update (fun _ _ -> relc_branch_step)
         (ls_query_update (fun _ _ -> relc_qry)
           (conservative_local_spec
             (fun ch x e d -> relc_learn ch ys x e (forget_relc x d))
             (fun _ _ -> forget_relc) (fun _ eo _ -> relc_ret eo)
             (fun _ _ p -> [(fst p, top_relc)]) (fun _ _ _ _ -> top_relc)));;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec com_vnames
  = function SKIP uu -> bot_set
    | Assign (uv, x, a) -> inserta equal_literal x (exp_vnames a)
    | Check (uw, l, c) -> exp_vnames c
    | Seq (c1, c2) -> sup_set equal_literal (com_vnames c1) (com_vnames c2)
    | If (ux, b, c1, c2) ->
        sup_set equal_literal
          (sup_set equal_literal (exp_vnames b) (com_vnames c1)) (com_vnames c2)
    | While (uy, b, c) -> sup_set equal_literal (exp_vnames b) (com_vnames c)
    | Call (uz, dst, va, actuals) ->
        sup_set equal_literal
          (match dst with None -> bot_set
            | Some x -> inserta equal_literal x bot_set)
          (sup_seta equal_literal (Set (map exp_vnames actuals)))
    | Return (vb, e) -> (match e with None -> bot_set | Some a -> exp_vnames a)
    | Restore vc -> bot_set
    | Unwind vd -> bot_set;;

let rec scope_vnames
  p owner =
    sup_set equal_literal
      (sup_set equal_literal (Set (declared_global_vars p))
        (inserta equal_literal ret_var bot_set))
      (match prog_table p owner with None -> bot_set
        | Some decl ->
          sup_set equal_literal (Set (formals decl)) (com_vnames (body decl)));;

let rec scope_vnames_list
  p owner =
    sorted_list_of_set (equal_literal, linorder_literal)
      (scope_vnames p owner);;

let rec program_vars
  p = remdups equal_literal
        (maps (scope_vnames_list p) (prog_main_name :: prog_procs p));;

let rec set_slot8
  r v = Product
          (pleft r,
            Product
              (pleft (pright r),
                Product
                  (pleft (pright (pright r)),
                    Product
                      (pleft (pright (pright (pright r))),
                        Product
                          (pleft (pright (pright (pright (pright r)))),
                            Product
                              (pleft (pright
                                       (pright (pright (pright (pright r))))),
                                Product
                                  (pleft (pright
   (pright (pright (pright (pright (pright r)))))),
                                    v)))))));;

let rec set_slot7
  r v = Product
          (pleft r,
            Product
              (pleft (pright r),
                Product
                  (pleft (pright (pright r)),
                    Product
                      (pleft (pright (pright (pright r))),
                        Product
                          (pleft (pright (pright (pright (pright r)))),
                            Product
                              (pleft (pright
                                       (pright (pright (pright (pright r))))),
                                Product
                                  (v, pright
(pright (pright (pright (pright (pright (pright r)))))))))))));;

let rec set_slot6
  r v = Product
          (pleft r,
            Product
              (pleft (pright r),
                Product
                  (pleft (pright (pright r)),
                    Product
                      (pleft (pright (pright (pright r))),
                        Product
                          (pleft (pright (pright (pright (pright r)))),
                            Product
                              (v, pright
                                    (pright
                                      (pright
(pright (pright (pright r)))))))))));;

let rec set_slot5
  r v = Product
          (pleft r,
            Product
              (pleft (pright r),
                Product
                  (pleft (pright (pright r)),
                    Product
                      (pleft (pright (pright (pright r))),
                        Product
                          (v, pright
                                (pright (pright (pright (pright r)))))))));;

let rec set_slot4
  r v = Product
          (pleft r,
            Product
              (pleft (pright r),
                Product
                  (pleft (pright (pright r)),
                    Product (v, pright (pright (pright (pright r)))))));;

let rec set_slot3
  r v = Product
          (pleft r,
            Product
              (pleft (pright r), Product (v, pright (pright (pright r)))));;

let rec set_slot2 r v = Product (pleft r, Product (v, pright (pright r)));;

let rec set_slot1 r v = Product (v, pright r);;

let rec registration_of
  = function
    Sign_Analysis ->
      Analysis_registration_ext
        ((fun g p ->
           lens_of
             (lift_get
               (bot_lifted
                 (semilattice_sup_gdefault_st
                   (infinite_key_literal, equal_literal)
                   bounded_semilattice_sup_bot_sign))
               slot1)
             (lift_put
               (bot_analysis_product
                 (order_bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_sign))
                 (order_bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_ivl))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_parity))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit)))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_congruence))
                             order_bot_relc)))))))
               ((equal_lifted
                  (equal_gdefault_st (infinite_key_literal, equal_literal)
                    (equal_sign,
                      bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot))),
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_sign)))
               set_slot1)
             (ask_assign
               (exec_local_spec bounded_semilattice_sup_bot_sign g
                 (default_st_is_bot_for executable_domain_sign
                   (declared_global_vars p))
                 (generic_tf_st_for executable_domain_sign sign_ops g)
                 (generic_enter_st_for (bot_sign, top_sign) sign_ops g)))),
          (fun r ->
            not (equal_lifteda
                  (equal_gdefault_st (infinite_key_literal, equal_literal)
                    (equal_sign, order_bot_sign))
                  (slot1 r)
                  (bot_lifteda
                    (semilattice_sup_gdefault_st
                      (infinite_key_literal, equal_literal)
                      bounded_semilattice_sup_bot_sign)))),
          (fun gs r ->
            (match slot1 r with Bot -> true
              | Lifted a -> default_st_is_bot_for executable_domain_sign gs a)),
          (fun v q ->
            (match slot1 v
              with Bot ->
                top_query_lifta (order_int_dom_ext bounded_lattice_unit)
              | Lifted st -> sign_eval_answer st q)),
          (fun v vars ->
            Field_Store
              (map (fun x ->
                     (x, SignValue
                           (match slot1 v with Bot -> bot_signa
                             | Lifted st -> st x)))
                vars)),
          (fun ctx -> map (fun a -> SignValue a) (slot1 ctx)), ())
    | Interval_Analysis ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_ivl))
                 slot2)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_ivl,
                        bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_ivl)))
                 set_slot2)
               (ask_assign
                 (exec_local_spec bounded_semilattice_sup_bot_ivl g
                   (default_st_is_bot_for executable_domain_ivl
                     (declared_global_vars p))
                   (generic_tf_st_for executable_domain_ivl ivl_ops g)
                   (generic_enter_st_for (bot_ivl, top_ivl) ivl_ops g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_ivl, order_bot_ivl))
                    (slot2 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        bounded_semilattice_sup_bot_ivl)))),
            (fun gs r ->
              (match slot2 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for executable_domain_ivl gs a)),
            (fun v q ->
              (match slot2 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> interval_eval_answer st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, IntervalValue
                             (match slot2 v with Bot -> bot_ivla
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> IntervalValue a) (slot2 ctx)), ())
    | Parity_Analysis ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_parity))
                 slot3)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_parity,
                        bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_parity)))
                 set_slot3)
               (ask_assign
                 (exec_local_spec bounded_semilattice_sup_bot_parity g
                   (default_st_is_bot_for executable_domain_parity
                     (declared_global_vars p))
                   (generic_tf_st_for executable_domain_parity parity_ops g)
                   (generic_enter_st_for (bot_parity, top_parity) parity_ops
                     g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_parity, order_bot_parity))
                    (slot3 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        bounded_semilattice_sup_bot_parity)))),
            (fun gs r ->
              (match slot3 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for executable_domain_parity gs a)),
            (fun v q ->
              (match slot3 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> parity_eval_answer st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, ParityValue
                             (match slot3 v with Bot -> bot_paritya
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> ParityValue a) (slot3 ctx)), ())
    | Int_Analysis Refine_Fixpoint ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     (bounded_semilattice_sup_bot_int_dom_ext
                       bounded_lattice_unit)))
                 slot4)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       (bounded_semilattice_sup_bot_int_dom_ext
                         bounded_lattice_unit))))
                 set_slot4)
               (ask_assign
                 (exec_local_spec
                   (bounded_semilattice_sup_bot_int_dom_ext
                     bounded_lattice_unit)
                   g (default_st_is_bot_for
                       (executable_domain_int_dom_ext
                         (bounded_lattice_unit, warrowing_unit))
                       (declared_global_vars p))
                   (generic_tf_st_for
                     (executable_domain_int_dom_ext
                       (bounded_lattice_unit, warrowing_unit))
                     (int_dom_ops Refine_Fixpoint) g)
                   (generic_enter_st_for
                     ((bot_int_dom_ext bounded_lattice_unit),
                       (top_int_dom_ext bounded_lattice_unit))
                     (int_dom_ops Refine_Fixpoint) g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (order_bot_int_dom_ext bounded_lattice_unit)))
                    (slot4 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit))))),
            (fun gs r ->
              (match slot4 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for
                    (executable_domain_int_dom_ext
                      (bounded_lattice_unit, warrowing_unit))
                    gs a)),
            (fun v q ->
              (match slot4 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> int_eval_answer Refine_Fixpoint st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, IntDomValue
                             (match slot4 v
                               with Bot -> bot_int_dom_exta bounded_lattice_unit
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> IntDomValue a) (slot4 ctx)), ())
    | Int_Analysis Refine_Once ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     (bounded_semilattice_sup_bot_int_dom_ext
                       bounded_lattice_unit)))
                 slot5)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       (bounded_semilattice_sup_bot_int_dom_ext
                         bounded_lattice_unit))))
                 set_slot5)
               (ask_assign
                 (exec_local_spec
                   (bounded_semilattice_sup_bot_int_dom_ext
                     bounded_lattice_unit)
                   g (default_st_is_bot_for
                       (executable_domain_int_dom_ext
                         (bounded_lattice_unit, warrowing_unit))
                       (declared_global_vars p))
                   (generic_tf_st_for
                     (executable_domain_int_dom_ext
                       (bounded_lattice_unit, warrowing_unit))
                     (int_dom_ops Refine_Once) g)
                   (generic_enter_st_for
                     ((bot_int_dom_ext bounded_lattice_unit),
                       (top_int_dom_ext bounded_lattice_unit))
                     (int_dom_ops Refine_Once) g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (order_bot_int_dom_ext bounded_lattice_unit)))
                    (slot5 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit))))),
            (fun gs r ->
              (match slot5 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for
                    (executable_domain_int_dom_ext
                      (bounded_lattice_unit, warrowing_unit))
                    gs a)),
            (fun v q ->
              (match slot5 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> int_eval_answer Refine_Once st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, IntDomOnceValue
                             (match slot5 v
                               with Bot -> bot_int_dom_exta bounded_lattice_unit
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> IntDomOnceValue a) (slot5 ctx)), ())
    | Int_Analysis Refine_Never ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     (bounded_semilattice_sup_bot_int_dom_ext
                       bounded_lattice_unit)))
                 slot6)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       (bounded_semilattice_sup_bot_int_dom_ext
                         bounded_lattice_unit))))
                 set_slot6)
               (ask_assign
                 (exec_local_spec
                   (bounded_semilattice_sup_bot_int_dom_ext
                     bounded_lattice_unit)
                   g (default_st_is_bot_for
                       (executable_domain_int_dom_ext
                         (bounded_lattice_unit, warrowing_unit))
                       (declared_global_vars p))
                   (generic_tf_st_for
                     (executable_domain_int_dom_ext
                       (bounded_lattice_unit, warrowing_unit))
                     (int_dom_ops Refine_Never) g)
                   (generic_enter_st_for
                     ((bot_int_dom_ext bounded_lattice_unit),
                       (top_int_dom_ext bounded_lattice_unit))
                     (int_dom_ops Refine_Never) g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      ((equal_int_dom_ext equal_unit),
                        (order_bot_int_dom_ext bounded_lattice_unit)))
                    (slot6 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit))))),
            (fun gs r ->
              (match slot6 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for
                    (executable_domain_int_dom_ext
                      (bounded_lattice_unit, warrowing_unit))
                    gs a)),
            (fun v q ->
              (match slot6 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> int_eval_answer Refine_Never st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, IntDomNeverValue
                             (match slot6 v
                               with Bot -> bot_int_dom_exta bounded_lattice_unit
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> IntDomNeverValue a) (slot6 ctx)), ())
    | Congruence_Analysis ->
        Analysis_registration_ext
          ((fun g p ->
             lens_of
               (lift_get
                 (bot_lifted
                   (semilattice_sup_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_congruence))
                 slot7)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 ((equal_lifted
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_congruence,
                        bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot))),
                   (bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_congruence)))
                 set_slot7)
               (ask_assign
                 (exec_local_spec bounded_semilattice_sup_bot_congruence g
                   (default_st_is_bot_for executable_domain_congruence
                     (declared_global_vars p))
                   (generic_tf_st_for executable_domain_congruence
                     congruence_ops g)
                   (generic_enter_st_for (bot_congruence, top_congruence)
                     congruence_ops g)))),
            (fun r ->
              not (equal_lifteda
                    (equal_gdefault_st (infinite_key_literal, equal_literal)
                      (equal_congruence, order_bot_congruence))
                    (slot7 r)
                    (bot_lifteda
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        bounded_semilattice_sup_bot_congruence)))),
            (fun gs r ->
              (match slot7 r with Bot -> true
                | Lifted a ->
                  default_st_is_bot_for executable_domain_congruence gs a)),
            (fun v q ->
              (match slot7 v
                with Bot ->
                  top_query_lifta (order_int_dom_ext bounded_lattice_unit)
                | Lifted st -> congruence_eval_answer st q)),
            (fun v vars ->
              Field_Store
                (map (fun x ->
                       (x, CongruenceValue
                             (match slot7 v with Bot -> bot_congruencea
                               | Lifted st -> st x)))
                  vars)),
            (fun ctx -> map (fun a -> CongruenceValue a) (slot7 ctx)), ())
    | Order_Analysis ->
        Analysis_registration_ext
          ((fun _ p ->
             lens_of (lift_get bot_relc slot8)
               (lift_put
                 (bot_analysis_product
                   (order_bot_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (order_bot_analysis_product
                     (order_bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (order_bot_analysis_product
                       (order_bot_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (order_bot_analysis_product
                         (order_bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (order_bot_analysis_product
                           (order_bot_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (order_bot_analysis_product
                             (order_bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (order_bot_analysis_product
                               (order_bot_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               order_bot_relc)))))))
                 (equal_relc, bot_relc) set_slot8)
               (order_spec (program_vars p))),
            (fun r -> not (equal_relca (slot8 r) bot_relca)),
            (fun _ r -> equal_relca (slot8 r) RelBot),
            (fun v -> relc_qry (slot8 v)),
            (fun v _ -> Field_Whole (OrderValue (order_pairs (slot8 v)))),
            (fun _ -> []), ());;

let rec mcp_emp
  asa p r =
    list_ex
      (fun a -> field_empty (registration_of a) (declared_global_vars p) r)
      asa;;

let rec initial_default_st _A
  local_value global_value =
    Abs_default_st ((local_value, []), (global_value, []));;

let rec mcp_init
  asa = Product
          ((if membera equal_analysis_domain asa Sign_Analysis
             then Lifted (initial_default_st bot_sign STop SZero)
             else bot_lifteda
                    (semilattice_sup_gdefault_st
                      (infinite_key_literal, equal_literal)
                      bounded_semilattice_sup_bot_sign)),
            Product
              ((if membera equal_analysis_domain asa Interval_Analysis
                 then Lifted
                        (initial_default_st bot_ivl (Ivl (MinInf, PlusInf))
                          (Ivl (Fin zero_inta, Fin zero_inta)))
                 else bot_lifteda
                        (semilattice_sup_gdefault_st
                          (infinite_key_literal, equal_literal)
                          bounded_semilattice_sup_bot_ivl)),
                Product
                  ((if membera equal_analysis_domain asa Parity_Analysis
                     then Lifted (initial_default_st bot_parity PTop PEven)
                     else bot_lifteda
                            (semilattice_sup_gdefault_st
                              (infinite_key_literal, equal_literal)
                              bounded_semilattice_sup_bot_parity)),
                    Product
                      ((if membera equal_analysis_domain asa
                             (Int_Analysis Refine_Fixpoint)
                         then Lifted
                                (initial_default_st
                                  (bot_int_dom_ext bounded_lattice_unit)
                                  (top_int_dom_exta bounded_lattice_unit)
                                  (int_dom_of_int zero_inta))
                         else bot_lifteda
                                (semilattice_sup_gdefault_st
                                  (infinite_key_literal, equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit))),
                        Product
                          ((if membera equal_analysis_domain asa
                                 (Int_Analysis Refine_Once)
                             then Lifted
                                    (initial_default_st
                                      (bot_int_dom_ext bounded_lattice_unit)
                                      (top_int_dom_exta bounded_lattice_unit)
                                      (int_dom_of_int zero_inta))
                             else bot_lifteda
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_literal, equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit))),
                            Product
                              ((if membera equal_analysis_domain asa
                                     (Int_Analysis Refine_Never)
                                 then Lifted
(initial_default_st (bot_int_dom_ext bounded_lattice_unit)
  (top_int_dom_exta bounded_lattice_unit) (int_dom_of_int zero_inta))
                                 else bot_lifteda
(semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
  (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit))),
                                Product
                                  ((if membera equal_analysis_domain asa
 Congruence_Analysis
                                     then Lifted
    (initial_default_st bot_congruence top_congruencea
      (congruence_of_int zero_inta))
                                     else bot_lifteda
    (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
      bounded_semilattice_sup_bot_congruence)),
                                    (if membera equal_analysis_domain asa
  Order_Analysis
                                      then top_relc else bot_relca))))))));;

let rec mcp_en_from
  cs ch ci p = fold (fun c -> maps (ls_enter c ch ci)) cs [p];;

let rec mcp_combine
  = function [c] -> c
    | [] -> make_local_spec (mcp_qry []) (mcp_step []) (mcp_en_from [])
              (mcp_comb []) (fun _ _ dc _ -> dc)
    | v :: vb :: vc ->
        make_local_spec (mcp_qry (v :: vb :: vc)) (mcp_step (v :: vb :: vc))
          (mcp_en_from (v :: vb :: vc)) (mcp_comb (v :: vb :: vc))
          (fun _ _ dc _ -> dc);;

let rec cfg_node_list (_A1, _A2) (_B1, _B2)
  g = remdups equal_cfg_node
        (maps (fun (u, (_, v)) -> [u; v])
           (cfg_intra_list (_A1, _A2) (_B1, _B2) g) @
          maps (fun (u, (_, (ce, after))) -> [u; ce; after])
            (cfg_calls_list (_A1, _A2) (_B1, _B2) g) @
            [cfg_entry g]);;

let rec map_local_spec
  k c = make_local_spec (ls_query c) (fun ch a x -> k (ls_step c ch a x))
          (fun ch ci p -> map (fun (q, e) -> (q, k e)) (ls_enter c ch ci p))
          (ls_combine_env c)
          (fun ch ci x de -> k (ls_combine_assign c ch ci x de));;

let rec field_spec
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = field_spec;;

let rec value_answer
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = value_answer;;

let rec part_answer
  g a x q =
    (match x
      with Bot -> top_query_lifta (order_int_dom_ext bounded_lattice_unit)
      | Lifted r -> value_answer (registration_of a) (mcp_rd g r) q);;

let rec mcp_field
  g p a =
    with_qry (fun _ -> part_answer g a) (field_spec (registration_of a) g p);;

let rec field_live
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = field_live;;

let rec mcp_norm
  asa x =
    (match x with Bot -> Bot
      | Lifted r ->
        (if list_all (fun a -> field_live (registration_of a) r) asa then x
          else Bot));;

let rec mcp_comp
  asa g p =
    map_local_spec (mcp_norm asa) (mcp_combine (map (mcp_field g p) asa));;

let rec arithmetic_diagnostic_of
  v i obligation x3 = match v, i, obligation, x3 with
    v, i, obligation, Lifted Check_Refuted ->
      [Arithmetic_Diagnostic (v, i, obligation, Check_Refuted)]
    | v, i, obligation, Lifted Check_Unknown ->
        [Arithmetic_Diagnostic (v, i, obligation, Check_Unknown)]
    | v, i, obligation, Bot -> []
    | v, i, obligation, Lifted Check_Proved -> [];;

let rec arithmetic_divisor (Arithmetic_Obligation (x1, x2)) = x2;;

let rec arithmetic_condition
  obligation = NotEq (arithmetic_divisor obligation, N zero_inta);;

let rec edge_expressions = function EA_Assign (x, e) -> [e]
                           | EA_Assume e -> [e]
                           | EA_AssumeNot e -> [e]
                           | EA_Check (l, e) -> [e]
                           | EA_Ret (Some e, p) -> [e]
                           | EA_Special (Min (a, b), x) -> [a; b]
                           | EA_Special (Max (a, b), x) -> [a; b]
                           | EA_Nop -> []
                           | EA_Special (Nondet_Int, va) -> []
                           | EA_Body v -> []
                           | EA_Ret (None, va) -> [];;

let rec arithmetic_expression_sites
  g = (let edges =
         cfg_intra_list (equal_literal, linorder_literal)
           (equal_exp, linorder_exp) g
         in
        map_filter
          (fun x ->
            (if (match x with (_, (EA_Nop, _)) -> true
                  | (_, (EA_Assign (_, _), _)) -> true
                  | (_, (EA_Special (_, _), _)) -> true
                  | (_, (EA_Assume _, _)) -> true
                  | (u, (EA_AssumeNot e, _)) ->
                    not (list_ex
                          (fun (ua, (a, _)) ->
                            equal_cfg_nodea u ua &&
                              equal_gedge_actiona equal_literal equal_exp a
                                (EA_Assume e))
                          edges)
                  | (_, (EA_Body _, _)) -> true
                  | (_, (EA_Ret (_, _), _)) -> true
                  | (_, (EA_Check (_, _), _)) -> true)
              then Some (let (u, (a, _)) = x in (u, edge_expressions a))
              else None))
          edges) @
        map (fun (u, (ca, (_, _))) -> (u, ce_args ca))
          (cfg_calls_list (equal_literal, linorder_literal)
            (equal_exp, linorder_exp) g);;

let rec arithmetic_obligations
  = function N n -> []
    | V x -> []
    | Not a -> arithmetic_obligations a
    | And (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Or (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Div (a, b) ->
        arithmetic_obligations a @
          arithmetic_obligations b @ [Arithmetic_Obligation (Div (a, b), b)]
    | Mod (a, b) ->
        arithmetic_obligations a @
          arithmetic_obligations b @ [Arithmetic_Obligation (Mod (a, b), b)]
    | Plus (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Minus (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Times (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Less (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | LessEq (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Greater (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | GreaterEq (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Eq (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | NotEq (a, b) -> arithmetic_obligations a @ arithmetic_obligations b
    | Cast (uu, a) -> arithmetic_obligations a;;

let rec arithmetic_sites
  g = map (fun (v, es) -> (v, maps arithmetic_obligations es))
        (arithmetic_expression_sites g);;

let rec aggregate_verdicts
  (Set vs) = fold (sup_lifteda semilattice_sup_check_result) vs Bot;;

let rec classify_point
  classify c x2 = match classify, c, x2 with classify, c, Bot -> Bot
    | classify, c, Lifted st -> Lifted (classify c st);;

let rec table_contexts
  r v = image snd
          (filter (fun (va, _) -> equal_cfg_nodea va v) (covered_keys r));;

let rec point_verdict _A
  r classify v e =
    aggregate_verdicts
      (image (fun ctx -> classify_point classify e (lookup_table _A r v ctx))
        (table_contexts r v));;

let rec arithmetic_diagnostics _A
  g r classify =
    maps (fun (v, obligations) ->
           maps (fun (i, obligation) ->
                  arithmetic_diagnostic_of v i obligation
                    (point_verdict _A r classify v
                      (arithmetic_condition obligation)))
             (zip (upt zero_nat (size_list obligations)) obligations))
      (arithmetic_sites g);;

let rec config_globals (Analysis_Config (x1, x2, x3, x4)) = x4;;

let rec run_shared
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_shared;;

let rec run_table
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_table;;

let rec run_succ
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_succ;;

let rec run_seed
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_seed;;

let rec ea_check_label (EA_Check (x81, x82)) = x81;;

let rec result_checks_of _A
  g r classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      Result_check_ext
                        (u, ea_check_label a, ea_check_cond a,
                          point_verdict _A r classify u (ea_check_cond a), ()))
          else None))
      (cfg_intra_list (equal_literal, linorder_literal)
        (equal_exp, linorder_exp) g);;

let rec minus_set _A
  a x1 = match a, x1 with a, Set xs -> fold (remove _A) xs a
    | a, Coset xs -> Set (filtera (fun x -> member _A x a) xs);;

let rec context_indices _A
  indexed ctx =
    map_filter
      (fun x ->
        (if (let (_, ctxa) = x in eq _A ctxa ctx) then Some (fst x) else None))
      indexed;;

let rec callee_of_entry = function FunctionEntry p -> p
                          | Statement v -> ""
                          | FunctionResult v -> "";;

let rec prog_cfg
  p = compile_prog equal_literal equal_exp (prog_table p) (prog_procs p);;

let rec ordered_by_key _A (_B1, _B2)
  rank s =
    map (fun k -> the_elem _A (filter (fun x -> eq _B1 (rank x) k) s))
      (sorted_list_of_set (_B1, _B2) (image rank s));;

let rec live_targets
  succ u ctx ca q =
    (match succ u ctx ca q with None -> [] | Some ctxa -> [ctxa]);;

let rec run_step
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_step;;

let rec report_row _A
  sr classify conds obls edges i ctx v =
    (let state = lookup_table _A (run_table sr) v ctx in
      Result_state_ext
        (v, i, state,
          map (fun cond -> (cond, classify_point classify cond state))
            (group_lookup linorder_cfg_node conds v),
          map (fun obligation ->
                (obligation,
                  classify_point classify (arithmetic_condition obligation)
                    state))
            (concat (group_lookup linorder_cfg_node obls v)),
          map (fun (a, w) -> (w, run_step sr v ctx a))
            (group_lookup linorder_cfg_node edges v),
          ()));;

let rec report_of _A
  config ctx_key ctx_tag classify sr p =
    (let g = prog_cfg p in
     let r = run_table sr in
     let ctxs =
       ordered_by_key _A (equal_order_key, linorder_order_key) ctx_key
         (image snd (covered_keys r))
       in
     let indexed = enumerate zero_nat ctxs in
     let nodes =
       cfg_node_list (equal_literal, linorder_literal) (equal_exp, linorder_exp)
         g @
         sorted_list_of_set (equal_cfg_node, linorder_cfg_node)
           (minus_set equal_cfg_node (image fst (covered_keys r))
             (Set (cfg_node_list (equal_literal, linorder_literal)
                    (equal_exp, linorder_exp) g)))
       in
     let intra =
       cfg_intra_list (equal_literal, linorder_literal)
         (equal_exp, linorder_exp) g
       in
     let steps =
       group_by_key linorder_cfg_node (fun (u, (_, _)) -> u)
         (fun (_, (a, w)) -> Some (a, w)) intra
       in
     let checks =
       group_by_key linorder_cfg_node (fun (u, (_, _)) -> u)
         (fun (_, (a, _)) ->
           (if is_EA_Check a then Some (ea_check_cond a) else None))
         intra
       in
     let obligations =
       group_by_key linorder_cfg_node fst (comp (fun a -> Some a) snd)
         (arithmetic_sites g)
       in
     let state_at = report_row _A sr classify checks obligations steps in
     let route_at =
       (fun u ca ce i ctx ->
         Call_route_ext
           (u, i, callee_of_entry ce,
             (match lookup_table _A r u ctx with Bot -> []
               | Lifted _ ->
                 remdups equal_nat
                   (maps (context_indices _A indexed)
                     (live_targets (run_succ sr) u ctx ca
                       (callee_of_entry ce)))),
             ()))
       in
     let seeds_of =
       (fun f ->
         (match
           filtera
             (fun (_, ctx) ->
               member (equal_prod equal_cfg_node _A) (FunctionEntry f, ctx)
                 (covered_keys r))
             indexed
           with [] -> [Result_global_ext (Global_Seed (f, None), Bot, ())]
           | a :: lista ->
             map (fun (i, ctx) ->
                   Result_global_ext
                     (Global_Seed (f, Some i), run_seed sr f ctx, ()))
               (a :: lista)))
       in
      Analysis_report_ext
        (config, program_vars p, g, map ctx_tag ctxs,
          maps (fun (i, ctx) ->
                 map_filter
                   (fun x ->
                     (if member (equal_prod equal_cfg_node _A) (x, ctx)
                           (covered_keys r)
                       then Some (state_at i ctx x) else None))
                   nodes)
            indexed,
          maps (fun (u, (ca, (ce, _))) ->
                 map_filter
                   (fun x ->
                     (if (let (_, ctx) = x in
                           member (equal_prod equal_cfg_node _A) (u, ctx)
                             (covered_keys r))
                       then Some (let (a, b) = x in route_at u ca ce a b)
                       else None))
                   indexed)
            (cfg_calls_list (equal_literal, linorder_literal)
              (equal_exp, linorder_exp) g),
          result_checks_of _A g r classify,
          (match config_globals config with Program_Globals_Flow_Sensitive -> []
            | Program_Globals_Flow_Insensitive ->
              map (fun x ->
                    Result_global_ext (Global_Named x, run_shared sr x, ()))
                (declared_global_vars p)) @
            maps seeds_of (prog_main_name :: prog_procs p),
          arithmetic_diagnostics _A g r classify, ()));;

let rec explode s = map char_of_integer (Str_Literal.asciis_of_literal s);;

let rec body_update
  bodya (Gproc_decl_ext (formals, body, more)) =
    Gproc_decl_ext (formals, bodya body, more);;

let rec map_gcom
  f1 f2 f3 x3 = match f1, f2, f3, x3 with f1, f2, f3, SKIP x1 -> SKIP (f1 x1)
    | f1, f2, f3, Assign (x21, x22, x23) -> Assign (f1 x21, f2 x22, f3 x23)
    | f1, f2, f3, Check (x31, x32, x33) -> Check (f1 x31, x32, f3 x33)
    | f1, f2, f3, Seq (x41, x42) ->
        Seq (map_gcom f1 f2 f3 x41, map_gcom f1 f2 f3 x42)
    | f1, f2, f3, If (x51, x52, x53, x54) ->
        If (f1 x51, f3 x52, map_gcom f1 f2 f3 x53, map_gcom f1 f2 f3 x54)
    | f1, f2, f3, While (x61, x62, x63) ->
        While (f1 x61, f3 x62, map_gcom f1 f2 f3 x63)
    | f1, f2, f3, Call (x71, x72, x73, x74) ->
        Call (f1 x71, map_option f2 x72, x73, map f3 x74)
    | f1, f2, f3, Return (x81, x82) -> Return (f1 x81, map_option f3 x82)
    | f1, f2, f3, Restore x9 -> Restore (f1 x9)
    | f1, f2, f3, Unwind x10 -> Unwind (f1 x10);;

let rec typed_proc
  p ds q d =
    body_update
      (fun _ ->
        map_gcom id var_name lower
          (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q
            (body d)))
      d;;

let rec proc_rep_update
  proc_repa (Imp_prog_ext (proc_rep, declared_global_vars, more)) =
    Imp_prog_ext (proc_repa proc_rep, declared_global_vars, more);;

let rec typed_prog
  p ds =
    proc_rep_update
      (fun _ -> map (fun (q, d) -> (q, typed_proc p ds q d)) (proc_rep p)) p;;

let rec comp_entry _A (_C1, _C2) _D
  comp g p ci w =
    snd (hd (ls_enter (comp g p) (ls_channel _C1 (comp g p) w) ci (w, w)));;

let rec entry_alt _A (_C1, _C2) _D
  comp place_rl place_enter ga p ci d g =
    (let w = place_enter p ci d g in
      (place_rl ga w,
        place_rl ga (comp_entry _A (_C1, _C2) _D comp ga p ci w)));;

let rec entry_of _A (_C1, _C2) _D
  comp place_rl place_enter ga p ci d g =
    snd (entry_alt _A (_C1, _C2) _D comp place_rl place_enter ga p ci d g);;

let rec solved_run_of _A (_C1, _C2) (_D1, _D2)
  comp emp rd global_of seed route place_cmb place_rl place_enter g p sol =
    (let c = comp g p in
     let ga = genv global_of (snd sol) in
     let read = (fun d -> map_lift (rd g) (canonicalize_lift (emp p) d)) in
      Gsolved_run_ext
        (dg_result_for (rd g) (emp p) (place_cmb p) global_of sol,
          (fun n -> map_lift (rd g) (ga n)),
          (fun f ctx ->
            read (place_cmb p
                    (dg_local (snd sol (Inr (seed (FunctionEntry f) ctx))))
                   ga)),
          (fun v ctx a ->
            read (let b = place_cmb p (dg_local (snd sol (Inl (v, ctx)))) ga in
                   closed_step _C1 c a b)),
          (fun u ctx ca q ->
            (let d =
               entry_of _A (_C1, _C2) _D2 comp place_rl place_enter g p
                 (call_info_of ca q) (dg_local (snd sol (Inl (u, ctx)))) ga
               in
              (if equal_lifteda _D1 d Bot then None
                else Some (route g u ctx d ca)))),
          ()));;

let rec global_names_in g xs = remdups equal_literal (filtera g xs);;

let rec call_global_reads
  g es =
    global_names_in g
      (sorted_list_of_set (equal_literal, linorder_literal)
        (sup_seta equal_literal (image exp_vnames (Set es))));;

let rec view_of _A
  rg xs e acc = fold (fun x -> sup _A.sup_semilattice_sup (rg x (e x))) xs acc;;

let rec mcp_place_enter
  pg = (match pg with Program_Globals_Flow_Sensitive -> (fun _ _ d _ -> d)
         | Program_Globals_Flow_Insensitive ->
           (fun p ci d e ->
             split_cmb_lifted
               ((semilattice_sup_analysis_product
                  (semilattice_sup_lifted
                    (semilattice_sup_gdefault_st
                      (global_name_literal.infinite_key_global_name,
                        equal_literal)
                      bounded_semilattice_sup_bot_sign))
                  (semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_ivl))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_parity))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            (bounded_semilattice_sup_bot_int_dom_ext
                              bounded_lattice_unit)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_congruence))
                              semilattice_sup_relc))))))),
                 (ownership_split_analysis_product
                   (ownership_split_lifted
                     ((semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign),
                       (ownership_split_gdefault_st
                         (global_name_literal, equal_literal)
                         (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                           order_top_sign))))
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                             order_top_ivl))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                               order_top_parity))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               ((bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                 (order_top_int_dom_ext
                                   bounded_lattice_unit)))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
                                       order_top_congruence))))
                               ownership_split_relc))))))))
               d (view_of
                   (semilattice_sup_lifted
                     (semilattice_sup_analysis_product
                       (semilattice_sup_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_sign))
                       (semilattice_sup_analysis_product
                         (semilattice_sup_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_ivl))
                         (semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_parity))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       bounded_semilattice_sup_bot_congruence))
                                   semilattice_sup_relc))))))))
                   (split_global_at_lifted
                     ((semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_sign))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_ivl))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_parity))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
bounded_semilattice_sup_bot_congruence))
                                    semilattice_sup_relc))))))),
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_sign),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                                 order_top_sign))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_ivl),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                                   order_top_ivl))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_parity),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                     order_top_parity))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       ((bounded_semilattice_sup_bot_int_dom_ext
  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
 (order_top_int_dom_ext bounded_lattice_unit)))))
                                 (ownership_split_analysis_product
                                   (ownership_split_lifted
                                     ((semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
(bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
                                       (ownership_split_gdefault_st
 (global_name_literal, equal_literal)
 ((bounded_semilattice_sup_bot_int_dom_ext
    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
   (order_top_int_dom_ext bounded_lattice_unit)))))
                                   (ownership_split_analysis_product
                                     (ownership_split_lifted
                                       ((semilattice_sup_gdefault_st
  (global_name_literal.infinite_key_global_name, equal_literal)
  bounded_semilattice_sup_bot_congruence),
 (ownership_split_gdefault_st (global_name_literal, equal_literal)
   (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
     order_top_congruence))))
                                     ownership_split_relc)))))))))
                   (call_global_reads (declared_global p) (ci_args ci)) e
                   (split_free_lifted
                     ((semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_sign))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_ivl))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_parity))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
bounded_semilattice_sup_bot_congruence))
                                    semilattice_sup_relc))))))),
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_sign),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                                 order_top_sign))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_ivl),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                                   order_top_ivl))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_parity),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                     order_top_parity))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       ((bounded_semilattice_sup_bot_int_dom_ext
  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
 (order_top_int_dom_ext bounded_lattice_unit)))))
                                 (ownership_split_analysis_product
                                   (ownership_split_lifted
                                     ((semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
(bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
                                       (ownership_split_gdefault_st
 (global_name_literal, equal_literal)
 ((bounded_semilattice_sup_bot_int_dom_ext
    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
   (order_top_int_dom_ext bounded_lattice_unit)))))
                                   (ownership_split_analysis_product
                                     (ownership_split_lifted
                                       ((semilattice_sup_gdefault_st
  (global_name_literal.infinite_key_global_name, equal_literal)
  bounded_semilattice_sup_bot_congruence),
 (ownership_split_gdefault_st (global_name_literal, equal_literal)
   (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
     order_top_congruence))))
                                     ownership_split_relc))))))))
                     (call_global_reads (declared_global p) (ci_args ci))))));;

let rec full_view _A
  rg xs e =
    view_of _A.semilattice_sup_bounded_semilattice_sup_bot rg xs e
      (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec mcp_place_cmb
  pg = (match pg with Program_Globals_Flow_Sensitive -> (fun _ d _ -> d)
         | Program_Globals_Flow_Insensitive ->
           (fun p d e ->
             split_cmb_lifted
               ((semilattice_sup_analysis_product
                  (semilattice_sup_lifted
                    (semilattice_sup_gdefault_st
                      (global_name_literal.infinite_key_global_name,
                        equal_literal)
                      bounded_semilattice_sup_bot_sign))
                  (semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_ivl))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_parity))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            (bounded_semilattice_sup_bot_int_dom_ext
                              bounded_lattice_unit)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_congruence))
                              semilattice_sup_relc))))))),
                 (ownership_split_analysis_product
                   (ownership_split_lifted
                     ((semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign),
                       (ownership_split_gdefault_st
                         (global_name_literal, equal_literal)
                         (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                           order_top_sign))))
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                             order_top_ivl))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                               order_top_parity))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               ((bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                 (order_top_int_dom_ext
                                   bounded_lattice_unit)))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
                                       order_top_congruence))))
                               ownership_split_relc))))))))
               d (full_view
                   (bounded_semilattice_sup_bot_lifted
                     (semilattice_sup_analysis_product
                       (semilattice_sup_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_sign))
                       (semilattice_sup_analysis_product
                         (semilattice_sup_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_ivl))
                         (semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_parity))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       bounded_semilattice_sup_bot_congruence))
                                   semilattice_sup_relc))))))))
                   (split_global_at_lifted
                     ((semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_sign))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_ivl))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_parity))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
bounded_semilattice_sup_bot_congruence))
                                    semilattice_sup_relc))))))),
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_sign),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                                 order_top_sign))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                bounded_semilattice_sup_bot_ivl),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                                   order_top_ivl))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_parity),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                     order_top_parity))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      (bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit)),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       ((bounded_semilattice_sup_bot_int_dom_ext
  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
 (order_top_int_dom_ext bounded_lattice_unit)))))
                                 (ownership_split_analysis_product
                                   (ownership_split_lifted
                                     ((semilattice_sup_gdefault_st
(global_name_literal.infinite_key_global_name, equal_literal)
(bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
                                       (ownership_split_gdefault_st
 (global_name_literal, equal_literal)
 ((bounded_semilattice_sup_bot_int_dom_ext
    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
   (order_top_int_dom_ext bounded_lattice_unit)))))
                                   (ownership_split_analysis_product
                                     (ownership_split_lifted
                                       ((semilattice_sup_gdefault_st
  (global_name_literal.infinite_key_global_name, equal_literal)
  bounded_semilattice_sup_bot_congruence),
 (ownership_split_gdefault_st (global_name_literal, equal_literal)
   (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
     order_top_congruence))))
                                     ownership_split_relc)))))))))
                   (declared_global_vars p) e)));;

let rec mcp_place_rl
  pg = (match pg with Program_Globals_Flow_Sensitive -> (fun _ d -> d)
         | Program_Globals_Flow_Insensitive ->
           (fun _ ->
             split_rl_lifted
               ((semilattice_sup_analysis_product
                  (semilattice_sup_lifted
                    (semilattice_sup_gdefault_st
                      (global_name_literal.infinite_key_global_name,
                        equal_literal)
                      bounded_semilattice_sup_bot_sign))
                  (semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_ivl))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_parity))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            (bounded_semilattice_sup_bot_int_dom_ext
                              bounded_lattice_unit)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  bounded_semilattice_sup_bot_congruence))
                              semilattice_sup_relc))))))),
                 (ownership_split_analysis_product
                   (ownership_split_lifted
                     ((semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign),
                       (ownership_split_gdefault_st
                         (global_name_literal, equal_literal)
                         (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                           order_top_sign))))
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                             order_top_ivl))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                               order_top_parity))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               ((bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                 (order_top_int_dom_ext
                                   bounded_lattice_unit)))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
                                       order_top_congruence))))
                               ownership_split_relc))))))))));;

let rec mcp_run_of
  asa pg global seed route =
    solved_run_of linorder_literal (equal_exp, linorder_exp)
      ((equal_analysis_product
         (equal_lifted
           (equal_gdefault_st (infinite_key_literal, equal_literal)
             (equal_sign,
               bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot)))
         (equal_analysis_product
           (equal_lifted
             (equal_gdefault_st (infinite_key_literal, equal_literal)
               (equal_ivl,
                 bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot)))
           (equal_analysis_product
             (equal_lifted
               (equal_gdefault_st (infinite_key_literal, equal_literal)
                 (equal_parity,
                   bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot)))
             (equal_analysis_product
               (equal_lifted
                 (equal_gdefault_st (infinite_key_literal, equal_literal)
                   ((equal_int_dom_ext equal_unit),
                     (bounded_semilattice_sup_bot_int_dom_ext
                       bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
               (equal_analysis_product
                 (equal_lifted
                   (equal_gdefault_st (infinite_key_literal, equal_literal)
                     ((equal_int_dom_ext equal_unit),
                       (bounded_semilattice_sup_bot_int_dom_ext
                         bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                 (equal_analysis_product
                   (equal_lifted
                     (equal_gdefault_st (infinite_key_literal, equal_literal)
                       ((equal_int_dom_ext equal_unit),
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_literal, equal_literal)
                         (equal_congruence,
                           bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot)))
                     equal_relc))))))),
        (semilattice_sup_analysis_product
          (semilattice_sup_lifted
            (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
              bounded_semilattice_sup_bot_sign))
          (semilattice_sup_analysis_product
            (semilattice_sup_lifted
              (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
                bounded_semilattice_sup_bot_ivl))
            (semilattice_sup_analysis_product
              (semilattice_sup_lifted
                (semilattice_sup_gdefault_st
                  (infinite_key_literal, equal_literal)
                  bounded_semilattice_sup_bot_parity))
              (semilattice_sup_analysis_product
                (semilattice_sup_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_literal, equal_literal)
                    (bounded_semilattice_sup_bot_int_dom_ext
                      bounded_lattice_unit)))
                (semilattice_sup_analysis_product
                  (semilattice_sup_lifted
                    (semilattice_sup_gdefault_st
                      (infinite_key_literal, equal_literal)
                      (bounded_semilattice_sup_bot_int_dom_ext
                        bounded_lattice_unit)))
                  (semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit)))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_literal, equal_literal)
                          bounded_semilattice_sup_bot_congruence))
                      semilattice_sup_relc))))))))
      (mcp_comp asa) (mcp_emp asa) mcp_rd global seed route (mcp_place_cmb pg)
      (mcp_place_rl pg) (mcp_place_enter pg);;

let rec edge_reads
  a = sorted_list_of_set (equal_literal, linorder_literal)
        (sup_seta equal_literal (image exp_vnames (Set (edge_expressions a))));;

let rec activation
  asa = (if null asa then [Int_Analysis Refine_Fixpoint]
          else remdups equal_analysis_domain asa);;

let rec mcp_answer
  asa v q =
    fold (fun a r ->
           inf_query_lift (inf_int_dom_ext bounded_lattice_unit) r
             (value_answer (registration_of a) v q))
      asa (top_query_lifta (order_int_dom_ext bounded_lattice_unit));;

let rec int_of_char x = comp (fun a -> Int_of_integer a) integer_of_char x;;

let rec literal_key
  s = Key_List (map (fun c -> Key_Int (int_of_char c)) (explode s));;

let rec order_view_key
  v = (match v with None -> Key_List []
        | Some ps ->
          Key_List
            [Key_List
               (map (fun (a, b) -> Key_List [literal_key a; literal_key b])
                 ps)]);;

let rec congruence_key
  v = (match rep_congruence v with None -> Key_List []
        | Some (r, m) -> Key_List [Key_Int r; Key_Int m]);;

let rec parity_key = function PBot -> Key_Int zero_inta
                     | PEven -> Key_Int one_inta
                     | POdd -> Key_Int (Int_of_integer (Z.of_int 2))
                     | PTop -> Key_Int (Int_of_integer (Z.of_int 3));;

let rec sign_key = function SBot -> Key_Int zero_inta
                   | SNeg -> Key_Int one_inta
                   | SNonPos -> Key_Int (Int_of_integer (Z.of_int 2))
                   | SZero -> Key_Int (Int_of_integer (Z.of_int 3))
                   | SNonNeg -> Key_Int (Int_of_integer (Z.of_int 4))
                   | SPos -> Key_Int (Int_of_integer (Z.of_int 5))
                   | STop -> Key_Int (Int_of_integer (Z.of_int 6));;

let rec eint_key
  = function MinInf -> Key_List [Key_Int zero_inta]
    | Fin n -> Key_List [Key_Int one_inta; Key_Int n]
    | PlusInf -> Key_List [Key_Int (Int_of_integer (Z.of_int 2))];;

let rec ivl_key (Ivl (l, u)) = Key_List [eint_key l; eint_key u];;

let rec int_dom_key
  d = Key_List
        [sign_key (int_sign d); ivl_key (int_ivl d); parity_key (int_parity d);
          congruence_key (int_congruence d)];;

let rec abstract_value_key
  = function SignValue v -> Key_List [Key_Int zero_inta; sign_key v]
    | IntervalValue v -> Key_List [Key_Int one_inta; ivl_key v]
    | ParityValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 2)); parity_key v]
    | IntDomValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 3)); int_dom_key v]
    | IntDomOnceValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 4)); int_dom_key v]
    | IntDomNeverValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 5)); int_dom_key v]
    | CongruenceValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 6)); congruence_key v]
    | OrderValue v ->
        Key_List [Key_Int (Int_of_integer (Z.of_int 7)); order_view_key v];;

let rec mcp_ctx_key
  ctx = Key_List
          [Key_List
             (map abstract_value_key (map (fun a -> SignValue a) (slot1 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> IntervalValue a) (slot2 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> ParityValue a) (slot3 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> IntDomValue a) (slot4 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> IntDomOnceValue a) (slot5 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> IntDomNeverValue a) (slot6 ctx)));
            Key_List
              (map abstract_value_key
                (map (fun a -> CongruenceValue a) (slot7 ctx)));
            Key_List (map (fun _ -> Key_List []) (slot8 ctx))];;

let rec make
  proc_rep declared_global_vars =
    Imp_prog_ext (proc_rep, declared_global_vars, ());;

let rec mk_program
  ps m gv = make ((prog_main_name, Gproc_decl_ext ([], m, ())) :: ps) gv;;

let rec solve_c_traced _A _B (_C1, _C2, _C3)
  r t x =
    (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Start x) in
     let res = tD_side_rule_Interp_solve_c _A _B (_C1, _C2, _C3) r t x in
     let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Stop) in
      res);;

let rec mcp_solve_c _A _B
  r t x =
    solve_c_traced (equal_prod equal_cfg_node _A) _B
      ((equal_dg_state
         (equal_lifted
           (equal_analysis_product
             (equal_lifted
               (equal_gdefault_st (infinite_key_literal, equal_literal)
                 (equal_sign,
                   bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot)))
             (equal_analysis_product
               (equal_lifted
                 (equal_gdefault_st (infinite_key_literal, equal_literal)
                   (equal_ivl,
                     bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot)))
               (equal_analysis_product
                 (equal_lifted
                   (equal_gdefault_st (infinite_key_literal, equal_literal)
                     (equal_parity,
                       bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot)))
                 (equal_analysis_product
                   (equal_lifted
                     (equal_gdefault_st (infinite_key_literal, equal_literal)
                       ((equal_int_dom_ext equal_unit),
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_literal, equal_literal)
                         ((equal_int_dom_ext equal_unit),
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st
                           (infinite_key_literal, equal_literal)
                           ((equal_int_dom_ext equal_unit),
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (equal_congruence,
                               bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot)))
                         equal_relc))))))))
         (equal_lifted
           (equal_analysis_product
             (equal_lifted
               (equal_gdefault_st (infinite_key_literal, equal_literal)
                 (equal_sign,
                   bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot)))
             (equal_analysis_product
               (equal_lifted
                 (equal_gdefault_st (infinite_key_literal, equal_literal)
                   (equal_ivl,
                     bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot)))
               (equal_analysis_product
                 (equal_lifted
                   (equal_gdefault_st (infinite_key_literal, equal_literal)
                     (equal_parity,
                       bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot)))
                 (equal_analysis_product
                   (equal_lifted
                     (equal_gdefault_st (infinite_key_literal, equal_literal)
                       ((equal_int_dom_ext equal_unit),
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_literal, equal_literal)
                         ((equal_int_dom_ext equal_unit),
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st
                           (infinite_key_literal, equal_literal)
                           ((equal_int_dom_ext equal_unit),
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (equal_congruence,
                               bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot)))
                         equal_relc))))))))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_semilattice_sup_bot_lifted
            (bounded_semilattice_sup_bot_analysis_product
              (bounded_semilattice_sup_bot_lifted
                (bounded_semilattice_sup_bot_gdefault_st
                  (infinite_key_literal, equal_literal)
                  bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
              (bounded_semilattice_sup_bot_analysis_product
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_gdefault_st
                    (infinite_key_literal, equal_literal)
                    bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                (bounded_semilattice_sup_bot_analysis_product
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_gdefault_st
                      (infinite_key_literal, equal_literal)
                      bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                  (bounded_semilattice_sup_bot_analysis_product
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_literal, equal_literal)
                          (bounded_semilattice_sup_bot_int_dom_ext
                            bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_literal, equal_literal)
                            (bounded_semilattice_sup_bot_int_dom_ext
                              bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_literal, equal_literal)
                              bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                          bounded_semilattice_sup_bot_relc))))))).semilattice_sup_bounded_semilattice_sup_bot)
          (bounded_semilattice_sup_bot_lifted
            (bounded_semilattice_sup_bot_analysis_product
              (bounded_semilattice_sup_bot_lifted
                (bounded_semilattice_sup_bot_gdefault_st
                  (infinite_key_literal, equal_literal)
                  bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
              (bounded_semilattice_sup_bot_analysis_product
                (bounded_semilattice_sup_bot_lifted
                  (bounded_semilattice_sup_bot_gdefault_st
                    (infinite_key_literal, equal_literal)
                    bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                (bounded_semilattice_sup_bot_analysis_product
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_gdefault_st
                      (infinite_key_literal, equal_literal)
                      bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                  (bounded_semilattice_sup_bot_analysis_product
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_literal, equal_literal)
                          (bounded_semilattice_sup_bot_int_dom_ext
                            bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_literal, equal_literal)
                            (bounded_semilattice_sup_bot_int_dom_ext
                              bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_literal, equal_literal)
                              bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                          bounded_semilattice_sup_bot_relc))))))).semilattice_sup_bounded_semilattice_sup_bot)),
        (warrowing_dg_state
          ((bounded_semilattice_sup_bot_lifted
             (bounded_semilattice_sup_bot_analysis_product
               (bounded_semilattice_sup_bot_lifted
                 (bounded_semilattice_sup_bot_gdefault_st
                   (infinite_key_literal, equal_literal)
                   bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
               (bounded_semilattice_sup_bot_analysis_product
                 (bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                 (bounded_semilattice_sup_bot_analysis_product
                   (bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                   (bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                           bounded_semilattice_sup_bot_relc))))))).semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              ((bounded_semilattice_sup_bot_analysis_product
                 (bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
                 (bounded_semilattice_sup_bot_analysis_product
                   (bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                   (bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                             bounded_semilattice_sup_bot_relc))))))),
                (warrowing_analysis_product
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_sign),
                        (warrowing_gdefault_st
                          (infinite_key_literal, equal_literal)
                          (bounded_semilattice_sup_bot_sign, warrowing_sign)))))
                  ((bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                               bounded_semilattice_sup_bot_relc)))))),
                    (warrowing_analysis_product
                      ((bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot),
                        (warrowing_lifted
                          ((bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_ivl),
                            (warrowing_gdefault_st
                              (infinite_key_literal, equal_literal)
                              (bounded_semilattice_sup_bot_ivl,
                                warrowing_ivl)))))
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                 bounded_semilattice_sup_bot_relc))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_parity),
                                (warrowing_gdefault_st
                                  (infinite_key_literal, equal_literal)
                                  (bounded_semilattice_sup_bot_parity,
                                    warrowing_parity)))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                   bounded_semilattice_sup_bot_relc)))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)),
                                    (warrowing_gdefault_st
                                      (infinite_key_literal, equal_literal)
                                      ((bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit),
(warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                     bounded_semilattice_sup_bot_relc))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
                                    (warrowing_lifted
                                      ((bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
(warrowing_gdefault_st (infinite_key_literal, equal_literal)
  ((bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit),
    (warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext
   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_literal, equal_literal)
   bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                       bounded_semilattice_sup_bot_relc)),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_literal, equal_literal)
   (bounded_semilattice_sup_bot_int_dom_ext
     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st
     (infinite_key_literal, equal_literal)
     (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
    (warrowing_gdefault_st (infinite_key_literal, equal_literal)
      ((bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit),
        (warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st
     (infinite_key_literal, equal_literal)
     bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
 bounded_semilattice_sup_bot_relc),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_literal, equal_literal)
       bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_literal, equal_literal)
         bounded_semilattice_sup_bot_congruence),
        (warrowing_gdefault_st (infinite_key_literal, equal_literal)
          (bounded_semilattice_sup_bot_congruence, warrowing_congruence)))))
  (bounded_semilattice_sup_bot_relc, warrowing_relc)))))))))))))))))
          ((bounded_semilattice_sup_bot_lifted
             (bounded_semilattice_sup_bot_analysis_product
               (bounded_semilattice_sup_bot_lifted
                 (bounded_semilattice_sup_bot_gdefault_st
                   (infinite_key_literal, equal_literal)
                   bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
               (bounded_semilattice_sup_bot_analysis_product
                 (bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                 (bounded_semilattice_sup_bot_analysis_product
                   (bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                   (bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                           bounded_semilattice_sup_bot_relc))))))).semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              ((bounded_semilattice_sup_bot_analysis_product
                 (bounded_semilattice_sup_bot_lifted
                   (bounded_semilattice_sup_bot_gdefault_st
                     (infinite_key_literal, equal_literal)
                     bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot)
                 (bounded_semilattice_sup_bot_analysis_product
                   (bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                   (bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           (bounded_semilattice_sup_bot_int_dom_ext
                             bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                             bounded_semilattice_sup_bot_relc))))))),
                (warrowing_analysis_product
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_sign),
                        (warrowing_gdefault_st
                          (infinite_key_literal, equal_literal)
                          (bounded_semilattice_sup_bot_sign, warrowing_sign)))))
                  ((bounded_semilattice_sup_bot_analysis_product
                     (bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot)
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                               bounded_semilattice_sup_bot_relc)))))),
                    (warrowing_analysis_product
                      ((bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_ivl).semilattice_sup_bounded_semilattice_sup_bot),
                        (warrowing_lifted
                          ((bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_ivl),
                            (warrowing_gdefault_st
                              (infinite_key_literal, equal_literal)
                              (bounded_semilattice_sup_bot_ivl,
                                warrowing_ivl)))))
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                 bounded_semilattice_sup_bot_relc))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_literal, equal_literal)
                               bounded_semilattice_sup_bot_parity).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_parity),
                                (warrowing_gdefault_st
                                  (infinite_key_literal, equal_literal)
                                  (bounded_semilattice_sup_bot_parity,
                                    warrowing_parity)))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                   bounded_semilattice_sup_bot_relc)))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)),
                                    (warrowing_gdefault_st
                                      (infinite_key_literal, equal_literal)
                                      ((bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit),
(warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                     bounded_semilattice_sup_bot_relc))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
                                    (warrowing_lifted
                                      ((bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
(warrowing_gdefault_st (infinite_key_literal, equal_literal)
  ((bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit),
    (warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_literal, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext
   bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_literal, equal_literal)
   bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
                                       bounded_semilattice_sup_bot_relc)),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_literal, equal_literal)
   (bounded_semilattice_sup_bot_int_dom_ext
     bounded_lattice_unit)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st
     (infinite_key_literal, equal_literal)
     (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
    (warrowing_gdefault_st (infinite_key_literal, equal_literal)
      ((bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit),
        (warrowing_int_dom_ext (bounded_lattice_unit, warrowing_unit)))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st
     (infinite_key_literal, equal_literal)
     bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot)
 bounded_semilattice_sup_bot_relc),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_literal, equal_literal)
       bounded_semilattice_sup_bot_congruence).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_literal, equal_literal)
         bounded_semilattice_sup_bot_congruence),
        (warrowing_gdefault_st (infinite_key_literal, equal_literal)
          (bounded_semilattice_sup_bot_congruence, warrowing_congruence)))))
  (bounded_semilattice_sup_bot_relc, warrowing_relc)))))))))))))))))))
      r t x;;

let rec route_unit
  u ctx d ca =
    (let c = () in
     let _ = Solver_trace_hook.emit "route" (fun _ -> Ev_Route ((u, ctx), d, c))
       in
      c);;

let rec formals_context pars d = map d pars;;

let rec exec_formals_route _A
  g u ctx d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (default_st_to_fun equal_literal _A g
          (match d with Bot -> bot_gdefault_sta _A | Lifted d0 -> d0)));;

let rec mcp_formals_route
  asa g u ctx d ca =
    (let c =
       Product
         ((if membera equal_analysis_domain asa Sign_Analysis
            then exec_formals_route bot_sign g u []
                   (lift_get
                     (bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_sign))
                     slot1 d)
                   ca
            else []),
           Product
             ((if membera equal_analysis_domain asa Interval_Analysis
                then exec_formals_route bot_ivl g u []
                       (lift_get
                         (bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             bounded_semilattice_sup_bot_ivl))
                         slot2 d)
                       ca
                else []),
               Product
                 ((if membera equal_analysis_domain asa Parity_Analysis
                    then exec_formals_route bot_parity g u []
                           (lift_get
                             (bot_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 bounded_semilattice_sup_bot_parity))
                             slot3 d)
                           ca
                    else []),
                   Product
                     ((if membera equal_analysis_domain asa
                            (Int_Analysis Refine_Fixpoint)
                        then exec_formals_route
                               (bot_int_dom_ext bounded_lattice_unit) g u []
                               (lift_get
                                 (bot_lifted
                                   (semilattice_sup_gdefault_st
                                     (infinite_key_literal, equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)))
                                 slot4 d)
                               ca
                        else []),
                       Product
                         ((if membera equal_analysis_domain asa
                                (Int_Analysis Refine_Once)
                            then exec_formals_route
                                   (bot_int_dom_ext bounded_lattice_unit) g u []
                                   (lift_get
                                     (bot_lifted
                                       (semilattice_sup_gdefault_st
 (infinite_key_literal, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)))
                                     slot5 d)
                                   ca
                            else []),
                           Product
                             ((if membera equal_analysis_domain asa
                                    (Int_Analysis Refine_Never)
                                then exec_formals_route
                                       (bot_int_dom_ext bounded_lattice_unit) g
                                       u []
                                       (lift_get
 (bot_lifted
   (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
     (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)))
 slot6 d)
                                       ca
                                else []),
                               Product
                                 ((if membera equal_analysis_domain asa
Congruence_Analysis
                                    then exec_formals_route bot_congruence g u
   [] (lift_get
        (bot_lifted
          (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
            bounded_semilattice_sup_bot_congruence))
        slot7 d)
   ca
                                    else []),
                                   (if membera equal_analysis_domain asa
 Order_Analysis
                                     then [] else []))))))))
       in
     let _ = Solver_trace_hook.emit "route" (fun _ -> Ev_Route ((u, ctx), d, c))
       in
      c);;

let rec key_of_global_unknown = function Analysis_Buffer -> Trace_Buffer
                                | Analysis_Global x -> Trace_Global x
                                | Activation_Seed (n, c) -> Trace_Seed (n, c);;

let rec value_display
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = value_display;;

let rec mcp_render
  asa vars v =
    map (fun a -> (a, value_display (registration_of a) v vars)) asa;;

let rec mcp_trace_printers
  pg asa p ctx_view =
    (let raw =
       (fun vs d ->
         map_lift (mcp_render (activation asa) vs)
           (map_lift (mcp_rd (declared_global p)) d))
       in
     let view =
       (fun d ->
         raw (program_vars p)
           (canonicalize_lift (mcp_emp (activation asa) p) d))
       in
     let local =
       (match pg with Program_Globals_Flow_Sensitive -> view
         | Program_Globals_Flow_Insensitive ->
           raw (filtera (fun x -> not (declared_global p x)) (program_vars p)))
       in
     let globals =
       (fun a ->
         (match a with None -> filtera (declared_global p) (program_vars p)
           | Some x -> [x]))
       in
      Trace_Printers
        (ctx_view, key_of_global_unknown, (fun d -> local (dg_local d)),
          (fun n d -> raw (globals n) (dg_global d)), local));;

let rec cs_route
  k u ctx d ca =
    (let c = take k (u :: ctx) in
     let _ = Solver_trace_hook.emit "route" (fun _ -> Ev_Route ((u, ctx), d, c))
       in
      c);;

let rec context_values
  (Analysis_registration_ext
    (field_spec, field_live, field_empty, value_answer, value_display,
      context_values, more))
    = context_values;;

let rec mcp_ctx_values
  asa ctx = maps (fun a -> context_values (registration_of a) ctx) asa;;

let rec mcp_place_inits
  pg asa =
    (match pg with Program_Globals_Flow_Sensitive -> (fun _ _ -> [])
      | Program_Globals_Flow_Insensitive ->
        (fun _ p ->
          map (fun x ->
                (x, split_global_at_lifted
                      ((semilattice_sup_analysis_product
                         (semilattice_sup_lifted
                           (semilattice_sup_gdefault_st
                             (global_name_literal.infinite_key_global_name,
                               equal_literal)
                             bounded_semilattice_sup_bot_sign))
                         (semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (global_name_literal.infinite_key_global_name,
                                 equal_literal)
                               bounded_semilattice_sup_bot_ivl))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (global_name_literal.infinite_key_global_name,
                                   equal_literal)
                                 bounded_semilattice_sup_bot_parity))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (global_name_literal.infinite_key_global_name,
                                     equal_literal)
                                   (bounded_semilattice_sup_bot_int_dom_ext
                                     bounded_lattice_unit)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (global_name_literal.infinite_key_global_name,
                                       equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (global_name_literal.infinite_key_global_name,
 equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (global_name_literal.infinite_key_global_name, equal_literal)
 bounded_semilattice_sup_bot_congruence))
                                     semilattice_sup_relc))))))),
                        (ownership_split_analysis_product
                          (ownership_split_lifted
                            ((semilattice_sup_gdefault_st
                               (global_name_literal.infinite_key_global_name,
                                 equal_literal)
                               bounded_semilattice_sup_bot_sign),
                              (ownership_split_gdefault_st
                                (global_name_literal, equal_literal)
                                (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                                  order_top_sign))))
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (global_name_literal.infinite_key_global_name,
                                   equal_literal)
                                 bounded_semilattice_sup_bot_ivl),
                                (ownership_split_gdefault_st
                                  (global_name_literal, equal_literal)
                                  (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                                    order_top_ivl))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (global_name_literal.infinite_key_global_name,
                                     equal_literal)
                                   bounded_semilattice_sup_bot_parity),
                                  (ownership_split_gdefault_st
                                    (global_name_literal, equal_literal)
                                    (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                      order_top_parity))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (global_name_literal.infinite_key_global_name,
                                       equal_literal)
                                     (bounded_semilattice_sup_bot_int_dom_ext
                                       bounded_lattice_unit)),
                                    (ownership_split_gdefault_st
                                      (global_name_literal, equal_literal)
                                      ((bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
(order_top_int_dom_ext bounded_lattice_unit)))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (global_name_literal.infinite_key_global_name,
 equal_literal)
                                       (bounded_semilattice_sup_bot_int_dom_ext
 bounded_lattice_unit)),
                                      (ownership_split_gdefault_st
(global_name_literal, equal_literal)
((bounded_semilattice_sup_bot_int_dom_ext
   bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
  (order_top_int_dom_ext bounded_lattice_unit)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (global_name_literal.infinite_key_global_name, equal_literal)
 (bounded_semilattice_sup_bot_int_dom_ext bounded_lattice_unit)),
(ownership_split_gdefault_st (global_name_literal, equal_literal)
  ((bounded_semilattice_sup_bot_int_dom_ext
     bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
    (order_top_int_dom_ext bounded_lattice_unit)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (global_name_literal.infinite_key_global_name, equal_literal)
   bounded_semilattice_sup_bot_congruence),
  (ownership_split_gdefault_st (global_name_literal, equal_literal)
    (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
      order_top_congruence))))
                                      ownership_split_relc))))))))
                      x (Lifted (mcp_init asa))))
            (declared_global_vars p)));;

let rec man_sideg
  (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) = man_sideg;;

let rec publish_at
  m rg x2 r = match m, rg, x2, r with m, rg, [], r -> sp_return ()
    | m, rg, x :: xs, r ->
        sp_bind (man_sideg m x (rg x r)) (fun _ -> publish_at m rg xs r);;

let rec keyed_combine_transfer _A
  cmb rl rg free w h m de =
    sp_bind
      (publish_at m rg w (h (cmb (man_local m) (free [])) (cmb de (free []))))
      (fun _ ->
        sp_return (rl (h (cmb (man_local m) (free [])) (cmb de (free [])))));;

let rec join_list _A
  xs = foldr (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup)
         xs (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec man_global
  (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) = man_global;;

let rec read_view _C
  m rg x2 acc = match m, rg, x2, acc with m, rg, [], acc -> sp_return acc
    | m, rg, x :: xs, acc ->
        sp_bind (man_global m x)
          (fun g ->
            read_view _C m rg xs (sup _C.sup_semilattice_sup (rg x g) acc));;

let rec keyed_enter_transfer _A
  cmb rl rg free r w en m =
    sp_bind
      (read_view _A.semilattice_sup_bounded_semilattice_sup_bot m rg r (free r))
      (fun g ->
        sp_bind
          (publish_at m rg w
            (join_list _A (map (fun (_, e) -> e) (en (cmb (man_local m) g)))))
          (fun _ ->
            sp_return
              (map (fun (c, e) -> (rl c, rl e)) (en (cmb (man_local m) g)))));;

let rec keyed_transfer _A
  cmb rl rg free r w f m =
    sp_bind
      (read_view _A.semilattice_sup_bounded_semilattice_sup_bot m rg r (free r))
      (fun g ->
        sp_bind (publish_at m rg w (f (cmb (man_local m) g)))
          (fun _ -> sp_return (rl (f (cmb (man_local m) g)))));;

let rec edge_writes = function EA_Assign (x, a) -> [x]
                      | EA_Special (sc, x) -> [x]
                      | EA_Ret (e, p) -> [ret_var]
                      | EA_Nop -> []
                      | EA_Assume v -> []
                      | EA_AssumeNot v -> []
                      | EA_Body v -> []
                      | EA_Check (v, va) -> [];;

let rec edge_global_writes g a = global_names_in g (edge_writes a);;

let rec edge_global_reads g a = global_names_in g (edge_reads a);;

let rec keyed_split_spec _A
  g cmb rl rg free c =
    (let step =
       (fun a ->
         keyed_transfer _A cmb rl rg free (edge_global_reads g a)
           (edge_global_writes g a) (closed_step equal_exp c a))
       in
      dgs_combine_assign_update
        (fun _ ci ->
          keyed_combine_transfer _A cmb rl rg free
            (global_names_in g
              (match ci_dst ci with None -> [] | Some x -> [x]))
            (fun dc de ->
              ls_combine_assign c (ls_channel equal_exp c de) ci
                (ls_combine_env c (ls_channel equal_exp c dc)
                  (ls_channel equal_exp c de) ci dc de)
                de))
        (dgs_event_update (fun _ ev -> step (event_action ev))
          (dgs_enter_update
            (fun _ ci ->
              keyed_enter_transfer _A cmb rl rg free
                (call_global_reads g (ci_args ci))
                (global_names_in g (ci_formals ci))
                (fun d -> ls_enter c (ls_channel equal_exp c d) ci (d, d)))
            (dgs_return_update (fun _ e p -> step (EA_Ret (e, p)))
              (dgs_body_update (fun _ p -> step (EA_Body p))
                (dgs_branch_update
                  (fun _ b pol ->
                    step (if pol then EA_Assume b else EA_AssumeNot b))
                  (dgs_special_update (fun _ sc x -> step (EA_Special (sc, x)))
                    (dgs_assign_update (fun _ x e -> step (EA_Assign (x, e)))
                      (dgs_skip_update (fun _ -> step EA_Nop)
                        local_dg_spec_template)))))))));;

let rec mcp_place_spec
  pg = (match pg
         with Program_Globals_Flow_Sensitive ->
           (fun _ ->
             dg_spec_of equal_exp
               (bot_lifted
                 (semilattice_sup_analysis_product
                   (semilattice_sup_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (semilattice_sup_analysis_product
                     (semilattice_sup_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (semilattice_sup_analysis_product
                       (semilattice_sup_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (semilattice_sup_analysis_product
                         (semilattice_sup_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               semilattice_sup_relc)))))))))
         | Program_Globals_Flow_Insensitive ->
           (fun p ->
             keyed_split_spec
               (bounded_semilattice_sup_bot_lifted
                 (semilattice_sup_analysis_product
                   (semilattice_sup_lifted
                     (semilattice_sup_gdefault_st
                       (infinite_key_literal, equal_literal)
                       bounded_semilattice_sup_bot_sign))
                   (semilattice_sup_analysis_product
                     (semilattice_sup_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_literal, equal_literal)
                         bounded_semilattice_sup_bot_ivl))
                     (semilattice_sup_analysis_product
                       (semilattice_sup_lifted
                         (semilattice_sup_gdefault_st
                           (infinite_key_literal, equal_literal)
                           bounded_semilattice_sup_bot_parity))
                       (semilattice_sup_analysis_product
                         (semilattice_sup_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_literal, equal_literal)
                             (bounded_semilattice_sup_bot_int_dom_ext
                               bounded_lattice_unit)))
                         (semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (infinite_key_literal, equal_literal)
                               (bounded_semilattice_sup_bot_int_dom_ext
                                 bounded_lattice_unit)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (infinite_key_literal, equal_literal)
                                 (bounded_semilattice_sup_bot_int_dom_ext
                                   bounded_lattice_unit)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (infinite_key_literal, equal_literal)
                                   bounded_semilattice_sup_bot_congruence))
                               semilattice_sup_relc))))))))
               (declared_global p)
               (split_cmb_lifted
                 ((semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence))
                                semilattice_sup_relc))))))),
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_sign),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                             order_top_sign))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_ivl),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                               order_top_ivl))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_parity),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                 order_top_parity))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      bounded_semilattice_sup_bot_congruence),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
 order_top_congruence))))
                                 ownership_split_relc)))))))))
               (split_rl_lifted
                 ((semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence))
                                semilattice_sup_relc))))))),
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_sign),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                             order_top_sign))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_ivl),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                               order_top_ivl))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_parity),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                 order_top_parity))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      bounded_semilattice_sup_bot_congruence),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
 order_top_congruence))))
                                 ownership_split_relc)))))))))
               (split_global_at_lifted
                 ((semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence))
                                semilattice_sup_relc))))))),
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_sign),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                             order_top_sign))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_ivl),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                               order_top_ivl))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_parity),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                 order_top_parity))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      bounded_semilattice_sup_bot_congruence),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
 order_top_congruence))))
                                 ownership_split_relc)))))))))
               (split_free_lifted
                 ((semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (global_name_literal.infinite_key_global_name,
                          equal_literal)
                        bounded_semilattice_sup_bot_sign))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_ivl))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_parity))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              (bounded_semilattice_sup_bot_int_dom_ext
                                bounded_lattice_unit)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    bounded_semilattice_sup_bot_congruence))
                                semilattice_sup_relc))))))),
                   (ownership_split_analysis_product
                     (ownership_split_lifted
                       ((semilattice_sup_gdefault_st
                          (global_name_literal.infinite_key_global_name,
                            equal_literal)
                          bounded_semilattice_sup_bot_sign),
                         (ownership_split_gdefault_st
                           (global_name_literal, equal_literal)
                           (bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot,
                             order_top_sign))))
                     (ownership_split_analysis_product
                       (ownership_split_lifted
                         ((semilattice_sup_gdefault_st
                            (global_name_literal.infinite_key_global_name,
                              equal_literal)
                            bounded_semilattice_sup_bot_ivl),
                           (ownership_split_gdefault_st
                             (global_name_literal, equal_literal)
                             (bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot,
                               order_top_ivl))))
                       (ownership_split_analysis_product
                         (ownership_split_lifted
                           ((semilattice_sup_gdefault_st
                              (global_name_literal.infinite_key_global_name,
                                equal_literal)
                              bounded_semilattice_sup_bot_parity),
                             (ownership_split_gdefault_st
                               (global_name_literal, equal_literal)
                               (bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot,
                                 order_top_parity))))
                         (ownership_split_analysis_product
                           (ownership_split_lifted
                             ((semilattice_sup_gdefault_st
                                (global_name_literal.infinite_key_global_name,
                                  equal_literal)
                                (bounded_semilattice_sup_bot_int_dom_ext
                                  bounded_lattice_unit)),
                               (ownership_split_gdefault_st
                                 (global_name_literal, equal_literal)
                                 ((bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                   (order_top_int_dom_ext
                                     bounded_lattice_unit)))))
                           (ownership_split_analysis_product
                             (ownership_split_lifted
                               ((semilattice_sup_gdefault_st
                                  (global_name_literal.infinite_key_global_name,
                                    equal_literal)
                                  (bounded_semilattice_sup_bot_int_dom_ext
                                    bounded_lattice_unit)),
                                 (ownership_split_gdefault_st
                                   (global_name_literal, equal_literal)
                                   ((bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                     (order_top_int_dom_ext
                                       bounded_lattice_unit)))))
                             (ownership_split_analysis_product
                               (ownership_split_lifted
                                 ((semilattice_sup_gdefault_st
                                    (global_name_literal.infinite_key_global_name,
                                      equal_literal)
                                    (bounded_semilattice_sup_bot_int_dom_ext
                                      bounded_lattice_unit)),
                                   (ownership_split_gdefault_st
                                     (global_name_literal, equal_literal)
                                     ((bounded_semilattice_sup_bot_int_dom_ext
bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot,
                                       (order_top_int_dom_ext
 bounded_lattice_unit)))))
                               (ownership_split_analysis_product
                                 (ownership_split_lifted
                                   ((semilattice_sup_gdefault_st
                                      (global_name_literal.infinite_key_global_name,
equal_literal)
                                      bounded_semilattice_sup_bot_congruence),
                                     (ownership_split_gdefault_st
                                       (global_name_literal, equal_literal)
                                       (bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot,
 order_top_congruence))))
                                 ownership_split_relc)))))))))));;

let rec mcp_place_rg pg = (fun _ _ -> Bot);;

let rec mcp_equations _A _B
  asa pg buffer global seed route root =
    equations (equal_literal, linorder_literal) (equal_exp, linorder_exp)
      ((equal_analysis_product
         (equal_lifted
           (equal_gdefault_st (infinite_key_literal, equal_literal)
             (equal_sign,
               bounded_semilattice_sup_bot_sign.order_bot_bounded_semilattice_sup_bot)))
         (equal_analysis_product
           (equal_lifted
             (equal_gdefault_st (infinite_key_literal, equal_literal)
               (equal_ivl,
                 bounded_semilattice_sup_bot_ivl.order_bot_bounded_semilattice_sup_bot)))
           (equal_analysis_product
             (equal_lifted
               (equal_gdefault_st (infinite_key_literal, equal_literal)
                 (equal_parity,
                   bounded_semilattice_sup_bot_parity.order_bot_bounded_semilattice_sup_bot)))
             (equal_analysis_product
               (equal_lifted
                 (equal_gdefault_st (infinite_key_literal, equal_literal)
                   ((equal_int_dom_ext equal_unit),
                     (bounded_semilattice_sup_bot_int_dom_ext
                       bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
               (equal_analysis_product
                 (equal_lifted
                   (equal_gdefault_st (infinite_key_literal, equal_literal)
                     ((equal_int_dom_ext equal_unit),
                       (bounded_semilattice_sup_bot_int_dom_ext
                         bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                 (equal_analysis_product
                   (equal_lifted
                     (equal_gdefault_st (infinite_key_literal, equal_literal)
                       ((equal_int_dom_ext equal_unit),
                         (bounded_semilattice_sup_bot_int_dom_ext
                           bounded_lattice_unit).order_bot_bounded_semilattice_sup_bot)))
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_literal, equal_literal)
                         (equal_congruence,
                           bounded_semilattice_sup_bot_congruence.order_bot_bounded_semilattice_sup_bot)))
                     equal_relc))))))),
        (semilattice_sup_analysis_product
          (semilattice_sup_lifted
            (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
              bounded_semilattice_sup_bot_sign))
          (semilattice_sup_analysis_product
            (semilattice_sup_lifted
              (semilattice_sup_gdefault_st (infinite_key_literal, equal_literal)
                bounded_semilattice_sup_bot_ivl))
            (semilattice_sup_analysis_product
              (semilattice_sup_lifted
                (semilattice_sup_gdefault_st
                  (infinite_key_literal, equal_literal)
                  bounded_semilattice_sup_bot_parity))
              (semilattice_sup_analysis_product
                (semilattice_sup_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_literal, equal_literal)
                    (bounded_semilattice_sup_bot_int_dom_ext
                      bounded_lattice_unit)))
                (semilattice_sup_analysis_product
                  (semilattice_sup_lifted
                    (semilattice_sup_gdefault_st
                      (infinite_key_literal, equal_literal)
                      (bounded_semilattice_sup_bot_int_dom_ext
                        bounded_lattice_unit)))
                  (semilattice_sup_analysis_product
                    (semilattice_sup_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_literal, equal_literal)
                        (bounded_semilattice_sup_bot_int_dom_ext
                          bounded_lattice_unit)))
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_literal, equal_literal)
                          bounded_semilattice_sup_bot_congruence))
                      semilattice_sup_relc))))))))
      _A _B (mcp_comp asa) (mcp_init asa) buffer global seed route root
      (mcp_place_spec pg) (mcp_place_rg pg) (mcp_place_inits pg asa) prog_cfg
      (fun _ -> FunctionEntry prog_main_name);;

let rec entry_ctx_key
  asa ctx =
    Key_List
      [Key_List (map abstract_value_key (mcp_ctx_values asa ctx));
        mcp_ctx_key ctx];;

let rec classify_answer
  = function QBot -> Bot
    | QLifted v ->
        (if equal_option equal_int (answer_const (QLifted v)) (Some one_inta)
          then Lifted Check_Proved
          else (if equal_option equal_int (answer_const (QLifted v))
                     (Some zero_inta)
                 then Lifted Check_Refuted else Lifted Check_Unknown))
    | QTop ->
        (if equal_option equal_int (answer_const QTop) (Some one_inta)
          then Lifted Check_Proved
          else (if equal_option equal_int (answer_const QTop) (Some zero_inta)
                 then Lifted Check_Refuted else Lifted Check_Unknown));;

let rec check_truth_exp
  c = (if bool_valued c then c else NotEq (c, N zero_inta));;

let rec answer_check
  q c v =
    (match classify_answer (q v (EvalInt (check_truth_exp c)))
      with Bot -> Check_Unknown | Lifted r -> r);;

let rec mcp_classify asa = answer_check (mcp_answer asa);;

let mcp_root_ctx :
  ((sign list),
    ((ivl list),
      ((parity list),
        ((unit int_dom_ext list),
          ((unit int_dom_ext list),
            ((unit int_dom_ext list),
              ((congruence list), (unit list)) analysis_product)
              analysis_product)
            analysis_product)
          analysis_product)
        analysis_product)
      analysis_product)
    analysis_product
  = Product
      ([], Product
             ([], Product
                    ([], Product
                           ([], Product
                                  ([], Product ([], Product ([], [])))))));;

let rec analysis_report_of
  x0 p = match x0, p with
    Analysis_Config (asa, r, Ctx_None, pg), p ->
      (let _ =
         Solver_trace_hook.emit "run"
           (fun _ -> mcp_trace_printers pg asa p (fun _ -> Context_Unit))
         in
        map_option
          (fun sol ->
            report_of equal_unit (Analysis_Config (asa, r, Ctx_None, pg))
              (fun _ -> Key_List []) (fun _ -> Report_Unit)
              (mcp_classify (activation asa))
              (mcp_run_of (activation asa) pg (fun a -> Analysis_Global a)
                (fun a b -> Activation_Seed (a, b)) (fun _ -> route_unit)
                (declared_global p) p sol)
              p)
          (mcp_solve_c equal_unit
            (equal_global_unknown equal_literal equal_unit) r
            (mcp_equations (equal_global_unknown equal_literal equal_unit)
              equal_unit (activation asa) pg Analysis_Buffer
              (fun a -> Analysis_Global a) (fun a b -> Activation_Seed (a, b))
              (fun _ -> route_unit) () (declared_global p) p)
            (cfg_exit (prog_cfg p), ())))
    | Analysis_Config (asa, r, Ctx_EntryState, pg), p ->
        (let _ =
           Solver_trace_hook.emit "run"
             (fun _ ->
               mcp_trace_printers pg asa p
                 (fun ctx ->
                   Context_Entry (mcp_ctx_values (activation asa) ctx)))
           in
          map_option
            (fun sol ->
              report_of
                (equal_analysis_product (equal_list equal_sign)
                  (equal_analysis_product (equal_list equal_ivl)
                    (equal_analysis_product (equal_list equal_parity)
                      (equal_analysis_product
                        (equal_list (equal_int_dom_ext equal_unit))
                        (equal_analysis_product
                          (equal_list (equal_int_dom_ext equal_unit))
                          (equal_analysis_product
                            (equal_list (equal_int_dom_ext equal_unit))
                            (equal_analysis_product
                              (equal_list equal_congruence)
                              (equal_list equal_unit))))))))
                (Analysis_Config (asa, r, Ctx_EntryState, pg))
                (entry_ctx_key (activation asa)) (fun a -> Report_Entry a)
                (mcp_classify (activation asa))
                (mcp_run_of (activation asa) pg (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b))
                  (mcp_formals_route (activation asa)) (declared_global p) p
                  sol)
                p)
            (mcp_solve_c
              (equal_analysis_product (equal_list equal_sign)
                (equal_analysis_product (equal_list equal_ivl)
                  (equal_analysis_product (equal_list equal_parity)
                    (equal_analysis_product
                      (equal_list (equal_int_dom_ext equal_unit))
                      (equal_analysis_product
                        (equal_list (equal_int_dom_ext equal_unit))
                        (equal_analysis_product
                          (equal_list (equal_int_dom_ext equal_unit))
                          (equal_analysis_product (equal_list equal_congruence)
                            (equal_list equal_unit))))))))
              (equal_global_unknown equal_literal
                (equal_analysis_product (equal_list equal_sign)
                  (equal_analysis_product (equal_list equal_ivl)
                    (equal_analysis_product (equal_list equal_parity)
                      (equal_analysis_product
                        (equal_list (equal_int_dom_ext equal_unit))
                        (equal_analysis_product
                          (equal_list (equal_int_dom_ext equal_unit))
                          (equal_analysis_product
                            (equal_list (equal_int_dom_ext equal_unit))
                            (equal_analysis_product
                              (equal_list equal_congruence)
                              (equal_list equal_unit)))))))))
              r (mcp_equations
                  (equal_global_unknown equal_literal
                    (equal_analysis_product (equal_list equal_sign)
                      (equal_analysis_product (equal_list equal_ivl)
                        (equal_analysis_product (equal_list equal_parity)
                          (equal_analysis_product
                            (equal_list (equal_int_dom_ext equal_unit))
                            (equal_analysis_product
                              (equal_list (equal_int_dom_ext equal_unit))
                              (equal_analysis_product
                                (equal_list (equal_int_dom_ext equal_unit))
                                (equal_analysis_product
                                  (equal_list equal_congruence)
                                  (equal_list equal_unit)))))))))
                  (equal_analysis_product (equal_list equal_sign)
                    (equal_analysis_product (equal_list equal_ivl)
                      (equal_analysis_product (equal_list equal_parity)
                        (equal_analysis_product
                          (equal_list (equal_int_dom_ext equal_unit))
                          (equal_analysis_product
                            (equal_list (equal_int_dom_ext equal_unit))
                            (equal_analysis_product
                              (equal_list (equal_int_dom_ext equal_unit))
                              (equal_analysis_product
                                (equal_list equal_congruence)
                                (equal_list equal_unit))))))))
                  (activation asa) pg Analysis_Buffer
                  (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b))
                  (mcp_formals_route (activation asa)) mcp_root_ctx
                  (declared_global p) p)
              (cfg_exit (prog_cfg p), mcp_root_ctx)))
    | Analysis_Config (asa, r, Ctx_CallString k, pg), p ->
        (let _ =
           Solver_trace_hook.emit "run"
             (fun _ ->
               mcp_trace_printers pg asa p (fun a -> Context_Call_String a))
           in
          map_option
            (fun sol ->
              report_of (equal_list equal_cfg_node)
                (Analysis_Config (asa, r, Ctx_CallString k, pg))
                (fun ctx -> Key_List (map (fun a -> Key_Node a) ctx))
                (fun a -> Report_Call_String a) (mcp_classify (activation asa))
                (mcp_run_of (activation asa) pg (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b)) (fun _ -> cs_route k)
                  (declared_global p) p sol)
                p)
            (mcp_solve_c (equal_list equal_cfg_node)
              (equal_global_unknown equal_literal (equal_list equal_cfg_node)) r
              (mcp_equations
                (equal_global_unknown equal_literal (equal_list equal_cfg_node))
                (equal_list equal_cfg_node) (activation asa) pg Analysis_Buffer
                (fun a -> Analysis_Global a) (fun a b -> Activation_Seed (a, b))
                (fun _ -> cs_route k) [] (declared_global p) p)
              (cfg_exit (prog_cfg p), [])));;

let rec config_analyses (Analysis_Config (x1, x2, x3, x4)) = x1;;

let rec valid_config
  config =
    not (null (config_analyses config)) &&
      distinct equal_analysis_domain (config_analyses config);;

let rec run_voblint
  config p =
    (if not (valid_config config) then Invalid_Activation
      else (if not (wf_program_compile_input_exec p) then Malformed_Program
             else (match analysis_report_of config p with None -> No_Answer
                    | Some a -> Analysed a)));;

let rec report_routes
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_routes;;

let rec route_targets
  (Call_route_ext
    (route_point, route_context, route_callee, route_targets, more))
    = route_targets;;

let rec route_context
  (Call_route_ext
    (route_point, route_context, route_callee, route_targets, more))
    = route_context;;

let rec route_point
  (Call_route_ext
    (route_point, route_context, route_callee, route_targets, more))
    = route_point;;

let rec report_route_targets
  res u c =
    concat
      (map_filter
        (fun x ->
          (if equal_cfg_nodea (route_point x) u &&
                equal_nata (route_context x) c
            then Some (route_targets x) else None))
        (report_routes res));;

let rec callee_of
  entry =
    (match entry with Statement _ -> "" | FunctionEntry f -> f
      | FunctionResult f -> f);;

let rec call_deps
  res g rows u c e =
    (let (ua, (ca, (entry, after))) = e in
      (if not (equal_cfg_nodea ua u) then []
        else (let targets = report_route_targets res u c in
              let result = FunctionResult (callee_of entry) in
               maps (fun t ->
                      (if membera (equal_prod equal_cfg_node equal_nat) rows
                            (entry, t)
                        then [(Local_Node (u, c),
                                (Enter_Dep ca, Local_Node (entry, t)))]
                        else []) @
                        (if membera (equal_prod equal_cfg_node equal_nat) rows
                              (result, t) &&
                              membera (equal_prod equal_cfg_node equal_nat) rows
                                (after, c)
                          then [(Local_Node (result, t),
                                  (Combine_Dep ca, Local_Node (after, c)))]
                          else []))
                 targets @
                 (if membera (equal_prod equal_cfg_node equal_nat) rows
                       (after, c)
                   then (Local_Node (u, c),
                          (Continue_Dep ca, Local_Node (after, c))) ::
                          (let CallEdge (dst, pars, args) = ca in
                            map (fun x ->
                                  (Global_Node x,
                                    (Global_Read, Local_Node (after, c))))
                              (call_global_reads g args) @
                              map (fun x ->
                                    (Local_Node (after, c),
                                      (Global_Write, Global_Node x)))
                                (global_names_in g
                                  ((match dst with None -> [] | Some x -> [x]) @
                                    pars)))
                   else []))));;

let rec intra_deps
  g rows u c e =
    (let (ua, (a, v)) = e in
      (if equal_cfg_nodea ua u &&
            membera (equal_prod equal_cfg_node equal_nat) rows (v, c)
        then (Local_Node (u, c), (Intra_Dep a, Local_Node (v, c))) ::
               map (fun x -> (Global_Node x, (Global_Read, Local_Node (v, c))))
                 (edge_global_reads g a) @
                 map (fun x ->
                       (Local_Node (v, c), (Global_Write, Global_Node x)))
                   (edge_global_writes g a)
        else []));;

let rec cfg_points
  x = cfg_node_list (equal_literal, linorder_literal) (equal_exp, linorder_exp)
        x;;

let rec report_diagnostics
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_diagnostics;;

let rec report_contexts
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_contexts;;

let rec report_globals
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_globals;;

let rec report_states
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_states;;

let rec report_config
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_config;;

let rec report_checks
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_checks;;

let rec report_vars
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_vars;;

let rec report_cfg
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_cfg;;

let rec state_steps
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_steps;;

let rec state_point
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_point;;

let rec report_steps_join
  res v =
    (match
      map_filter
        (fun x ->
          (if equal_cfg_nodea (state_point x) v then Some (state_steps x)
            else None))
        (report_states res)
      with [] -> []
      | s :: ss ->
        fold (fun xs ys ->
               map (fun (a, b) ->
                     (let (w, aa) = a in
                       (fun (_, ba) ->
                         (w, vjoin_lifted
                               (join_val_analysis_product
                                 (join_val_lifted
                                   (join_val_fun semilattice_sup_sign))
                                 (join_val_analysis_product
                                   (join_val_lifted
                                     (join_val_fun semilattice_sup_ivl))
                                   (join_val_analysis_product
                                     (join_val_lifted
                                       (join_val_fun semilattice_sup_parity))
                                     (join_val_analysis_product
                                       (join_val_lifted
 (join_val_fun (semilattice_sup_int_dom_ext bounded_lattice_unit)))
                                       (join_val_analysis_product
 (join_val_lifted
   (join_val_fun (semilattice_sup_int_dom_ext bounded_lattice_unit)))
 (join_val_analysis_product
   (join_val_lifted
     (join_val_fun (semilattice_sup_int_dom_ext bounded_lattice_unit)))
   (join_val_analysis_product
     (join_val_lifted (join_val_fun semilattice_sup_congruence))
     join_val_relc)))))))
                               aa ba)))
                       b)
                 (zip xs ys))
          ss s);;

let rec state_value
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_value;;

let rec report_point_join
  res v =
    fold (vjoin_lifted
           (join_val_analysis_product
             (join_val_lifted (join_val_fun semilattice_sup_sign))
             (join_val_analysis_product
               (join_val_lifted (join_val_fun semilattice_sup_ivl))
               (join_val_analysis_product
                 (join_val_lifted (join_val_fun semilattice_sup_parity))
                 (join_val_analysis_product
                   (join_val_lifted
                     (join_val_fun
                       (semilattice_sup_int_dom_ext bounded_lattice_unit)))
                   (join_val_analysis_product
                     (join_val_lifted
                       (join_val_fun
                         (semilattice_sup_int_dom_ext bounded_lattice_unit)))
                     (join_val_analysis_product
                       (join_val_lifted
                         (join_val_fun
                           (semilattice_sup_int_dom_ext bounded_lattice_unit)))
                       (join_val_analysis_product
                         (join_val_lifted
                           (join_val_fun semilattice_sup_congruence))
                         join_val_relc))))))))
      (map_filter
        (fun x ->
          (if equal_cfg_nodea (state_point x) v then Some (state_value x)
            else None))
        (report_states res))
      Bot;;

let rec map_field_state
  f x1 = match f, x1 with
    f, Field_Store bs -> Field_Store (map (fun (x, v) -> (x, f v)) bs)
    | f, Field_Whole v -> Field_Whole (f v);;

let rec map_analysis_view f = map (fun (a, s) -> (a, map_field_state f s));;

let rec global_unknown
  (Result_global_ext (global_unknown, global_state, more)) = global_unknown;;

let rec report_global_names
  res = maps (fun g ->
               (match global_unknown g with Global_Named x -> [x]
                 | Global_Seed (_, _) -> []))
          (report_globals res);;

let rec state_context
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_context;;

let rec report_rows_of
  res = map (fun st -> (state_point st, state_context st)) (report_states res);;

let rec analysis_graph_of
  res = (let g = report_cfg res in
         let rows = report_rows_of res in
         let names = report_global_names res in
         let ga = membera equal_literal names in
          Analysis_graph_ext
            (map (fun (a, b) -> Local_Node (a, b)) rows @
               map (fun a -> Global_Node a) names,
              maps (fun e -> maps (fun (u, c) -> intra_deps ga rows u c e) rows)
                (cfg_intra_list (equal_literal, linorder_literal)
                  (equal_exp, linorder_exp) g) @
                maps (fun e ->
                       maps (fun (u, c) -> call_deps res ga rows u c e) rows)
                  (cfg_calls_list (equal_literal, linorder_literal)
                    (equal_exp, linorder_exp) g) @
                  maps (fun (u, c) ->
                         (if equal_cfg_nodea u (cfg_entry g)
                           then map (fun x ->
                                      (Local_Node (u, c),
(Global_Write, Global_Node x)))
                                  names
                           else []))
                    rows,
              ()));;

let rec global_state
  (Result_global_ext (global_unknown, global_state, more)) = global_state;;

let rec map_result_global
  f g = Result_global_ext (global_unknown g, map_lift f (global_state g), ());;

let rec render_context
  show asa x2 = match show, asa, x2 with show, asa, Report_Unit -> Context_Unit
    | show, asa, Report_Entry ctx ->
        Context_Entry (map show (mcp_ctx_values asa ctx))
    | show, asa, Report_Call_String us -> Context_Call_String us;;

let rec state_diagnostics
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_diagnostics;;

let rec state_checks
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_checks;;

let rec map_result_state
  f st =
    Result_state_ext
      (state_point st, state_context st, map_lift f (state_value st),
        state_checks st, state_diagnostics st,
        map (fun (w, s) -> (w, map_lift f s)) (state_steps st), ());;

let rec render_report
  show res =
    (let asa = activation (config_analyses (report_config res)) in
     let state =
       comp (map_analysis_view show) (mcp_render asa (report_vars res)) in
      Run_result_ext
        (report_cfg res, map (render_context show asa) (report_contexts res),
          map (map_result_state state) (report_states res),
          map (fun v ->
                (v, (map_lift state (report_point_join res v),
                      map (fun (w, s) -> (w, map_lift state s))
                        (report_steps_join res v))))
            (cfg_node_list (equal_literal, linorder_literal)
              (equal_exp, linorder_exp) (report_cfg res)),
          report_routes res, report_checks res,
          map (map_result_global state) (report_globals res),
          report_diagnostics res, analysis_graph_of res, ()));;

let rec string_of_pairs
  = function [] -> ""
    | [(x, y)] -> (x ^ "<le>") ^ y
    | (x, y) :: p :: ps ->
        (((((x ^ "<le>") ^ y) ^ " ") ^ "<and>") ^ " ") ^
          string_of_pairs (p :: ps);;

let rec cfg_call_edges
  x = cfg_calls_list (equal_literal, linorder_literal) (equal_exp, linorder_exp)
        x;;

let rec cfg_intra_edges
  x = cfg_intra_list (equal_literal, linorder_literal) (equal_exp, linorder_exp)
        x;;

let rec res_cfg
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_cfg;;

let rec procs_stmt_next
  pi x1 n = match pi, x1, n with pi, [], n -> n
    | pi, p :: ps, n ->
        (match pi p with None -> procs_stmt_next pi ps n
          | Some decl ->
            procs_stmt_next pi ps (suc (plus_nat n (csize (body decl)))));;

let rec to_string_relc
  d = (match d with RelBot -> "<bottom>"
        | RelC ps ->
          (if equal_set (equal_prod equal_literal equal_literal) ps bot_set
            then "<top>"
            else ("{" ^
                   string_of_pairs
                     (sorted_list_of_set
                       ((equal_prod equal_literal equal_literal),
                         (linorder_prod linorder_literal linorder_literal))
                       ps)) ^
                   "}"));;

let rec order_view_string
  v = to_string_relc (match v with None -> RelBot | Some ps -> RelC (Set ps));;

let rec check_exp
  (Result_check_ext (check_point, check_label, check_exp, check_verdict, more))
    = check_exp;;

let rec res_graph
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_graph;;

let rec route_callee
  (Call_route_ext
    (route_point, route_context, route_callee, route_targets, more))
    = route_callee;;

let rec string_of_abstract_value
  = function SignValue v -> to_string_sign v
    | IntervalValue v -> to_string_ivl v
    | ParityValue v -> to_string_parity v
    | IntDomValue v ->
        to_string_int_dom_ext (bounded_lattice_unit, warrowing_unit) v
    | IntDomOnceValue v ->
        to_string_int_dom_ext (bounded_lattice_unit, warrowing_unit) v
    | IntDomNeverValue v ->
        to_string_int_dom_ext (bounded_lattice_unit, warrowing_unit) v
    | CongruenceValue v -> to_string_congruence v
    | OrderValue v -> order_view_string v;;

let rec res_checks
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_checks;;

let rec res_joined
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_joined;;

let rec res_routes
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_routes;;

let rec res_states
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_states;;

let rec check_label
  (Result_check_ext (check_point, check_label, check_exp, check_verdict, more))
    = check_label;;

let rec check_point
  (Result_check_ext (check_point, check_label, check_exp, check_verdict, more))
    = check_point;;

let rec res_globals
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_globals;;

let rec com_stmt_post_order
  n x1 = match n, x1 with n, SKIP i -> [Statement n]
    | n, Assign (i, x, a) -> [Statement n]
    | n, Check (i, l, c) -> [Statement n]
    | n, Seq (c1, c2) ->
        com_stmt_post_order n c1 @
          com_stmt_post_order (plus_nat n (csize c1)) c2
    | n, If (i, b, c1, c2) ->
        com_stmt_post_order (suc n) c1 @
          com_stmt_post_order (plus_nat (suc n) (csize c1)) c2 @ [Statement n]
    | n, While (i, b, c) -> com_stmt_post_order (suc n) c @ [Statement n]
    | n, Call (i, dst, q, actuals) -> [Statement n]
    | n, Return (i, e) -> [Statement n]
    | n, Restore i -> [Statement n]
    | n, Unwind i -> [Statement n];;

let rec res_contexts
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_contexts;;

let rec check_verdict
  (Result_check_ext (check_point, check_label, check_exp, check_verdict, more))
    = check_verdict;;

let rec defs_stmt_post_order
  pi x1 n = match pi, x1, n with pi, [], n -> []
    | pi, p :: ps, n ->
        (match pi p with None -> defs_stmt_post_order pi ps n
          | Some decl ->
            (p, com_stmt_post_order n (body decl)) ::
              defs_stmt_post_order pi ps
                (suc (plus_nat n (csize (body decl)))));;

let rec prog_stmt_post_order
  p = defs_stmt_post_order (prog_table p) (prog_procs p) zero_nat @
        [(prog_main_name,
           com_stmt_post_order
             (procs_stmt_next (prog_table p) (prog_procs p) zero_nat)
             (prog_main p))];;

let rec graph_edges
  (Analysis_graph_ext (graph_nodes, graph_edges, more)) = graph_edges;;

let rec graph_nodes
  (Analysis_graph_ext (graph_nodes, graph_edges, more)) = graph_nodes;;

let rec res_diagnostics
  (Run_result_ext
    (res_cfg, res_contexts, res_states, res_joined, res_routes, res_checks,
      res_globals, res_diagnostics, res_graph, more))
    = res_diagnostics;;

let rec map_analysis_answer
  f x1 = match f, x1 with f, Invalid_Activation -> Invalid_Activation
    | f, Malformed_Program -> Malformed_Program
    | f, No_Answer -> No_Answer
    | f, Analysed x4 -> Analysed (f x4);;

let rec diagnostic_point (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x1;;

let rec diagnostic_verdict (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x4;;

let rec arithmetic_operation (Arithmetic_Obligation (x1, x2)) = x1;;

let rec diagnostic_obligation (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x3;;

let rec diagnostic_occurrence (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x2;;

end;; (*struct Generated*)
