
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
  type aop = AAdd | ASub | AMul | ADiv | AMod
  type ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64
  type var_id = GlobalId of string | ScopedId of string * string |
    ReturnId of string | ReturnVar
  type cop = CLt | CLe | CGt | CGe | CEq | CNe
  type exp = TN of ikind * int | TVar of ikind * var_id |
    TArith of ikind * aop * exp * exp | TCast of ikind * exp |
    TCmp of cop * exp * exp | TNot of exp | TAnd of exp * exp | TOr of exp * exp
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type 'a kd
  type cfg_node = Statement of nat | FunctionEntry of string |
    FunctionResult of string
  type sign
  val ik_signed : ikind -> bool
  type signed_overflow_policy = Assume_Top | Assume_Wraparound
  type congruence
  type parity
  type ivl
  type src_exp = N of int | V of string | Plus of src_exp * src_exp |
    Minus of src_exp * src_exp | Times of src_exp * src_exp |
    Div of src_exp * src_exp | Mod of src_exp * src_exp |
    Less of src_exp * src_exp | LessEq of src_exp * src_exp |
    Greater of src_exp * src_exp | GreaterEq of src_exp * src_exp |
    NotEq of src_exp * src_exp | Eq of src_exp * src_exp | Not of src_exp |
    And of src_exp * src_exp | Or of src_exp * src_exp | Cast of ikind * src_exp
  type ('a, 'b) gcall_action = CallEdge of 'a option * 'a list * 'b list
  type 'a gspecial_call = Nondet_Int | Min of 'a * 'a | Max of 'a * 'a
  type ('a, 'b) gedge_action = EA_Nop | EA_Assign of 'a * 'b |
    EA_Special of 'b gspecial_call * 'a | EA_Assume of 'b | EA_AssumeNot of 'b |
    EA_Body of string | EA_Ret of 'b option * string |
    EA_Check of (nat * nat) * 'b
  type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint
  type int_once
  type analysis = Interval | Congruence | Ana_Int of refine_mode | Order | Sign
    | Parity
  type int_never
  type 'a int_tuple
  type 'a order_rel
  type 'a lifted = Bot | Lifted of 'a
  type check_result = Check_Proved | Check_Refuted | Check_Unknown
  type int_fixpoint
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
  type arithmetic_hazard = Division_By_Zero | Signed_Overflow |
    Remainder_Overflow | Conversion_Overflow | Min_Conversion_Overflow |
    Max_Conversion_Overflow
  type 'a arithmetic_obligation
  type 'a trace_key = Trace_Buffer | Trace_Global of string |
    Trace_Seed of cfg_node * 'a
  type ('a, 'b, 'c) gcfg_ext
  type ('a, 'b, 'c) route_event = Ev_Route of 'a * 'b * 'c
  type report_value
  type 'a analysis_context = Context_Unit | Context_Entry of 'a list |
    Context_Call_String of cfg_node list
  type 'a field_state = Field_Store of (string * 'a) list | Field_Whole of 'a
  type ('a, 'b, 'c, 'd) trace_printers =
    Trace_Printers of
      ('a -> string analysis_context) * ('b -> 'a trace_key) *
        ('c -> ((string * string field_state) list) lifted) *
        (string option -> 'c -> ((string * string field_state) list) lifted) *
        ('d -> ((string * string field_state) list) lifted)
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
  type 'a report_context
  type 'a unknown_node = Local_Node of cfg_node * nat | Global_Node of 'a
  type 'a analysis_answer = Invalid_Activation | Malformed_Program | No_Answer |
    Analysed of 'a
  type ('a, 'b) analysis_edge = Intra_Dep of ('a, 'b) gedge_action |
    Enter_Dep of ('a, 'b) gcall_action | Combine_Dep of ('a, 'b) gcall_action |
    Continue_Dep of ('a, 'b) gcall_action | Global_Read | Global_Write
  type context_policy = Call_String of nat | Entry_State
  type program_globals = Program_Globals_Flow_Sensitive |
    Program_Globals_Flow_Insensitive
  type 'a result_global_unknown = Global_Named of 'a |
    Global_Seed of string * nat option
  type 'a imp_prog_ext
  type 'a call_route_ext
  type ('a, 'b, 'c, 'd) analysis_graph_ext
  type 'a arithmetic_diagnostic
  type ('a, 'b, 'c) result_global_ext
  type ('a, 'b, 'c) result_state_ext
  type ('a, 'b) result_check_ext
  type ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext
  type 'a sem_conf_ext = Sem_conf_ext of signed_overflow_policy * 'a
  type 'a voblint_conf_ext =
    Voblint_conf_ext of
      analysis list * context_policy * globals_rule * program_globals *
        unit sem_conf_ext * 'a
  type ('a, 'b, 'c, 'd, 'e, 'f, 'g) analysis_report_ext
  type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) report_renderer_ext
  val cfg_entry : ('a, 'b, 'c) gcfg_ext -> cfg_node
  val sem_int_signed_overflow : 'a sem_conf_ext -> signed_overflow_policy
  val declared_global_vars : 'a imp_prog_ext -> string list
  val prog_table :
    unit imp_prog_ext ->
      string -> (unit, string, src_exp, unit) gproc_decl_ext option
  val prog_procs : unit imp_prog_ext -> string list
  val conf_program_globals : 'a voblint_conf_ext -> program_globals
  val conf_analyses : 'a voblint_conf_ext -> analysis list
  val conf_globals : 'a voblint_conf_ext -> globals_rule
  val conf_sem : 'a voblint_conf_ext -> unit sem_conf_ext
  val elab_cfg :
    unit imp_prog_ext -> (var_id * ikind) list -> (var_id, exp, unit) gcfg_ext
  val arithmetic_operation : 'a arithmetic_obligation -> 'a
  val arithmetic_operand : 'a arithmetic_obligation -> 'a
  val arithmetic_hazard : 'a arithmetic_obligation -> arithmetic_hazard
  val string_of_report_value : report_value -> string
  val var_label : var_id -> string
  val conf_context : 'a voblint_conf_ext -> context_policy
  val prog_main : unit imp_prog_ext -> (unit, string, src_exp) gcom
  val run_voblint :
    unit voblint_conf_ext ->
      (var_id * ikind) list ->
        unit imp_prog_ext ->
          (unit voblint_conf_ext,
            ((ivl kd list),
              ((congruence kd list),
                (((int_never int_tuple kd list),
                   ((int_once int_tuple kd list),
                     (int_fixpoint int_tuple kd list))
                     analysis_product)
                   analysis_product,
                  ((sign kd list),
                    ((parity kd list), (unit list)) analysis_product)
                    analysis_product)
                  analysis_product)
                analysis_product)
              analysis_product
              report_context,
            var_id, exp, var_id,
            ((var_id -> ivl kd) lifted,
              ((var_id -> congruence kd) lifted,
                (((var_id -> int_never int_tuple kd) lifted,
                   ((var_id -> int_once int_tuple kd) lifted,
                     (var_id -> int_fixpoint int_tuple kd) lifted)
                     analysis_product)
                   analysis_product,
                  ((var_id -> sign kd) lifted,
                    ((var_id -> parity kd) lifted, var_id order_rel lifted)
                      analysis_product)
                    analysis_product)
                  analysis_product)
                analysis_product)
              analysis_product,
            unit)
            analysis_report_ext
            analysis_answer
  val mk_program :
    (string * (unit, string, src_exp, unit) gproc_decl_ext) list ->
      (unit, string, src_exp) gcom -> string list -> unit imp_prog_ext
  val route_targets : 'a call_route_ext -> nat list
  val route_context : 'a call_route_ext -> nat
  val route_point : 'a call_route_ext -> cfg_node
  val cfg_points : (var_id, exp, unit) gcfg_ext -> cfg_node list
  val state_steps : ('a, 'b, 'c) result_state_ext -> (cfg_node * 'b lifted) list
  val state_point : ('a, 'b, 'c) result_state_ext -> cfg_node
  val state_value : ('a, 'b, 'c) result_state_ext -> 'b lifted
  val global_unknown :
    ('a, 'b, 'c) result_global_ext -> 'a result_global_unknown
  val state_context : ('a, 'b, 'c) result_state_ext -> nat
  val global_state : ('a, 'b, 'c) result_global_ext -> 'b lifted
  val state_diagnostics :
    ('a, 'b, 'c) result_state_ext ->
      ('a arithmetic_obligation * check_result lifted) list
  val state_checks :
    ('a, 'b, 'c) result_state_ext -> ('a * check_result lifted) list
  val prog_render_report :
    (report_value -> 'a) ->
      (unit voblint_conf_ext,
        ((ivl kd list),
          ((congruence kd list),
            (((int_never int_tuple kd list),
               ((int_once int_tuple kd list), (int_fixpoint int_tuple kd list))
                 analysis_product)
               analysis_product,
              ((sign kd list), ((parity kd list), (unit list)) analysis_product)
                analysis_product)
              analysis_product)
            analysis_product)
          analysis_product
          report_context,
        var_id, exp, var_id,
        ((var_id -> ivl kd) lifted,
          ((var_id -> congruence kd) lifted,
            (((var_id -> int_never int_tuple kd) lifted,
               ((var_id -> int_once int_tuple kd) lifted,
                 (var_id -> int_fixpoint int_tuple kd) lifted)
                 analysis_product)
               analysis_product,
              ((var_id -> sign kd) lifted,
                ((var_id -> parity kd) lifted, var_id order_rel lifted)
                  analysis_product)
                analysis_product)
              analysis_product)
            analysis_product)
          analysis_product,
        unit)
        analysis_report_ext ->
        (var_id, exp, var_id, analysis, 'a, unit) run_result_ext
  val cfg_call_edges :
    (var_id, exp, unit) gcfg_ext ->
      (cfg_node * ((var_id, exp) gcall_action * (cfg_node * cfg_node))) list
  val cfg_intra_edges :
    (var_id, exp, unit) gcfg_ext ->
      (cfg_node * ((var_id, exp) gedge_action * cfg_node)) list
  val res_cfg :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext -> ('a, 'b, unit) gcfg_ext
  val check_exp : ('a, 'b) result_check_ext -> 'a
  val res_graph :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext ->
      ('a, 'b, 'c, unit) analysis_graph_ext
  val route_callee : 'a call_route_ext -> string
  val res_checks :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext -> ('b, unit) result_check_ext list
  val res_joined :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext ->
      (cfg_node *
        ((('d * 'e field_state) list) lifted *
          (cfg_node * (('d * 'e field_state) list) lifted) list)) list
  val res_routes :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext -> unit call_route_ext list
  val res_states :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext ->
      ('b, (('d * 'e field_state) list), unit) result_state_ext list
  val check_label : ('a, 'b) result_check_ext -> nat * nat
  val check_point : ('a, 'b) result_check_ext -> cfg_node
  val default_sem_conf : unit sem_conf_ext
  val res_globals :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext ->
      ('c, (('d * 'e field_state) list), unit) result_global_ext list
  val res_contexts :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext -> 'e analysis_context list
  val check_verdict : ('a, 'b) result_check_ext -> check_result lifted
  val prog_stmt_post_order : unit imp_prog_ext -> (string * cfg_node list) list
  val graph_edges :
    ('a, 'b, 'c, 'd) analysis_graph_ext ->
      ('c unknown_node * (('a, 'b) analysis_edge * 'c unknown_node)) list
  val graph_nodes : ('a, 'b, 'c, 'd) analysis_graph_ext -> 'c unknown_node list
  val res_diagnostics :
    ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext -> 'b arithmetic_diagnostic list
  val map_analysis_answer :
    ('a -> 'b) -> 'a analysis_answer -> 'b analysis_answer
  val diagnostic_point : 'a arithmetic_diagnostic -> cfg_node
  val diagnostic_verdict : 'a arithmetic_diagnostic -> check_result
  val diagnostic_obligation :
    'a arithmetic_diagnostic -> 'a arithmetic_obligation
  val diagnostic_occurrence : 'a arithmetic_diagnostic -> nat
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

type aop = AAdd | ASub | AMul | ADiv | AMod;;

let rec equal_aopa x0 x1 = match x0, x1 with ADiv, AMod -> false
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

let equal_aop = ({equal = equal_aopa} : aop equal);;

type ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64;;

let rec equal_ikinda x0 x1 = match x0, x1 with I64, U64 -> false
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

type exp = TN of ikind * int | TVar of ikind * var_id |
  TArith of ikind * aop * exp * exp | TCast of ikind * exp |
  TCmp of cop * exp * exp | TNot of exp | TAnd of exp * exp | TOr of exp * exp;;

let rec equal_expa
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
    | TOr (x81, x82), TOr (y81, y82) -> equal_expa x81 y81 && equal_expa x82 y82
    | TAnd (x71, x72), TAnd (y71, y72) ->
        equal_expa x71 y71 && equal_expa x72 y72
    | TNot x6, TNot y6 -> equal_expa x6 y6
    | TCmp (x51, x52, x53), TCmp (y51, y52, y53) ->
        equal_cop x51 y51 && (equal_expa x52 y52 && equal_expa x53 y53)
    | TCast (x41, x42), TCast (y41, y42) ->
        equal_ikinda x41 y41 && equal_expa x42 y42
    | TArith (x31, x32, x33, x34), TArith (y31, y32, y33, y34) ->
        equal_ikinda x31 y31 &&
          (equal_aopa x32 y32 && (equal_expa x33 y33 && equal_expa x34 y34))
    | TVar (x21, x22), TVar (y21, y22) ->
        equal_ikinda x21 y21 && equal_var_ida x22 y22
    | TN (x11, x12), TN (y11, y12) ->
        equal_ikinda x11 y11 && equal_inta x12 y12;;

let equal_exp = ({equal = equal_expa} : exp equal);;

type ordera = Eqa | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

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

let rec comparator_exp
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
                (match comparator_exp xb yf with Eqa -> comparator_exp xc yg
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
        (match comparator_ikind x yh with Eqa -> comparator_exp xa yi | Lt -> Lt
          | Gt -> Gt)
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
            (match comparator_exp xa yk with Eqa -> comparator_exp xb yl
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
    | TNot x, TNot ym -> comparator_exp x ym
    | TNot x, TAnd (yn, yo) -> Lt
    | TNot x, TOr (yp, yq) -> Lt
    | TAnd (x, xa), TN (y, ya) -> Gt
    | TAnd (x, xa), TVar (yb, yc) -> Gt
    | TAnd (x, xa), TArith (yd, ye, yf, yg) -> Gt
    | TAnd (x, xa), TCast (yh, yi) -> Gt
    | TAnd (x, xa), TCmp (yj, yk, yl) -> Gt
    | TAnd (x, xa), TNot ym -> Gt
    | TAnd (x, xa), TAnd (yn, yo) ->
        (match comparator_exp x yn with Eqa -> comparator_exp xa yo | Lt -> Lt
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
        (match comparator_exp x yp with Eqa -> comparator_exp xa yq | Lt -> Lt
          | Gt -> Gt);;

let rec le_of_comp
  acomp x y = (match acomp x y with Eqa -> true | Lt -> true | Gt -> false);;

let rec less_eq_exp x = le_of_comp comparator_exp x;;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eqa -> false | Lt -> true | Gt -> false);;

let rec less_exp x = lt_of_comp comparator_exp x;;

let ord_exp = ({less_eq = less_eq_exp; less = less_exp} : exp ord);;

let preorder_exp = ({ord_preorder = ord_exp} : exp preorder);;

let order_exp = ({preorder_order = preorder_exp} : exp order);;

let linorder_exp = ({order_linorder = order_exp} : exp linorder);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec equal_suma _A _B x0 x1 = match x0, x1 with Inl x1, Inr x2 -> false
                           | Inr x2, Inl x1 -> false
                           | Inr x2, Inr y2 -> eq _B x2 y2
                           | Inl x1, Inl y1 -> eq _A x1 y1;;

let rec equal_sum _A _B = ({equal = equal_suma _A _B} : ('a, 'b) sum equal);;

let equal_var_id = ({equal = equal_var_ida} : var_id equal);;

let rec less_eq_var_id x = le_of_comp comparator_var_id x;;

let rec less_var_id x = lt_of_comp comparator_var_id x;;

let ord_var_id = ({less_eq = less_eq_var_id; less = less_var_id} : var_id ord);;

let preorder_var_id = ({ord_preorder = ord_var_id} : var_id preorder);;

let order_var_id = ({preorder_order = preorder_var_id} : var_id order);;

let linorder_var_id = ({order_linorder = order_var_id} : var_id linorder);;

let rec key_of_var_var_id x = x;;

type 'a infinite_key = unit;;

type 'a split_key =
  {infinite_key_split_key : 'a infinite_key; key_of_var : var_id -> 'a};;
let key_of_var _A = _A.key_of_var;;

let infinite_key_var_id = (() : var_id infinite_key);;

let split_key_var_id =
  ({infinite_key_split_key = infinite_key_var_id;
     key_of_var = key_of_var_var_id}
    : var_id split_key);;

type 'a kd = KBot | KD of ikind * 'a | KTop;;

let rec equal_kda _A
  x0 x1 = match x0, x1 with KD (x21, x22), KTop -> false
    | KTop, KD (x21, x22) -> false
    | KBot, KTop -> false
    | KTop, KBot -> false
    | KBot, KD (x21, x22) -> false
    | KD (x21, x22), KBot -> false
    | KD (x21, x22), KD (y21, y22) -> equal_ikinda x21 y21 && eq _A x22 y22
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
        (if equal_ikinda k l
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
        equal_ikinda k l &&
          less_eq
            _A.numeric_domain_ik_domain.executable_domain_numeric_domain.warrowing_executable_domain.widening_warrowing.order_widening.preorder_order.ord_preorder
            a b
    | KD (v, va), KBot -> false
    | KTop, KBot -> false
    | KTop, KD (v, va) -> false;;

let rec less_kd _A a b = less_eq_kd _A a b && not (less_eq_kd _A b a);;

let rec ord_kd _A = ({less_eq = less_eq_kd _A; less = less_kd _A} : 'a kd ord);;

let rec top_kda _A = KTop;;

let rec top_kd _A = ({top = top_kda _A} : 'a kd top);;

let rec preorder_kd _A = ({ord_preorder = (ord_kd _A)} : 'a kd preorder);;

let rec order_kd _A = ({preorder_order = (preorder_kd _A)} : 'a kd order);;

let rec widen_kd _A
  x0 b = match x0, b with KBot, b -> b
    | KD (v, va), KBot -> KD (v, va)
    | KTop, KBot -> KTop
    | KD (k, a), KD (l, b) ->
        (if equal_ikinda k l then KD (k, widen_ik _A k a b) else KTop)
    | KD (v, va), KTop -> KTop
    | KTop, KD (v, va) -> KTop
    | KTop, KTop -> KTop;;

let rec widening_kd _A =
  ({order_widening = (order_kd _A); widen = widen_kd _A} : 'a kd widening);;

let rec order_bot_kd _A =
  ({bot_order_bot = (bot_kd _A); order_order_bot = (order_kd _A)} :
    'a kd order_bot);;

let rec order_top_kd _A =
  ({order_order_top = (order_kd _A); top_order_top = (top_kd _A)} :
    'a kd order_top);;

let rec narrow_kd _A
  x0 b = match x0, b with KTop, b -> b
    | KD (k, a), KD (l, b) ->
        (if equal_ikinda k l then KD (k, narrow_ik _A k a b) else KD (k, a))
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

let rec order_name_literala x = x;;

type 'a order_name =
  {linorder_order_name : 'a linorder; order_name : 'a -> string};;
let order_name _A = _A.order_name;;

let order_name_literal =
  ({linorder_order_name = linorder_literal; order_name = order_name_literala} :
    string order_name);;

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

let order_bot_unit =
  ({bot_order_bot = bot_unit; order_order_bot = order_unit} : unit order_bot);;

let order_top_unit =
  ({order_order_top = order_unit; top_order_top = top_unit} : unit order_top);;

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

type signed_overflow_policy = Assume_Top | Assume_Wraparound;;

type congruence = Abs_congruence of (int * int) option;;

type parity = PBot | PEven | POdd | PTop;;

type eint = MinInf | Fin of int | PlusInf;;

type ivl = Ivl of eint * eint;;

type 'a int_dom_ext = Int_dom_ext of sign * ivl * parity * congruence * 'a;;

type 'a query_lift = QBot | QLifted of 'a | QTop;;

type 'a kind_int_domain =
  {ik_domain_kind_int_domain : 'a ik_domain; top_ik : ikind -> 'a;
    of_int_ik : ikind -> int -> 'a;
    cast_ik : signed_overflow_policy -> ikind option -> ikind -> 'a -> 'a;
    arith_ik : signed_overflow_policy -> ikind -> aop -> bool -> 'a -> 'a -> 'a;
    cmp_ik : cop -> 'a -> 'a -> bool option; meet_ik : 'a -> 'a -> 'a;
    refine_ik : cop -> 'a -> 'a -> 'a * 'a; raw_aop_ik : aop -> 'a -> 'a -> 'a;
    fits_ik : ikind -> 'a -> bool;
    answer_ik : 'a -> unit int_dom_ext query_lift;
    of_answer_ik : ikind option -> unit int_dom_ext query_lift -> 'a};;
let top_ik _A = _A.top_ik;;
let of_int_ik _A = _A.of_int_ik;;
let cast_ik _A = _A.cast_ik;;
let arith_ik _A = _A.arith_ik;;
let cmp_ik _A = _A.cmp_ik;;
let meet_ik _A = _A.meet_ik;;
let refine_ik _A = _A.refine_ik;;
let raw_aop_ik _A = _A.raw_aop_ik;;
let fits_ik _A = _A.fits_ik;;
let answer_ik _A = _A.answer_ik;;
let of_answer_ik _A = _A.of_answer_ik;;

let rec int_sign
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_sign;;

let rec of_answer_ik_sign
  sk q =
    (match q with QBot -> bot_signa | QLifted a -> int_sign a
      | QTop -> top_signa);;

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

let rec swap p = (snd p, fst p);;

let rec sign_excl a b = match a, b with SNonNeg, SZero -> SPos
                    | SNonPos, SZero -> SNeg
                    | SZero, SZero -> SBot
                    | SBot, b -> SBot
                    | SNeg, b -> SNeg
                    | SNonPos, SBot -> SNonPos
                    | SNonPos, SNeg -> SNonPos
                    | SNonPos, SNonPos -> SNonPos
                    | SNonPos, SNonNeg -> SNonPos
                    | SNonPos, SPos -> SNonPos
                    | SNonPos, STop -> SNonPos
                    | SZero, SBot -> SZero
                    | SZero, SNeg -> SZero
                    | SZero, SNonPos -> SZero
                    | SZero, SNonNeg -> SZero
                    | SZero, SPos -> SZero
                    | SZero, STop -> SZero
                    | SPos, b -> SPos
                    | STop, b -> STop
                    | a, SBot -> a
                    | a, SNeg -> a
                    | a, SNonPos -> a
                    | a, SNonNeg -> a
                    | a, SPos -> a
                    | a, STop -> a;;

let rec refine_ik_sign
  c a b =
    (match c with CLt -> inv_less_sign true a b
      | CLe -> swap (inv_less_sign false b a)
      | CGt -> swap (inv_less_sign true b a) | CGe -> inv_less_sign false a b
      | CEq -> (inf_sign a b, inf_sign a b)
      | CNe -> (sign_excl a b, sign_excl b a));;

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

let rec normalize_congruence_rep
  = function None -> None
    | Some (c, m) ->
        (if equal_inta m zero_inta then Some (c, zero_inta)
          else (let p = abs_int m in
                let r = modulo_inta c p in
                 Some (r, p)));;

let rec mk_congruence
  xb xc = Abs_congruence (normalize_congruence_rep (Some (xb, xc)));;

let top_congruencea : congruence = mk_congruence zero_inta one_inta;;

let top_paritya : parity = PTop;;

let ivl_top : ivl = Ivl (MinInf, PlusInf);;

let top_ivla : ivl = ivl_top;;

let rec top_int_dom_ext _A
  = Int_dom_ext
      (top_signa, top_ivla, top_paritya, top_congruencea,
        top _A.bounded_lattice_top_bounded_lattice.bounded_semilattice_inf_top_bounded_lattice_top.order_top_bounded_semilattice_inf_top.top_order_top);;

let rec int_sign_update
  int_signa (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more))
    = Int_dom_ext
        (int_signa int_sign, int_ivl, int_parity, int_congruence, more);;

let rec answer_ik_sign
  a = QLifted
        (int_sign_update (fun _ -> a) (top_int_dom_ext bounded_lattice_unit));;

let rec sign_cast
  ik a =
    (if equal_signa a SBot then SBot
      else (if equal_signa a SZero then SZero
             else (if ik_signed ik then STop else SNonNeg)));;

let rec sign_safe
  x0 a b = match x0, a, b with
    AAdd, a, b ->
      less_eq_sign a SZero ||
        (less_eq_sign b SZero ||
          (less_eq_sign a SNonNeg && less_eq_sign b SNonPos ||
            less_eq_sign a SNonPos && less_eq_sign b SNonNeg))
    | ASub, a, b ->
        less_eq_sign b SZero ||
          (less_eq_sign a SNonNeg && less_eq_sign b SNonNeg ||
            less_eq_sign a SNeg && less_eq_sign b SNonPos)
    | AMul, a, b -> less_eq_sign a SZero || less_eq_sign b SZero
    | ADiv, a, b -> less_eq_sign a SNonNeg || less_eq_sign b SNonNeg
    | AMod, a, b -> true;;

let rec arith_ik_sign
  ovp k op fits a b =
    (if fits && (ik_signed k && sign_safe op a b) then sign_aop op a b
      else sign_cast k (sign_aop op a b));;

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

let rec ik_widens
  k ik =
    less_eq_int (ik_min ik) (ik_min k) && less_eq_int (ik_max k) (ik_max ik);;

let rec cast_ik_sign
  ovp sk k a =
    (match sk with None -> sign_cast k a
      | Some s -> (if ik_widens s k then a else sign_cast k a));;

let rec top_ik_sign k = (if ik_signed k then STop else SNonNeg);;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec cop_of
  lt eq x2 a b = match lt, eq, x2, a, b with lt, eq, CLt, a, b -> lt a b
    | lt, eq, CGt, a, b -> lt b a
    | lt, eq, CLe, a, b -> map_option not (lt b a)
    | lt, eq, CGe, a, b -> map_option not (lt a b)
    | lt, eq, CEq, a, b -> eq a b
    | lt, eq, CNe, a, b -> map_option not (eq a b);;

let rec sign_eqb
  a b = (if equal_signa a SZero && equal_signa b SZero then Some true
          else (if sign_le a SNeg && sign_le b SNonNeg ||
                     (sign_le b SNeg && sign_le a SNonNeg ||
                       (sign_le a SPos && sign_le b SNonPos ||
                         sign_le b SPos && sign_le a SNonPos))
                 then Some false else None));;

let rec sign_lt
  a b = (if sign_le a SNeg && sign_le b SNonNeg then Some true
          else (if sign_le a SNonPos && sign_le b SPos then Some true
                 else (if sign_le b SNonPos && sign_le a SNonNeg then Some false
                        else (if sign_le b SNeg && sign_le a SPos
                               then Some false else None))));;

let rec cmp_ik_sign x = cop_of sign_lt sign_eqb x;;

let kind_int_domain_sign =
  ({ik_domain_kind_int_domain = ik_domain_sign; top_ik = top_ik_sign;
     of_int_ik = of_int_ik_sign; cast_ik = cast_ik_sign;
     arith_ik = arith_ik_sign; cmp_ik = cmp_ik_sign; meet_ik = meet_ik_sign;
     refine_ik = refine_ik_sign; raw_aop_ik = raw_aop_ik_sign;
     fits_ik = fits_ik_sign; answer_ik = answer_ik_sign;
     of_answer_ik = of_answer_ik_sign}
    : sign kind_int_domain);;

let equal_ikind = ({equal = equal_ikinda} : ikind equal);;

type src_exp = N of int | V of string | Plus of src_exp * src_exp |
  Minus of src_exp * src_exp | Times of src_exp * src_exp |
  Div of src_exp * src_exp | Mod of src_exp * src_exp |
  Less of src_exp * src_exp | LessEq of src_exp * src_exp |
  Greater of src_exp * src_exp | GreaterEq of src_exp * src_exp |
  NotEq of src_exp * src_exp | Eq of src_exp * src_exp | Not of src_exp |
  And of src_exp * src_exp | Or of src_exp * src_exp | Cast of ikind * src_exp;;

let rec equal_src_expa
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
        equal_ikinda x171 y171 && equal_src_expa x172 y172
    | Or (x161, x162), Or (y161, y162) ->
        equal_src_expa x161 y161 && equal_src_expa x162 y162
    | And (x151, x152), And (y151, y152) ->
        equal_src_expa x151 y151 && equal_src_expa x152 y152
    | Not x14, Not y14 -> equal_src_expa x14 y14
    | Eq (x131, x132), Eq (y131, y132) ->
        equal_src_expa x131 y131 && equal_src_expa x132 y132
    | NotEq (x121, x122), NotEq (y121, y122) ->
        equal_src_expa x121 y121 && equal_src_expa x122 y122
    | GreaterEq (x111, x112), GreaterEq (y111, y112) ->
        equal_src_expa x111 y111 && equal_src_expa x112 y112
    | Greater (x101, x102), Greater (y101, y102) ->
        equal_src_expa x101 y101 && equal_src_expa x102 y102
    | LessEq (x91, x92), LessEq (y91, y92) ->
        equal_src_expa x91 y91 && equal_src_expa x92 y92
    | Less (x81, x82), Less (y81, y82) ->
        equal_src_expa x81 y81 && equal_src_expa x82 y82
    | Mod (x71, x72), Mod (y71, y72) ->
        equal_src_expa x71 y71 && equal_src_expa x72 y72
    | Div (x61, x62), Div (y61, y62) ->
        equal_src_expa x61 y61 && equal_src_expa x62 y62
    | Times (x51, x52), Times (y51, y52) ->
        equal_src_expa x51 y51 && equal_src_expa x52 y52
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_src_expa x41 y41 && equal_src_expa x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_src_expa x31 y31 && equal_src_expa x32 y32
    | V x2, V y2 -> ((x2 : string) = y2)
    | N x1, N y1 -> equal_inta x1 y1;;

let equal_src_exp = ({equal = equal_src_expa} : src_exp equal);;

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

let rec equal_eint x0 x1 = match x0, x1 with Fin x2, PlusInf -> false
                     | PlusInf, Fin x2 -> false
                     | MinInf, PlusInf -> false
                     | PlusInf, MinInf -> false
                     | MinInf, Fin x2 -> false
                     | Fin x2, MinInf -> false
                     | Fin x2, Fin y2 -> equal_inta x2 y2
                     | PlusInf, PlusInf -> true
                     | MinInf, MinInf -> true;;

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

let rec int_ivl
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_ivl;;

let rec ik_ivl k = Ivl (ik_lo k, ik_hi k);;

let rec of_answer_ik_ivl
  sk q =
    (let r = (match sk with None -> top_ivla | Some a -> ik_ivl a) in
      (match q with QBot -> bot_ivla | QLifted d -> inf_ivl (int_ivl d) r
        | QTop -> r));;

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

let rec ivl_excl
  a x1 = match a, x1 with
    Ivl (l, u), Ivl (Fin x, Fin y) ->
      (if equal_inta x y
        then Ivl ((if equal_eint l (Fin x) then Fin (plus_inta x one_inta)
                    else l),
                   (if equal_eint u (Fin x) then Fin (minus_inta x one_inta)
                     else u))
        else Ivl (l, u))
    | a, Ivl (MinInf, va) -> a
    | a, Ivl (PlusInf, va) -> a
    | a, Ivl (v, MinInf) -> a
    | a, Ivl (v, PlusInf) -> a;;

let rec ivl_refine x0 a b = match x0, a, b with CLt, a, b -> ivl_lt_bounds a b
                     | CLe, a, b -> ivl_le_bounds a b
                     | CGt, a, b -> swap (ivl_lt_bounds b a)
                     | CGe, a, b -> swap (ivl_le_bounds b a)
                     | CEq, a, b -> (inf_ivl a b, inf_ivl a b)
                     | CNe, a, b -> (ivl_excl a b, ivl_excl b a);;

let rec refine_ik_ivl x = ivl_refine x;;

let rec of_int_ik_ivl k n = Ivl (Fin (ik_norm k n), Fin (ik_norm k n));;

let rec int_ivl_update
  int_ivla (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext (int_sign, int_ivla int_ivl, int_parity, int_congruence, more);;

let rec answer_of_ivl
  i = QLifted
        (int_ivl_update (fun _ -> i) (top_int_dom_ext bounded_lattice_unit));;

let rec answer_ik_ivl x = answer_of_ivl x;;

let rec equal_signed_overflow_policy
  x0 x1 = match x0, x1 with Assume_Top, Assume_Wraparound -> false
    | Assume_Wraparound, Assume_Top -> false
    | Assume_Wraparound, Assume_Wraparound -> true
    | Assume_Top, Assume_Top -> true;;

let rec should_wrap
  ovp k =
    not (ik_signed k) || equal_signed_overflow_policy ovp Assume_Wraparound;;

let rec wrap_ivl_ik
  k x y =
    (if less_int (minus_inta y x) (ik_mod k) &&
          less_eq_int (ik_norm k x) (ik_norm k y)
      then Ivl (Fin (ik_norm k x), Fin (ik_norm k y)) else ik_ivl k);;

let rec norm_ivl_ik
  ovp k a =
    (if less_eq_ivl a (ik_ivl k) then a
      else (match a with Ivl (MinInf, _) -> ik_ivl k
             | Ivl (Fin _, MinInf) -> ik_ivl k
             | Ivl (Fin x, Fin y) ->
               (if should_wrap ovp k then wrap_ivl_ik k x y else ik_ivl k)
             | Ivl (Fin _, PlusInf) -> ik_ivl k
             | Ivl (PlusInf, _) -> ik_ivl k));;

let rec arith_ik_ivl ovp k op fits a b = norm_ivl_ik ovp k (ivl_aop op a b);;

let rec meet_ik_ivl a b = inf_ivl a b;;

let rec fits_ik_ivl k a = less_eq_ivl a (ik_ivl k);;

let rec cast_ik_ivl ovp sk = norm_ivl_ik ovp;;

let rec top_ik_ivl x = ik_ivl x;;

let rec interval_less_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || less_eq_eint u2 l1);;

let rec interval_less_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u1 l2);;

let rec interval_less
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

let rec interval_eq
  a b = (if interval_eq_true a b then Some true
          else (if interval_eq_false a b then Some false else None));;

let rec cmp_ik_ivl x = cop_of interval_less interval_eq x;;

let kind_int_domain_ivl =
  ({ik_domain_kind_int_domain = ik_domain_ivl; top_ik = top_ik_ivl;
     of_int_ik = of_int_ik_ivl; cast_ik = cast_ik_ivl; arith_ik = arith_ik_ivl;
     cmp_ik = cmp_ik_ivl; meet_ik = meet_ik_ivl; refine_ik = refine_ik_ivl;
     raw_aop_ik = raw_aop_ik_ivl; fits_ik = fits_ik_ivl;
     answer_ik = answer_ik_ivl; of_answer_ik = of_answer_ik_ivl}
    : ivl kind_int_domain);;

type 'a gquery = EvalInt of 'a;;

let rec equal_gquerya _A (EvalInt x) (EvalInt ya) = eq _A x ya;;

let rec equal_gquery _A = ({equal = equal_gquerya _A} : 'a gquery equal);;

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

let rec int_parity
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_parity;;

let rec of_answer_ik_parity
  sk q =
    (match q with QBot -> bot_paritya | QLifted a -> int_parity a
      | QTop -> top_paritya);;

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

let rec int_parity_update
  int_paritya
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_paritya int_parity, int_congruence, more);;

let rec answer_ik_parity
  a = QLifted
        (int_parity_update (fun _ -> a)
          (top_int_dom_ext bounded_lattice_unit));;

let rec arith_ik_parity ovp k op fits = parity_aop op;;

let rec meet_ik_parity a b = inf_parity a b;;

let rec fits_ik_parity k a = equal_paritya a PBot;;

let rec cast_ik_parity ovp sk k a = a;;

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

let rec parity_lt uu uv = None;;

let rec cmp_ik_parity x = cop_of parity_lt parity_eqb x;;

let kind_int_domain_parity =
  ({ik_domain_kind_int_domain = ik_domain_parity; top_ik = top_ik_parity;
     of_int_ik = of_int_ik_parity; cast_ik = cast_ik_parity;
     arith_ik = arith_ik_parity; cmp_ik = cmp_ik_parity;
     meet_ik = meet_ik_parity; refine_ik = refine_ik_parity;
     raw_aop_ik = raw_aop_ik_parity; fits_ik = fits_ik_parity;
     answer_ik = answer_ik_parity; of_answer_ik = of_answer_ik_parity}
    : parity kind_int_domain);;

type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint;;

type int_once = Int_Once;;

type 'a itself = Type;;

let rec int_mode_int_once uu = Refine_Once;;

type 'a int_refinement = {int_mode : 'a itself -> refine_mode};;
let int_mode _A = _A.int_mode;;

let int_refinement_int_once =
  ({int_mode = int_mode_int_once} : int_once int_refinement);;

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

type analysis = Interval | Congruence | Ana_Int of refine_mode | Order | Sign |
  Parity;;

let rec equal_analysisa x0 x1 = match x0, x1 with Sign, Parity -> false
                          | Parity, Sign -> false
                          | Order, Parity -> false
                          | Parity, Order -> false
                          | Order, Sign -> false
                          | Sign, Order -> false
                          | Ana_Int x3, Parity -> false
                          | Parity, Ana_Int x3 -> false
                          | Ana_Int x3, Sign -> false
                          | Sign, Ana_Int x3 -> false
                          | Ana_Int x3, Order -> false
                          | Order, Ana_Int x3 -> false
                          | Congruence, Parity -> false
                          | Parity, Congruence -> false
                          | Congruence, Sign -> false
                          | Sign, Congruence -> false
                          | Congruence, Order -> false
                          | Order, Congruence -> false
                          | Congruence, Ana_Int x3 -> false
                          | Ana_Int x3, Congruence -> false
                          | Interval, Parity -> false
                          | Parity, Interval -> false
                          | Interval, Sign -> false
                          | Sign, Interval -> false
                          | Interval, Order -> false
                          | Order, Interval -> false
                          | Interval, Ana_Int x3 -> false
                          | Ana_Int x3, Interval -> false
                          | Interval, Congruence -> false
                          | Congruence, Interval -> false
                          | Ana_Int x3, Ana_Int y3 -> equal_refine_mode x3 y3
                          | Parity, Parity -> true
                          | Sign, Sign -> true
                          | Order, Order -> true
                          | Congruence, Congruence -> true
                          | Interval, Interval -> true;;

let equal_analysis = ({equal = equal_analysisa} : analysis equal);;

type int_never = Int_Never;;

let rec int_mode_int_never uu = Refine_Never;;

let int_refinement_int_never =
  ({int_mode = int_mode_int_never} : int_never int_refinement);;

let rec rep_congruence (Abs_congruence x) = x;;

let rec equal_congruencea
  a b = equal_option (equal_prod equal_int equal_int) (rep_congruence a)
          (rep_congruence b);;

type 'a int_tuple = IT of ivl * congruence;;

let rec equal_int_tuplea
  (IT (x1, x2)) (IT (y1, y2)) = equal_ivla x1 y1 && equal_congruencea x2 y2;;

let equal_int_tuple = ({equal = equal_int_tuplea} : 'a int_tuple equal);;

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

let sup_int_tuple = ({sup = sup_int_tuplea} : 'a int_tuple sup);;

let bottom_congruence : congruence = Abs_congruence None;;

let bot_congruencea : congruence = bottom_congruence;;

let bot_int_tuplea : 'a int_tuple = IT (bot_ivla, bot_congruencea);;

let bot_int_tuple = ({bot = bot_int_tuplea} : 'a int_tuple bot);;

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
  ({less_eq = less_eq_int_tuple; less = less_int_tuple} : 'a int_tuple ord);;

let top_int_tuplea : 'a int_tuple = IT (top_ivla, top_congruencea);;

let top_int_tuple = ({top = top_int_tuplea} : 'a int_tuple top);;

let preorder_int_tuple =
  ({ord_preorder = ord_int_tuple} : 'a int_tuple preorder);;

let order_int_tuple =
  ({preorder_order = preorder_int_tuple} : 'a int_tuple order);;

let rec widen_congruence a b = join_congruence a b;;

let rec widen_int_tuple
  a b = IT (widen_ivl (it_ivl a) (it_ivl b),
             widen_congruence (it_cong a) (it_cong b));;

let widening_int_tuple =
  ({order_widening = order_int_tuple; widen = widen_int_tuple} :
    'a int_tuple widening);;

let order_bot_int_tuple =
  ({bot_order_bot = bot_int_tuple; order_order_bot = order_int_tuple} :
    'a int_tuple order_bot);;

let order_top_int_tuple =
  ({order_order_top = order_int_tuple; top_order_top = top_int_tuple} :
    'a int_tuple order_top);;

let rec narrow_congruence_td a b = a;;

let rec narrow_congruence a b = narrow_congruence_td a b;;

let rec narrow_int_tuple
  a b = IT (narrow_ivl (it_ivl a) (it_ivl b),
             narrow_congruence (it_cong a) (it_cong b));;

let narrowing_int_tuple =
  ({order_narrowing = order_int_tuple; narrow = narrow_int_tuple} :
    'a int_tuple narrowing);;

let warrowing_int_tuple =
  ({narrowing_warrowing = narrowing_int_tuple;
     widening_warrowing = widening_int_tuple}
    : 'a int_tuple warrowing);;

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

let rec congruence_constant
  c = (match rep_congruence c with None -> None
        | Some (r, m) -> (if equal_inta m zero_inta then Some r else None));;

let rec ivl_constant
  = function Ivl (Fin l, Fin u) -> (if equal_inta l u then Some l else None)
    | Ivl (MinInf, va) -> None
    | Ivl (PlusInf, va) -> None
    | Ivl (v, MinInf) -> None
    | Ivl (v, PlusInf) -> None;;

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

let rec to_string_int_tuple
  a = (if it_empty (it_ivl a) (it_cong a) then "<bottom>"
        else (match ivl_constant (it_ivl a)
               with None ->
                 (match congruence_constant (it_cong a)
                   with None ->
                     (("intervals:" ^ to_string_ivl (it_ivl a)) ^
                       "; congruences:") ^
                       to_string_congruence (it_cong a)
                   | Some aa -> string_of_int aa)
               | Some aa -> string_of_int aa));;

let rec is_empty_int_tuple a = it_empty (it_ivl a) (it_cong a);;

let gamma_congruence _ = failwith "Congruence_Lattice.gamma_congruence";;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec insertb _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec remove _A
  x xa1 = match x, xa1 with x, Set xs -> Set (removeAll _A x xs)
    | x, Coset xs -> Coset (insertb _A x xs);;

let rec member _A x xa1 = match x, xa1 with x, Set xs -> membera _A xs x
                    | x, Coset xs -> not (membera _A xs x);;

let rec inf_set _A
  a x1 = match a, x1 with a, Set xs -> Set (filtera (fun x -> member _A x a) xs)
    | a, Coset xs -> fold (remove _A) xs a;;

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
    : 'a int_tuple semilattice_sup);;

let bounded_semilattice_sup_bot_int_tuple =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_int_tuple;
     order_bot_bounded_semilattice_sup_bot = order_bot_int_tuple}
    : 'a int_tuple bounded_semilattice_sup_bot);;

let executable_domain_int_tuple =
  ({bounded_semilattice_sup_bot_executable_domain =
      bounded_semilattice_sup_bot_int_tuple;
     order_top_executable_domain = order_top_int_tuple;
     warrowing_executable_domain = warrowing_int_tuple;
     is_empty = is_empty_int_tuple; to_string = to_string_int_tuple}
    : 'a int_tuple executable_domain);;

let numeric_domain_int_tuple =
  ({executable_domain_numeric_domain = executable_domain_int_tuple;
     gamma = gamma_int_tuple}
    : 'a int_tuple numeric_domain);;

let ik_domain_int_tuple =
  ({numeric_domain_ik_domain = numeric_domain_int_tuple;
     widen_ik = widen_ik_int_tuple; narrow_ik = narrow_ik_int_tuple;
     empty_ik = empty_ik_int_tuple}
    : 'a int_tuple ik_domain);;

let rec int_congruence
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_congruence;;

let rec of_answer_ik_congruence
  sk q =
    (match q with QBot -> bot_congruencea | QLifted a -> int_congruence a
      | QTop -> top_congruencea);;

let rec of_answer_ik_int_tuple _A
  sk q = IT (of_answer_ik_ivl sk q, of_answer_ik_congruence sk q);;

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

let rec raw_aop_ik_int_tuple _A
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

let rec while_option b c s = (if b s then while_option b c (c s) else Some s);;

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

let rec it_refine_mode
  md a =
    (match md with Refine_Never -> a | Refine_Once -> it_refine a
      | Refine_Fixpoint ->
        (match
          while_option (fun x -> not (equal_int_tuplea (it_refine x) x))
            it_refine a
          with None -> a | Some r -> r));;

let rec refine_ik_int_tuple _A
  c a b =
    (let (i1, i2) = refine_ik_ivl c (it_ivl a) (it_ivl b) in
     let (c1, c2) = refine_ik_congruence c (it_cong a) (it_cong b) in
      (it_refine_mode (int_mode _A Type) (IT (i1, c1)),
        it_refine_mode (int_mode _A Type) (IT (i2, c2))));;

let rec of_int_ik_congruence k n = congruence_of_int (ik_norm k n);;

let rec of_int_ik_int_tuple _A
  k n = IT (of_int_ik_ivl k n, of_int_ik_congruence k n);;

let rec int_congruence_update
  int_congruencea
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_parity, int_congruencea int_congruence, more);;

let rec answer_ik_congruence
  a = QLifted
        (int_congruence_update (fun _ -> a)
          (top_int_dom_ext bounded_lattice_unit));;

let rec inf_query_lift _A x0 uu = match x0, uu with QBot, uu -> QBot
                            | QLifted v, QBot -> QBot
                            | QTop, QBot -> QBot
                            | QTop, QLifted v -> QLifted v
                            | QTop, QTop -> QTop
                            | QLifted v, QTop -> QLifted v
                            | QLifted a, QLifted b -> QLifted (inf _A a b);;

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

let rec answer_ik_int_tuple _A
  a = inf_query_lift (inf_int_dom_ext bounded_lattice_unit)
        (answer_ik_ivl (it_ivl a)) (answer_ik_congruence (it_cong a));;

let rec cong_excludes
  x a = (match rep_congruence a with None -> true
          | Some (c, m) ->
            not (dvd (equal_int, semidom_modulo_int) m (minus_inta x c)));;

let rec norm_cong_ik
  k a = (match rep_congruence a with None -> bot_congruencea
          | Some (c, m) ->
            (let g = gcd_intc m (ik_mod k) in
              (if equal_inta g (ik_mod k) then congruence_of_int (ik_norm k c)
                else mk_congruence c g)));;

let rec cong_fits
  k a = (match rep_congruence a with None -> true
          | Some (c, m) ->
            equal_inta m zero_inta &&
              (less_eq_int (ik_min k) c && less_eq_int c (ik_max k)));;

let rec cong_arith_ik
  ovp k op operands_fit a b =
    (let r = cong_aop op a b in
      (if operands_fit &&
            (equal_aopa op AMod ||
              equal_aopa op ADiv && cong_excludes (uminus_inta one_inta) b)
        then r
        else (if should_wrap ovp k then norm_cong_ik k r
               else (if equal_aopa op ASub && cong_fits k r then r
                      else top_congruencea))));;

let rec arith_ik_congruence x = cong_arith_ik x;;

let rec arith_ik_int_tuple _A
  ovp k op fits a b =
    (let r = raw_aop_ik_ivl op (it_ivl a) (it_ivl b) in
      it_refine_mode (int_mode _A Type)
        (IT (cast_ik_ivl ovp None k r,
              (if fits_ik_ivl k r
                then raw_aop_ik_congruence op (it_cong a) (it_cong b)
                else arith_ik_congruence ovp k op fits (it_cong a)
                       (it_cong b)))));;

let rec meet_ik_congruence a b = inf_congruence a b;;

let rec meet_ik_int_tuple _A
  a b = it_refine_mode (int_mode _A Type)
          (IT (meet_ik_ivl (it_ivl a) (it_ivl b),
                meet_ik_congruence (it_cong a) (it_cong b)));;

let rec fits_ik_congruence x = cong_fits x;;

let rec fits_ik_int_tuple _A
  k a = fits_ik_ivl k (it_ivl a) || fits_ik_congruence k (it_cong a);;

let rec cast_cong_ik
  k a = (match rep_congruence a with None -> bot_congruencea
          | Some (c, m) ->
            (if equal_inta m zero_inta then congruence_of_int (ik_norm k c)
              else top_congruencea));;

let rec cast_ik_congruence
  ovp sk k a =
    (match sk with None -> cast_cong_ik k a
      | Some s -> (if ik_widens s k then a else cast_cong_ik k a));;

let rec cast_ik_int_tuple _A
  ovp sk k a =
    it_refine_mode (int_mode _A Type)
      (IT (cast_ik_ivl ovp sk k (it_ivl a),
            (if fits_ik_ivl k (it_ivl a) then it_cong a
              else cast_ik_congruence ovp sk k (it_cong a))));;

let rec top_ik_congruence k = top_congruencea;;

let rec top_ik_int_tuple _A k = IT (top_ik_ivl k, top_ik_congruence k);;

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

let rec cmp_ik_congruence x = cop_of congruence_lt cong_eq x;;

let rec cmp_ik_int_tuple _A
  c a b =
    (match cmp_ik_ivl c (it_ivl a) (it_ivl b)
      with None -> cmp_ik_congruence c (it_cong a) (it_cong b)
      | Some aa -> Some aa);;

let rec kind_int_domain_int_tuple _A =
  ({ik_domain_kind_int_domain = ik_domain_int_tuple;
     top_ik = top_ik_int_tuple _A; of_int_ik = of_int_ik_int_tuple _A;
     cast_ik = cast_ik_int_tuple _A; arith_ik = arith_ik_int_tuple _A;
     cmp_ik = cmp_ik_int_tuple _A; meet_ik = meet_ik_int_tuple _A;
     refine_ik = refine_ik_int_tuple _A; raw_aop_ik = raw_aop_ik_int_tuple _A;
     fits_ik = fits_ik_int_tuple _A; answer_ik = answer_ik_int_tuple _A;
     of_answer_ik = of_answer_ik_int_tuple _A}
    : 'a int_tuple kind_int_domain);;

type 'a order_rel = OBot | OFacts of bool * ('a * 'a) set;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec less_eq_set _A
  a b = match a, b with Set xs, b -> list_all (fun x -> member _A x b) xs
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Coset [], Set [] -> false;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec equal_order_rela _A
  x0 x1 = match x0, x1 with OBot, OFacts (x21, x22) -> false
    | OFacts (x21, x22), OBot -> false
    | OFacts (x21, x22), OFacts (y21, y22) ->
        equal_boola x21 y21 && equal_set (equal_prod _A _A) x22 y22
    | OBot, OBot -> true;;

let rec equal_order_rel _A =
  ({equal = equal_order_rela _A} : 'a order_rel equal);;

let rec sup_order_rela _A
  x0 b = match x0, b with OBot, b -> b
    | OFacts (v, va), OBot -> OFacts (v, va)
    | OFacts (t, a), OFacts (u, b) ->
        OFacts (t && u, inf_set (equal_prod _A _A) a b);;

let rec sup_order_rel _A = ({sup = sup_order_rela _A} : 'a order_rel sup);;

let bot_order_rela : 'a order_rel = OBot;;

let bot_order_rel = ({bot = bot_order_rela} : 'a order_rel bot);;

let rec less_eq_order_rel _A
  x0 uu = match x0, uu with OBot, uu -> true
    | OFacts (uv, uw), OBot -> false
    | OFacts (t, a), OFacts (u, b) ->
        less_eq_set (equal_prod _A _A) b a && (if u then t else true);;

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

let rec vjoin_order_rel _A = sup_order_rela _A;;

let rec join_val_order_rel _A =
  ({vjoin = vjoin_order_rel _A} : 'a order_rel join_val);;

let rec semilattice_sup_order_rel _A =
  ({sup_semilattice_sup = (sup_order_rel _A);
     order_semilattice_sup = (order_order_rel _A)}
    : 'a order_rel semilattice_sup);;

let rec split_global_at_order_rel x d = bot_order_rela;;

let rec split_free_order_rel r = bot_order_rela;;

let rec split_cmb_order_rel gs d g = d;;

let rec split_rl_order_rel gs d = d;;

type 'a ownership_split =
  {order_bot_ownership_split : 'a order_bot;
    split_cmb : var_id list -> 'a -> 'a -> 'a;
    split_rl : var_id list -> 'a -> 'a; split_global_at : var_id -> 'a -> 'a;
    split_free : var_id list -> 'a};;
let split_cmb _A = _A.split_cmb;;
let split_rl _A = _A.split_rl;;
let split_global_at _A = _A.split_global_at;;
let split_free _A = _A.split_free;;

let rec ownership_split_order_rel _A =
  ({order_bot_ownership_split = (order_bot_order_rel _A);
     split_cmb = split_cmb_order_rel; split_rl = split_rl_order_rel;
     split_global_at = split_global_at_order_rel;
     split_free = split_free_order_rel}
    : 'a order_rel ownership_split);;

let rec bounded_semilattice_sup_bot_order_rel _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_order_rel _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_order_rel _A)}
    : 'a order_rel bounded_semilattice_sup_bot);;

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
  gs d g =
    (match d with Bot -> Bot
      | Lifted a ->
        Lifted
          (split_cmb _A2 gs a
            (match g with Bot -> bot _A2.order_bot_ownership_split.bot_order_bot
              | Lifted b -> b)));;

let rec split_rl_lifted (_A1, _A2) gs = map_lift (split_rl _A2 gs);;

let rec ownership_split_lifted (_A1, _A2) =
  ({order_bot_ownership_split = (order_bot_lifted _A1);
     split_cmb = split_cmb_lifted (_A1, _A2);
     split_rl = split_rl_lifted (_A1, _A2);
     split_global_at = split_global_at_lifted (_A1, _A2);
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
  x d = default_st_set _A1 _B1.bot_order_bot
          (bot_gdefault_sta _B1.bot_order_bot)
          (Global_Location (key_of_var _A2 x))
          (default_st_get _A1 _B1.bot_order_bot d
            (Global_Location (key_of_var _A2 x)));;

let rec split_free_gdefault_st _A (_B1, _B2)
  r = Abs_default_st
        ((bot _B1.bot_order_bot, []),
          (top _B2.top_order_top,
            map (fun x -> (key_of_var _A x, bot _B1.bot_order_bot)) r));;

let rec split_cmb_gdefault_st (_A1, _A2) (_B1, _B2)
  gs d g =
    fold (fun x a ->
           default_st_set _A1 _B1.bot_order_bot a
             (Global_Location (key_of_var _A2 x))
             (default_st_get _A1 _B1.bot_order_bot g
               (Global_Location (key_of_var _A2 x))))
      gs d;;

let rec split_rl_gdefault_st (_A1, _A2) (_B1, _B2)
  gs d =
    fold (fun x a ->
           default_st_set _A1 _B1.bot_order_bot a
             (Global_Location (key_of_var _A2 x)) (bot _B1.bot_order_bot))
      gs d;;

let rec ownership_split_gdefault_st (_A1, _A2) (_B1, _B2) =
  ({order_bot_ownership_split =
      (order_bot_gdefault_st (_A2.infinite_key_split_key, _A1) _B1);
     split_cmb = split_cmb_gdefault_st (_A1, _A2) (_B1, _B2);
     split_rl = split_rl_gdefault_st (_A1, _A2) (_B1, _B2);
     split_global_at = split_global_at_gdefault_st (_A1, _A2) (_B1, _B2);
     split_free = split_free_gdefault_st _A2 (_B1, _B2)}
    : ('a, 'b) gdefault_st ownership_split);;

let rec bounded_semilattice_sup_bot_gdefault_st (_A1, _A2) _B =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_gdefault_st (_A1, _A2) _B);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_gdefault_st (_A1, _A2)
         _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) gdefault_st bounded_semilattice_sup_bot);;

type int_fixpoint = Int_Fixpoint;;

let rec int_mode_int_fixpoint uu = Refine_Fixpoint;;

let int_refinement_int_fixpoint =
  ({int_mode = int_mode_int_fixpoint} : int_fixpoint int_refinement);;

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
     fits_ik = fits_ik_congruence; answer_ik = answer_ik_congruence;
     of_answer_ik = of_answer_ik_congruence}
    : congruence kind_int_domain);;

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

let rec preorder_int_dom_ext _A =
  ({ord_preorder = (ord_int_dom_ext _A)} : 'a int_dom_ext preorder);;

let rec order_int_dom_ext _A =
  ({preorder_order = (preorder_int_dom_ext _A)} : 'a int_dom_ext order);;

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
  gs d g =
    Product
      (split_cmb _A gs (pleft d) (pleft g),
        split_cmb _B gs (pright d) (pright g));;

let rec split_rl_analysis_product _A _B
  gs d = Product (split_rl _A gs (pleft d), split_rl _B gs (pright d));;

let rec ownership_split_analysis_product _A _B =
  ({order_bot_ownership_split =
      (order_bot_analysis_product _A.order_bot_ownership_split
        _B.order_bot_ownership_split);
     split_cmb = split_cmb_analysis_product _A _B;
     split_rl = split_rl_analysis_product _A _B;
     split_global_at = split_global_at_analysis_product _A _B;
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

type arithmetic_hazard = Division_By_Zero | Signed_Overflow | Remainder_Overflow
  | Conversion_Overflow | Min_Conversion_Overflow | Max_Conversion_Overflow;;

let rec equal_arithmetic_hazard
  x0 x1 = match x0, x1 with
    Min_Conversion_Overflow, Max_Conversion_Overflow -> false
    | Max_Conversion_Overflow, Min_Conversion_Overflow -> false
    | Conversion_Overflow, Max_Conversion_Overflow -> false
    | Max_Conversion_Overflow, Conversion_Overflow -> false
    | Conversion_Overflow, Min_Conversion_Overflow -> false
    | Min_Conversion_Overflow, Conversion_Overflow -> false
    | Remainder_Overflow, Max_Conversion_Overflow -> false
    | Max_Conversion_Overflow, Remainder_Overflow -> false
    | Remainder_Overflow, Min_Conversion_Overflow -> false
    | Min_Conversion_Overflow, Remainder_Overflow -> false
    | Remainder_Overflow, Conversion_Overflow -> false
    | Conversion_Overflow, Remainder_Overflow -> false
    | Signed_Overflow, Max_Conversion_Overflow -> false
    | Max_Conversion_Overflow, Signed_Overflow -> false
    | Signed_Overflow, Min_Conversion_Overflow -> false
    | Min_Conversion_Overflow, Signed_Overflow -> false
    | Signed_Overflow, Conversion_Overflow -> false
    | Conversion_Overflow, Signed_Overflow -> false
    | Signed_Overflow, Remainder_Overflow -> false
    | Remainder_Overflow, Signed_Overflow -> false
    | Division_By_Zero, Max_Conversion_Overflow -> false
    | Max_Conversion_Overflow, Division_By_Zero -> false
    | Division_By_Zero, Min_Conversion_Overflow -> false
    | Min_Conversion_Overflow, Division_By_Zero -> false
    | Division_By_Zero, Conversion_Overflow -> false
    | Conversion_Overflow, Division_By_Zero -> false
    | Division_By_Zero, Remainder_Overflow -> false
    | Remainder_Overflow, Division_By_Zero -> false
    | Division_By_Zero, Signed_Overflow -> false
    | Signed_Overflow, Division_By_Zero -> false
    | Max_Conversion_Overflow, Max_Conversion_Overflow -> true
    | Min_Conversion_Overflow, Min_Conversion_Overflow -> true
    | Conversion_Overflow, Conversion_Overflow -> true
    | Remainder_Overflow, Remainder_Overflow -> true
    | Signed_Overflow, Signed_Overflow -> true
    | Division_By_Zero, Division_By_Zero -> true;;

type 'a arithmetic_obligation =
  Arithmetic_Obligation of arithmetic_hazard * 'a * 'a;;

let rec equal_arithmetic_obligationa _A
  (Arithmetic_Obligation (x1, x2, x3)) (Arithmetic_Obligation (y1, y2, y3)) =
    equal_arithmetic_hazard x1 y1 && (eq _A x2 y2 && eq _A x3 y3);;

let rec equal_arithmetic_obligation _A =
  ({equal = equal_arithmetic_obligationa _A} : 'a arithmetic_obligation equal);;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type ('b, 'a) rbt = RBT of ('b, 'a) rbta;;

type 'a fset = Abs_fset of 'a set;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

type phase = Widening | Narrowing;;

type 'a trace_key = Trace_Buffer | Trace_Global of string |
  Trace_Seed of cfg_node * 'a;;

type 'a bool_view = BV_Not of 'a | BV_And of 'a * 'a | BV_Or of 'a * 'a |
  BV_Atom;;

type ('a, 'b, 'c) gcfg_ext =
  Gcfg_ext of
    (cfg_node * (('a, 'b) gedge_action * cfg_node)) set *
      (cfg_node * (('a, 'b) gcall_action * (cfg_node * cfg_node))) set *
      cfg_node * 'c;;

type ('a, 'b, 'c) route_event = Ev_Route of 'a * 'b * 'c;;

type 'a ganalysis_event = Check_Event of (nat * nat) * 'a;;

type report_value = Interval_Value of ivl kd | Congruence_Value of congruence kd
  | Int_Value of unit int_tuple kd | Sign_Value of sign kd |
  Parity_Value of parity kd | Order_Value of ((string * string) list) option;;

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

type ('a, 'b, 'c, 'd) trace_printers =
  Trace_Printers of
    ('a -> string analysis_context) * ('b -> 'a trace_key) *
      ('c -> ((string * string field_state) list) lifted) *
      (string option -> 'c -> ((string * string field_state) list) lifted) *
      ('d -> ((string * string field_state) list) lifted);;

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

type 'a report_context = Report_Unit | Report_Entry of 'a |
  Report_Call_String of cfg_node list;;

type 'a unknown_node = Local_Node of cfg_node * nat | Global_Node of 'a;;

type 'a analysis_answer = Invalid_Activation | Malformed_Program | No_Answer |
  Analysed of 'a;;

type ('a, 'b) analysis_edge = Intra_Dep of ('a, 'b) gedge_action |
  Enter_Dep of ('a, 'b) gcall_action | Combine_Dep of ('a, 'b) gcall_action |
  Continue_Dep of ('a, 'b) gcall_action | Global_Read | Global_Write;;

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

type context_policy = Call_String of nat | Entry_State;;

type program_globals = Program_Globals_Flow_Sensitive |
  Program_Globals_Flow_Insensitive;;

type ('a, 'b) state_exta = State_exta of 'a set * 'b;;

type 'a result_global_unknown = Global_Named of 'a |
  Global_Seed of string * nat option;;

type ('a, 'b, 'c, 'd) ug_state_ext =
  Ug_state_ext of ('b -> ('a, 'c) fmap) * 'd;;

type 'a imp_prog_ext =
  Imp_prog_ext of
    (string * (unit, string, src_exp, unit) gproc_decl_ext) list * string list *
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

type ('a, 'b, 'c, 'd) footprints_ext =
  Footprints_ext of
    (('c -> bool) -> ('a, 'b) gedge_action -> 'c list) *
      (('c -> bool) -> ('a, 'b) gedge_action -> 'c list) *
      (('c -> bool) -> 'b list -> 'c list) *
      (('c -> bool) -> ('a, 'b) gcall_action -> 'c list) * 'd;;

type ('a, 'b, 'c, 'd) analysis_graph_ext =
  Analysis_graph_ext of
    'c unknown_node list *
      ('c unknown_node * (('a, 'b) analysis_edge * 'c unknown_node)) list * 'd;;

type 'a arithmetic_diagnostic =
  Arithmetic_Diagnostic of
    cfg_node * nat * 'a arithmetic_obligation * check_result;;

type ('a, 'b, 'c) result_global_ext =
  Result_global_ext of 'a result_global_unknown * 'b lifted * 'c;;

type ('a, 'b, 'c) result_state_ext =
  Result_state_ext of
    cfg_node * nat * 'b lifted * ('a * check_result lifted) list *
      ('a arithmetic_obligation * check_result lifted) list *
      (cfg_node * 'b lifted) list * 'c;;

type ('a, 'b) result_check_ext =
  Result_check_ext of cfg_node * (nat * nat) * 'a * check_result lifted * 'b;;

type ('a, 'b, 'c, 'd, 'e, 'f) run_result_ext =
  Run_result_ext of
    ('a, 'b, unit) gcfg_ext * 'e analysis_context list *
      ('b, (('d * 'e field_state) list), unit) result_state_ext list *
      (cfg_node *
        ((('d * 'e field_state) list) lifted *
          (cfg_node * (('d * 'e field_state) list) lifted) list)) list *
      unit call_route_ext list * ('b, unit) result_check_ext list *
      ('c, (('d * 'e field_state) list), unit) result_global_ext list *
      'b arithmetic_diagnostic list * ('a, 'b, 'c, unit) analysis_graph_ext *
      'f;;

type 'a sem_conf_ext = Sem_conf_ext of signed_overflow_policy * 'a;;

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

type 'a voblint_conf_ext =
  Voblint_conf_ext of
    analysis list * context_policy * globals_rule * program_globals *
      unit sem_conf_ext * 'a;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) analysis_report_ext =
  Analysis_report_ext of
    'a * 'c list * ('c, 'd, unit) gcfg_ext * 'b list *
      ('d, 'f, unit) result_state_ext list * unit call_route_ext list *
      ('d, unit) result_check_ext list * ('e, 'f, unit) result_global_ext list *
      'd arithmetic_diagnostic list * 'g;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) report_renderer_ext =
  Report_renderer_ext of
    ('a -> 'd list -> 'c -> ('g * 'h field_state) list) *
      ('a -> 'b -> 'h list) * ('d, 'e, 'f, unit) footprints_ext * 'i;;

type ('a, 'b, 'c) ug_state_with_gas_ext =
  Ug_state_with_gas_ext of ('b -> 'a -> phase * nat) * 'c;;

let rec id x = (fun xa -> xa) x;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec bex (Set xs) p = list_ex p xs;;

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

let rec nonrel_init_st _A
  ds = Abs_default_st
         ((KTop, []),
           (KD (I32, of_int_ik _A I32 zero_inta),
             map (fun (v, k) -> (v, KD (k, of_int_ik _A k zero_inta))) ds));;

let bot_set : 'a set = Set [];;

let rec mcp_init
  ds asa =
    Product
      ((if membera equal_analysis asa Interval
         then Lifted (nonrel_init_st kind_int_domain_ivl ds) else Bot),
        Product
          ((if membera equal_analysis asa Congruence
             then Lifted (nonrel_init_st kind_int_domain_congruence ds)
             else Bot),
            Product
              (Product
                 ((if membera equal_analysis asa (Ana_Int Refine_Never)
                    then Lifted
                           (nonrel_init_st
                             (kind_int_domain_int_tuple
                               int_refinement_int_never)
                             ds)
                    else Bot),
                   Product
                     ((if membera equal_analysis asa (Ana_Int Refine_Once)
                        then Lifted
                               (nonrel_init_st
                                 (kind_int_domain_int_tuple
                                   int_refinement_int_once)
                                 ds)
                        else Bot),
                       (if membera equal_analysis asa (Ana_Int Refine_Fixpoint)
                         then Lifted
                                (nonrel_init_st
                                  (kind_int_domain_int_tuple
                                    int_refinement_int_fixpoint)
                                  ds)
                         else Bot))),
                Product
                  ((if membera equal_analysis asa Sign
                     then Lifted (nonrel_init_st kind_int_domain_sign ds)
                     else Bot),
                    Product
                      ((if membera equal_analysis asa Parity
                         then Lifted (nonrel_init_st kind_int_domain_parity ds)
                         else Bot),
                        (if membera equal_analysis asa Order
                          then Lifted (OFacts (true, bot_set)) else Bot))))));;

let rec the_elem _A
  (Set xs) =
    (match remdups _A xs
      with [] ->
        failwith "the_elem: not a singleton" (fun _ -> the_elem _A (Set xs))
      | [x] -> x
      | _ :: _ :: _ ->
        failwith "the_elem: not a singleton" (fun _ -> the_elem _A (Set xs)));;

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
      (if equal_ikinda a b then a
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

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec location_of
  g x = (if g x then Global_Location x else Local_Location x);;

let rec default_st_to_fun _A _B
  g s x = default_st_get _A _B s (location_of g x);;

let rec nonrel_es_ctx _A
  g d ca =
    (let CallEdge (_, pars, _) = ca in
      (match d
        with Bot -> map (fun _ -> bot_kda _A.ik_domain_kind_int_domain) pars
        | Lifted st ->
          map (default_st_to_fun equal_var_id
                (bot_kd _A.ik_domain_kind_int_domain) g st)
            pars));;

let rec slot3 r = pleft (pright (pright r));;

let rec slot3o r = pleft (pright (slot3 r));;

let rec slot3n r = pleft (slot3 r);;

let rec slot3f r = pright (pright (slot3 r));;

let rec lift_get _B f x = (match x with Bot -> bot _B | Lifted a -> f a);;

let rec slot5 r = pleft (pright (pright (pright (pright r))));;

let rec slot4 r = pleft (pright (pright (pright r)));;

let rec slot2 r = pleft (pright r);;

let rec slot1 r = pleft r;;

let rec mcp_route
  asa g u ctx d ca =
    (let c =
       Product
         ((if membera equal_analysis asa Interval
            then nonrel_es_ctx kind_int_domain_ivl g
                   (lift_get
                     (bot_lifted
                       (semilattice_sup_gdefault_st
                         (infinite_key_var_id, equal_var_id)
                         (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                     slot1 d)
                   ca
            else []),
           Product
             ((if membera equal_analysis asa Congruence
                then nonrel_es_ctx kind_int_domain_congruence g
                       (lift_get
                         (bot_lifted
                           (semilattice_sup_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence)))
                         slot2 d)
                       ca
                else []),
               Product
                 (Product
                    ((if membera equal_analysis asa (Ana_Int Refine_Never)
                       then nonrel_es_ctx
                              (kind_int_domain_int_tuple
                                int_refinement_int_never)
                              g (lift_get
                                  (bot_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))
                                  slot3n d)
                              ca
                       else []),
                      Product
                        ((if membera equal_analysis asa (Ana_Int Refine_Once)
                           then nonrel_es_ctx
                                  (kind_int_domain_int_tuple
                                    int_refinement_int_once)
                                  g (lift_get
                                      (bot_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                      slot3o d)
                                  ca
                           else []),
                          (if membera equal_analysis asa
                                (Ana_Int Refine_Fixpoint)
                            then nonrel_es_ctx
                                   (kind_int_domain_int_tuple
                                     int_refinement_int_fixpoint)
                                   g (lift_get
                                       (bot_lifted
 (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       slot3f d)
                                   ca
                            else []))),
                   Product
                     ((if membera equal_analysis asa Sign
                        then nonrel_es_ctx kind_int_domain_sign g
                               (lift_get
                                 (bot_lifted
                                   (semilattice_sup_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 slot4 d)
                               ca
                        else []),
                       Product
                         ((if membera equal_analysis asa Parity
                            then nonrel_es_ctx kind_int_domain_parity g
                                   (lift_get
                                     (bot_lifted
                                       (semilattice_sup_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     slot5 d)
                                   ca
                            else []),
                           [])))))
       in
     let _ = Solver_trace_hook.emit "route" (fun _ -> Ev_Route ((u, ctx), d, c))
       in
      c);;

let rec enumerate n x1 = match n, x1 with n, [] -> []
                    | n, x :: xs -> (n, x) :: enumerate (suc n) xs;;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec cfg_entry (Gcfg_ext (intra, calls, cfg_entry, more)) = cfg_entry;;

let rec cfg_exit
  g = (match cfg_entry g
        with Statement nat ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> Statement nat)
        | FunctionEntry a -> FunctionResult a
        | FunctionResult literal ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> FunctionResult literal));;

let rec kenv_of
  ds v = (match map_of equal_var_id ds v with None -> I32 | Some k -> k);;

let rec cast_to ik k a = (if equal_ikinda ik k then a else TCast (ik, a));;

let rec top_query_lift _A = QTop;;

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
                 (top_query_lift (order_int_dom_ext bounded_lattice_unit)))
      else (if member (equal_gquery _A) q asked
             then sp_return
                    (top_query_lift (order_int_dom_ext bounded_lattice_unit))
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

let mcp_root_ctx :
  ((ivl kd list),
    ((congruence kd list),
      (((int_never int_tuple kd list),
         ((int_once int_tuple kd list), (int_fixpoint int_tuple kd list))
           analysis_product)
         analysis_product,
        ((sign kd list), ((parity kd list), (unit list)) analysis_product)
          analysis_product)
        analysis_product)
      analysis_product)
    analysis_product
  = Product
      ([], Product
             ([], Product
                    (Product ([], Product ([], [])),
                      Product ([], Product ([], [])))));;

let rec slot6 r = pright (pright (pright (pright (pright r))));;

let rec live
  x0 r = match x0, r with
    Interval, r ->
      not (equal_lifteda
            (equal_gdefault_st (infinite_key_var_id, equal_var_id)
              ((equal_kd equal_ivl), (order_bot_kd ik_domain_ivl)))
            (slot1 r) Bot)
    | Congruence, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_congruence),
                  (order_bot_kd ik_domain_congruence)))
              (slot2 r) Bot)
    | Ana_Int Refine_Never, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_int_tuple),
                  (order_bot_kd ik_domain_int_tuple)))
              (slot3n r) Bot)
    | Ana_Int Refine_Once, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_int_tuple),
                  (order_bot_kd ik_domain_int_tuple)))
              (slot3o r) Bot)
    | Ana_Int Refine_Fixpoint, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_int_tuple),
                  (order_bot_kd ik_domain_int_tuple)))
              (slot3f r) Bot)
    | Sign, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_sign), (order_bot_kd ik_domain_sign)))
              (slot4 r) Bot)
    | Parity, r ->
        not (equal_lifteda
              (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                ((equal_kd equal_parity), (order_bot_kd ik_domain_parity)))
              (slot5 r) Bot)
    | Order, r ->
        not (equal_lifteda (equal_order_rel equal_var_id) (slot6 r) Bot);;

let rec ask_rec _A
  h n asked x q =
    (if equal_nata n zero_nat
      then failwith "query recursion exceeded query_depth"
             (fun _ -> top_query_lift (order_int_dom_ext bounded_lattice_unit))
      else (if member (equal_gquery _A) q asked
             then top_query_lift (order_int_dom_ext bounded_lattice_unit)
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

let rec mcp_qry
  cs ch x q =
    fold (fun c r ->
           inf_query_lift (inf_int_dom_ext bounded_lattice_unit) r
             (ls_query c ch x q))
      cs (top_query_lift (order_int_dom_ext bounded_lattice_unit));;

let rec elaborate
  rho kappa ik x3 = match rho, kappa, ik, x3 with
    rho, kappa, ik, N n -> TN (ik, n)
    | rho, kappa, ik, V x ->
        cast_to ik (kappa (rho x)) (TVar (kappa (rho x), rho x))
    | rho, kappa, ik, Plus (a, b) ->
        (let k = esyn (comp kappa rho) (Plus (a, b)) in
          cast_to ik k
            (TArith
              (k, AAdd, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Minus (a, b) ->
        (let k = esyn (comp kappa rho) (Minus (a, b)) in
          cast_to ik k
            (TArith
              (k, ASub, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Times (a, b) ->
        (let k = esyn (comp kappa rho) (Times (a, b)) in
          cast_to ik k
            (TArith
              (k, AMul, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Div (a, b) ->
        (let k = esyn (comp kappa rho) (Div (a, b)) in
          cast_to ik k
            (TArith
              (k, ADiv, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Mod (a, b) ->
        (let k = esyn (comp kappa rho) (Mod (a, b)) in
          cast_to ik k
            (TArith
              (k, AMod, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Less (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CLt, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, LessEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CLe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Greater (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CGt, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, GreaterEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CGe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, NotEq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CNe, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Eq (a, b) ->
        (let k = usual_kind (esyn (comp kappa rho) a) (esyn (comp kappa rho) b)
           in
          cast_to ik I32
            (TCmp (CEq, elaborate rho kappa k a, elaborate rho kappa k b)))
    | rho, kappa, ik, Not a ->
        cast_to ik I32 (TNot (elaborate rho kappa (esyn (comp kappa rho) a) a))
    | rho, kappa, ik, And (a, b) ->
        cast_to ik I32
          (TAnd (elaborate rho kappa (esyn (comp kappa rho) a) a,
                  elaborate rho kappa (esyn (comp kappa rho) b) b))
    | rho, kappa, ik, Or (a, b) ->
        cast_to ik I32
          (TOr (elaborate rho kappa (esyn (comp kappa rho) a) a,
                 elaborate rho kappa (esyn (comp kappa rho) b) b))
    | rho, kappa, ik, Cast (k, a) ->
        cast_to ik k
          (TCast (k, elaborate rho kappa (esyn (comp kappa rho) a) a));;

let rec elaborate_syn
  rho kappa e = elaborate rho kappa (esyn (comp kappa rho) e) e;;

let rec resolve_var g q x = (if g x then GlobalId x else ScopedId (q, x));;

let rec elab_args
  rho kappa x2 es = match rho, kappa, x2, es with
    rho, kappa, f :: fs, e :: es ->
      elaborate rho kappa (kappa f) e :: elab_args rho kappa fs es
    | rho, kappa, [], es -> map (elaborate_syn rho kappa) es
    | rho, kappa, v :: va, [] -> [];;

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

let rec exp_kind = function TN (ik, uu) -> ik
                   | TVar (ik, uv) -> ik
                   | TArith (ik, uw, ux, uy) -> ik
                   | TCast (ik, uz) -> ik
                   | TCmp (va, vb, vc) -> I32
                   | TNot vd -> I32
                   | TAnd (ve, vf) -> I32
                   | TOr (vg, vh) -> I32;;

let rec sup_set _A
  x0 a = match x0, a with Set xs, a -> fold (inserta _A) xs a
    | Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs);;

let rec exp_vars
  = function TN (uu, uv) -> bot_set
    | TVar (uw, v) -> inserta equal_var_id v bot_set
    | TArith (ux, uy, a, b) -> sup_set equal_var_id (exp_vars a) (exp_vars b)
    | TCast (uz, a) -> exp_vars a
    | TCmp (va, a, b) -> sup_set equal_var_id (exp_vars a) (exp_vars b)
    | TNot a -> exp_vars a
    | TAnd (a, b) -> sup_set equal_var_id (exp_vars a) (exp_vars b)
    | TOr (a, b) -> sup_set equal_var_id (exp_vars a) (exp_vars b);;

let query_depth : nat = nat_of_integer (Z.of_int 1024);;

let rec outer_man _A
  q m = man_ask_update (fun _ -> ask_with _A q query_depth bot_set m) m;;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filtera (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (eq _A aa a));;

let rec activation_of
  asa = (if null asa then [Interval] else remdups equal_analysis asa);;

let rec combine_default_st_rep _A sc se = (fst sc, snd se);;

let rec combine_default_st _B
  (Abs_default_st xa) (Abs_default_st x) =
    Abs_default_st (combine_default_st_rep _B xa x);;

let rec sem_int_signed_overflow
  (Sem_conf_ext (sem_int_signed_overflow, more)) = sem_int_signed_overflow;;

let rec kd_kind
  d = (match d with KBot -> None | KD (k, _) -> Some k | KTop -> None);;

let rec kd_val _A
  = function
    KBot ->
      bot _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
    | KD (k, a) -> a
    | KTop ->
        top _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.order_top_executable_domain.top_order_top;;

let rec is_global = function GlobalId uu -> true
                    | ScopedId (v, va) -> false
                    | ReturnId v -> false
                    | ReturnVar -> false;;

let rec combine_assign_st _A
  sem kappa dst st ste =
    (match dst with None -> st
      | Some x ->
        default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
          (location_of is_global x)
          (KD (kappa x,
                cast_ik _A (sem_int_signed_overflow sem)
                  (kd_kind
                    (default_st_to_fun equal_var_id
                      (bot_kd _A.ik_domain_kind_int_domain) is_global ste
                      ReturnVar))
                  (kappa x)
                  (kd_val _A
                    (default_st_to_fun equal_var_id
                      (bot_kd _A.ik_domain_kind_int_domain) is_global ste
                      ReturnVar)))));;

let rec src_kind
  kappa e =
    (match e with TN (_, _) -> Some (exp_kind e)
      | TVar (ik, v) ->
        (if not (equal_var_ida v ReturnVar) && equal_ikinda ik (kappa v)
          then Some ik else None)
      | TArith (_, _, _, _) -> Some (exp_kind e)
      | TCast (_, _) -> Some (exp_kind e) | TCmp (_, _, _) -> Some (exp_kind e)
      | TNot _ -> Some (exp_kind e) | TAnd (_, _) -> Some (exp_kind e)
      | TOr (_, _) -> Some (exp_kind e));;

let rec truth_ik _A a = cmp_ik _A CNe a (of_int_ik _A I32 zero_inta);;

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

let rec aeval _A
  sem kappa ch x3 sigma = match sem, kappa, ch, x3, sigma with
    sem, kappa, ch, TN (ik, n), sigma -> of_int_ik _A ik n
    | sem, kappa, ch, TVar (ik, v), sigma -> read_var _A kappa sigma v
    | sem, kappa, ch, TArith (ik, op, a, b), sigma ->
        arith_ik _A (sem_int_signed_overflow sem) ik op
          (equal_option equal_ikind (src_kind kappa a) (Some ik) &&
            equal_option equal_ikind (src_kind kappa b) (Some ik))
          (aeval_ask _A sem kappa ch a sigma)
          (aeval_ask _A sem kappa ch b sigma)
    | sem, kappa, ch, TCast (ik, a), sigma ->
        cast_ik _A (sem_int_signed_overflow sem) (src_kind kappa a) ik
          (aeval_ask _A sem kappa ch a sigma)
    | sem, kappa, ch, TCmp (op, a, b), sigma ->
        bool_val _A
          (cmp_ik _A op (aeval_ask _A sem kappa ch a sigma)
            (aeval_ask _A sem kappa ch b sigma))
    | sem, kappa, ch, TNot a, sigma ->
        bool_val _A
          (map_option not (truth_ik _A (aeval_ask _A sem kappa ch a sigma)))
    | sem, kappa, ch, TAnd (a, b), sigma ->
        bool_val _A
          (match
            (truth_ik _A (aeval_ask _A sem kappa ch a sigma),
              truth_ik _A (aeval_ask _A sem kappa ch b sigma))
            with (None, None) -> None | (None, Some true) -> None
            | (None, Some false) -> Some false | (Some true, None) -> None
            | (Some true, Some true) -> Some true
            | (Some true, Some false) -> Some false
            | (Some false, _) -> Some false)
    | sem, kappa, ch, TOr (a, b), sigma ->
        bool_val _A
          (match
            (truth_ik _A (aeval_ask _A sem kappa ch a sigma),
              truth_ik _A (aeval_ask _A sem kappa ch b sigma))
            with (None, None) -> None | (None, Some true) -> Some true
            | (None, Some false) -> None | (Some true, _) -> Some true
            | (Some false, None) -> None | (Some false, Some true) -> Some true
            | (Some false, Some false) -> Some false)
and aeval_ask _A
  sem kappa ch e sigma =
    (match e with TN (a, b) -> of_int_ik _A a b
      | TVar (_, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TArith (_, _, _, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TCast (_, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TCmp (_, _, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TNot _ ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TAnd (_, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma)
      | TOr (_, _) ->
        (match ch (EvalInt e)
          with QBot ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) QBot)
          | QLifted a ->
            meet_ik _A (aeval _A sem kappa ch e sigma)
              (of_answer_ik _A (src_kind kappa e) (QLifted a))
          | QTop -> aeval _A sem kappa ch e sigma));;

let rec nonrel_query _A
  sem kappa ch sigma (EvalInt e) =
    answer_ik _A (aeval _A sem kappa ch e sigma);;

let rec normalize_lift empty_pred a = (if empty_pred a then Bot else Lifted a);;

let rec transfer_lift2
  empty_pred f x y =
    bind_lift x
      (fun a -> bind_lift y (fun b -> normalize_lift empty_pred (f a b)));;

let rec transfer_lift
  empty_pred f x = bind_lift x (fun a -> normalize_lift empty_pred (f a));;

let rec pair_kind
  kappa a b =
    (if equal_option equal_ikind (src_kind kappa a) (src_kind kappa b)
      then src_kind kappa a else None);;

let rec min_ik _A
  a b = sup _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
          (fst (refine_ik _A CLe a b)) (snd (refine_ik _A CGt a b));;

let rec max_ik _A
  a b = sup _A.ik_domain_kind_int_domain.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
          (snd (refine_ik _A CLe a b)) (fst (refine_ik _A CGt a b));;

let rec special_val _A
  sem kappa ch sc x sigma =
    (match sc with Nondet_Int -> top_ik _A (kappa x)
      | Min (a, b) ->
        cast_ik _A (sem_int_signed_overflow sem) (pair_kind kappa a b) (kappa x)
          (min_ik _A (aeval_ask _A sem kappa ch a sigma)
            (aeval_ask _A sem kappa ch b sigma))
      | Max (a, b) ->
        cast_ik _A (sem_int_signed_overflow sem) (pair_kind kappa a b) (kappa x)
          (max_ik _A (aeval_ask _A sem kappa ch a sigma)
            (aeval_ask _A sem kappa ch b sigma)));;

let rec special_st _A
  sem kappa ch sc x st =
    default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
      (location_of is_global x)
      (KD (kappa x,
            special_val _A sem kappa ch sc x
              (default_st_to_fun equal_var_id
                (bot_kd _A.ik_domain_kind_int_domain) is_global st)));;

let rec ci_formals
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_formals;;

let rec is_empty_kd _A = function KBot -> true
                         | KD (k, a) -> empty_ik _A k a
                         | KTop -> false;;

let rec st_rep_is_bot _A
  ((dl, ls), (dg, gs)) =
    is_empty_kd _A.ik_domain_kind_int_domain dl ||
      (is_empty_kd _A.ik_domain_kind_int_domain dg ||
        (list_ex
           (fun x ->
             not (is_global x) &&
               is_empty_kd _A.ik_domain_kind_int_domain
                 (default_dict_get equal_var_id (dl, ls) x))
           (map fst ls) ||
          list_ex
            (fun x ->
              is_global x &&
                is_empty_kd _A.ik_domain_kind_int_domain
                  (default_dict_get equal_var_id (dg, gs) x))
            (map fst gs)));;

let rec st_is_bot _A (Abs_default_st x) = st_rep_is_bot _A x;;

let rec ret_kd _A
  sem kappa ch e sigma =
    (match e
      with TN (_, _) -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TVar (_, v) ->
        (if equal_var_ida v ReturnVar then KTop
          else KD (kappa v, read_var _A kappa sigma v))
      | TArith (_, _, _, _) ->
        KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TCast (_, _) -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TCmp (_, _, _) -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TNot _ -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TAnd (_, _) -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma)
      | TOr (_, _) -> KD (exp_kind e, aeval_ask _A sem kappa ch e sigma));;

let rec return_st _A
  sem kappa ch r st =
    (match r with None -> st
      | Some e ->
        default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
          (location_of is_global ReturnVar)
          (ret_kd _A sem kappa ch e
            (default_st_to_fun equal_var_id
              (bot_kd _A.ik_domain_kind_int_domain) is_global st)));;

let rec nonrel_view = function TNot a -> BV_Not a
                      | TAnd (a, b) -> BV_And (a, b)
                      | TOr (a, b) -> BV_Or (a, b)
                      | TN (v, va) -> BV_Atom
                      | TVar (v, va) -> BV_Atom
                      | TArith (v, va, vb, vc) -> BV_Atom
                      | TCast (v, va) -> BV_Atom
                      | TCmp (v, va, vb) -> BV_Atom;;

let rec nonrel_feas _A
  sem kappa ch e pol sigma =
    not (equal_option equal_bool
          (truth_ik _A (aeval_ask _A sem kappa ch e sigma)) (Some (not pol)));;

let rec narrow_var _A
  kappa v a sigma =
    (if equal_var_ida v ReturnVar then sigma
      else fun_upd equal_var_id sigma v
             (KD (kappa v, meet_ik _A a (read_var _A kappa sigma v))));;

let rec refine_var _A
  sem kappa ch x3 a sigma = match sem, kappa, ch, x3, a, sigma with
    sem, kappa, ch, TVar (ik, v), a, sigma -> narrow_var _A kappa v a sigma
    | sem, kappa, ch, TCast (ik, e), a, sigma ->
        (if fits_ik _A ik (aeval_ask _A sem kappa ch e sigma)
          then refine_var _A sem kappa ch e a sigma else sigma)
    | sem, kappa, ch, TArith (ik, op, e_1, e_2), a, sigma ->
        (let a_1 = aeval_ask _A sem kappa ch e_1 sigma in
         let a_2 = aeval_ask _A sem kappa ch e_2 sigma in
          (if fits_ik _A ik (raw_aop_ik _A op a_1 a_2)
            then (match op
                   with AAdd ->
                     refine_var _A sem kappa ch e_2 (raw_aop_ik _A ASub a a_1)
                       (refine_var _A sem kappa ch e_1
                         (raw_aop_ik _A ASub a a_2) sigma)
                   | ASub ->
                     refine_var _A sem kappa ch e_2 (raw_aop_ik _A ASub a_1 a)
                       (refine_var _A sem kappa ch e_1
                         (raw_aop_ik _A AAdd a a_2) sigma)
                   | AMul -> sigma | ADiv -> sigma | AMod -> sigma)
            else (if not (member equal_aop op
                           (inserta equal_aop AAdd
                             (inserta equal_aop ASub bot_set)))
                   then sigma
                   else (let sigmaa =
                           (if equal_option equal_ikind (src_kind kappa e_1)
                                 (Some ik)
                             then refine_var _A sem kappa ch e_1
                                    (arith_ik _A (sem_int_signed_overflow sem)
                                      ik (if equal_aopa op AAdd then ASub
   else AAdd)
                                      false a a_2)
                                    sigma
                             else sigma)
                           in
                          (if equal_option equal_ikind (src_kind kappa e_2)
                                (Some ik)
                            then refine_var _A sem kappa ch e_2
                                   (if equal_aopa op AAdd
                                     then arith_ik _A
    (sem_int_signed_overflow sem) ik ASub false a a_1
                                     else arith_ik _A
    (sem_int_signed_overflow sem) ik ASub false a_1 a)
                                   sigmaa
                            else sigmaa)))))
    | sem, kappa, ch, TN (v, va), a, sigma -> sigma
    | sem, kappa, ch, TCmp (v, va, vb), a, sigma -> sigma
    | sem, kappa, ch, TNot v, a, sigma -> sigma
    | sem, kappa, ch, TAnd (v, va), a, sigma -> sigma
    | sem, kappa, ch, TOr (v, va), a, sigma -> sigma;;

let rec neg_cop = function CLt -> CGe
                  | CLe -> CGt
                  | CGt -> CLe
                  | CGe -> CLt
                  | CEq -> CNe
                  | CNe -> CEq;;

let rec nonrel_narrow _A
  sem kappa ch e pol sigma =
    (match e
      with TN (_, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TVar (_, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TArith (_, _, _, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TCast (_, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TCmp (c, l, r) ->
        (let (al, ar) =
           refine_ik _A (if pol then c else neg_cop c)
             (aeval_ask _A sem kappa ch l sigma)
             (aeval_ask _A sem kappa ch r sigma)
           in
          refine_var _A sem kappa ch l al
            (refine_var _A sem kappa ch r ar sigma))
      | TNot _ ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TAnd (_, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma
      | TOr (_, _) ->
        refine_var _A sem kappa ch e
          (fst (refine_ik _A (if pol then CNe else CEq)
                 (aeval_ask _A sem kappa ch e sigma)
                 (of_int_ik _A (exp_kind e) zero_inta)))
          sigma);;

let rec bot_fun _B x = bot _B;;

let rec nonrel_atom _A
  sem kappa ch e pol sigma =
    (let sigmaa = nonrel_narrow _A sem kappa ch e pol sigma in
      (if bex (exp_vars e)
            (fun v -> is_empty_kd _A.ik_domain_kind_int_domain (sigmaa v))
        then bot_fun (bot_kd _A.ik_domain_kind_int_domain) else sigmaa));;

let rec sup_fun _B f g x = sup _B.sup_semilattice_sup (f x) (g x);;

let rec nonrel_refine_exec _A
  sem kappa ch e pol sigma =
    (match nonrel_view e
      with BV_Not a -> nonrel_refine_exec _A sem kappa ch a (not pol) sigma
      | BV_And (a, b) ->
        (if pol
          then nonrel_refine_exec _A sem kappa ch b true
                 (nonrel_refine_exec _A sem kappa ch a true sigma)
          else (match
                 (nonrel_feas _A sem kappa ch a false sigma,
                   nonrel_feas _A sem kappa ch b false sigma)
                 with (true, true) ->
                   sup_fun (semilattice_sup_kd _A.ik_domain_kind_int_domain)
                     (nonrel_refine_exec _A sem kappa ch a false sigma)
                     (nonrel_refine_exec _A sem kappa ch b false sigma)
                 | (true, false) ->
                   nonrel_refine_exec _A sem kappa ch a false sigma
                 | (false, true) ->
                   nonrel_refine_exec _A sem kappa ch b false sigma
                 | (false, false) ->
                   bot_fun (bot_kd _A.ik_domain_kind_int_domain)))
      | BV_Or (a, b) ->
        (if pol
          then (match
                 (nonrel_feas _A sem kappa ch a true sigma,
                   nonrel_feas _A sem kappa ch b true sigma)
                 with (true, true) ->
                   sup_fun (semilattice_sup_kd _A.ik_domain_kind_int_domain)
                     (nonrel_refine_exec _A sem kappa ch a true sigma)
                     (nonrel_refine_exec _A sem kappa ch b true sigma)
                 | (true, false) ->
                   nonrel_refine_exec _A sem kappa ch a true sigma
                 | (false, true) ->
                   nonrel_refine_exec _A sem kappa ch b true sigma
                 | (false, false) ->
                   bot_fun (bot_kd _A.ik_domain_kind_int_domain))
          else nonrel_refine_exec _A sem kappa ch b false
                 (nonrel_refine_exec _A sem kappa ch a false sigma))
      | BV_Atom -> nonrel_atom _A sem kappa ch e pol sigma);;

let rec nonrel_refine _A sem kappa ch = nonrel_refine_exec _A sem kappa ch;;

let rec write_back _A
  vs sigma st =
    fold (fun v sta ->
           default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) sta
             (location_of is_global v) (sigma v))
      vs st;;

let rec var_list = function TN (uu, uv) -> []
                   | TVar (uw, v) -> [v]
                   | TArith (ux, uy, a, b) -> var_list a @ var_list b
                   | TCast (uz, a) -> var_list a
                   | TCmp (va, a, b) -> var_list a @ var_list b
                   | TNot a -> var_list a
                   | TAnd (a, b) -> var_list a @ var_list b
                   | TOr (a, b) -> var_list a @ var_list b;;

let rec branch_st _A
  sem kappa ch b pol st =
    (let refined =
       write_back _A (var_list b)
         (nonrel_refine _A sem kappa ch b pol
           (default_st_to_fun equal_var_id (bot_kd _A.ik_domain_kind_int_domain)
             is_global st))
         st
       in
      (match
        truth_ik _A
          (aeval_ask _A sem kappa ch b
            (default_st_to_fun equal_var_id
              (bot_kd _A.ik_domain_kind_int_domain) is_global st))
        with None -> refined
        | Some r ->
          (if equal_boola r pol then refined
            else bot_gdefault_sta (bot_kd _A.ik_domain_kind_int_domain))));;

let rec assign_st _A
  sem kappa ch x e st =
    default_st_set equal_var_id (bot_kd _A.ik_domain_kind_int_domain) st
      (location_of is_global x)
      (KD (kappa x,
            cast_ik _A (sem_int_signed_overflow sem) (src_kind kappa e)
              (kappa x)
              (aeval_ask _A sem kappa ch e
                (default_st_to_fun equal_var_id
                  (bot_kd _A.ik_domain_kind_int_domain) is_global st))));;

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

let rec enter_st _A
  sem kappa ch ps es st =
    bind_formals_default_st equal_var_id (bot_kd _A.ik_domain_kind_int_domain)
      is_global ps
      (map (fun (x, y) ->
             KD (kappa x,
                  cast_ik _A (sem_int_signed_overflow sem) (src_kind kappa y)
                    (kappa x)
                    (aeval_ask _A sem kappa ch y
                      (default_st_to_fun equal_var_id
                        (bot_kd _A.ik_domain_kind_int_domain) is_global st))))
        (zip ps es))
      (enter_frame_D_default_st (bot_kd _A.ik_domain_kind_int_domain) KTop st);;

let rec ci_args
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_args;;

let rec ci_dst
  (Gcall_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_dst;;

let rec nonrel_exec_spec _A
  sem kappa =
    Glocal_spec_ext
      ((fun ch d q ->
         (match d
           with Bot -> top_query_lift (order_int_dom_ext bounded_lattice_unit)
           | Lifted x ->
             nonrel_query _A sem kappa ch
               (default_st_to_fun equal_var_id
                 (bot_kd _A.ik_domain_kind_int_domain) is_global x)
               q)),
        (fun _ d -> d),
        (fun ch x e ->
          transfer_lift (st_is_bot _A) (assign_st _A sem kappa ch x e)),
        (fun ch sc x ->
          transfer_lift (st_is_bot _A) (special_st _A sem kappa ch sc x)),
        (fun ch b pol ->
          transfer_lift (st_is_bot _A) (branch_st _A sem kappa ch b pol)),
        (fun _ _ d -> d),
        (fun ch r _ ->
          transfer_lift (st_is_bot _A) (return_st _A sem kappa ch r)),
        (fun _ _ d -> d),
        (fun ch ci p ->
          [(fst p,
             transfer_lift (st_is_bot _A)
               (enter_st _A sem kappa ch (ci_formals ci) (ci_args ci))
               (fst p))]),
        (fun _ _ _ x y ->
          bind_lift x
            (fun a ->
              bind_lift y
                (fun b ->
                  Lifted
                    (combine_default_st (bot_kd _A.ik_domain_kind_int_domain) a
                      b)))),
        (fun _ ci ->
          transfer_lift2 (st_is_bot _A)
            (combine_assign_st _A sem kappa (ci_dst ci))),
        ());;

let rec length_tailrec x0 n = match x0, n with [], n -> n
                         | x :: xs, n -> length_tailrec xs (suc n);;

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

let rec declared_global_vars
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = declared_global_vars;;

let rec formals (Gproc_decl_ext (formals, body, more)) = formals;;

let rec body (Gproc_decl_ext (formals, body, more)) = body;;

let rec proc_rep
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = proc_rep;;

let rec prog_table p = map_of equal_literal (proc_rep p);;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

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

let ret_var : string = "#ret";;

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

let rec declared_global p x = membera equal_literal (declared_global_vars p) x;;

let prog_main_name : string = "main";;

let rec prog_procs
  p = filtera (fun n -> not ((n : string) = prog_main_name))
        (map fst (proc_rep p));;

let rec ord_vars
  p = remdups equal_var_id
        (maps (fun q ->
                map_filter
                  (fun x ->
                    (if not ((x : string) = ret_var)
                      then Some (resolve_var (declared_global p) q x)
                      else None))
                  (scope_vnames_list p q))
          (prog_main_name :: prog_procs p));;

let rec combine_env_identity cha ch ci x de = x;;

let rec ord_in_kinds
  d = (match d with Bot -> false | Lifted OBot -> false
        | Lifted (OFacts (t, _)) -> t);;

let rec ord_forget _A
  x xa1 = match x, xa1 with x, OBot -> OBot
    | x, OFacts (t, ps) ->
        OFacts
          (t, filter (fun (a, b) -> not (eq _A a x) && not (eq _A b x)) ps);;

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
    TCmp (c, TVar (ka, x), TVar (k, y)), pol, OFacts (t, ps) ->
      OFacts
        (t, sup_set (equal_prod equal_var_id equal_var_id) ps
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

let rec int_dom_of_int
  n = int_congruence_update (fun _ -> congruence_of_int n)
        (int_parity_update (fun _ -> parity_of_int n)
          (int_ivl_update (fun _ -> Ivl (Fin n, Fin n))
            (int_sign_update (fun _ -> sign_of_int n)
              (top_int_dom_ext bounded_lattice_unit))));;

let rec answer_of_int n = QLifted (int_dom_of_int n);;

let rec ord_le
  d x y =
    (match d with OBot -> false
      | OFacts (_, ps) ->
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

let rec ord_query
  ch d q = match ch, d, q with
    ch, Lifted d, EvalInt (TCmp (c, TVar (ka, x), TVar (k, y))) ->
      (match ord_decide c d x y
        with None -> top_query_lift (order_int_dom_ext bounded_lattice_unit)
        | Some b -> answer_of_int (if b then one_inta else zero_inta))
    | ch, Bot, q -> top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TN (va, vb)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TVar (va, vb)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TArith (va, vb, vc, vd)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCast (va, vb)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TN (vd, ve), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TArith (vd, ve, vf, vg), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TCast (vd, ve), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TCmp (vd, ve, vf), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TNot vd, vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TAnd (vd, ve), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, TOr (vd, ve), vc)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TN (vd, ve))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TArith (vd, ve, vf, vg))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TCast (vd, ve))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TCmp (vd, ve, vf))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TNot vd)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TAnd (vd, ve))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TCmp (va, vb, TOr (vd, ve))) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TNot va) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TAnd (va, vb)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit)
    | ch, d, EvalInt (TOr (va, vb)) ->
        top_query_lift (order_int_dom_ext bounded_lattice_unit);;

let rec int_dom_constant
  d = (if equal_signa (int_sign d) SZero then Some zero_inta
        else (match ivl_constant (int_ivl d)
               with None -> congruence_constant (int_congruence d)
               | Some a -> Some a));;

let rec answer_const = function QLifted d -> int_dom_constant d
                       | QBot -> None
                       | QTop -> None;;

let rec ord_copy
  kappa x e ps =
    (match e with TN (_, _) -> bot_set
      | TVar (_, y) ->
        (if not (equal_var_ida y x) &&
              (not (equal_var_ida y ReturnVar) &&
                equal_ikinda (kappa y) (kappa x))
          then sup_set (equal_prod equal_var_id equal_var_id)
                 (sup_set (equal_prod equal_var_id equal_var_id)
                   (inserta (equal_prod equal_var_id equal_var_id) (x, y)
                     (inserta (equal_prod equal_var_id equal_var_id) (y, x)
                       bot_set))
                   (image (fun (_, a) -> (x, a))
                     (filter (fun (a, _) -> equal_var_ida a y) ps)))
                 (image (fun (a, _) -> (a, x))
                   (filter (fun (_, b) -> equal_var_ida b y) ps))
          else bot_set)
      | TArith (_, _, _, _) -> bot_set | TCast (_, _) -> bot_set
      | TCmp (_, _, _) -> bot_set | TNot _ -> bot_set | TAnd (_, _) -> bot_set
      | TOr (_, _) -> bot_set);;

let rec ord_learn
  kappa ys ch x e d =
    (match d with OBot -> OBot
      | OFacts (t, ps) ->
        OFacts
          (t, sup_set (equal_prod equal_var_id equal_var_id)
                (sup_set (equal_prod equal_var_id equal_var_id)
                  (sup_set (equal_prod equal_var_id equal_var_id) ps
                    (if t then ord_copy kappa x e ps else bot_set))
                  (Set (map_filter
                         (fun xa ->
                           (if not (equal_var_ida xa x) &&
                                 equal_option equal_int
                                   (answer_const
                                     (ch (EvalInt
   (TCmp (CLe, TCast (kappa x, e), TVar (kappa xa, xa))))))
                                   (Some one_inta)
                             then Some (x, xa) else None))
                         ys)))
                (Set (map_filter
                       (fun xa ->
                         (if not (equal_var_ida xa x) &&
                               equal_option equal_int
                                 (answer_const
                                   (ch (EvalInt
 (TCmp (CLe, TVar (kappa xa, xa), TCast (kappa x, e))))))
                                 (Some one_inta)
                           then Some (xa, x) else None))
                       ys))));;

let rec ord_enter ps es d = OFacts (ord_in_kinds d, bot_set);;

let rec ord_spec
  kappa ys =
    Glocal_spec_ext
      (ord_query, (fun _ d -> d),
        (fun ch x e ->
          map_lift
            (comp (ord_learn kappa ys ch x e) (ord_forget equal_var_id x))),
        (fun _ _ x -> map_lift (ord_forget equal_var_id x)),
        (fun _ b pol -> map_lift (ord_branch b pol)), (fun _ _ d -> d),
        (fun _ r _ d ->
          (match r with None -> d
            | Some _ -> map_lift (ord_forget equal_var_id ReturnVar) d)),
        (fun _ _ d -> d),
        (fun _ ci p ->
          [(fst p, Lifted (ord_enter (ci_formals ci) (ci_args ci) (fst p)))]),
        combine_env_identity,
        (fun _ _ d de ->
          Lifted (OFacts (ord_in_kinds d && ord_in_kinds de, bot_set))),
        ());;

let rec set_slot3
  r v = Product
          (pleft r,
            Product
              (pleft (pright r), Product (v, pright (pright (pright r)))));;

let rec set_slot3o
  r v = set_slot3 r (Product (slot3n r, Product (v, slot3f r)));;

let rec set_slot3n r v = set_slot3 r (Product (v, pright (slot3 r)));;

let rec set_slot3f
  r v = set_slot3 r (Product (slot3n r, Product (slot3o r, v)));;

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
                          (pleft (pright (pright (pright (pright r)))), v)))));;

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

let rec set_slot2 r v = Product (pleft r, Product (v, pright (pright r)));;

let rec set_slot1 r v = Product (v, pright r);;

let rec lift_put _A (_B1, _B2)
  u x v =
    (match x
      with Bot -> (if eq _B1 v (bot _B2) then Bot else Lifted (u (bot _A) v))
      | Lifted r -> Lifted (u r v));;

let rec field
  sem kappa p a =
    (match a
      with Interval ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
            slot1)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_ivl),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl))))
            set_slot1)
          (nonrel_exec_spec kind_int_domain_ivl sem kappa)
      | Congruence ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
            slot2)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_congruence),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_congruence).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_congruence))))
            set_slot2)
          (nonrel_exec_spec kind_int_domain_congruence sem kappa)
      | Ana_Int Refine_Never ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
            slot3n)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_int_tuple),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple))))
            set_slot3n)
          (nonrel_exec_spec (kind_int_domain_int_tuple int_refinement_int_never)
            sem kappa)
      | Ana_Int Refine_Once ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
            slot3o)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_int_tuple),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple))))
            set_slot3o)
          (nonrel_exec_spec (kind_int_domain_int_tuple int_refinement_int_once)
            sem kappa)
      | Ana_Int Refine_Fixpoint ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
            slot3f)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_int_tuple),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple))))
            set_slot3f)
          (nonrel_exec_spec
            (kind_int_domain_int_tuple int_refinement_int_fixpoint) sem kappa)
      | Order ->
        lens_of
          (lift_get (bot_lifted (semilattice_sup_order_rel equal_var_id)) slot6)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted (equal_order_rel equal_var_id)),
              (bot_lifted (semilattice_sup_order_rel equal_var_id)))
            set_slot6)
          (ord_spec kappa (ord_vars p))
      | Sign ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_sign)))
            slot4)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_sign),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_sign))))
            set_slot4)
          (nonrel_exec_spec kind_int_domain_sign sem kappa)
      | Parity ->
        lens_of
          (lift_get
            (bot_lifted
              (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                (bounded_semilattice_sup_bot_kd ik_domain_parity)))
            slot5)
          (lift_put
            (bot_analysis_product
              (order_bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
              (order_bot_analysis_product
                (order_bot_lifted
                  (semilattice_sup_gdefault_st
                    (infinite_key_var_id, equal_var_id)
                    (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                (order_bot_analysis_product
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_int_tuple)))))
                  (order_bot_analysis_product
                    (order_bot_lifted
                      (semilattice_sup_gdefault_st
                        (infinite_key_var_id, equal_var_id)
                        (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                    (order_bot_analysis_product
                      (order_bot_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                      (order_bot_lifted
                        (semilattice_sup_order_rel equal_var_id)))))))
            ((equal_lifted
               (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                 ((equal_kd equal_parity),
                   (bounded_semilattice_sup_bot_kd
                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot))),
              (bot_lifted
                (semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
                  (bounded_semilattice_sup_bot_kd ik_domain_parity))))
            set_slot5)
          (nonrel_exec_spec kind_int_domain_parity sem kappa));;

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

let rec conf_program_globals
  (Voblint_conf_ext
    (conf_analyses, conf_context, conf_globals, conf_program_globals, conf_sem,
      more))
    = conf_program_globals;;

let rec conf_analyses
  (Voblint_conf_ext
    (conf_analyses, conf_context, conf_globals, conf_program_globals, conf_sem,
      more))
    = conf_analyses;;

let rec conf_globals
  (Voblint_conf_ext
    (conf_analyses, conf_context, conf_globals, conf_program_globals, conf_sem,
      more))
    = conf_globals;;

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

let rec sp_bind m f k = m (fun v -> f v k);;

let rec man_sideg
  (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) = man_sideg;;

let rec publish_at
  m rg x2 r = match m, rg, x2, r with m, rg, [], r -> sp_return ()
    | m, rg, x :: xs, r ->
        sp_bind (man_sideg m x (rg x r)) (fun _ -> publish_at m rg xs r);;

let rec man_local
  (Gman_ext (man_local, man_global, man_sideg, man_ask, more)) = man_local;;

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

let rec read_view _E
  m rg x2 acc = match m, rg, x2, acc with m, rg, [], acc -> sp_return acc
    | m, rg, x :: xs, acc ->
        sp_bind (man_global m x)
          (fun g ->
            read_view _E m rg xs (sup _E.sup_semilattice_sup (rg x g) acc));;

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

let rec keyed_transfer _A
  cmb rl rg free r w f m =
    sp_bind
      (read_view _A.semilattice_sup_bounded_semilattice_sup_bot m rg r (free r))
      (fun g ->
        sp_bind (publish_at m rg w (f (cmb (man_local m) g)))
          (fun _ -> sp_return (rl (f (cmb (man_local m) g)))));;

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

let rec gedge_writes rv x1 = match rv, x1 with rv, EA_Assign (x, a) -> [x]
                       | rv, EA_Special (sc, x) -> [x]
                       | rv, EA_Ret (e, p) -> [rv]
                       | rv, EA_Nop -> []
                       | rv, EA_Assume v -> []
                       | rv, EA_AssumeNot v -> []
                       | rv, EA_Body v -> []
                       | rv, EA_Check (v, va) -> [];;

let rec global_names_in _A g xs = remdups _A (filtera g xs);;

let rec gedge_global_writes _A
  rv g a = global_names_in _A g (gedge_writes rv a);;

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

let rec gedge_reads (_B1, _B2)
  evars a =
    sorted_list_of_set (_B1, _B2)
      (sup_seta _B1 (image evars (Set (edge_expressions a))));;

let rec gedge_global_reads (_B1, _B2)
  evars g a = global_names_in _B1 g (gedge_reads (_B1, _B2) evars a);;

let rec gcall_global_reads (_B1, _B2)
  evars g es =
    global_names_in _B1 g
      (sorted_list_of_set (_B1, _B2) (sup_seta _B1 (image evars (Set es))));;

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
          sp_return (top_query_lift (order_int_dom_ext bounded_lattice_unit))),
        ());;

let rec ls_channel _B c x = ask_rec _B (ls_query c) query_depth bot_set x;;

let rec closed_step _B c a d = ls_step c (ls_channel _B c d) a d;;

let rec gkeyed_split_spec _A (_B1, _B2) _C
  evars rv g cmb rl rg free c =
    (let step =
       (fun a ->
         keyed_transfer _C cmb rl rg free
           (gedge_global_reads (_B1, _B2) evars g a)
           (gedge_global_writes _B1 rv g a) (closed_step _A c a))
       in
      dgs_combine_assign_update
        (fun _ ci ->
          keyed_combine_transfer _C cmb rl rg free
            (global_names_in _B1 g
              (match ci_dst ci with None -> [] | Some x -> [x]))
            (fun dc de ->
              ls_combine_assign c (ls_channel _A c de) ci
                (ls_combine_env c (ls_channel _A c dc) (ls_channel _A c de) ci
                  dc de)
                de))
        (dgs_event_update (fun _ ev -> step (event_action ev))
          (dgs_enter_update
            (fun _ ci ->
              keyed_enter_transfer _C cmb rl rg free
                (gcall_global_reads (_B1, _B2) evars g (ci_args ci))
                (global_names_in _B1 g (ci_formals ci))
                (fun d -> ls_enter c (ls_channel _A c d) ci (d, d)))
            (dgs_return_update (fun _ e p -> step (EA_Ret (e, p)))
              (dgs_body_update (fun _ p -> step (EA_Body p))
                (dgs_branch_update
                  (fun _ b pol ->
                    step (if pol then EA_Assume b else EA_AssumeNot b))
                  (dgs_special_update (fun _ sc x -> step (EA_Special (sc, x)))
                    (dgs_assign_update (fun _ x e -> step (EA_Assign (x, e)))
                      (dgs_skip_update (fun _ -> step EA_Nop)
                        local_dg_spec_template)))))))));;

let rec canonicalize_lift empty_pred = transfer_lift empty_pred id;;

let rec genv key tau v = dg_global (tau (Inr (key v)));;

let rec dg_result_for
  rd emp rc gk sol =
    Solved_Table
      (fst sol,
        (fun v ctx ->
          map_lift rd
            (canonicalize_lift emp
              (rc (dg_local (snd sol (Inl (v, ctx)))) (genv gk (snd sol))))));;

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

let rec ce_formals (CallEdge (x1, x2, x3)) = x2;;

let rec ce_args (CallEdge (x1, x2, x3)) = x3;;

let rec ce_dst (CallEdge (x1, x2, x3)) = x1;;

let rec call_info_of
  ca p = Gcall_info_ext (ce_dst ca, p, ce_formals ca, ce_args ca, ());;

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

let rec conf_sem
  (Voblint_conf_ext
    (conf_analyses, conf_context, conf_globals, conf_program_globals, conf_sem,
      more))
    = conf_sem;;

let rec group_lookup _A
  m k = (match lookup _A m k with None -> [] | Some ys -> ys);;

let rec group_by_key _B
  key_of f xs =
    foldr (fun x m ->
            (match f x with None -> m
              | Some y ->
                insert _B (key_of x) (y :: group_lookup _B m (key_of x)) m))
      xs (empty _B);;

let rec intra (Gcfg_ext (intra, calls, cfg_entry, more)) = intra;;

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

let rec calls (Gcfg_ext (intra, calls, cfg_entry, more)) = calls;;

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

let rec sp_publish g d k = Side (g, d, k ());;

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

let rec dg_sideg _D gk gd = sp_publish gk (DG (bot _D, gd));;

let rec mk_dg_man _A
  d unknown_of =
    Gman_ext
      (d, (fun v -> dg_read_global (unknown_of v)),
        (fun v -> dg_sideg _A (unknown_of v)),
        (fun _ ->
          sp_return (top_query_lift (order_int_dom_ext bounded_lattice_unit))),
        ());;

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

let rec view_of _B
  rg xs e acc = fold (fun x -> sup _B.sup_semilattice_sup (rg x (e x))) xs acc;;

let rec full_view _B
  rg xs e =
    view_of _B.semilattice_sup_bounded_semilattice_sup_bot rg xs e
      (bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec cs_route k u ctx d ca = take k (u :: ctx);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

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

let rec truncate r = Ug_state_ext (rho r, ());;

let rec changed _A
  d res =
    (match res with None -> None
      | Some da -> (if eq _A da d then None else Some da));;

let rec lift_basic_rule _A
  f da orig g d state =
    (let (res, st) = f da orig g d (truncate state) in
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

let rec stabl (State_ext (called, infl, stabl, sigma, more)) = stabl;;

let rec infl (State_ext (called, infl, stabl, sigma, more)) = infl;;

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

let rec solve_c_traced _A _B (_C1, _C2, _C3)
  r t x =
    (let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Start x) in
     let res = tD_side_rule_Interp_solve_c _A _B (_C1, _C2, _C3) r t x in
     let _ = Solver_trace_hook.emit "solver" (fun _ -> Ev_Stop) in
      res);;

let rec declared_globals
  p = map (fun a -> GlobalId a) (declared_global_vars p);;

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
          FunctionEntry prog_main_name, ()));;

let rec prog_formals
  p q = (match prog_table p q with None -> [] | Some a -> formals a);;

let rec elab_ptable
  p ds q =
    map_option
      (fun d ->
        Gproc_decl_ext
          (map (resolve_var (declared_global p) q) (formals d),
            elab_com (declared_global p) (prog_formals p) (kenv_of ds) q
              (body d),
            ()))
      (prog_table p q);;

let rec elab_cfg
  p ds = compile_prog equal_var_id equal_exp (elab_ptable p ds) (prog_procs p);;

let rec arithmetic_expression_sites (_A1, _A2) (_B1, _B2)
  g = (let edges = cfg_intra_list (_A1, _A2) (_B1, _B2) g in
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
                              equal_gedge_actiona _A1 _B1 a (EA_Assume e))
                          edges)
                  | (_, (EA_Body _, _)) -> true
                  | (_, (EA_Ret (_, _), _)) -> true
                  | (_, (EA_Check (_, _), _)) -> true)
              then Some (let (u, (a, _)) = x in (u, edge_expressions a))
              else None))
          edges) @
        map (fun (u, (ca, (_, _))) -> (u, ce_args ca))
          (cfg_calls_list (_A1, _A2) (_B1, _B2) g);;

let rec obligation_sites (_A1, _A2) (_B1, _B2)
  obls g =
    map (fun (v, es) -> (v, maps obls es))
      (arithmetic_expression_sites (_B1, _B2) (_A1, _A2) g);;

let rec arith_obligations
  = function
    TN (k, n) ->
      (if less_eq_int (ik_min k) n && less_eq_int n (ik_max k) then []
        else [Arithmetic_Obligation
                (Conversion_Overflow, TN (k, n), TN (k, n))])
    | TVar (uu, uv) -> []
    | TArith (k, op, a, b) ->
        arith_obligations a @
          arith_obligations b @
            (if equal_aopa op ADiv || equal_aopa op AMod
              then [Arithmetic_Obligation
                      (Division_By_Zero, TArith (k, op, a, b), b)]
              else []) @
              (if not (ik_signed k) then []
                else (if equal_aopa op AMod
                       then [Arithmetic_Obligation
                               (Remainder_Overflow, TArith (k, op, a, b),
                                 TArith (k, ADiv, a, b))]
                       else [Arithmetic_Obligation
                               (Signed_Overflow, TArith (k, op, a, b),
                                 TArith (k, op, a, b))]))
    | TCast (k, a) ->
        arith_obligations a @
          (if ik_widens (exp_kind a) k then []
            else [Arithmetic_Obligation (Conversion_Overflow, TCast (k, a), a)])
    | TCmp (uw, a, b) -> arith_obligations a @ arith_obligations b
    | TNot a -> arith_obligations a
    | TAnd (a, b) -> arith_obligations a @ arith_obligations b
    | TOr (a, b) -> arith_obligations a @ arith_obligations b;;

let rec special_obligations
  k x1 = match k, x1 with
    k, Min (a, b) ->
      (if ik_widens (exp_kind a) k && ik_widens (exp_kind b) k then []
        else [Arithmetic_Obligation (Min_Conversion_Overflow, TCast (k, a), b)])
    | k, Max (a, b) ->
        (if ik_widens (exp_kind a) k && ik_widens (exp_kind b) k then []
          else [Arithmetic_Obligation
                  (Max_Conversion_Overflow, TCast (k, a), b)])
    | k, Nondet_Int -> [];;

let rec special_sites
  ds p =
    maps (fun a ->
           (match a with (_, (EA_Nop, _)) -> []
             | (_, (EA_Assign (_, _), _)) -> []
             | (v, (EA_Special (sc, x), _)) ->
               (if not (null (special_obligations (kenv_of ds x) sc))
                 then [(v, special_obligations (kenv_of ds x) sc)] else [])
             | (_, (EA_Assume _, _)) -> [] | (_, (EA_AssumeNot _, _)) -> []
             | (_, (EA_Body _, _)) -> [] | (_, (EA_Ret (_, _), _)) -> []
             | (_, (EA_Check (_, _), _)) -> []))
      (cfg_intra_list (equal_var_id, linorder_var_id) (equal_exp, linorder_exp)
        (elab_cfg p ds));;

let rec callee_of_entry = function FunctionEntry p -> p
                          | Statement v -> ""
                          | FunctionResult v -> "";;

let rec return_sites
  ds p =
    (let g = elab_cfg p ds in
      remdups
        (equal_prod equal_cfg_node
          (equal_list (equal_arithmetic_obligation equal_exp)))
        (maps (fun (_, (ca, (ce, _))) ->
                (match ce_dst ca with None -> []
                  | Some x ->
                    maps (fun a ->
                           (match a with (_, (EA_Nop, _)) -> []
                             | (_, (EA_Assign (_, _), _)) -> []
                             | (_, (EA_Special (_, _), _)) -> []
                             | (_, (EA_Assume _, _)) -> []
                             | (_, (EA_AssumeNot _, _)) -> []
                             | (_, (EA_Body _, _)) -> []
                             | (_, (EA_Ret (None, _), _)) -> []
                             | (v, (EA_Ret (Some e, q), _)) ->
                               (if ((q : string) = (callee_of_entry ce)) &&
                                     not (ik_widens (exp_kind e) (kenv_of ds x))
                                 then [(v,
 [Arithmetic_Obligation (Conversion_Overflow, TCast (kenv_of ds x, e), e)])]
                                 else [])
                             | (_, (EA_Check (_, _), _)) -> []))
                      (cfg_intra_list (equal_var_id, linorder_var_id)
                        (equal_exp, linorder_exp) g)))
          (cfg_calls_list (equal_var_id, linorder_var_id)
            (equal_exp, linorder_exp) g)));;

let rec prog_obligation_sites
  ds p =
    obligation_sites (equal_exp, linorder_exp) (equal_var_id, linorder_var_id)
      arith_obligations (elab_cfg p ds) @
      return_sites ds p @ special_sites ds p;;

let rec arithmetic_operation (Arithmetic_Obligation (x1, x2, x3)) = x2;;

let rec arithmetic_operand (Arithmetic_Obligation (x1, x2, x3)) = x3;;

let rec arithmetic_hazard (Arithmetic_Obligation (x1, x2, x3)) = x1;;

let rec ivl_min
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (min ord_eint l1 l2, min ord_eint u1 u2));;

let rec ivl_max
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (max ord_eint l1 l2, max ord_eint u1 u2));;

let rec arith_condition
  ob = TCmp (CNe, arithmetic_operand ob,
              TN (exp_kind (arithmetic_operand ob), zero_inta));;

let rec operand_ivl
  ch x1 = match ch, x1 with
    ch, TN (k, n) -> Ivl (Fin (ik_norm k n), Fin (ik_norm k n))
    | ch, TCmp (c, a, b) ->
        inf_ivl (of_answer_ik_ivl None (ch (EvalInt (TCmp (c, a, b)))))
          (Ivl (Fin zero_inta, Fin one_inta))
    | ch, TNot a ->
        inf_ivl (of_answer_ik_ivl None (ch (EvalInt (TNot a))))
          (Ivl (Fin zero_inta, Fin one_inta))
    | ch, TAnd (a, b) ->
        inf_ivl (of_answer_ik_ivl None (ch (EvalInt (TAnd (a, b)))))
          (Ivl (Fin zero_inta, Fin one_inta))
    | ch, TOr (a, b) ->
        inf_ivl (of_answer_ik_ivl None (ch (EvalInt (TOr (a, b)))))
          (Ivl (Fin zero_inta, Fin one_inta))
    | ch, TVar (v, va) -> of_answer_ik_ivl None (ch (EvalInt (TVar (v, va))))
    | ch, TArith (v, va, vb, vc) ->
        of_answer_ik_ivl None (ch (EvalInt (TArith (v, va, vb, vc))))
    | ch, TCast (v, va) ->
        of_answer_ik_ivl None (ch (EvalInt (TCast (v, va))));;

let rec unwrapped_ivl
  ch x1 = match ch, x1 with ch, TN (k, n) -> Ivl (Fin n, Fin n)
    | ch, TArith (k, op, a, b) ->
        ivl_aop op (operand_ivl ch a) (operand_ivl ch b)
    | ch, TCast (k, a) -> operand_ivl ch a
    | ch, TVar (v, va) -> operand_ivl ch (TVar (v, va))
    | ch, TCmp (v, va, vb) -> operand_ivl ch (TCmp (v, va, vb))
    | ch, TNot v -> operand_ivl ch (TNot v)
    | ch, TAnd (v, va) -> operand_ivl ch (TAnd (v, va))
    | ch, TOr (v, va) -> operand_ivl ch (TOr (v, va));;

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

let rec answer_excludes
  n x1 = match n, x1 with
    n, QLifted d ->
      is_bottom_int_dom
        (inf_int_dom_exta bounded_lattice_unit d (int_dom_of_int n))
    | n, QBot -> true
    | n, QTop -> false;;

let rec classify_answer
  = function QBot -> Bot
    | QLifted v ->
        (if answer_excludes zero_inta (QLifted v) then Lifted Check_Proved
          else (if answer_excludes one_inta (QLifted v)
                 then Lifted Check_Refuted else Lifted Check_Unknown))
    | QTop ->
        (if answer_excludes zero_inta QTop then Lifted Check_Proved
          else (if answer_excludes one_inta QTop then Lifted Check_Refuted
                 else Lifted Check_Unknown));;

let rec answer_check
  tx q c v =
    (match classify_answer (q v (EvalInt (tx c))) with Bot -> Check_Unknown
      | Lifted r -> r);;

let rec truth_exp
  = function TCmp (op, a, b) -> TCmp (op, a, b)
    | TNot a -> TNot a
    | TAnd (a, b) -> TAnd (a, b)
    | TOr (a, b) -> TOr (a, b)
    | TN (v, va) -> TCmp (CNe, TN (v, va), TN (I32, zero_inta))
    | TVar (v, va) -> TCmp (CNe, TVar (v, va), TN (I32, zero_inta))
    | TArith (v, va, vb, vc) ->
        TCmp (CNe, TArith (v, va, vb, vc), TN (I32, zero_inta))
    | TCast (v, va) -> TCmp (CNe, TCast (v, va), TN (I32, zero_inta));;

let rec t_answer _A
  sem kappa x ch q =
    (match x with Bot -> top_query_lift (order_int_dom_ext bounded_lattice_unit)
      | Lifted d -> nonrel_query _A sem kappa ch d q);;

let rec answer
  sem kappa x2 v ch = match sem, kappa, x2, v, ch with
    sem, kappa, Interval, v, ch ->
      t_answer kind_int_domain_ivl sem kappa (slot1 v) ch
    | sem, kappa, Congruence, v, ch ->
        t_answer kind_int_domain_congruence sem kappa (slot2 v) ch
    | sem, kappa, Ana_Int Refine_Never, v, ch ->
        t_answer (kind_int_domain_int_tuple int_refinement_int_never) sem kappa
          (slot3n v) ch
    | sem, kappa, Ana_Int Refine_Once, v, ch ->
        t_answer (kind_int_domain_int_tuple int_refinement_int_once) sem kappa
          (slot3o v) ch
    | sem, kappa, Ana_Int Refine_Fixpoint, v, ch ->
        t_answer (kind_int_domain_int_tuple int_refinement_int_fixpoint) sem
          kappa (slot3f v) ch
    | sem, kappa, Sign, v, ch ->
        t_answer kind_int_domain_sign sem kappa (slot4 v) ch
    | sem, kappa, Parity, v, ch ->
        t_answer kind_int_domain_parity sem kappa (slot5 v) ch
    | sem, kappa, Order, v, ch -> ord_query ch (slot6 v);;

let rec mcp_answer
  sem ds asa ch v q =
    fold (fun a r ->
           inf_query_lift (inf_int_dom_ext bounded_lattice_unit) r
             (answer sem (kenv_of ds) a v ch q))
      asa (top_query_lift (order_int_dom_ext bounded_lattice_unit));;

let rec mcp_ask
  sem ds asa v =
    ask_rec equal_exp (mcp_answer sem ds asa) query_depth bot_set v;;

let rec mcp_classify sem ds asa = answer_check truth_exp (mcp_ask sem ds asa);;

let rec fits_verdict
  k i = (if is_bottom_ivl i then Check_Unknown
          else (if less_eq_ivl i (ik_ivl k) then Check_Proved
                 else (if is_bottom_ivl (inf_ivl i (ik_ivl k))
                        then Check_Refuted else Check_Unknown)));;

let rec obligation_classify
  sem ds asa ob v =
    (let ch = mcp_ask sem ds asa v in
     let e = arithmetic_operation ob in
     let i = unwrapped_ivl ch e in
     let j = operand_ivl ch (arithmetic_operand ob) in
      (match arithmetic_hazard ob
        with Division_By_Zero -> mcp_classify sem ds asa (arith_condition ob) v
        | Signed_Overflow -> fits_verdict (exp_kind e) i
        | Remainder_Overflow ->
          fits_verdict (exp_kind e) (unwrapped_ivl ch (arithmetic_operand ob))
        | Conversion_Overflow -> fits_verdict (exp_kind e) i
        | Min_Conversion_Overflow -> fits_verdict (exp_kind e) (ivl_min i j)
        | Max_Conversion_Overflow -> fits_verdict (exp_kind e) (ivl_max i j)));;

let rec arithmetic_diagnostic_of
  v i obligation x3 = match v, i, obligation, x3 with
    v, i, obligation, Lifted Check_Refuted ->
      [Arithmetic_Diagnostic (v, i, obligation, Check_Refuted)]
    | v, i, obligation, Lifted Check_Unknown ->
        [Arithmetic_Diagnostic (v, i, obligation, Check_Unknown)]
    | v, i, obligation, Bot -> []
    | v, i, obligation, Lifted Check_Proved -> [];;

let rec aggregate_verdicts
  (Set vs) = fold (sup_lifteda semilattice_sup_check_result) vs Bot;;

let rec classify_point
  classify c x2 = match classify, c, x2 with classify, c, Bot -> Bot
    | classify, c, Lifted st -> Lifted (classify c st);;

let rec covered_keys (Solved_Table (x1, x2)) = x1;;

let rec table_contexts
  r v = image snd
          (filter (fun (va, _) -> equal_cfg_nodea va v) (covered_keys r));;

let rec table_at (Solved_Table (x1, x2)) = x2;;

let rec lookup_table _A
  r v ctx =
    (if member (equal_prod equal_cfg_node _A) (v, ctx) (covered_keys r)
      then table_at r v ctx else Bot);;

let rec point_verdict _A
  r classify v e =
    aggregate_verdicts
      (image (fun ctx -> classify_point classify e (lookup_table _A r v ctx))
        (table_contexts r v));;

let rec arithmetic_diagnostics _B
  sites r classify =
    maps (fun (v, obligations) ->
           maps (fun (i, obligation) ->
                  arithmetic_diagnostic_of v i obligation
                    (point_verdict _B r classify v obligation))
             (zip (upt zero_nat (size_list obligations)) obligations))
      sites;;

let rec run_shared
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_shared;;

let rec ea_check_cond (EA_Check (x81, x82)) = x82;;

let rec run_table
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_table;;

let rec run_succ
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_succ;;

let rec run_seed
  (Gsolved_run_ext (run_table, run_shared, run_seed, run_step, run_succ, more))
    = run_seed;;

let rec is_EA_Check = function EA_Nop -> false
                      | EA_Assign (x21, x22) -> false
                      | EA_Special (x31, x32) -> false
                      | EA_Assume x4 -> false
                      | EA_AssumeNot x5 -> false
                      | EA_Body x6 -> false
                      | EA_Ret (x71, x72) -> false
                      | EA_Check (x81, x82) -> true;;

let rec ea_check_label (EA_Check (x81, x82)) = x81;;

let rec result_checks_of (_A1, _A2) (_B1, _B2) _C
  g r classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      Result_check_ext
                        (u, ea_check_label a, ea_check_cond a,
                          point_verdict _C r classify u (ea_check_cond a), ()))
          else None))
      (cfg_intra_list (_A1, _A2) (_B1, _B2) g);;

let rec minus_set _A
  a x1 = match a, x1 with a, Set xs -> fold (remove _A) xs a
    | a, Coset xs -> Set (filtera (fun x -> member _A x a) xs);;

let rec context_indices _A
  indexed ctx =
    map_filter
      (fun x ->
        (if (let (_, ctxa) = x in eq _A ctxa ctx) then Some (fst x) else None))
      indexed;;

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

let rec report_row _C
  sr classify classify_ob conds obls edges i ctx v =
    (let state = lookup_table _C (run_table sr) v ctx in
      Result_state_ext
        (v, i, state,
          map (fun c -> (c, classify_point classify c state))
            (group_lookup linorder_cfg_node conds v),
          map (fun obligation ->
                (obligation, classify_point classify_ob obligation state))
            (concat (group_lookup linorder_cfg_node obls v)),
          map (fun (a, w) -> (w, run_step sr v ctx a))
            (group_lookup linorder_cfg_node edges v),
          ()));;

let rec cfg_node_list (_A1, _A2) (_B1, _B2)
  g = remdups equal_cfg_node
        (maps (fun (u, (_, v)) -> [u; v])
           (cfg_intra_list (_A1, _A2) (_B1, _B2) g) @
          maps (fun (u, (_, (ce, after))) -> [u; ce; after])
            (cfg_calls_list (_A1, _A2) (_B1, _B2) g) @
            [cfg_entry g]);;

let rec report_of (_B1, _B2) (_C1, _C2) _F
  config vars g globals sites classify_ob procs ctx_key ctx_tag classify sr =
    (let r = run_table sr in
     let ctxs =
       ordered_by_key _F (equal_order_key, linorder_order_key) ctx_key
         (image snd (covered_keys r))
       in
     let indexed = enumerate zero_nat ctxs in
     let nodes =
       cfg_node_list (_B1, _B2) (_C1, _C2) g @
         sorted_list_of_set (equal_cfg_node, linorder_cfg_node)
           (minus_set equal_cfg_node (image fst (covered_keys r))
             (Set (cfg_node_list (_B1, _B2) (_C1, _C2) g)))
       in
     let intra = cfg_intra_list (_B1, _B2) (_C1, _C2) g in
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
       group_by_key linorder_cfg_node fst (comp (fun a -> Some a) snd) sites in
     let state_at =
       report_row _F sr classify classify_ob checks obligations steps in
     let route_at =
       (fun u ca ce i ctx ->
         Call_route_ext
           (u, i, callee_of_entry ce,
             (match lookup_table _F r u ctx with Bot -> []
               | Lifted _ ->
                 remdups equal_nat
                   (maps (context_indices _F indexed)
                     (live_targets (run_succ sr) u ctx ca
                       (callee_of_entry ce)))),
             ()))
       in
     let seeds_of =
       (fun f ->
         (match
           filtera
             (fun (_, ctx) ->
               member (equal_prod equal_cfg_node _F) (FunctionEntry f, ctx)
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
        (config, vars, g, map ctx_tag ctxs,
          maps (fun (i, ctx) ->
                 map_filter
                   (fun x ->
                     (if member (equal_prod equal_cfg_node _F) (x, ctx)
                           (covered_keys r)
                       then Some (state_at i ctx x) else None))
                   nodes)
            indexed,
          maps (fun (u, (ca, (ce, _))) ->
                 map_filter
                   (fun x ->
                     (if (let (_, ctx) = x in
                           member (equal_prod equal_cfg_node _F) (u, ctx)
                             (covered_keys r))
                       then Some (let (a, b) = x in route_at u ca ce a b)
                       else None))
                   indexed)
            (cfg_calls_list (_B1, _B2) (_C1, _C2) g),
          result_checks_of (_B1, _B2) (_C1, _C2) _F g r classify,
          map (fun x -> Result_global_ext (Global_Named x, run_shared sr x, ()))
            globals @
            maps seeds_of procs,
          arithmetic_diagnostics _F sites r classify_ob, ()));;

let rec special_vars = function Nondet_Int -> []
                       | Min (a, b) -> var_list a @ var_list b
                       | Max (a, b) -> var_list a @ var_list b;;

let rec edge_vars
  = function EA_Assign (x, e) -> x :: var_list e
    | EA_Special (sc, x) -> x :: special_vars sc
    | EA_Assume b -> var_list b
    | EA_AssumeNot b -> var_list b
    | EA_Ret (e, uu) -> (match e with None -> [] | Some a -> var_list a)
    | EA_Check (uv, e) -> var_list e
    | EA_Nop -> []
    | EA_Body v -> [];;

let rec call_vars
  (CallEdge (dst, ps, args)) =
    (match dst with None -> [] | Some x -> [x]) @ ps @ maps var_list args;;

let rec cfg_vars
  g = sorted_list_of_set (equal_var_id, linorder_var_id)
        (Set (maps (fun (_, (a, _)) -> edge_vars a)
                (cfg_intra_list (equal_var_id, linorder_var_id)
                  (equal_exp, linorder_exp) g) @
               maps (fun (_, (ca, (_, _))) -> call_vars ca)
                 (cfg_calls_list (equal_var_id, linorder_var_id)
                   (equal_exp, linorder_exp) g)));;

let rec prog_report_of _A
  conf ds p gs ctx_key ctx_tag sr =
    report_of (equal_var_id, linorder_var_id) (equal_exp, linorder_exp) _A conf
      (cfg_vars (elab_cfg p ds)) (elab_cfg p ds) gs (prog_obligation_sites ds p)
      (obligation_classify (conf_sem conf) ds
        (activation_of (conf_analyses conf)))
      (prog_main_name :: prog_procs p) ctx_key ctx_tag
      (mcp_classify (conf_sem conf) ds (activation_of (conf_analyses conf)))
      sr;;

let rec to_string_kd _A
  = function
    KBot ->
      to_string _A.numeric_domain_ik_domain.executable_domain_numeric_domain
        (bot _A.numeric_domain_ik_domain.executable_domain_numeric_domain.bounded_semilattice_sup_bot_executable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
    | KD (k, a) ->
        to_string _A.numeric_domain_ik_domain.executable_domain_numeric_domain a
    | KTop -> "<top>";;

let rec string_of_facts _A
  = function [] -> ""
    | [(x, y)] -> (order_name _A x ^ "<le>") ^ order_name _A y
    | (x, y) :: p :: ps ->
        (((((order_name _A x ^ "<le>") ^ order_name _A y) ^ " ") ^ "<and>") ^
          " ") ^
          string_of_facts _A (p :: ps);;

let rec to_string_order_rel (_A1, _A2)
  d = (match d with OBot -> "<bottom>"
        | OFacts (_, ps) ->
          (if equal_set (equal_prod _A1 _A1) ps bot_set then "<top>"
            else ("{" ^
                   string_of_facts _A2
                     (sorted_list_of_set
                       ((equal_prod _A1 _A1),
                         (linorder_prod _A2.linorder_order_name
                           _A2.linorder_order_name))
                       ps)) ^
                   "}"));;

let rec order_view_string
  v = to_string_order_rel (equal_literal, order_name_literal)
        (match v with None -> OBot | Some ps -> OFacts (false, Set ps));;

let rec string_of_report_value
  = function Interval_Value v -> to_string_kd ik_domain_ivl v
    | Congruence_Value v -> to_string_kd ik_domain_congruence v
    | Int_Value v -> to_string_kd ik_domain_int_tuple v
    | Sign_Value v -> to_string_kd ik_domain_sign v
    | Parity_Value v -> to_string_kd ik_domain_parity v
    | Order_Value v -> order_view_string v;;

let rec var_label = function GlobalId x -> x
                    | ScopedId (f, x) -> (f ^ "::") ^ x
                    | ReturnId f -> f ^ "::return"
                    | ReturnVar -> "return";;

let rec key_of_global_unknown
  = function Analysis_Buffer -> Trace_Buffer
    | Analysis_Global x -> Trace_Global (var_label x)
    | Activation_Seed (n, c) -> Trace_Seed (n, c);;

let rec map_field_state
  f x1 = match f, x1 with
    f, Field_Store bs -> Field_Store (map (fun (x, v) -> (x, f v)) bs)
    | f, Field_Whole v -> Field_Whole (f v);;

let rec trace_view_of
  name text = map (fun (a, f) -> (name a, map_field_state text f));;

let rec analysis_name = function Sign -> "sign"
                        | Interval -> "interval"
                        | Ana_Int uu -> "int"
                        | Parity -> "parity"
                        | Congruence -> "congruence"
                        | Order -> "order";;

let rec mcp_rd
  g r = Product
          (map_lift (default_st_to_fun equal_var_id (bot_kd ik_domain_ivl) g)
             (slot1 r),
            Product
              (map_lift
                 (default_st_to_fun equal_var_id (bot_kd ik_domain_congruence)
                   g)
                 (slot2 r),
                Product
                  (Product
                     (map_lift
                        (default_st_to_fun equal_var_id
                          (bot_kd ik_domain_int_tuple) g)
                        (slot3n r),
                       Product
                         (map_lift
                            (default_st_to_fun equal_var_id
                              (bot_kd ik_domain_int_tuple) g)
                            (slot3o r),
                           map_lift
                             (default_st_to_fun equal_var_id
                               (bot_kd ik_domain_int_tuple) g)
                             (slot3f r))),
                    Product
                      (map_lift
                         (default_st_to_fun equal_var_id (bot_kd ik_domain_sign)
                           g)
                         (slot4 r),
                        Product
                          (map_lift
                             (default_st_to_fun equal_var_id
                               (bot_kd ik_domain_parity) g)
                             (slot5 r),
                            slot6 r)))));;

let rec order_var_label = function ScopedId (f, x) -> x
                          | GlobalId v -> var_label (GlobalId v)
                          | ReturnId v -> var_label (ReturnId v)
                          | ReturnVar -> var_label ReturnVar;;

let rec order_field_view
  d = Field_Whole
        (Order_Value
          (match d with Bot -> None | Lifted OBot -> None
            | Lifted (OFacts (_, ps)) ->
              Some (map (fun (a, b) -> (order_var_label a, order_var_label b))
                     (sorted_list_of_set
                       ((equal_prod equal_var_id equal_var_id),
                         (linorder_prod linorder_var_id linorder_var_id))
                       ps))));;

let rec field_view
  mk vars d =
    Field_Store
      (map (fun x ->
             (var_label x,
               mk (match d with Bot -> KBot | Lifted sigma -> sigma x)))
        vars);;

let rec map_kd f x1 = match f, x1 with f, KBot -> KBot
                 | f, KD (x21, x22) -> KD (x21, f x22)
                 | f, KTop -> KTop;;

let rec it_untag a = IT (it_ivl a, it_cong a);;

let rec render
  asa vars v =
    map (fun a ->
          (a, (match a
                with Interval ->
                  field_view (fun aa -> Interval_Value aa) vars (slot1 v)
                | Congruence ->
                  field_view (fun aa -> Congruence_Value aa) vars (slot2 v)
                | Ana_Int Refine_Never ->
                  field_view (comp (fun aa -> Int_Value aa) (map_kd it_untag))
                    vars (slot3n v)
                | Ana_Int Refine_Once ->
                  field_view (comp (fun aa -> Int_Value aa) (map_kd it_untag))
                    vars (slot3o v)
                | Ana_Int Refine_Fixpoint ->
                  field_view (comp (fun aa -> Int_Value aa) (map_kd it_untag))
                    vars (slot3f v)
                | Order -> order_field_view (slot6 v)
                | Sign -> field_view (fun aa -> Sign_Value aa) vars (slot4 v)
                | Parity ->
                  field_view (fun aa -> Parity_Value aa) vars (slot5 v))))
      asa;;

let rec trace_printers
  pg asa ds p ctx_view =
    (let raw =
       (fun vs d ->
         map_lift
           (comp (trace_view_of analysis_name string_of_report_value)
             (render (activation_of asa) vs))
           (map_lift (mcp_rd is_global) d))
       in
     let vars = cfg_vars (elab_cfg p ds) @ [ReturnVar] in
     let gs = declared_globals p in
     let local =
       (match pg with Program_Globals_Flow_Sensitive -> raw vars
         | Program_Globals_Flow_Insensitive ->
           raw (filtera (fun x -> not (membera equal_var_id gs x)) vars))
       in
     let globals = (fun a -> (match a with None -> gs | Some x -> [GlobalId x]))
       in
      Trace_Printers
        (ctx_view, key_of_global_unknown, (fun d -> local (dg_local d)),
          (fun n d -> raw (globals n) (dg_global d)), local));;

let rec map_local_spec
  k c = make_local_spec (ls_query c) (fun ch a x -> k (ls_step c ch a x))
          (fun ch ci p -> map (fun (q, e) -> (q, k e)) (ls_enter c ch ci p))
          (ls_combine_env c)
          (fun ch ci x de -> k (ls_combine_assign c ch ci x de));;

let rec part_answer
  sem ds g a ch x q =
    (match x with Bot -> top_query_lift (order_int_dom_ext bounded_lattice_unit)
      | Lifted r -> answer sem (kenv_of ds) a (mcp_rd g r) ch q);;

let rec mcp_field
  sem ds g p a =
    with_qry (part_answer sem ds g a) (field sem (kenv_of ds) p a);;

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

let rec mcp_norm
  asa x =
    (match x with Bot -> Bot
      | Lifted r -> (if list_all (fun a -> live a r) asa then x else Bot));;

let rec mcp_comp
  sem ds asa g p =
    map_local_spec (mcp_norm asa)
      (mcp_combine (map (mcp_field sem ds g p) asa));;

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

let rec local_transfer f m = sp_return (f (man_local m));;

let rec local_query h m q = sp_return (h (man_local m) q);;

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

let rec st_lift_empty _A
  x = (match x with Bot -> true | Lifted a -> st_is_bot _A a);;

let rec field_empty
  x0 r = match x0, r with
    Interval, r -> st_lift_empty kind_int_domain_ivl (slot1 r)
    | Congruence, r -> st_lift_empty kind_int_domain_congruence (slot2 r)
    | Ana_Int Refine_Never, r ->
        st_lift_empty (kind_int_domain_int_tuple int_refinement_int_never)
          (slot3n r)
    | Ana_Int Refine_Once, r ->
        st_lift_empty (kind_int_domain_int_tuple int_refinement_int_once)
          (slot3o r)
    | Ana_Int Refine_Fixpoint, r ->
        st_lift_empty (kind_int_domain_int_tuple int_refinement_int_fixpoint)
          (slot3f r)
    | Sign, r -> st_lift_empty kind_int_domain_sign (slot4 r)
    | Parity, r -> st_lift_empty kind_int_domain_parity (slot5 r)
    | Order, r -> equal_lifteda (equal_order_rel equal_var_id) (slot6 r) Bot;;

let rec mcp_emp asa p r = list_ex (fun a -> field_empty a r) asa;;

let rec cs_run
  conf k ds p =
    (let sem = conf_sem conf in
     let asa = conf_analyses conf in
     let r = conf_globals conf in
     let key = (fun ctx -> Key_List (map (fun a -> Key_Node a) ctx)) in
     let tag =
       (if equal_nata k zero_nat then (fun _ -> Report_Unit)
         else (fun a -> Report_Call_String a))
       in
     let root = (cfg_exit (elab_cfg p ds), []) in
     let _ =
       Solver_trace_hook.emit "run"
         (fun _ ->
           trace_printers (conf_program_globals conf) asa ds p
             (if equal_nata k zero_nat then (fun _ -> Context_Unit)
               else (fun a -> Context_Call_String a)))
       in
      (match conf_program_globals conf
        with Program_Globals_Flow_Sensitive ->
          map_option
            (fun sol ->
              prog_report_of (equal_list equal_cfg_node) conf ds p [] key tag
                (solved_run_of linorder_var_id (equal_exp, linorder_exp)
                  ((equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))),
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)))
                              (semilattice_sup_lifted
                                (semilattice_sup_order_rel equal_var_id))))))))
                  (mcp_comp sem ds (activation_of asa))
                  (mcp_emp (activation_of asa)) mcp_rd
                  (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b)) (fun _ -> cs_route k)
                  (fun _ d _ -> d) (fun _ d -> d) (fun _ _ d _ -> d) is_global p
                  sol))
            (solve_c_traced
              (equal_prod equal_cfg_node (equal_list equal_cfg_node))
              (equal_global_unknown equal_var_id (equal_list equal_cfg_node))
              ((equal_dg_state
                 (equal_lifted
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))))
                 (equal_lifted
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_order_rel equal_var_id))))))))),
                (bounded_semilattice_sup_bot_dg_state
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_order_rel
                                  equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_order_rel
                                  equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)),
                (warrowing_dg_state
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_order_rel
                                   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (warrowing_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl),
                                    (warrowing_kd ik_domain_ivl))))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (warrowing_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence),
(warrowing_kd ik_domain_congruence))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
        (warrowing_kd ik_domain_int_tuple))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_sign),
        (warrowing_kd ik_domain_sign))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_parity),
            (warrowing_kd ik_domain_parity))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_order_rel equal_var_id),
        (warrowing_order_rel equal_var_id))))))))))))))))
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_order_rel
                                   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (warrowing_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl),
                                    (warrowing_kd ik_domain_ivl))))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (warrowing_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence),
(warrowing_kd ik_domain_congruence))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
        (warrowing_kd ik_domain_int_tuple))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_sign),
        (warrowing_kd ik_domain_sign))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_parity),
            (warrowing_kd ik_domain_parity))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_order_rel equal_var_id),
        (warrowing_order_rel equal_var_id))))))))))))))))))
              r (equations (equal_var_id, linorder_var_id)
                  (equal_exp, linorder_exp)
                  ((equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))),
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)))
                              (semilattice_sup_lifted
                                (semilattice_sup_order_rel equal_var_id))))))))
                  (equal_global_unknown equal_var_id
                    (equal_list equal_cfg_node))
                  (equal_list equal_cfg_node)
                  (mcp_comp sem ds (activation_of asa))
                  (mcp_init ds (activation_of asa)) Analysis_Buffer
                  (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b)) (fun _ -> cs_route k) []
                  (fun _ ->
                    dg_spec_of equal_exp
                      (bot_lifted
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_congruence)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_sign)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_parity)))
                                  (semilattice_sup_lifted
                                    (semilattice_sup_order_rel
                                      equal_var_id)))))))))
                  (fun _ _ -> Bot) (fun _ _ -> []) (fun pa -> elab_cfg pa ds)
                  (fun _ -> FunctionEntry prog_main_name) is_global p)
              root)
        | Program_Globals_Flow_Insensitive ->
          (let gs = declared_globals p in
            map_option
              (fun sol ->
                prog_report_of (equal_list equal_cfg_node) conf ds p gs key tag
                  (solved_run_of linorder_var_id (equal_exp, linorder_exp)
                    ((equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))),
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_order_rel
                                    equal_var_id))))))))
                    (mcp_comp sem ds (activation_of asa))
                    (mcp_emp (activation_of asa)) mcp_rd
                    (fun a -> Analysis_Global a)
                    (fun a b -> Activation_Seed (a, b)) (fun _ -> cs_route k)
                    (fun _ d e ->
                      split_cmb_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs d
                        (full_view
                          (bounded_semilattice_sup_bot_lifted
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_ivl)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_congruence)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                      (semilattice_sup_lifted
(semilattice_sup_order_rel equal_var_id))))))))
                          (split_global_at_lifted
                            ((semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                       (semilattice_sup_lifted
 (semilattice_sup_order_rel equal_var_id))))))),
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_ivl)))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_congruence)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_sign)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_parity)))))
(ownership_split_lifted
  ((semilattice_sup_order_rel equal_var_id),
    (ownership_split_order_rel equal_var_id))))))))))
                          gs e))
                    (fun _ ->
                      split_rl_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs)
                    (fun _ ci d e ->
                      split_cmb_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs d
                        (view_of
                          (semilattice_sup_lifted
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_ivl)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_congruence)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                      (semilattice_sup_lifted
(semilattice_sup_order_rel equal_var_id))))))))
                          (split_global_at_lifted
                            ((semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                       (semilattice_sup_lifted
 (semilattice_sup_order_rel equal_var_id))))))),
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_ivl)))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_congruence)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_sign)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_parity)))))
(ownership_split_lifted
  ((semilattice_sup_order_rel equal_var_id),
    (ownership_split_order_rel equal_var_id))))))))))
                          (gcall_global_reads (equal_var_id, linorder_var_id)
                            exp_vars is_global (ci_args ci))
                          e (split_free_lifted
                              ((semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)))
 (semilattice_sup_lifted (semilattice_sup_order_rel equal_var_id))))))),
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_ivl)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_ivl)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_congruence)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_congruence)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_analysis_product
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_int_tuple)))))
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_int_tuple)))))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_sign)))))
(ownership_split_analysis_product
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_parity)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_parity)))))
  (ownership_split_lifted
    ((semilattice_sup_order_rel equal_var_id),
      (ownership_split_order_rel equal_var_id)))))))))
                              (gcall_global_reads
                                (equal_var_id, linorder_var_id) exp_vars
                                is_global (ci_args ci)))))
                    is_global p sol))
              (solve_c_traced
                (equal_prod equal_cfg_node (equal_list equal_cfg_node))
                (equal_global_unknown equal_var_id (equal_list equal_cfg_node))
                ((equal_dg_state
                   (equal_lifted
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))))
                   (equal_lifted
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))))),
                  (bounded_semilattice_sup_bot_dg_state
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_order_rel
                                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_order_rel
                                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)),
                  (warrowing_dg_state
                    ((bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                      (warrowing_lifted
                        ((bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                          (warrowing_analysis_product
                            ((bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                              (warrowing_lifted
                                ((bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (warrowing_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl),
                                      (warrowing_kd ik_domain_ivl))))))
                            ((bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                              (warrowing_analysis_product
                                ((bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                  (warrowing_lifted
                                    ((bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (warrowing_gdefault_st
(infinite_key_var_id, equal_var_id)
((bounded_semilattice_sup_bot_kd ik_domain_congruence),
  (warrowing_kd ik_domain_congruence))))))
                                ((bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                  (warrowing_analysis_product
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
          (warrowing_kd ik_domain_int_tuple))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))))))
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_sign),
          (warrowing_kd ik_domain_sign))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_parity),
              (warrowing_kd ik_domain_parity))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_order_rel
         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_order_rel equal_var_id),
          (warrowing_order_rel equal_var_id))))))))))))))))
                    ((bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                      (warrowing_lifted
                        ((bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                          (warrowing_analysis_product
                            ((bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                              (warrowing_lifted
                                ((bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (warrowing_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl),
                                      (warrowing_kd ik_domain_ivl))))))
                            ((bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                              (warrowing_analysis_product
                                ((bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                  (warrowing_lifted
                                    ((bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (warrowing_gdefault_st
(infinite_key_var_id, equal_var_id)
((bounded_semilattice_sup_bot_kd ik_domain_congruence),
  (warrowing_kd ik_domain_congruence))))))
                                ((bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                  (warrowing_analysis_product
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
          (warrowing_kd ik_domain_int_tuple))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))))))
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_sign),
          (warrowing_kd ik_domain_sign))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_parity),
              (warrowing_kd ik_domain_parity))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_order_rel
         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_order_rel equal_var_id),
          (warrowing_order_rel equal_var_id))))))))))))))))))
                r (equations (equal_var_id, linorder_var_id)
                    (equal_exp, linorder_exp)
                    ((equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))),
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_order_rel
                                    equal_var_id))))))))
                    (equal_global_unknown equal_var_id
                      (equal_list equal_cfg_node))
                    (equal_list equal_cfg_node)
                    (mcp_comp sem ds (activation_of asa))
                    (mcp_init ds (activation_of asa)) Analysis_Buffer
                    (fun a -> Analysis_Global a)
                    (fun a b -> Activation_Seed (a, b)) (fun _ -> cs_route k) []
                    (fun _ ->
                      gkeyed_split_spec equal_exp
                        (equal_var_id, linorder_var_id)
                        (bounded_semilattice_sup_bot_lifted
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_congruence)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_sign)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                    (semilattice_sup_lifted
                                      (semilattice_sup_order_rel
equal_var_id))))))))
                        exp_vars ReturnVar is_global
                        (split_cmb_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))
                          gs)
                        (split_rl_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))
                          gs)
                        (split_global_at_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id))))))))))
                        (split_free_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))))
                    (fun _ _ -> Bot)
                    (fun _ _ ->
                      map (fun x ->
                            (x, split_global_at_lifted
                                  ((semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_analysis_product
   (semilattice_sup_lifted
     (semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
   (semilattice_sup_analysis_product
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
 (semilattice_sup_analysis_product
   (semilattice_sup_lifted
     (semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)))
   (semilattice_sup_analysis_product
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)))
     (semilattice_sup_lifted (semilattice_sup_order_rel equal_var_id))))))),
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_ivl)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_ivl)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_congruence)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_congruence)))))
(ownership_split_analysis_product
  (ownership_split_analysis_product
    (ownership_split_lifted
      ((semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
          ((bounded_semilattice_sup_bot_kd
             ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
            (order_top_kd ik_domain_int_tuple)))))
    (ownership_split_analysis_product
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_int_tuple)))))
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_int_tuple)))))))
  (ownership_split_analysis_product
    (ownership_split_lifted
      ((semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_sign)),
        (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
          ((bounded_semilattice_sup_bot_kd
             ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
            (order_top_kd ik_domain_sign)))))
    (ownership_split_analysis_product
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_parity)))))
      (ownership_split_lifted
        ((semilattice_sup_order_rel equal_var_id),
          (ownership_split_order_rel equal_var_id)))))))))
                                  x (Lifted (mcp_init ds (activation_of asa)))))
                        gs)
                    (fun pa -> elab_cfg pa ds)
                    (fun _ -> FunctionEntry prog_main_name) is_global p)
                root))));;

let rec context_values
  asa (Product
        (i, Product
              (c, Product
                    (Product (tn, Product (toa, tf)),
                      Product (s, Product (q, u))))))
    = maps (fun a ->
             (match a with Interval -> map (fun aa -> Interval_Value aa) i
               | Congruence -> map (fun aa -> Congruence_Value aa) c
               | Ana_Int Refine_Never ->
                 map (comp (fun aa -> Int_Value aa) (map_kd it_untag)) tn
               | Ana_Int Refine_Once ->
                 map (comp (fun aa -> Int_Value aa) (map_kd it_untag)) toa
               | Ana_Int Refine_Fixpoint ->
                 map (comp (fun aa -> Int_Value aa) (map_kd it_untag)) tf
               | Order -> [] | Sign -> map (fun aa -> Sign_Value aa) s
               | Parity -> map (fun aa -> Parity_Value aa) q))
        asa;;

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

let rec int_tuple_key
  a = Key_List [ivl_key (it_ivl a); congruence_key (it_cong a)];;

let rec ikind_key = function I8 -> Key_Int zero_inta
                    | U8 -> Key_Int one_inta
                    | I16 -> Key_Int (Int_of_integer (Z.of_int 2))
                    | U16 -> Key_Int (Int_of_integer (Z.of_int 3))
                    | I32 -> Key_Int (Int_of_integer (Z.of_int 4))
                    | U32 -> Key_Int (Int_of_integer (Z.of_int 5))
                    | I64 -> Key_Int (Int_of_integer (Z.of_int 6))
                    | U64 -> Key_Int (Int_of_integer (Z.of_int 7));;

let rec kd_key
  f x1 = match f, x1 with f, KBot -> Key_List [Key_Int zero_inta]
    | f, KD (k, a) -> Key_List [Key_Int one_inta; ikind_key k; f a]
    | f, KTop -> Key_List [Key_Int (Int_of_integer (Z.of_int 2))];;

let rec mcp_ctx_key
  (Product
    (i, Product
          (c, Product
                (Product (tn, Product (toa, tf)),
                  Product (s, Product (q, u))))))
    = Key_List
        [Key_List (map (kd_key ivl_key) i);
          Key_List (map (kd_key congruence_key) c);
          Key_List (map (kd_key int_tuple_key) tn);
          Key_List (map (kd_key int_tuple_key) toa);
          Key_List (map (kd_key int_tuple_key) tf);
          Key_List (map (kd_key sign_key) s);
          Key_List (map (kd_key parity_key) q);
          Key_List (map (fun _ -> Key_List []) u)];;

let rec es_run
  conf ds p =
    (let sem = conf_sem conf in
     let asa = conf_analyses conf in
     let r = conf_globals conf in
     let root = (cfg_exit (elab_cfg p ds), mcp_root_ctx) in
     let _ =
       Solver_trace_hook.emit "run"
         (fun _ ->
           trace_printers (conf_program_globals conf) asa ds p
             (fun ctx ->
               Context_Entry
                 (map string_of_report_value
                   (context_values (activation_of asa) ctx))))
       in
      (match conf_program_globals conf
        with Program_Globals_Flow_Sensitive ->
          map_option
            (fun sol ->
              prog_report_of
                (equal_analysis_product (equal_list (equal_kd equal_ivl))
                  (equal_analysis_product
                    (equal_list (equal_kd equal_congruence))
                    (equal_analysis_product
                      (equal_analysis_product
                        (equal_list (equal_kd equal_int_tuple))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_list (equal_kd equal_int_tuple))))
                      (equal_analysis_product (equal_list (equal_kd equal_sign))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_parity))
                          (equal_list equal_unit))))))
                conf ds p [] mcp_ctx_key (fun a -> Report_Entry a)
                (solved_run_of linorder_var_id (equal_exp, linorder_exp)
                  ((equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))),
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)))
                              (semilattice_sup_lifted
                                (semilattice_sup_order_rel equal_var_id))))))))
                  (mcp_comp sem ds (activation_of asa))
                  (mcp_emp (activation_of asa)) mcp_rd
                  (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b))
                  (mcp_route (activation_of asa)) (fun _ d _ -> d)
                  (fun _ d -> d) (fun _ _ d _ -> d) is_global p sol))
            (solve_c_traced
              (equal_prod equal_cfg_node
                (equal_analysis_product (equal_list (equal_kd equal_ivl))
                  (equal_analysis_product
                    (equal_list (equal_kd equal_congruence))
                    (equal_analysis_product
                      (equal_analysis_product
                        (equal_list (equal_kd equal_int_tuple))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_list (equal_kd equal_int_tuple))))
                      (equal_analysis_product (equal_list (equal_kd equal_sign))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_parity))
                          (equal_list equal_unit)))))))
              (equal_global_unknown equal_var_id
                (equal_analysis_product (equal_list (equal_kd equal_ivl))
                  (equal_analysis_product
                    (equal_list (equal_kd equal_congruence))
                    (equal_analysis_product
                      (equal_analysis_product
                        (equal_list (equal_kd equal_int_tuple))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_list (equal_kd equal_int_tuple))))
                      (equal_analysis_product (equal_list (equal_kd equal_sign))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_parity))
                          (equal_list equal_unit)))))))
              ((equal_dg_state
                 (equal_lifted
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))))
                 (equal_lifted
                   (equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_order_rel equal_var_id))))))))),
                (bounded_semilattice_sup_bot_dg_state
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_order_rel
                                  equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)
                  (bounded_semilattice_sup_bot_lifted
                    (bounded_semilattice_sup_bot_analysis_product
                      (bounded_semilattice_sup_bot_lifted
                        (bounded_semilattice_sup_bot_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd
                            ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_lifted
                              (bounded_semilattice_sup_bot_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_order_rel
                                  equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)),
                (warrowing_dg_state
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_order_rel
                                   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (warrowing_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl),
                                    (warrowing_kd ik_domain_ivl))))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (warrowing_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence),
(warrowing_kd ik_domain_congruence))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
        (warrowing_kd ik_domain_int_tuple))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_sign),
        (warrowing_kd ik_domain_sign))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_parity),
            (warrowing_kd ik_domain_parity))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_order_rel equal_var_id),
        (warrowing_order_rel equal_var_id))))))))))))))))
                  ((bounded_semilattice_sup_bot_lifted
                     (bounded_semilattice_sup_bot_analysis_product
                       (bounded_semilattice_sup_bot_lifted
                         (bounded_semilattice_sup_bot_gdefault_st
                           (infinite_key_var_id, equal_var_id)
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_order_rel
                                   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                    (warrowing_lifted
                      ((bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                        (warrowing_analysis_product
                          ((bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                            (warrowing_lifted
                              ((bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (warrowing_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl),
                                    (warrowing_kd ik_domain_ivl))))))
                          ((bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                            (warrowing_analysis_product
                              ((bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                (warrowing_lifted
                                  ((bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (warrowing_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence),
(warrowing_kd ik_domain_congruence))))))
                              ((bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                (warrowing_analysis_product
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
        (warrowing_kd ik_domain_int_tuple))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
            (warrowing_kd ik_domain_int_tuple))))))))))
                                  ((bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                    (warrowing_analysis_product
                                      ((bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
(warrowing_lifted
  ((bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
      ((bounded_semilattice_sup_bot_kd ik_domain_sign),
        (warrowing_kd ik_domain_sign))))))
                                      ((bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
(warrowing_analysis_product
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)),
        (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
          ((bounded_semilattice_sup_bot_kd ik_domain_parity),
            (warrowing_kd ik_domain_parity))))))
  ((bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
    (warrowing_lifted
      ((bounded_semilattice_sup_bot_order_rel equal_var_id),
        (warrowing_order_rel equal_var_id))))))))))))))))))
              r (equations (equal_var_id, linorder_var_id)
                  (equal_exp, linorder_exp)
                  ((equal_analysis_product
                     (equal_lifted
                       (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                         ((equal_kd equal_ivl),
                           (bounded_semilattice_sup_bot_kd
                             ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_congruence),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_int_tuple),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                         (equal_analysis_product
                           (equal_lifted
                             (equal_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               ((equal_kd equal_sign),
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_parity),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                             (equal_lifted (equal_order_rel equal_var_id))))))),
                    (semilattice_sup_analysis_product
                      (semilattice_sup_lifted
                        (semilattice_sup_gdefault_st
                          (infinite_key_var_id, equal_var_id)
                          (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_congruence)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_int_tuple)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_sign)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_parity)))
                              (semilattice_sup_lifted
                                (semilattice_sup_order_rel equal_var_id))))))))
                  (equal_global_unknown equal_var_id
                    (equal_analysis_product (equal_list (equal_kd equal_ivl))
                      (equal_analysis_product
                        (equal_list (equal_kd equal_congruence))
                        (equal_analysis_product
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_analysis_product
                              (equal_list (equal_kd equal_int_tuple))
                              (equal_list (equal_kd equal_int_tuple))))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_sign))
                            (equal_analysis_product
                              (equal_list (equal_kd equal_parity))
                              (equal_list equal_unit)))))))
                  (equal_analysis_product (equal_list (equal_kd equal_ivl))
                    (equal_analysis_product
                      (equal_list (equal_kd equal_congruence))
                      (equal_analysis_product
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_list (equal_kd equal_int_tuple))))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_sign))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_parity))
                            (equal_list equal_unit))))))
                  (mcp_comp sem ds (activation_of asa))
                  (mcp_init ds (activation_of asa)) Analysis_Buffer
                  (fun a -> Analysis_Global a)
                  (fun a b -> Activation_Seed (a, b))
                  (mcp_route (activation_of asa)) mcp_root_ctx
                  (fun _ ->
                    dg_spec_of equal_exp
                      (bot_lifted
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd
                                  ik_domain_congruence)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_sign)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_parity)))
                                  (semilattice_sup_lifted
                                    (semilattice_sup_order_rel
                                      equal_var_id)))))))))
                  (fun _ _ -> Bot) (fun _ _ -> []) (fun pa -> elab_cfg pa ds)
                  (fun _ -> FunctionEntry prog_main_name) is_global p)
              root)
        | Program_Globals_Flow_Insensitive ->
          (let gs = declared_globals p in
            map_option
              (fun sol ->
                prog_report_of
                  (equal_analysis_product (equal_list (equal_kd equal_ivl))
                    (equal_analysis_product
                      (equal_list (equal_kd equal_congruence))
                      (equal_analysis_product
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_list (equal_kd equal_int_tuple))))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_sign))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_parity))
                            (equal_list equal_unit))))))
                  conf ds p gs mcp_ctx_key (fun a -> Report_Entry a)
                  (solved_run_of linorder_var_id (equal_exp, linorder_exp)
                    ((equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))),
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_order_rel
                                    equal_var_id))))))))
                    (mcp_comp sem ds (activation_of asa))
                    (mcp_emp (activation_of asa)) mcp_rd
                    (fun a -> Analysis_Global a)
                    (fun a b -> Activation_Seed (a, b))
                    (mcp_route (activation_of asa))
                    (fun _ d e ->
                      split_cmb_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs d
                        (full_view
                          (bounded_semilattice_sup_bot_lifted
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_ivl)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_congruence)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                      (semilattice_sup_lifted
(semilattice_sup_order_rel equal_var_id))))))))
                          (split_global_at_lifted
                            ((semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                       (semilattice_sup_lifted
 (semilattice_sup_order_rel equal_var_id))))))),
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_ivl)))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_congruence)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_sign)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_parity)))))
(ownership_split_lifted
  ((semilattice_sup_order_rel equal_var_id),
    (ownership_split_order_rel equal_var_id))))))))))
                          gs e))
                    (fun _ ->
                      split_rl_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs)
                    (fun _ ci d e ->
                      split_cmb_lifted
                        ((semilattice_sup_analysis_product
                           (semilattice_sup_lifted
                             (semilattice_sup_gdefault_st
                               (split_key_var_id.infinite_key_split_key,
                                 equal_var_id)
                               (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                           (semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)))
                                   (semilattice_sup_lifted
                                     (semilattice_sup_order_rel
                                       equal_var_id))))))),
                          (ownership_split_analysis_product
                            (ownership_split_lifted
                              ((semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)),
                                (ownership_split_gdefault_st
                                  (equal_var_id, split_key_var_id)
                                  ((bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                    (order_top_kd ik_domain_ivl)))))
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_congruence)))))
                              (ownership_split_analysis_product
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_int_tuple)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_sign)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_parity)))))
                                    (ownership_split_lifted
                                      ((semilattice_sup_order_rel equal_var_id),
(ownership_split_order_rel equal_var_id)))))))))
                        gs d
                        (view_of
                          (semilattice_sup_lifted
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_ivl)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_congruence)))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                    (semilattice_sup_analysis_product
                                      (semilattice_sup_lifted
(semilattice_sup_gdefault_st (infinite_key_var_id, equal_var_id)
  (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                      (semilattice_sup_lifted
(semilattice_sup_order_rel equal_var_id))))))))
                          (split_global_at_lifted
                            ((semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                       (semilattice_sup_lifted
 (semilattice_sup_order_rel equal_var_id))))))),
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_ivl)))))
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_congruence)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_sign)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_parity)))))
(ownership_split_lifted
  ((semilattice_sup_order_rel equal_var_id),
    (ownership_split_order_rel equal_var_id))))))))))
                          (gcall_global_reads (equal_var_id, linorder_var_id)
                            exp_vars is_global (ci_args ci))
                          e (split_free_lifted
                              ((semilattice_sup_analysis_product
                                 (semilattice_sup_lifted
                                   (semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl)))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_sign)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_lifted
   (semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_parity)))
 (semilattice_sup_lifted (semilattice_sup_order_rel equal_var_id))))))),
                                (ownership_split_analysis_product
                                  (ownership_split_lifted
                                    ((semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_ivl)),
                                      (ownership_split_gdefault_st
(equal_var_id, split_key_var_id)
((bounded_semilattice_sup_bot_kd
   ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
  (order_top_kd ik_domain_ivl)))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_congruence)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_congruence)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_int_tuple)))))
(ownership_split_analysis_product
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_int_tuple)))))
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_int_tuple)))))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_sign)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_sign)))))
(ownership_split_analysis_product
  (ownership_split_lifted
    ((semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_parity)),
      (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
        ((bounded_semilattice_sup_bot_kd
           ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
          (order_top_kd ik_domain_parity)))))
  (ownership_split_lifted
    ((semilattice_sup_order_rel equal_var_id),
      (ownership_split_order_rel equal_var_id)))))))))
                              (gcall_global_reads
                                (equal_var_id, linorder_var_id) exp_vars
                                is_global (ci_args ci)))))
                    is_global p sol))
              (solve_c_traced
                (equal_prod equal_cfg_node
                  (equal_analysis_product (equal_list (equal_kd equal_ivl))
                    (equal_analysis_product
                      (equal_list (equal_kd equal_congruence))
                      (equal_analysis_product
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_list (equal_kd equal_int_tuple))))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_sign))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_parity))
                            (equal_list equal_unit)))))))
                (equal_global_unknown equal_var_id
                  (equal_analysis_product (equal_list (equal_kd equal_ivl))
                    (equal_analysis_product
                      (equal_list (equal_kd equal_congruence))
                      (equal_analysis_product
                        (equal_analysis_product
                          (equal_list (equal_kd equal_int_tuple))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_list (equal_kd equal_int_tuple))))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_sign))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_parity))
                            (equal_list equal_unit)))))))
                ((equal_dg_state
                   (equal_lifted
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))))
                   (equal_lifted
                     (equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))))),
                  (bounded_semilattice_sup_bot_dg_state
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_order_rel
                                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)
                    (bounded_semilattice_sup_bot_lifted
                      (bounded_semilattice_sup_bot_analysis_product
                        (bounded_semilattice_sup_bot_lifted
                          (bounded_semilattice_sup_bot_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd
                              ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                        (bounded_semilattice_sup_bot_analysis_product
                          (bounded_semilattice_sup_bot_lifted
                            (bounded_semilattice_sup_bot_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                          (bounded_semilattice_sup_bot_analysis_product
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                            (bounded_semilattice_sup_bot_analysis_product
                              (bounded_semilattice_sup_bot_lifted
                                (bounded_semilattice_sup_bot_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                              (bounded_semilattice_sup_bot_analysis_product
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                (bounded_semilattice_sup_bot_lifted
                                  (bounded_semilattice_sup_bot_order_rel
                                    equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot)),
                  (warrowing_dg_state
                    ((bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                      (warrowing_lifted
                        ((bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                          (warrowing_analysis_product
                            ((bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                              (warrowing_lifted
                                ((bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (warrowing_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl),
                                      (warrowing_kd ik_domain_ivl))))))
                            ((bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                              (warrowing_analysis_product
                                ((bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                  (warrowing_lifted
                                    ((bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (warrowing_gdefault_st
(infinite_key_var_id, equal_var_id)
((bounded_semilattice_sup_bot_kd ik_domain_congruence),
  (warrowing_kd ik_domain_congruence))))))
                                ((bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                  (warrowing_analysis_product
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
          (warrowing_kd ik_domain_int_tuple))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))))))
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_sign),
          (warrowing_kd ik_domain_sign))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_parity),
              (warrowing_kd ik_domain_parity))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_order_rel
         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_order_rel equal_var_id),
          (warrowing_order_rel equal_var_id))))))))))))))))
                    ((bounded_semilattice_sup_bot_lifted
                       (bounded_semilattice_sup_bot_analysis_product
                         (bounded_semilattice_sup_bot_lifted
                           (bounded_semilattice_sup_bot_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                         (bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_order_rel
                                     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))).semilattice_sup_bounded_semilattice_sup_bot),
                      (warrowing_lifted
                        ((bounded_semilattice_sup_bot_analysis_product
                           (bounded_semilattice_sup_bot_lifted
                             (bounded_semilattice_sup_bot_gdefault_st
                               (infinite_key_var_id, equal_var_id)
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot)
                           (bounded_semilattice_sup_bot_analysis_product
                             (bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                             (bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_order_rel
                                       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))))),
                          (warrowing_analysis_product
                            ((bounded_semilattice_sup_bot_lifted
                               (bounded_semilattice_sup_bot_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)).semilattice_sup_bounded_semilattice_sup_bot),
                              (warrowing_lifted
                                ((bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (warrowing_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl),
                                      (warrowing_kd ik_domain_ivl))))))
                            ((bounded_semilattice_sup_bot_analysis_product
                               (bounded_semilattice_sup_bot_lifted
                                 (bounded_semilattice_sup_bot_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot)
                               (bounded_semilattice_sup_bot_analysis_product
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                 (bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_lifted
                                     (bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_order_rel
 equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))))),
                              (warrowing_analysis_product
                                ((bounded_semilattice_sup_bot_lifted
                                   (bounded_semilattice_sup_bot_gdefault_st
                                     (infinite_key_var_id, equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)).semilattice_sup_bounded_semilattice_sup_bot),
                                  (warrowing_lifted
                                    ((bounded_semilattice_sup_bot_gdefault_st
                                       (infinite_key_var_id, equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_congruence)),
                                      (warrowing_gdefault_st
(infinite_key_var_id, equal_var_id)
((bounded_semilattice_sup_bot_kd ik_domain_congruence),
  (warrowing_kd ik_domain_congruence))))))
                                ((bounded_semilattice_sup_bot_analysis_product
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)))
                                   (bounded_semilattice_sup_bot_analysis_product
                                     (bounded_semilattice_sup_bot_lifted
                                       (bounded_semilattice_sup_bot_gdefault_st
 (infinite_key_var_id, equal_var_id)
 (bounded_semilattice_sup_bot_kd
   ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                     (bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_order_rel
   equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)))),
                                  (warrowing_analysis_product
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
          (warrowing_kd ik_domain_int_tuple))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_int_tuple)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_int_tuple),
              (warrowing_kd ik_domain_int_tuple))))))))))
                                    ((bounded_semilattice_sup_bot_analysis_product
                                       (bounded_semilattice_sup_bot_lifted
 (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
   (bounded_semilattice_sup_bot_kd
     ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot)
                                       (bounded_semilattice_sup_bot_analysis_product
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
 (bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_order_rel
     equal_var_id).semilattice_sup_bounded_semilattice_sup_bot))),
                                      (warrowing_analysis_product
((bounded_semilattice_sup_bot_lifted
   (bounded_semilattice_sup_bot_gdefault_st (infinite_key_var_id, equal_var_id)
     (bounded_semilattice_sup_bot_kd
       ik_domain_sign)).semilattice_sup_bounded_semilattice_sup_bot),
  (warrowing_lifted
    ((bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)),
      (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
        ((bounded_semilattice_sup_bot_kd ik_domain_sign),
          (warrowing_kd ik_domain_sign))))))
((bounded_semilattice_sup_bot_analysis_product
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_gdefault_st
       (infinite_key_var_id, equal_var_id)
       (bounded_semilattice_sup_bot_kd
         ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot)
   (bounded_semilattice_sup_bot_lifted
     (bounded_semilattice_sup_bot_order_rel
       equal_var_id).semilattice_sup_bounded_semilattice_sup_bot)),
  (warrowing_analysis_product
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_gdefault_st
         (infinite_key_var_id, equal_var_id)
         (bounded_semilattice_sup_bot_kd
           ik_domain_parity)).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_gdefault_st
           (infinite_key_var_id, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (warrowing_gdefault_st (infinite_key_var_id, equal_var_id)
            ((bounded_semilattice_sup_bot_kd ik_domain_parity),
              (warrowing_kd ik_domain_parity))))))
    ((bounded_semilattice_sup_bot_lifted
       (bounded_semilattice_sup_bot_order_rel
         equal_var_id).semilattice_sup_bounded_semilattice_sup_bot),
      (warrowing_lifted
        ((bounded_semilattice_sup_bot_order_rel equal_var_id),
          (warrowing_order_rel equal_var_id))))))))))))))))))
                r (equations (equal_var_id, linorder_var_id)
                    (equal_exp, linorder_exp)
                    ((equal_analysis_product
                       (equal_lifted
                         (equal_gdefault_st (infinite_key_var_id, equal_var_id)
                           ((equal_kd equal_ivl),
                             (bounded_semilattice_sup_bot_kd
                               ik_domain_ivl).order_bot_bounded_semilattice_sup_bot)))
                       (equal_analysis_product
                         (equal_lifted
                           (equal_gdefault_st
                             (infinite_key_var_id, equal_var_id)
                             ((equal_kd equal_congruence),
                               (bounded_semilattice_sup_bot_kd
                                 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot)))
                         (equal_analysis_product
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_int_tuple),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_int_tuple),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot)))))
                           (equal_analysis_product
                             (equal_lifted
                               (equal_gdefault_st
                                 (infinite_key_var_id, equal_var_id)
                                 ((equal_kd equal_sign),
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_sign).order_bot_bounded_semilattice_sup_bot)))
                             (equal_analysis_product
                               (equal_lifted
                                 (equal_gdefault_st
                                   (infinite_key_var_id, equal_var_id)
                                   ((equal_kd equal_parity),
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_parity).order_bot_bounded_semilattice_sup_bot)))
                               (equal_lifted
                                 (equal_order_rel equal_var_id))))))),
                      (semilattice_sup_analysis_product
                        (semilattice_sup_lifted
                          (semilattice_sup_gdefault_st
                            (infinite_key_var_id, equal_var_id)
                            (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                        (semilattice_sup_analysis_product
                          (semilattice_sup_lifted
                            (semilattice_sup_gdefault_st
                              (infinite_key_var_id, equal_var_id)
                              (bounded_semilattice_sup_bot_kd
                                ik_domain_congruence)))
                          (semilattice_sup_analysis_product
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_int_tuple)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_int_tuple)))))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_sign)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_lifted
                                  (semilattice_sup_gdefault_st
                                    (infinite_key_var_id, equal_var_id)
                                    (bounded_semilattice_sup_bot_kd
                                      ik_domain_parity)))
                                (semilattice_sup_lifted
                                  (semilattice_sup_order_rel
                                    equal_var_id))))))))
                    (equal_global_unknown equal_var_id
                      (equal_analysis_product (equal_list (equal_kd equal_ivl))
                        (equal_analysis_product
                          (equal_list (equal_kd equal_congruence))
                          (equal_analysis_product
                            (equal_analysis_product
                              (equal_list (equal_kd equal_int_tuple))
                              (equal_analysis_product
                                (equal_list (equal_kd equal_int_tuple))
                                (equal_list (equal_kd equal_int_tuple))))
                            (equal_analysis_product
                              (equal_list (equal_kd equal_sign))
                              (equal_analysis_product
                                (equal_list (equal_kd equal_parity))
                                (equal_list equal_unit)))))))
                    (equal_analysis_product (equal_list (equal_kd equal_ivl))
                      (equal_analysis_product
                        (equal_list (equal_kd equal_congruence))
                        (equal_analysis_product
                          (equal_analysis_product
                            (equal_list (equal_kd equal_int_tuple))
                            (equal_analysis_product
                              (equal_list (equal_kd equal_int_tuple))
                              (equal_list (equal_kd equal_int_tuple))))
                          (equal_analysis_product
                            (equal_list (equal_kd equal_sign))
                            (equal_analysis_product
                              (equal_list (equal_kd equal_parity))
                              (equal_list equal_unit))))))
                    (mcp_comp sem ds (activation_of asa))
                    (mcp_init ds (activation_of asa)) Analysis_Buffer
                    (fun a -> Analysis_Global a)
                    (fun a b -> Activation_Seed (a, b))
                    (mcp_route (activation_of asa)) mcp_root_ctx
                    (fun _ ->
                      gkeyed_split_spec equal_exp
                        (equal_var_id, linorder_var_id)
                        (bounded_semilattice_sup_bot_lifted
                          (semilattice_sup_analysis_product
                            (semilattice_sup_lifted
                              (semilattice_sup_gdefault_st
                                (infinite_key_var_id, equal_var_id)
                                (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                            (semilattice_sup_analysis_product
                              (semilattice_sup_lifted
                                (semilattice_sup_gdefault_st
                                  (infinite_key_var_id, equal_var_id)
                                  (bounded_semilattice_sup_bot_kd
                                    ik_domain_congruence)))
                              (semilattice_sup_analysis_product
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_int_tuple)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                (semilattice_sup_analysis_product
                                  (semilattice_sup_lifted
                                    (semilattice_sup_gdefault_st
                                      (infinite_key_var_id, equal_var_id)
                                      (bounded_semilattice_sup_bot_kd
ik_domain_sign)))
                                  (semilattice_sup_analysis_product
                                    (semilattice_sup_lifted
                                      (semilattice_sup_gdefault_st
(infinite_key_var_id, equal_var_id)
(bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                    (semilattice_sup_lifted
                                      (semilattice_sup_order_rel
equal_var_id))))))))
                        exp_vars ReturnVar is_global
                        (split_cmb_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))
                          gs)
                        (split_rl_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))
                          gs)
                        (split_global_at_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id))))))))))
                        (split_free_lifted
                          ((semilattice_sup_analysis_product
                             (semilattice_sup_lifted
                               (semilattice_sup_gdefault_st
                                 (split_key_var_id.infinite_key_split_key,
                                   equal_var_id)
                                 (bounded_semilattice_sup_bot_kd
                                   ik_domain_ivl)))
                             (semilattice_sup_analysis_product
                               (semilattice_sup_lifted
                                 (semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_congruence)))
                               (semilattice_sup_analysis_product
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_int_tuple)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
                                 (semilattice_sup_analysis_product
                                   (semilattice_sup_lifted
                                     (semilattice_sup_gdefault_st
                                       (split_key_var_id.infinite_key_split_key,
 equal_var_id)
                                       (bounded_semilattice_sup_bot_kd
 ik_domain_sign)))
                                   (semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_parity)))
                                     (semilattice_sup_lifted
                                       (semilattice_sup_order_rel
 equal_var_id))))))),
                            (ownership_split_analysis_product
                              (ownership_split_lifted
                                ((semilattice_sup_gdefault_st
                                   (split_key_var_id.infinite_key_split_key,
                                     equal_var_id)
                                   (bounded_semilattice_sup_bot_kd
                                     ik_domain_ivl)),
                                  (ownership_split_gdefault_st
                                    (equal_var_id, split_key_var_id)
                                    ((bounded_semilattice_sup_bot_kd
                                       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
                                      (order_top_kd ik_domain_ivl)))))
                              (ownership_split_analysis_product
                                (ownership_split_lifted
                                  ((semilattice_sup_gdefault_st
                                     (split_key_var_id.infinite_key_split_key,
                                       equal_var_id)
                                     (bounded_semilattice_sup_bot_kd
                                       ik_domain_congruence)),
                                    (ownership_split_gdefault_st
                                      (equal_var_id, split_key_var_id)
                                      ((bounded_semilattice_sup_bot_kd
 ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
(order_top_kd ik_domain_congruence)))))
                                (ownership_split_analysis_product
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_int_tuple)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_int_tuple)))))))
                                  (ownership_split_analysis_product
                                    (ownership_split_lifted
                                      ((semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_sign)),
(ownership_split_gdefault_st (equal_var_id, split_key_var_id)
  ((bounded_semilattice_sup_bot_kd
     ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
    (order_top_kd ik_domain_sign)))))
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_parity)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_parity)))))
                                      (ownership_split_lifted
((semilattice_sup_order_rel equal_var_id),
  (ownership_split_order_rel equal_var_id)))))))))))
                    (fun _ _ -> Bot)
                    (fun _ _ ->
                      map (fun x ->
                            (x, split_global_at_lifted
                                  ((semilattice_sup_analysis_product
                                     (semilattice_sup_lifted
                                       (semilattice_sup_gdefault_st
 (split_key_var_id.infinite_key_split_key, equal_var_id)
 (bounded_semilattice_sup_bot_kd ik_domain_ivl)))
                                     (semilattice_sup_analysis_product
                                       (semilattice_sup_lifted
 (semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_congruence)))
                                       (semilattice_sup_analysis_product
 (semilattice_sup_analysis_product
   (semilattice_sup_lifted
     (semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
   (semilattice_sup_analysis_product
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)))))
 (semilattice_sup_analysis_product
   (semilattice_sup_lifted
     (semilattice_sup_gdefault_st
       (split_key_var_id.infinite_key_split_key, equal_var_id)
       (bounded_semilattice_sup_bot_kd ik_domain_sign)))
   (semilattice_sup_analysis_product
     (semilattice_sup_lifted
       (semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_parity)))
     (semilattice_sup_lifted (semilattice_sup_order_rel equal_var_id))))))),
                                    (ownership_split_analysis_product
                                      (ownership_split_lifted
((semilattice_sup_gdefault_st
   (split_key_var_id.infinite_key_split_key, equal_var_id)
   (bounded_semilattice_sup_bot_kd ik_domain_ivl)),
  (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
    ((bounded_semilattice_sup_bot_kd
       ik_domain_ivl).order_bot_bounded_semilattice_sup_bot,
      (order_top_kd ik_domain_ivl)))))
                                      (ownership_split_analysis_product
(ownership_split_lifted
  ((semilattice_sup_gdefault_st
     (split_key_var_id.infinite_key_split_key, equal_var_id)
     (bounded_semilattice_sup_bot_kd ik_domain_congruence)),
    (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
      ((bounded_semilattice_sup_bot_kd
         ik_domain_congruence).order_bot_bounded_semilattice_sup_bot,
        (order_top_kd ik_domain_congruence)))))
(ownership_split_analysis_product
  (ownership_split_analysis_product
    (ownership_split_lifted
      ((semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
        (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
          ((bounded_semilattice_sup_bot_kd
             ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
            (order_top_kd ik_domain_int_tuple)))))
    (ownership_split_analysis_product
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_int_tuple)))))
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_int_tuple)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_int_tuple).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_int_tuple)))))))
  (ownership_split_analysis_product
    (ownership_split_lifted
      ((semilattice_sup_gdefault_st
         (split_key_var_id.infinite_key_split_key, equal_var_id)
         (bounded_semilattice_sup_bot_kd ik_domain_sign)),
        (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
          ((bounded_semilattice_sup_bot_kd
             ik_domain_sign).order_bot_bounded_semilattice_sup_bot,
            (order_top_kd ik_domain_sign)))))
    (ownership_split_analysis_product
      (ownership_split_lifted
        ((semilattice_sup_gdefault_st
           (split_key_var_id.infinite_key_split_key, equal_var_id)
           (bounded_semilattice_sup_bot_kd ik_domain_parity)),
          (ownership_split_gdefault_st (equal_var_id, split_key_var_id)
            ((bounded_semilattice_sup_bot_kd
               ik_domain_parity).order_bot_bounded_semilattice_sup_bot,
              (order_top_kd ik_domain_parity)))))
      (ownership_split_lifted
        ((semilattice_sup_order_rel equal_var_id),
          (ownership_split_order_rel equal_var_id)))))))))
                                  x (Lifted (mcp_init ds (activation_of asa)))))
                        gs)
                    (fun pa -> elab_cfg pa ds)
                    (fun _ -> FunctionEntry prog_main_name) is_global p)
                root))));;

let rec lits_fit
  = function N n -> less_eq_int (ik_min I64) n && less_eq_int n (ik_max I64)
    | V uu -> true
    | Plus (a, b) -> lits_fit a && lits_fit b
    | Minus (a, b) -> lits_fit a && lits_fit b
    | Times (a, b) -> lits_fit a && lits_fit b
    | Div (a, b) -> lits_fit a && lits_fit b
    | Mod (a, b) -> lits_fit a && lits_fit b
    | Less (a, b) -> lits_fit a && lits_fit b
    | LessEq (a, b) -> lits_fit a && lits_fit b
    | Greater (a, b) -> lits_fit a && lits_fit b
    | GreaterEq (a, b) -> lits_fit a && lits_fit b
    | NotEq (a, b) -> lits_fit a && lits_fit b
    | Eq (a, b) -> lits_fit a && lits_fit b
    | Not a -> lits_fit a
    | And (a, b) -> lits_fit a && lits_fit b
    | Or (a, b) -> lits_fit a && lits_fit b
    | Cast (uv, a) -> lits_fit a;;

let rec com_exps
  = function SKIP uu -> []
    | Assign (uv, uw, e) -> [e]
    | Check (ux, uy, e) -> [e]
    | Seq (c1, c2) -> com_exps c1 @ com_exps c2
    | If (uz, b, c1, c2) -> b :: com_exps c1 @ com_exps c2
    | While (va, b, c) -> b :: com_exps c
    | Call (vb, vc, vd, es) -> es
    | Return (ve, e) -> (match e with None -> [] | Some ea -> [ea])
    | Restore vf -> []
    | Unwind vg -> [];;

let footprints : (var_id, exp, var_id, unit) footprints_ext
  = Footprints_ext
      (gedge_global_reads (equal_var_id, linorder_var_id) exp_vars,
        gedge_global_writes equal_var_id ReturnVar,
        gcall_global_reads (equal_var_id, linorder_var_id) exp_vars,
        (fun g (CallEdge (dst, pars, _)) ->
          global_names_in equal_var_id g
            ((match dst with None -> [] | Some x -> [x]) @ pars)),
        ());;

let renderer :
  (unit voblint_conf_ext,
    ((ivl kd list),
      ((congruence kd list),
        (((int_never int_tuple kd list),
           ((int_once int_tuple kd list), (int_fixpoint int_tuple kd list))
             analysis_product)
           analysis_product,
          ((sign kd list), ((parity kd list), (unit list)) analysis_product)
            analysis_product)
          analysis_product)
        analysis_product)
      analysis_product,
    ((var_id -> ivl kd) lifted,
      ((var_id -> congruence kd) lifted,
        (((var_id -> int_never int_tuple kd) lifted,
           ((var_id -> int_once int_tuple kd) lifted,
             (var_id -> int_fixpoint int_tuple kd) lifted)
             analysis_product)
           analysis_product,
          ((var_id -> sign kd) lifted,
            ((var_id -> parity kd) lifted, var_id order_rel lifted)
              analysis_product)
            analysis_product)
          analysis_product)
        analysis_product)
      analysis_product,
    var_id, exp, var_id, analysis, report_value, unit)
    report_renderer_ext
  = Report_renderer_ext
      ((fun conf -> render (activation_of (conf_analyses conf))),
        (fun conf -> context_values (activation_of (conf_analyses conf))),
        footprints, ());;

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

let rec conf_context
  (Voblint_conf_ext
    (conf_analyses, conf_context, conf_globals, conf_program_globals, conf_sem,
      more))
    = conf_context;;

let rec report_run
  conf ds p =
    (match conf_context conf with Call_String k -> cs_run conf k ds p
      | Entry_State -> es_run conf ds p);;

let rec gsource_exp _B vars rv a = not (member _B rv (vars a));;

let rec prog_main p = main_body (prog_table p);;

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

let rec value_providing
  c = source_com c &&
        (not (may_fallthrough c) &&
          (not (may_return_none c) && may_return_value c));;

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
                   (equal_gproc_decl_ext equal_unit equal_literal equal_src_exp
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
                        (list_all (fun (q, _) -> is_none (special_table q))
                           procs &&
                          (list_all lits_fit (com_exps (prog_main p)) &&
                            list_all
                              (fun (_, decl) ->
                                list_all lits_fit (com_exps (body decl)))
                              procs))))))))));;

let rec valid_activation asa = not (null asa) && distinct equal_analysis asa;;

let rec run_voblint
  conf ds p =
    (if not (valid_activation (conf_analyses conf)) then Invalid_Activation
      else (if not (wf_program_compile_input_exec p) then Malformed_Program
             else (match report_run conf ds p with None -> No_Answer
                    | Some a -> Analysed a)));;

let rec make
  proc_rep declared_global_vars =
    Imp_prog_ext (proc_rep, declared_global_vars, ());;

let rec mk_program
  ps m gv = make ((prog_main_name, Gproc_decl_ext ([], m, ())) :: ps) gv;;

let rec fp_call_writes
  (Footprints_ext
    (fp_edge_reads, fp_edge_writes, fp_call_reads, fp_call_writes, more))
    = fp_call_writes;;

let rec fp_call_reads
  (Footprints_ext
    (fp_edge_reads, fp_edge_writes, fp_call_reads, fp_call_writes, more))
    = fp_call_reads;;

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
  fp res g rows u c e =
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
                          map (fun x ->
                                (Global_Node x,
                                  (Global_Read, Local_Node (after, c))))
                            (fp_call_reads fp g (ce_args ca)) @
                            map (fun x ->
                                  (Local_Node (after, c),
                                    (Global_Write, Global_Node x)))
                              (fp_call_writes fp g ca)
                   else []))));;

let rec fp_edge_writes
  (Footprints_ext
    (fp_edge_reads, fp_edge_writes, fp_call_reads, fp_call_writes, more))
    = fp_edge_writes;;

let rec fp_edge_reads
  (Footprints_ext
    (fp_edge_reads, fp_edge_writes, fp_call_reads, fp_call_writes, more))
    = fp_edge_reads;;

let rec intra_deps
  fp g rows u c e =
    (let (ua, (a, v)) = e in
      (if equal_cfg_nodea ua u &&
            membera (equal_prod equal_cfg_node equal_nat) rows (v, c)
        then (Local_Node (u, c), (Intra_Dep a, Local_Node (v, c))) ::
               map (fun x -> (Global_Node x, (Global_Read, Local_Node (v, c))))
                 (fp_edge_reads fp g a) @
                 map (fun x ->
                       (Local_Node (v, c), (Global_Write, Global_Node x)))
                   (fp_edge_writes fp g a)
        else []));;

let rec cfg_points
  x = cfg_node_list (equal_var_id, linorder_var_id) (equal_exp, linorder_exp)
        x;;

let rec report_diagnostics
  (Analysis_report_ext
    (report_config, report_vars, report_cfg, report_contexts, report_states,
      report_routes, report_checks, report_globals, report_diagnostics, more))
    = report_diagnostics;;

let rec rr_footprints
  (Report_renderer_ext (rr_view, rr_context, rr_footprints, more)) =
    rr_footprints;;

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

let rec rr_context
  (Report_renderer_ext (rr_view, rr_context, rr_footprints, more)) =
    rr_context;;

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

let rec rr_view
  (Report_renderer_ext (rr_view, rr_context, rr_footprints, more)) = rr_view;;

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

let rec report_steps_join _F
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
                       (fun (_, ba) -> (w, vjoin_lifted _F aa ba)))
                       b)
                 (zip xs ys))
          ss s);;

let rec state_value
  (Result_state_ext
    (state_point, state_context, state_value, state_checks, state_diagnostics,
      state_steps, more))
    = state_value;;

let rec report_point_join _F
  res v =
    fold (vjoin_lifted _F)
      (map_filter
        (fun x ->
          (if equal_cfg_nodea (state_point x) v then Some (state_value x)
            else None))
        (report_states res))
      Bot;;

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

let rec analysis_graph_of (_A1, _A2) (_B1, _B2) _C
  fp res =
    (let g = report_cfg res in
     let rows = report_rows_of res in
     let names = report_global_names res in
     let ga = membera _C names in
      Analysis_graph_ext
        (map (fun (a, b) -> Local_Node (a, b)) rows @
           map (fun a -> Global_Node a) names,
          maps (fun e -> maps (fun (u, c) -> intra_deps fp ga rows u c e) rows)
            (cfg_intra_list (_A1, _A2) (_B1, _B2) g) @
            maps (fun e ->
                   maps (fun (u, c) -> call_deps fp res ga rows u c e) rows)
              (cfg_calls_list (_A1, _A2) (_B1, _B2) g) @
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
  show vals x2 = match show, vals, x2 with
    show, vals, Report_Unit -> Context_Unit
    | show, vals, Report_Entry ctx -> Context_Entry (map show (vals ctx))
    | show, vals, Report_Call_String us -> Context_Call_String us;;

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

let rec render_report _C (_D1, _D2) (_E1, _E2) _F
  rr show res =
    (let config = report_config res in
     let state =
       comp (map_analysis_view show) (rr_view rr config (report_vars res)) in
      Run_result_ext
        (report_cfg res,
          map (render_context show (rr_context rr config))
            (report_contexts res),
          map (map_result_state state) (report_states res),
          map (fun v ->
                (v, (map_lift state (report_point_join _C res v),
                      map (fun (w, s) -> (w, map_lift state s))
                        (report_steps_join _C res v))))
            (cfg_node_list (_D1, _D2) (_E1, _E2) (report_cfg res)),
          report_routes res, report_checks res,
          map (map_result_global state) (report_globals res),
          report_diagnostics res,
          analysis_graph_of (_D1, _D2) (_E1, _E2) _F (rr_footprints rr) res,
          ()));;

let rec prog_render_report
  x = render_report
        (join_val_analysis_product
          (join_val_lifted (join_val_fun (semilattice_sup_kd ik_domain_ivl)))
          (join_val_analysis_product
            (join_val_lifted
              (join_val_fun (semilattice_sup_kd ik_domain_congruence)))
            (join_val_analysis_product
              (join_val_analysis_product
                (join_val_lifted
                  (join_val_fun (semilattice_sup_kd ik_domain_int_tuple)))
                (join_val_analysis_product
                  (join_val_lifted
                    (join_val_fun (semilattice_sup_kd ik_domain_int_tuple)))
                  (join_val_lifted
                    (join_val_fun (semilattice_sup_kd ik_domain_int_tuple)))))
              (join_val_analysis_product
                (join_val_lifted
                  (join_val_fun (semilattice_sup_kd ik_domain_sign)))
                (join_val_analysis_product
                  (join_val_lifted
                    (join_val_fun (semilattice_sup_kd ik_domain_parity)))
                  (join_val_lifted (join_val_order_rel equal_var_id)))))))
        (equal_var_id, linorder_var_id) (equal_exp, linorder_exp) equal_var_id
        renderer x;;

let rec cfg_call_edges
  x = cfg_calls_list (equal_var_id, linorder_var_id) (equal_exp, linorder_exp)
        x;;

let rec cfg_intra_edges
  x = cfg_intra_list (equal_var_id, linorder_var_id) (equal_exp, linorder_exp)
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

let default_sem_conf : unit sem_conf_ext = Sem_conf_ext (Assume_Top, ());;

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

let rec diagnostic_obligation (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x3;;

let rec diagnostic_occurrence (Arithmetic_Diagnostic (x1, x2, x3, x4)) = x2;;

end;; (*struct Generated*)
