
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

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Core : sig
  type int = Int_of_integer of Z.t
  val integer_of_int : int -> Z.t
  type 'a order
  type 'a linorder
  type nat
  val integer_of_nat : nat -> Z.t
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val linorder_nat : nat linorder
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  type char
  val integer_of_char : char -> Z.t
  val equal_chara : char -> char -> bool
  val equal_char : char HOL.equal
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  val equal_sum : 'a HOL.equal -> 'b HOL.equal -> ('a, 'b) sum HOL.equal
  val equal_literal : string HOL.equal
  val linorder_literal : string linorder
  type cfg_node = Statement of nat | FunctionEntry of string |
    FunctionResult of string
  val equal_cfg_nodea : cfg_node -> cfg_node -> bool
  val equal_cfg_node : cfg_node HOL.equal
  type location
  type aexp = N of int | V of string | Plus of aexp * aexp |
    Minus of aexp * aexp | Times of aexp * aexp
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val equal_unit : unit HOL.equal
  type sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop
  type 'a sup
  type 'a bot
  type 'a semilattice_sup
  type 'a bounded_semilattice_sup_bot
  val equal_option : 'a HOL.equal -> 'a option -> 'a option -> bool
  type call_action = CallEdge of string option * string list * aexp list
  val equal_call_actiona : call_action -> call_action -> bool
  type special_call = Nondet_Int | Min of aexp * aexp | Max of aexp * aexp
  type bexp = Bc of bool | Not of bexp | And of bexp * bexp | Or of bexp * bexp
    | Less of aexp * aexp | Eqa of aexp * aexp
  type edge_action = EA_Nop | EA_Assign of string * aexp |
    EA_Special of special_call * string | EA_Assume of bexp |
    EA_AssumeNot of bexp | EA_Ret of aexp option * string | EA_Check of bexp
  val equal_edge_actiona : edge_action -> edge_action -> bool
  type eint = MinInf | Fin of int | PlusInf
  type ivl = Ivl of eint * eint
  val equal_ivl : ivl HOL.equal
  val bot_ivl : ivl bot
  type 'a order_top
  val semilattice_sup_ivl : ivl semilattice_sup
  val is_bot_ivl : ivl -> bool
  type 'a computable_domain
  val computable_domain_ivl : ivl computable_domain
  type ('a, 'b) dg_state
  val fst : 'a * 'b -> 'a
  val list_all : ('a -> bool) -> 'a list -> bool
  val map : ('a -> 'b) -> 'a list -> 'b list
  type 'a resolved_st_q
  type 'a lifted = Bot | Lifted of 'a
  type gk
  type check_result = Check_Proved | Check_Refuted | Check_Unknown
  type com = SKIP | Assign of string * aexp | Check of bexp | Seq of com * com |
    If of bexp * com * com | While of bexp * com |
    Call of string option * string * aexp list | Return of aexp option | Restore
    | Unwind
  type 'a proc_decl_ext
  type num
  type 'a set = Set of 'a list | Coset of 'a list
  type 'a cfg_ext
  type ('a, 'b, 'c) strategy_tree
  type special_desc
  type 'a imp_prog_ext
  val id : 'a -> 'a
  val nat_of_integer : Z.t -> nat
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val suc : nat -> nat
  val rev : 'a list -> 'a list
  val find : ('a -> bool) -> 'a list -> 'a option
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val null : 'a list -> bool
  val image : ('a -> 'b) -> 'a set -> 'b set
  val filtera : ('a -> bool) -> 'a list -> 'a list
  val filter : ('a -> bool) -> 'a set -> 'a set
  val membera : 'a HOL.equal -> 'a list -> 'a -> bool
  val list_ex : ('a -> bool) -> 'a list -> bool
  val remdups : 'a HOL.equal -> 'a list -> 'a list
  val distinct : 'a HOL.equal -> 'a list -> bool
  val implode : char list -> string
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val ret_var : string
  val cfg_entry : 'a cfg_ext -> cfg_node
  val bot_set : 'a set
  val sup_seta : 'a HOL.equal -> 'a set set -> 'a set
  val bexp_vnames : bexp -> string set
  val snd : 'a * 'b -> 'b
  val sup_fin : 'a semilattice_sup -> 'a set -> 'a
  val char_of_integer : Z.t -> char
  val explode : string -> char list
  val proc_decl_of : string list -> com -> unit proc_decl_ext
  val zero_nat : nat
  val prog_main_name : string
  val prog_table : unit imp_prog_ext -> string -> unit proc_decl_ext option
  val prog_main : unit imp_prog_ext -> com
  val char_0x2D : char
  val show_int : int -> char list
  val sort_key : 'b linorder -> ('a -> 'b) -> 'a list -> 'a list
  val sorted_list_of_set : 'a HOL.equal * 'a linorder -> 'a set -> 'a list
  val cfg_calls_list :
    unit cfg_ext -> (cfg_node * (call_action * (cfg_node * cfg_node))) list
  val cfg_intra_list :
    unit cfg_ext -> (cfg_node * (edge_action * cfg_node)) list
  val mk_program :
    (string * unit proc_decl_ext) list ->
      com -> string list -> unit imp_prog_ext
  val prog_procs : unit imp_prog_ext -> string list
  val declared_global_vars : 'a imp_prog_ext -> string list
  val declared_global : unit imp_prog_ext -> string -> bool
  val compile_proc :
    (string -> unit proc_decl_ext option) ->
      string ->
        unit proc_decl_ext ->
          nat ->
            nat * ((cfg_node * (edge_action * cfg_node)) set *
                    (cfg_node * (call_action * (cfg_node * cfg_node))) set)
  val compile_prog :
    (string -> unit proc_decl_ext option) ->
      string list -> string -> com -> unit cfg_ext
  val char_0x0A : char
  val char_0x20 : char
  val char_0x21 : char
  val char_0x22 : char
  val char_0x23 : char
  val char_0x26 : char
  val char_0x28 : char
  val char_0x29 : char
  val char_0x2B : char
  val char_0x2C : char
  val char_0x2E : char
  val char_0x2F : char
  val char_0x30 : char
  val char_0x31 : char
  val char_0x32 : char
  val char_0x34 : char
  val char_0x35 : char
  val char_0x36 : char
  val char_0x37 : char
  val char_0x38 : char
  val char_0x3A : char
  val char_0x3B : char
  val char_0x3C : char
  val char_0x3D : char
  val char_0x3E : char
  val char_0x41 : char
  val char_0x42 : char
  val char_0x43 : char
  val char_0x44 : char
  val char_0x45 : char
  val char_0x46 : char
  val char_0x47 : char
  val char_0x48 : char
  val char_0x49 : char
  val char_0x4C : char
  val char_0x4D : char
  val char_0x4E : char
  val char_0x4F : char
  val char_0x50 : char
  val char_0x52 : char
  val char_0x53 : char
  val char_0x54 : char
  val char_0x55 : char
  val char_0x57 : char
  val char_0x58 : char
  val char_0x5A : char
  val char_0x5B : char
  val char_0x5C : char
  val char_0x5D : char
  val char_0x5F : char
  val char_0x61 : char
  val char_0x62 : char
  val char_0x63 : char
  val char_0x64 : char
  val char_0x65 : char
  val char_0x66 : char
  val char_0x67 : char
  val char_0x68 : char
  val char_0x69 : char
  val char_0x6B : char
  val char_0x6C : char
  val char_0x6D : char
  val char_0x6E : char
  val char_0x6F : char
  val char_0x70 : char
  val char_0x72 : char
  val char_0x73 : char
  val char_0x74 : char
  val char_0x75 : char
  val char_0x76 : char
  val char_0x77 : char
  val char_0x78 : char
  val char_0x79 : char
  val char_0x7A : char
  val char_0x7B : char
  val char_0x7D : char
  val equal_set : 'a HOL.equal -> 'a set -> 'a set -> bool
  val bot_fun : 'b bot -> 'a -> 'b
  val join_source : char list -> (char list) list -> char list
  val analyse_sign_report :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val scope_vnames_list : unit imp_prog_ext -> string -> string list
  val string_of_nat : nat -> char list
  val string_of_aexp : aexp -> char list
  val string_of_bexp : bexp -> char list
  val resolved_st_q_is_bot_for :
    'a computable_domain -> string list -> 'a resolved_st_q -> bool
  val analyse_sign_env_for :
    (string -> bool) -> unit imp_prog_ext -> cfg_node -> string -> sign
  val analyse_interval_report :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val entry_state_sol :
    (string -> bool) ->
      (ivl resolved_st_q -> bool) ->
        (string -> unit proc_decl_ext option) ->
          string list ->
            string ->
              com ->
                (cfg_node * ivl list) set *
                  (((cfg_node * ivl list), gk) sum ->
                    (ivl resolved_st_q lifted, ivl resolved_st_q lifted)
                      dg_state)
  val analyse_interval_td_report :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val analyse_interval_td_at :
    (ivl resolved_st_q -> bool) ->
      (string -> bool) ->
        (string -> unit proc_decl_ext option) ->
          string list -> string -> com -> cfg_node -> (string -> ivl) lifted
  val analyse_sign_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val analyse_sign_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (bexp * (check_result * (string -> sign)))) list
  val pretty_string_of_program :
    (string -> unit proc_decl_ext option) ->
      string list -> com -> string list -> char list
  val wf_program_compile_input_exec : unit imp_prog_ext -> bool
  val entry_state_sg_exec_from_sol :
    (string -> bool) ->
      (cfg_node * ivl list) set *
        (((cfg_node * ivl list), gk) sum ->
          (ivl resolved_st_q lifted, ivl resolved_st_q lifted) dg_state) ->
        ((cfg_node * ivl list), gk) sum -> (string -> ivl) lifted
  val analyse_interval_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val entry_state_check_report_prog :
    string -> unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val analyse_interval_entry_state :
    unit imp_prog_ext -> (cfg_node * (bexp * check_result)) list
  val is_bot_sign : sign -> bool
  val analyse_interval_td_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (bexp * (check_result * (string -> ivl)))) list
end = struct

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta k l = Z.equal (integer_of_int k) (integer_of_int l);;

let equal_int = ({HOL.equal = equal_inta} : int HOL.equal);;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({HOL.equal = equal_nata} : nat HOL.equal);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({HOL.equal = equal_lista _A} : ('a list) HOL.equal);;

type char = Chr of Z.t;;

let rec integer_of_char (Chr x) = x;;

let rec equal_chara c d = Z.equal (integer_of_char c) (integer_of_char d);;

let equal_char = ({HOL.equal = equal_chara} : char HOL.equal);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec equal_suma _A _B x0 x1 = match x0, x1 with Inl x1, Inr x2 -> false
                           | Inr x2, Inl x1 -> false
                           | Inr x2, Inr y2 -> HOL.eq _B x2 y2
                           | Inl x1, Inl y1 -> HOL.eq _A x1 y1;;

let rec equal_sum _A _B =
  ({HOL.equal = equal_suma _A _B} : ('a, 'b) sum HOL.equal);;

let equal_literal =
  ({HOL.equal = (fun a b -> ((a : string) = b))} : string HOL.equal);;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

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

let equal_cfg_node = ({HOL.equal = equal_cfg_nodea} : cfg_node HOL.equal);;

type ordera = Eq | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if HOL.eq _A1 x y then Eq else Gt));;

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

let rec le_of_comp
  acomp x y = (match acomp x y with Eq -> true | Lt -> true | Gt -> false);;

let rec less_eq_cfg_node x = le_of_comp comparator_cfg_node x;;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eq -> false | Lt -> true | Gt -> false);;

let rec less_cfg_node x = lt_of_comp comparator_cfg_node x;;

let ord_cfg_node =
  ({less_eq = less_eq_cfg_node; less = less_cfg_node} : cfg_node ord);;

let preorder_cfg_node = ({ord_preorder = ord_cfg_node} : cfg_node preorder);;

let order_cfg_node = ({preorder_order = preorder_cfg_node} : cfg_node order);;

let linorder_cfg_node =
  ({order_linorder = order_cfg_node} : cfg_node linorder);;

type location = Local_Location of string | Global_Location of string;;

let rec equal_locationa
  x0 x1 = match x0, x1 with Local_Location x1, Global_Location x2 -> false
    | Global_Location x2, Local_Location x1 -> false
    | Global_Location x2, Global_Location y2 -> ((x2 : string) = y2)
    | Local_Location x1, Local_Location y1 -> ((x1 : string) = y1);;

let equal_location = ({HOL.equal = equal_locationa} : location HOL.equal);;

type aexp = N of int | V of string | Plus of aexp * aexp | Minus of aexp * aexp
  | Times of aexp * aexp;;

let rec equal_aexpa
  x0 x1 = match x0, x1 with Minus (x41, x42), Times (x51, x52) -> false
    | Times (x51, x52), Minus (x41, x42) -> false
    | Plus (x31, x32), Times (x51, x52) -> false
    | Times (x51, x52), Plus (x31, x32) -> false
    | Plus (x31, x32), Minus (x41, x42) -> false
    | Minus (x41, x42), Plus (x31, x32) -> false
    | V x2, Times (x51, x52) -> false
    | Times (x51, x52), V x2 -> false
    | V x2, Minus (x41, x42) -> false
    | Minus (x41, x42), V x2 -> false
    | V x2, Plus (x31, x32) -> false
    | Plus (x31, x32), V x2 -> false
    | N x1, Times (x51, x52) -> false
    | Times (x51, x52), N x1 -> false
    | N x1, Minus (x41, x42) -> false
    | Minus (x41, x42), N x1 -> false
    | N x1, Plus (x31, x32) -> false
    | Plus (x31, x32), N x1 -> false
    | N x1, V x2 -> false
    | V x2, N x1 -> false
    | Times (x51, x52), Times (y51, y52) ->
        equal_aexpa x51 y51 && equal_aexpa x52 y52
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_aexpa x41 y41 && equal_aexpa x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_aexpa x31 y31 && equal_aexpa x32 y32
    | V x2, V y2 -> ((x2 : string) = y2)
    | N x1, N y1 -> equal_inta x1 y1;;

let equal_aexp = ({HOL.equal = equal_aexpa} : aexp HOL.equal);;

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

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

let equal_unit = ({HOL.equal = equal_unita} : unit HOL.equal);;

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

let equal_sign = ({HOL.equal = equal_signa} : sign HOL.equal);;

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

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_sign = ({sup = sup_signa} : sign sup);;

let bot_signa : sign = SBot;;

type 'a bot = {bot : 'a};;
let bot _A = _A.bot;;

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

let preorder_sign = ({ord_preorder = ord_sign} : sign preorder);;

let order_sign = ({preorder_order = preorder_sign} : sign order);;

type 'a order_bot = {bot_order_bot : 'a bot; order_order_bot : 'a order};;

let order_bot_sign =
  ({bot_order_bot = bot_sign; order_order_bot = order_sign} : sign order_bot);;

let rec widen_sign a b = join_sign a b;;

type 'a widening = {order_widening : 'a order; widen : 'a -> 'a -> 'a};;
let widen _A = _A.widen;;

let widening_sign =
  ({order_widening = order_sign; widen = widen_sign} : sign widening);;

let rec narrow_sign_td a b = a;;

let rec narrow_sign a b = narrow_sign_td a b;;

type 'a narrowing = {order_narrowing : 'a order; narrow : 'a -> 'a -> 'a};;
let narrow _A = _A.narrow;;

let narrowing_sign =
  ({order_narrowing = order_sign; narrow = narrow_sign} : sign narrowing);;

type 'a warrowing =
  {narrowing_warrowing : 'a narrowing; widening_warrowing : 'a widening};;

let warrowing_sign =
  ({narrowing_warrowing = narrowing_sign; widening_warrowing = widening_sign} :
    sign warrowing);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

let semilattice_sup_sign =
  ({sup_semilattice_sup = sup_sign; order_semilattice_sup = order_sign} :
    sign semilattice_sup);;

type 'a bounded_semilattice_sup_bot =
  {semilattice_sup_bounded_semilattice_sup_bot : 'a semilattice_sup;
    order_bot_bounded_semilattice_sup_bot : 'a order_bot};;

type 'a bounded_warrowing =
  {bounded_semilattice_sup_bot_bounded_warrowing :
     'a bounded_semilattice_sup_bot;
    warrowing_bounded_warrowing : 'a warrowing};;

let bounded_semilattice_sup_bot_sign =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_sign;
     order_bot_bounded_semilattice_sup_bot = order_bot_sign}
    : sign bounded_semilattice_sup_bot);;

let bounded_warrowing_sign =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      bounded_semilattice_sup_bot_sign;
     warrowing_bounded_warrowing = warrowing_sign}
    : sign bounded_warrowing);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> HOL.eq _A x2 y2
                          | None, None -> true;;

type call_action = CallEdge of string option * string list * aexp list;;

let rec equal_call_actiona
  (CallEdge (x1, x2, x3)) (CallEdge (y1, y2, y3)) =
    equal_option equal_literal x1 y1 &&
      (equal_lista equal_literal x2 y2 && equal_lista equal_aexp x3 y3);;

let equal_call_action =
  ({HOL.equal = equal_call_actiona} : call_action HOL.equal);;

let rec comparator_option
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, None, None -> Eq
    | comp_a, None, Some y -> Lt
    | comp_a, Some x, None -> Gt
    | comp_a, Some x, Some y -> comp_a x y;;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, [], [] -> Eq
    | comp_a, [], y :: ya -> Lt
    | comp_a, x :: xa, [] -> Gt
    | comp_a, x :: xa, y :: ya ->
        (match comp_a x y with Eq -> comparator_list comp_a xa ya | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_aexp
  x0 x1 = match x0, x1 with
    N x, N y -> comparator_of (equal_int, linorder_int) x y
    | N x, V ya -> Lt
    | N x, Plus (yb, yc) -> Lt
    | N x, Minus (yd, ye) -> Lt
    | N x, Times (yf, yg) -> Lt
    | V x, N y -> Gt
    | V x, V ya -> comparator_of (equal_literal, linorder_literal) x ya
    | V x, Plus (yb, yc) -> Lt
    | V x, Minus (yd, ye) -> Lt
    | V x, Times (yf, yg) -> Lt
    | Plus (x, xa), N y -> Gt
    | Plus (x, xa), V ya -> Gt
    | Plus (x, xa), Plus (yb, yc) ->
        (match comparator_aexp x yb with Eq -> comparator_aexp xa yc | Lt -> Lt
          | Gt -> Gt)
    | Plus (x, xa), Minus (yd, ye) -> Lt
    | Plus (x, xa), Times (yf, yg) -> Lt
    | Minus (x, xa), N y -> Gt
    | Minus (x, xa), V ya -> Gt
    | Minus (x, xa), Plus (yb, yc) -> Gt
    | Minus (x, xa), Minus (yd, ye) ->
        (match comparator_aexp x yd with Eq -> comparator_aexp xa ye | Lt -> Lt
          | Gt -> Gt)
    | Minus (x, xa), Times (yf, yg) -> Lt
    | Times (x, xa), N y -> Gt
    | Times (x, xa), V ya -> Gt
    | Times (x, xa), Plus (yb, yc) -> Gt
    | Times (x, xa), Minus (yd, ye) -> Gt
    | Times (x, xa), Times (yf, yg) ->
        (match comparator_aexp x yf with Eq -> comparator_aexp xa yg | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_call_action
  (CallEdge (x, xa, xb)) (CallEdge (y, ya, yb)) =
    (match
      comparator_option (comparator_of (equal_literal, linorder_literal)) x y
      with Eq ->
        (match
          comparator_list (comparator_of (equal_literal, linorder_literal)) xa
            ya
          with Eq -> comparator_list comparator_aexp xb yb | Lt -> Lt
          | Gt -> Gt)
      | Lt -> Lt | Gt -> Gt);;

let rec less_eq_call_action x = le_of_comp comparator_call_action x;;

let rec less_call_action x = lt_of_comp comparator_call_action x;;

let ord_call_action =
  ({less_eq = less_eq_call_action; less = less_call_action} : call_action ord);;

let preorder_call_action =
  ({ord_preorder = ord_call_action} : call_action preorder);;

let order_call_action =
  ({preorder_order = preorder_call_action} : call_action order);;

let linorder_call_action =
  ({order_linorder = order_call_action} : call_action linorder);;

type special_call = Nondet_Int | Min of aexp * aexp | Max of aexp * aexp;;

let rec equal_special_call
  x0 x1 = match x0, x1 with Min (x21, x22), Max (x31, x32) -> false
    | Max (x31, x32), Min (x21, x22) -> false
    | Nondet_Int, Max (x31, x32) -> false
    | Max (x31, x32), Nondet_Int -> false
    | Nondet_Int, Min (x21, x22) -> false
    | Min (x21, x22), Nondet_Int -> false
    | Max (x31, x32), Max (y31, y32) ->
        equal_aexpa x31 y31 && equal_aexpa x32 y32
    | Min (x21, x22), Min (y21, y22) ->
        equal_aexpa x21 y21 && equal_aexpa x22 y22
    | Nondet_Int, Nondet_Int -> true;;

let rec equal_bool p pa = match p, pa with false, p -> not p
                     | true, p -> p
                     | p, false -> not p
                     | p, true -> p;;

type bexp = Bc of bool | Not of bexp | And of bexp * bexp | Or of bexp * bexp |
  Less of aexp * aexp | Eqa of aexp * aexp;;

let rec equal_bexp
  x0 x1 = match x0, x1 with Less (x51, x52), Eqa (x61, x62) -> false
    | Eqa (x61, x62), Less (x51, x52) -> false
    | Or (x41, x42), Eqa (x61, x62) -> false
    | Eqa (x61, x62), Or (x41, x42) -> false
    | Or (x41, x42), Less (x51, x52) -> false
    | Less (x51, x52), Or (x41, x42) -> false
    | And (x31, x32), Eqa (x61, x62) -> false
    | Eqa (x61, x62), And (x31, x32) -> false
    | And (x31, x32), Less (x51, x52) -> false
    | Less (x51, x52), And (x31, x32) -> false
    | And (x31, x32), Or (x41, x42) -> false
    | Or (x41, x42), And (x31, x32) -> false
    | Not x2, Eqa (x61, x62) -> false
    | Eqa (x61, x62), Not x2 -> false
    | Not x2, Less (x51, x52) -> false
    | Less (x51, x52), Not x2 -> false
    | Not x2, Or (x41, x42) -> false
    | Or (x41, x42), Not x2 -> false
    | Not x2, And (x31, x32) -> false
    | And (x31, x32), Not x2 -> false
    | Bc x1, Eqa (x61, x62) -> false
    | Eqa (x61, x62), Bc x1 -> false
    | Bc x1, Less (x51, x52) -> false
    | Less (x51, x52), Bc x1 -> false
    | Bc x1, Or (x41, x42) -> false
    | Or (x41, x42), Bc x1 -> false
    | Bc x1, And (x31, x32) -> false
    | And (x31, x32), Bc x1 -> false
    | Bc x1, Not x2 -> false
    | Not x2, Bc x1 -> false
    | Eqa (x61, x62), Eqa (y61, y62) ->
        equal_aexpa x61 y61 && equal_aexpa x62 y62
    | Less (x51, x52), Less (y51, y52) ->
        equal_aexpa x51 y51 && equal_aexpa x52 y52
    | Or (x41, x42), Or (y41, y42) -> equal_bexp x41 y41 && equal_bexp x42 y42
    | And (x31, x32), And (y31, y32) -> equal_bexp x31 y31 && equal_bexp x32 y32
    | Not x2, Not y2 -> equal_bexp x2 y2
    | Bc x1, Bc y1 -> equal_bool x1 y1;;

type edge_action = EA_Nop | EA_Assign of string * aexp |
  EA_Special of special_call * string | EA_Assume of bexp | EA_AssumeNot of bexp
  | EA_Ret of aexp option * string | EA_Check of bexp;;

let rec equal_edge_actiona
  x0 x1 = match x0, x1 with EA_Ret (x61, x62), EA_Check x7 -> false
    | EA_Check x7, EA_Ret (x61, x62) -> false
    | EA_AssumeNot x5, EA_Check x7 -> false
    | EA_Check x7, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_AssumeNot x5 -> false
    | EA_Assume x4, EA_Check x7 -> false
    | EA_Check x7, EA_Assume x4 -> false
    | EA_Assume x4, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Assume x4 -> false
    | EA_Assume x4, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assume x4 -> false
    | EA_Special (x31, x32), EA_Check x7 -> false
    | EA_Check x7, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assume x4 -> false
    | EA_Assume x4, EA_Special (x31, x32) -> false
    | EA_Assign (x21, x22), EA_Check x7 -> false
    | EA_Check x7, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Assume x4 -> false
    | EA_Assume x4, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assign (x21, x22) -> false
    | EA_Nop, EA_Check x7 -> false
    | EA_Check x7, EA_Nop -> false
    | EA_Nop, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Nop -> false
    | EA_Nop, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Nop -> false
    | EA_Nop, EA_Assume x4 -> false
    | EA_Assume x4, EA_Nop -> false
    | EA_Nop, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Nop -> false
    | EA_Nop, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Nop -> false
    | EA_Check x7, EA_Check y7 -> equal_bexp x7 y7
    | EA_Ret (x61, x62), EA_Ret (y61, y62) ->
        equal_option equal_aexp x61 y61 && ((x62 : string) = y62)
    | EA_AssumeNot x5, EA_AssumeNot y5 -> equal_bexp x5 y5
    | EA_Assume x4, EA_Assume y4 -> equal_bexp x4 y4
    | EA_Special (x31, x32), EA_Special (y31, y32) ->
        equal_special_call x31 y31 && ((x32 : string) = y32)
    | EA_Assign (x21, x22), EA_Assign (y21, y22) ->
        ((x21 : string) = y21) && equal_aexpa x22 y22
    | EA_Nop, EA_Nop -> true;;

let equal_edge_action =
  ({HOL.equal = equal_edge_actiona} : edge_action HOL.equal);;

let rec comparator_special_call
  x0 x1 = match x0, x1 with Nondet_Int, Nondet_Int -> Eq
    | Nondet_Int, Min (y, ya) -> Lt
    | Nondet_Int, Max (yb, yc) -> Lt
    | Min (x, xa), Nondet_Int -> Gt
    | Min (x, xa), Min (y, ya) ->
        (match comparator_aexp x y with Eq -> comparator_aexp xa ya | Lt -> Lt
          | Gt -> Gt)
    | Min (x, xa), Max (yb, yc) -> Lt
    | Max (x, xa), Nondet_Int -> Gt
    | Max (x, xa), Min (y, ya) -> Gt
    | Max (x, xa), Max (yb, yc) ->
        (match comparator_aexp x yb with Eq -> comparator_aexp xa yc | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_bool x0 x1 = match x0, x1 with false, false -> Eq
                          | false, true -> Lt
                          | true, true -> Eq
                          | true, false -> Gt;;

let rec comparator_bexp
  x0 x1 = match x0, x1 with Bc x, Bc y -> comparator_bool x y
    | Bc x, Not ya -> Lt
    | Bc x, And (yb, yc) -> Lt
    | Bc x, Or (yd, ye) -> Lt
    | Bc x, Less (yf, yg) -> Lt
    | Bc x, Eqa (yh, yi) -> Lt
    | Not x, Bc y -> Gt
    | Not x, Not ya -> comparator_bexp x ya
    | Not x, And (yb, yc) -> Lt
    | Not x, Or (yd, ye) -> Lt
    | Not x, Less (yf, yg) -> Lt
    | Not x, Eqa (yh, yi) -> Lt
    | And (x, xa), Bc y -> Gt
    | And (x, xa), Not ya -> Gt
    | And (x, xa), And (yb, yc) ->
        (match comparator_bexp x yb with Eq -> comparator_bexp xa yc | Lt -> Lt
          | Gt -> Gt)
    | And (x, xa), Or (yd, ye) -> Lt
    | And (x, xa), Less (yf, yg) -> Lt
    | And (x, xa), Eqa (yh, yi) -> Lt
    | Or (x, xa), Bc y -> Gt
    | Or (x, xa), Not ya -> Gt
    | Or (x, xa), And (yb, yc) -> Gt
    | Or (x, xa), Or (yd, ye) ->
        (match comparator_bexp x yd with Eq -> comparator_bexp xa ye | Lt -> Lt
          | Gt -> Gt)
    | Or (x, xa), Less (yf, yg) -> Lt
    | Or (x, xa), Eqa (yh, yi) -> Lt
    | Less (x, xa), Bc y -> Gt
    | Less (x, xa), Not ya -> Gt
    | Less (x, xa), And (yb, yc) -> Gt
    | Less (x, xa), Or (yd, ye) -> Gt
    | Less (x, xa), Less (yf, yg) ->
        (match comparator_aexp x yf with Eq -> comparator_aexp xa yg | Lt -> Lt
          | Gt -> Gt)
    | Less (x, xa), Eqa (yh, yi) -> Lt
    | Eqa (x, xa), Bc y -> Gt
    | Eqa (x, xa), Not ya -> Gt
    | Eqa (x, xa), And (yb, yc) -> Gt
    | Eqa (x, xa), Or (yd, ye) -> Gt
    | Eqa (x, xa), Less (yf, yg) -> Gt
    | Eqa (x, xa), Eqa (yh, yi) ->
        (match comparator_aexp x yh with Eq -> comparator_aexp xa yi | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_edge_action
  x0 x1 = match x0, x1 with EA_Nop, EA_Nop -> Eq
    | EA_Nop, EA_Assign (y, ya) -> Lt
    | EA_Nop, EA_Special (yb, yc) -> Lt
    | EA_Nop, EA_Assume yd -> Lt
    | EA_Nop, EA_AssumeNot ye -> Lt
    | EA_Nop, EA_Ret (yf, yg) -> Lt
    | EA_Nop, EA_Check yh -> Lt
    | EA_Assign (x, xa), EA_Nop -> Gt
    | EA_Assign (x, xa), EA_Assign (y, ya) ->
        (match comparator_of (equal_literal, linorder_literal) x y
          with Eq -> comparator_aexp xa ya | Lt -> Lt | Gt -> Gt)
    | EA_Assign (x, xa), EA_Special (yb, yc) -> Lt
    | EA_Assign (x, xa), EA_Assume yd -> Lt
    | EA_Assign (x, xa), EA_AssumeNot ye -> Lt
    | EA_Assign (x, xa), EA_Ret (yf, yg) -> Lt
    | EA_Assign (x, xa), EA_Check yh -> Lt
    | EA_Special (x, xa), EA_Nop -> Gt
    | EA_Special (x, xa), EA_Assign (y, ya) -> Gt
    | EA_Special (x, xa), EA_Special (yb, yc) ->
        (match comparator_special_call x yb
          with Eq -> comparator_of (equal_literal, linorder_literal) xa yc
          | Lt -> Lt | Gt -> Gt)
    | EA_Special (x, xa), EA_Assume yd -> Lt
    | EA_Special (x, xa), EA_AssumeNot ye -> Lt
    | EA_Special (x, xa), EA_Ret (yf, yg) -> Lt
    | EA_Special (x, xa), EA_Check yh -> Lt
    | EA_Assume x, EA_Nop -> Gt
    | EA_Assume x, EA_Assign (y, ya) -> Gt
    | EA_Assume x, EA_Special (yb, yc) -> Gt
    | EA_Assume x, EA_Assume yd -> comparator_bexp x yd
    | EA_Assume x, EA_AssumeNot ye -> Lt
    | EA_Assume x, EA_Ret (yf, yg) -> Lt
    | EA_Assume x, EA_Check yh -> Lt
    | EA_AssumeNot x, EA_Nop -> Gt
    | EA_AssumeNot x, EA_Assign (y, ya) -> Gt
    | EA_AssumeNot x, EA_Special (yb, yc) -> Gt
    | EA_AssumeNot x, EA_Assume yd -> Gt
    | EA_AssumeNot x, EA_AssumeNot ye -> comparator_bexp x ye
    | EA_AssumeNot x, EA_Ret (yf, yg) -> Lt
    | EA_AssumeNot x, EA_Check yh -> Lt
    | EA_Ret (x, xa), EA_Nop -> Gt
    | EA_Ret (x, xa), EA_Assign (y, ya) -> Gt
    | EA_Ret (x, xa), EA_Special (yb, yc) -> Gt
    | EA_Ret (x, xa), EA_Assume yd -> Gt
    | EA_Ret (x, xa), EA_AssumeNot ye -> Gt
    | EA_Ret (x, xa), EA_Ret (yf, yg) ->
        (match comparator_option comparator_aexp x yf
          with Eq -> comparator_of (equal_literal, linorder_literal) xa yg
          | Lt -> Lt | Gt -> Gt)
    | EA_Ret (x, xa), EA_Check yh -> Lt
    | EA_Check x, EA_Nop -> Gt
    | EA_Check x, EA_Assign (y, ya) -> Gt
    | EA_Check x, EA_Special (yb, yc) -> Gt
    | EA_Check x, EA_Assume yd -> Gt
    | EA_Check x, EA_AssumeNot ye -> Gt
    | EA_Check x, EA_Ret (yf, yg) -> Gt
    | EA_Check x, EA_Check yh -> comparator_bexp x yh;;

let rec less_eq_edge_action x = le_of_comp comparator_edge_action x;;

let rec less_edge_action x = lt_of_comp comparator_edge_action x;;

let ord_edge_action =
  ({less_eq = less_eq_edge_action; less = less_edge_action} : edge_action ord);;

let preorder_edge_action =
  ({ord_preorder = ord_edge_action} : edge_action preorder);;

let order_edge_action =
  ({preorder_order = preorder_edge_action} : edge_action order);;

let linorder_edge_action =
  ({order_linorder = order_edge_action} : edge_action linorder);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type eint = MinInf | Fin of int | PlusInf;;

let rec eint_le x0 uu = match x0, uu with MinInf, uu -> true
                  | Fin v, PlusInf -> true
                  | PlusInf, PlusInf -> true
                  | Fin n, Fin m -> less_eq_int n m
                  | Fin v, MinInf -> false
                  | PlusInf, MinInf -> false
                  | PlusInf, Fin v -> false;;

let rec less_eq_eint x = eint_le x;;

let rec less_eint a b = eint_le a b && not (eint_le b a);;

let ord_eint = ({less_eq = less_eq_eint; less = less_eint} : eint ord);;

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

let equal_ivl = ({HOL.equal = equal_ivla} : ivl HOL.equal);;

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

type 'a top = {top : 'a};;
let top _A = _A.top;;

let top_ivl = ({top = top_ivla} : ivl top);;

let preorder_ivl = ({ord_preorder = ord_ivl} : ivl preorder);;

let order_ivl = ({preorder_order = preorder_ivl} : ivl order);;

let order_bot_ivl =
  ({bot_order_bot = bot_ivl; order_order_bot = order_ivl} : ivl order_bot);;

type 'a order_top = {order_order_top : 'a order; top_order_top : 'a top};;

let order_top_ivl =
  ({order_order_top = order_ivl; top_order_top = top_ivl} : ivl order_top);;

let rec widen_ivl_core
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l1 l2 then l1 else MinInf),
          (if less_eq_eint u2 u1 then u1 else PlusInf));;

let rec widen_ivl
  a b = (if equal_ivla a bot_ivla then b
          else (if equal_ivla b bot_ivla then a else widen_ivl_core a b));;

let widening_ivl =
  ({order_widening = order_ivl; widen = widen_ivl} : ivl widening);;

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

let semilattice_sup_ivl =
  ({sup_semilattice_sup = sup_ivl; order_semilattice_sup = order_ivl} :
    ivl semilattice_sup);;

let bounded_semilattice_sup_bot_ivl =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_ivl;
     order_bot_bounded_semilattice_sup_bot = order_bot_ivl}
    : ivl bounded_semilattice_sup_bot);;

let bounded_warrowing_ivl =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      bounded_semilattice_sup_bot_ivl;
     warrowing_bounded_warrowing = warrowing_ivl}
    : ivl bounded_warrowing);;

let rec is_top_ivl i = equal_ivla i ivl_top;;

let rec is_top_ivla a = is_top_ivl a;;

let rec is_bottom_ivl
  i = (let Ivl (l, u) = i in
        equal_eint l PlusInf ||
          (equal_eint u MinInf || not (less_eq_eint l u)));;

let rec is_bot_ivl a = is_bottom_ivl a;;

type 'a computable_domain =
  {bounded_semilattice_sup_bot_computable_domain :
     'a bounded_semilattice_sup_bot;
    order_top_computable_domain : 'a order_top; is_bot : 'a -> bool;
    is_top : 'a -> bool};;
let is_bot _A = _A.is_bot;;
let is_top _A = _A.is_top;;

let computable_domain_ivl =
  ({bounded_semilattice_sup_bot_computable_domain =
      bounded_semilattice_sup_bot_ivl;
     order_top_computable_domain = order_top_ivl; is_bot = is_bot_ivl;
     is_top = is_top_ivla}
    : ivl computable_domain);;

type ('a, 'b) dg_state = DG of 'a * 'b;;

let rec equal_dg_statea _A _B
  (DG (x1, x2)) (DG (y1, y2)) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_dg_state _A _B =
  ({HOL.equal = equal_dg_statea _A _B} : ('a, 'b) dg_state HOL.equal);;

let rec locals (DG (x1, x2)) = x1;;

let rec globs (DG (x1, x2)) = x2;;

let rec sup_dg_statea _A _B
  d1 d2 =
    DG (sup _A.sup_semilattice_sup (locals d1) (locals d2),
         sup _B.sup_semilattice_sup (globs d1) (globs d2));;

let rec sup_dg_state _A _B =
  ({sup = sup_dg_statea _A _B} : ('a, 'b) dg_state sup);;

let rec bot_dg_statea _A _B = DG (bot _A.bot_order_bot, bot _B.bot_order_bot);;

let rec bot_dg_state _A _B =
  ({bot = bot_dg_statea _A _B} : ('a, 'b) dg_state bot);;

let rec less_eq_dg_state _A _B
  d1 d2 =
    less_eq _A (locals d1) (locals d2) && less_eq _B (globs d1) (globs d2);;

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

let rec order_bot_dg_state _A _B =
  ({bot_order_bot = (bot_dg_state _A _B);
     order_order_bot = (order_dg_state _A.order_order_bot _B.order_order_bot)}
    : ('a, 'b) dg_state order_bot);;

let rec widen_dg_state _A _B
  a b = DG (widen _A.warrowing_bounded_warrowing.widening_warrowing (locals a)
              (locals b),
             widen _B.warrowing_bounded_warrowing.widening_warrowing (globs a)
               (globs b));;

let rec widening_dg_state _A _B =
  ({order_widening =
      (order_dg_state
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     widen = widen_dg_state _A _B}
    : ('a, 'b) dg_state widening);;

let rec narrow_dg_state _A _B
  a b = DG (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing (locals a)
              (locals b),
             narrow _B.warrowing_bounded_warrowing.narrowing_warrowing (globs a)
               (globs b));;

let rec narrowing_dg_state _A _B =
  ({order_narrowing =
      (order_dg_state
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     narrow = narrow_dg_state _A _B}
    : ('a, 'b) dg_state narrowing);;

let rec warrowing_dg_state _A _B =
  ({narrowing_warrowing = (narrowing_dg_state _A _B);
     widening_warrowing = (widening_dg_state _A _B)}
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

let rec map_of _A
  x0 k = match x0, k with [], k -> None
    | (l, v) :: ps, k -> (if HOL.eq _A l k then Some v else map_of _A ps k);;

let rec lookup_resolved_st _A
  (dl, (dg, ps)) loc =
    (match map_of equal_location ps loc
      with None ->
        (match loc with Local_Location _ -> dl | Global_Location _ -> dg)
      | Some a -> a);;

let rec fst (x1, x2) = x1;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec le_resolved_st_code _A
  s t = (let (dl, (dg, ps)) = s in
         let (el, (eg, qs)) = t in
          less_eq _A.order_order_bot.preorder_order.ord_preorder dl el &&
            (less_eq _A.order_order_bot.preorder_order.ord_preorder dg eg &&
              list_all
                (fun loc ->
                  less_eq _A.order_order_bot.preorder_order.ord_preorder
                    (lookup_resolved_st _A.bot_order_bot (dl, (dg, ps)) loc)
                    (lookup_resolved_st _A.bot_order_bot (el, (eg, qs)) loc))
                (map fst ps @ map fst qs)));;

type 'a resolved_st_q = Abs_resolved_st of ('a * ('a * (location * 'a) list));;

let rec less_eq_resolved_st_q _A
  (Abs_resolved_st xb) (Abs_resolved_st x) = le_resolved_st_code _A xb x;;

let rec equal_resolved_st_qa (_A1, _A2)
  s t = less_eq_resolved_st_q _A2 s t && less_eq_resolved_st_q _A2 t s;;

let rec equal_resolved_st_q (_A1, _A2) =
  ({HOL.equal = equal_resolved_st_qa (_A1, _A2)} : 'a resolved_st_q HOL.equal);;

let rec merge_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup dl1
       dl2,
      (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
         dg1 dg2,
        map (fun (loc, _) ->
              (loc, sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                      (lookup_resolved_st
                        _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec sup_resolved_st_qa _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (merge_resolved_st _A xa x);;

let rec sup_resolved_st_q _A =
  ({sup = sup_resolved_st_qa _A} : 'a resolved_st_q sup);;

let rec bot_resolved_st_qa _A = Abs_resolved_st (bot _A, (bot _A, []));;

let rec bot_resolved_st_q _A =
  ({bot = bot_resolved_st_qa _A} : 'a resolved_st_q bot);;

let rec less_resolved_st_q _A
  s t = less_eq_resolved_st_q _A s t && not (less_eq_resolved_st_q _A t s);;

let rec ord_resolved_st_q _A =
  ({less_eq = less_eq_resolved_st_q _A; less = less_resolved_st_q _A} :
    'a resolved_st_q ord);;

let rec preorder_resolved_st_q _A =
  ({ord_preorder = (ord_resolved_st_q _A)} : 'a resolved_st_q preorder);;

let rec order_resolved_st_q _A =
  ({preorder_order = (preorder_resolved_st_q _A)} : 'a resolved_st_q order);;

let rec order_bot_resolved_st_q _A =
  ({bot_order_bot = (bot_resolved_st_q _A.bot_order_bot);
     order_order_bot = (order_resolved_st_q _A)}
    : 'a resolved_st_q order_bot);;

let rec widen_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (widen _A.warrowing_bounded_warrowing.widening_warrowing dl1 dl2,
      (widen _A.warrowing_bounded_warrowing.widening_warrowing dg1 dg2,
        map (fun (loc, _) ->
              (loc, widen _A.warrowing_bounded_warrowing.widening_warrowing
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec widen_on_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (widen_resolved_st _A xa x);;

let rec widen_resolved_st_q _A s t = widen_on_resolved_st_q _A s t;;

let rec widening_resolved_st_q _A =
  ({order_widening =
      (order_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot);
     widen = widen_resolved_st_q _A}
    : 'a resolved_st_q widening);;

let rec narrow_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing dl1 dl2,
      (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing dg1 dg2,
        map (fun (loc, _) ->
              (loc, narrow _A.warrowing_bounded_warrowing.narrowing_warrowing
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec narrow_on_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (narrow_resolved_st _A xa x);;

let rec narrow_resolved_st_q _A s t = narrow_on_resolved_st_q _A s t;;

let rec narrowing_resolved_st_q _A =
  ({order_narrowing =
      (order_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot);
     narrow = narrow_resolved_st_q _A}
    : 'a resolved_st_q narrowing);;

let rec warrowing_resolved_st_q _A =
  ({narrowing_warrowing = (narrowing_resolved_st_q _A);
     widening_warrowing = (widening_resolved_st_q _A)}
    : 'a resolved_st_q warrowing);;

let rec semilattice_sup_resolved_st_q _A =
  ({sup_semilattice_sup = (sup_resolved_st_q _A);
     order_semilattice_sup =
       (order_resolved_st_q _A.order_bot_bounded_semilattice_sup_bot)}
    : 'a resolved_st_q semilattice_sup);;

let rec bounded_semilattice_sup_bot_resolved_st_q _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_resolved_st_q _A);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_resolved_st_q _A.order_bot_bounded_semilattice_sup_bot)}
    : 'a resolved_st_q bounded_semilattice_sup_bot);;

let rec bounded_warrowing_resolved_st_q _A =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      (bounded_semilattice_sup_bot_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing);
     warrowing_bounded_warrowing = (warrowing_resolved_st_q _A)}
    : 'a resolved_st_q bounded_warrowing);;

type 'a lifted = Bot | Lifted of 'a;;

let rec equal_lifteda _A x0 x1 = match x0, x1 with Bot, Lifted x2 -> false
                           | Lifted x2, Bot -> false
                           | Lifted x2, Lifted y2 -> HOL.eq _A x2 y2
                           | Bot, Bot -> true;;

let rec equal_lifted _A =
  ({HOL.equal = equal_lifteda _A} : 'a lifted HOL.equal);;

let rec sup_lifteda _A
  x0 y = match x0, y with Bot, y -> y
    | Lifted v, Bot -> Lifted v
    | Lifted a, Lifted b -> Lifted (sup _A.sup_semilattice_sup a b);;

let rec sup_lifted _A = ({sup = sup_lifteda _A} : 'a lifted sup);;

let bot_lifteda : 'a lifted = Bot;;

let bot_lifted = ({bot = bot_lifteda} : 'a lifted bot);;

let rec less_eq_lifted _A
  x0 uu = match x0, uu with Bot, uu -> true
    | Lifted uv, Bot -> false
    | Lifted a, Lifted b -> less_eq _A.preorder_order.ord_preorder a b;;

let rec less_lifted _A
  x y = less_eq_lifted _A x y && not (less_eq_lifted _A y x);;

let rec ord_lifted _A =
  ({less_eq = less_eq_lifted _A; less = less_lifted _A} : 'a lifted ord);;

let rec preorder_lifted _A =
  ({ord_preorder = (ord_lifted _A)} : 'a lifted preorder);;

let rec order_lifted _A =
  ({preorder_order = (preorder_lifted _A)} : 'a lifted order);;

let rec order_bot_lifted _A =
  ({bot_order_bot = bot_lifted; order_order_bot = (order_lifted _A)} :
    'a lifted order_bot);;

let rec widen_lifted _A x0 y = match x0, y with Bot, y -> y
                          | Lifted v, Bot -> Lifted v
                          | Lifted a, Lifted b -> Lifted (widen _A a b);;

let rec widening_lifted _A =
  ({order_widening = (order_lifted _A.order_widening); widen = widen_lifted _A}
    : 'a lifted widening);;

let rec narrow_lifted _A x0 y = match x0, y with Bot, y -> Bot
                           | Lifted a, Bot -> Bot
                           | Lifted a, Lifted b -> Lifted (narrow _A a b);;

let rec narrowing_lifted _A =
  ({order_narrowing = (order_lifted _A.order_narrowing);
     narrow = narrow_lifted _A}
    : 'a lifted narrowing);;

let rec warrowing_lifted _A =
  ({narrowing_warrowing =
      (narrowing_lifted _A.warrowing_bounded_warrowing.narrowing_warrowing);
     widening_warrowing =
       (widening_lifted _A.warrowing_bounded_warrowing.widening_warrowing)}
    : 'a lifted warrowing);;

let rec semilattice_sup_lifted _A =
  ({sup_semilattice_sup = (sup_lifted _A);
     order_semilattice_sup = (order_lifted _A.order_semilattice_sup)}
    : 'a lifted semilattice_sup);;

let rec bounded_semilattice_sup_bot_lifted _A =
  ({semilattice_sup_bounded_semilattice_sup_bot = (semilattice_sup_lifted _A);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_lifted _A.order_semilattice_sup)}
    : 'a lifted bounded_semilattice_sup_bot);;

let rec bounded_warrowing_lifted _A =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      (bounded_semilattice_sup_bot_lifted
        _A.bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot);
     warrowing_bounded_warrowing = (warrowing_lifted _A)}
    : 'a lifted bounded_warrowing);;

type gk = Global | Seed of cfg_node * ivl list;;

let rec equal_gka
  x0 x1 = match x0, x1 with Global, Seed (x21, x22) -> false
    | Seed (x21, x22), Global -> false
    | Seed (x21, x22), Seed (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_lista equal_ivl x22 y22
    | Global, Global -> true;;

let equal_gk = ({HOL.equal = equal_gka} : gk HOL.equal);;

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

type com = SKIP | Assign of string * aexp | Check of bexp | Seq of com * com |
  If of bexp * com * com | While of bexp * com |
  Call of string option * string * aexp list | Return of aexp option | Restore |
  Unwind;;

let rec equal_com
  x0 x1 = match x0, x1 with Restore, Unwind -> false
    | Unwind, Restore -> false
    | Return x8, Unwind -> false
    | Unwind, Return x8 -> false
    | Return x8, Restore -> false
    | Restore, Return x8 -> false
    | Call (x71, x72, x73), Unwind -> false
    | Unwind, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Restore -> false
    | Restore, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Return x8 -> false
    | Return x8, Call (x71, x72, x73) -> false
    | While (x61, x62), Unwind -> false
    | Unwind, While (x61, x62) -> false
    | While (x61, x62), Restore -> false
    | Restore, While (x61, x62) -> false
    | While (x61, x62), Return x8 -> false
    | Return x8, While (x61, x62) -> false
    | While (x61, x62), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), While (x61, x62) -> false
    | If (x51, x52, x53), Unwind -> false
    | Unwind, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Restore -> false
    | Restore, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Return x8 -> false
    | Return x8, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), If (x51, x52, x53) -> false
    | If (x51, x52, x53), While (x61, x62) -> false
    | While (x61, x62), If (x51, x52, x53) -> false
    | Seq (x41, x42), Unwind -> false
    | Unwind, Seq (x41, x42) -> false
    | Seq (x41, x42), Restore -> false
    | Restore, Seq (x41, x42) -> false
    | Seq (x41, x42), Return x8 -> false
    | Return x8, Seq (x41, x42) -> false
    | Seq (x41, x42), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Seq (x41, x42) -> false
    | Seq (x41, x42), While (x61, x62) -> false
    | While (x61, x62), Seq (x41, x42) -> false
    | Seq (x41, x42), If (x51, x52, x53) -> false
    | If (x51, x52, x53), Seq (x41, x42) -> false
    | Check x3, Unwind -> false
    | Unwind, Check x3 -> false
    | Check x3, Restore -> false
    | Restore, Check x3 -> false
    | Check x3, Return x8 -> false
    | Return x8, Check x3 -> false
    | Check x3, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Check x3 -> false
    | Check x3, While (x61, x62) -> false
    | While (x61, x62), Check x3 -> false
    | Check x3, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Check x3 -> false
    | Check x3, Seq (x41, x42) -> false
    | Seq (x41, x42), Check x3 -> false
    | Assign (x21, x22), Unwind -> false
    | Unwind, Assign (x21, x22) -> false
    | Assign (x21, x22), Restore -> false
    | Restore, Assign (x21, x22) -> false
    | Assign (x21, x22), Return x8 -> false
    | Return x8, Assign (x21, x22) -> false
    | Assign (x21, x22), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Assign (x21, x22) -> false
    | Assign (x21, x22), While (x61, x62) -> false
    | While (x61, x62), Assign (x21, x22) -> false
    | Assign (x21, x22), If (x51, x52, x53) -> false
    | If (x51, x52, x53), Assign (x21, x22) -> false
    | Assign (x21, x22), Seq (x41, x42) -> false
    | Seq (x41, x42), Assign (x21, x22) -> false
    | Assign (x21, x22), Check x3 -> false
    | Check x3, Assign (x21, x22) -> false
    | SKIP, Unwind -> false
    | Unwind, SKIP -> false
    | SKIP, Restore -> false
    | Restore, SKIP -> false
    | SKIP, Return x8 -> false
    | Return x8, SKIP -> false
    | SKIP, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), SKIP -> false
    | SKIP, While (x61, x62) -> false
    | While (x61, x62), SKIP -> false
    | SKIP, If (x51, x52, x53) -> false
    | If (x51, x52, x53), SKIP -> false
    | SKIP, Seq (x41, x42) -> false
    | Seq (x41, x42), SKIP -> false
    | SKIP, Check x3 -> false
    | Check x3, SKIP -> false
    | SKIP, Assign (x21, x22) -> false
    | Assign (x21, x22), SKIP -> false
    | Return x8, Return y8 -> equal_option equal_aexp x8 y8
    | Call (x71, x72, x73), Call (y71, y72, y73) ->
        equal_option equal_literal x71 y71 &&
          (((x72 : string) = y72) && equal_lista equal_aexp x73 y73)
    | While (x61, x62), While (y61, y62) ->
        equal_bexp x61 y61 && equal_com x62 y62
    | If (x51, x52, x53), If (y51, y52, y53) ->
        equal_bexp x51 y51 && (equal_com x52 y52 && equal_com x53 y53)
    | Seq (x41, x42), Seq (y41, y42) -> equal_com x41 y41 && equal_com x42 y42
    | Check x3, Check y3 -> equal_bexp x3 y3
    | Assign (x21, x22), Assign (y21, y22) ->
        ((x21 : string) = y21) && equal_aexpa x22 y22
    | Unwind, Unwind -> true
    | Restore, Restore -> true
    | SKIP, SKIP -> true;;

type 'a proc_decl_ext = Proc_decl_ext of string list * com * 'a;;

let rec equal_proc_decl_exta _A
  (Proc_decl_ext (formalsa, bodya, morea)) (Proc_decl_ext (formals, body, more))
    = equal_lista equal_literal formalsa formals &&
        (equal_com bodya body && HOL.eq _A morea more);;

let rec equal_proc_decl_ext _A =
  ({HOL.equal = equal_proc_decl_exta _A} : 'a proc_decl_ext HOL.equal);;

type num = One | Bit0 of num | Bit1 of num;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a fset = Abs_fset of 'a set;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

type 'a cfg_ext =
  Cfg_ext of
    (cfg_node * (edge_action * cfg_node)) set *
      (cfg_node * (call_action * (cfg_node * cfg_node))) set * cfg_node *
      (cfg_node * bexp) set * 'a;;

type ('a, 'b, 'c, 'd) state_ext =
  State_ext of
    'a set * (('a, 'b) sum, ('a list)) fmap * 'a set * (('a, 'b) sum -> 'c) *
      'd;;

type ('a, 'b, 'c) strategy_tree = Answer of 'c |
  QueryL of 'a * ('c -> ('a, 'b, 'c) strategy_tree) |
  QueryG of 'b * ('c -> ('a, 'b, 'c) strategy_tree) |
  Side of 'b * 'c * ('a, 'b, 'c) strategy_tree;;

type source_location = LocalVar of string | GlobalVar;;

type special_desc = SD_Nondet_Int | SD_Min | SD_Max;;

type analysis_event = Check_Event of bexp;;

type ('a, 'b, 'c) dg_spec_ext =
  Dg_spec_ext of
    ('a -> 'b -> 'b * 'a) * (string -> aexp -> 'a -> 'b -> 'b * 'a) *
      (special_call -> string -> 'a -> 'b -> 'b * 'a) *
      (bexp -> bool -> 'a -> 'b -> 'b * 'a) * (string -> 'a -> 'b -> 'b * 'a) *
      (aexp option -> string -> 'a -> 'b -> 'b * 'a) *
      (string list -> aexp list -> 'a -> 'b -> 'b * 'a) *
      (analysis_event -> 'a -> 'b -> 'b * 'a) * ('a -> 'a -> 'b -> 'b * 'a) *
      (string option -> 'a -> 'b -> 'b * 'a -> 'b * 'a) * 'c;;

type ('a, 'b) state_exta = State_exta of 'a set * 'b;;

type ('a, 'b, 'c, 'd) ug_state_ext =
  Ug_state_ext of ('b -> ('a, 'c) fmap) * 'd;;

type 'a imp_prog_ext =
  Imp_prog_ext of (string * unit proc_decl_ext) list * string list * 'a;;

type ('a, 'b) numeric_ops_ext =
  Numeric_ops_ext of
    (aexp -> (string -> 'a) -> 'a) *
      ((string -> bool) ->
        bexp -> bool -> 'a resolved_st_q -> 'a resolved_st_q) *
      'a * 'b;;

type ('a, 'b, 'c, 'd) func_state =
  Q of ('a * ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext)))
  | I of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                 ('a, 'b, 'c, 'd) ug_state_ext))
  | R of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                 ('a, 'b, 'c, 'd) ug_state_ext))
  | E of ('a * (('a, 'b, 'c) strategy_tree *
                 (('b -> 'c) *
                   (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext))));;

type ('a, 'b, 'c) effectful_st_transfer_ext =
  Effectful_st_transfer_ext of
    (cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string -> aexp -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (special_call -> string -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (bexp -> bool -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string list ->
        aexp list -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (cfg_node -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string option ->
        cfg_node -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      'c;;

let rec id x = (fun xa -> xa) x;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec comp f g = (fun x -> f (g x));;

let rec nat x = comp nat_of_integer integer_of_int x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec fold f x1 s = match f, x1, s with f, [], s -> s
               | f, x :: xs, s -> fold f xs (f x s);;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec find uu x1 = match uu, x1 with uu, [] -> None
               | p, x :: xs -> (if p x then Some x else find p xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec image f (Set xs) = Set (map f xs);;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if HOL.eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> HOL.eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A x xa1 = match x, xa1 with x, Set xs -> Set (inserta _A x xs)
                    | x, Coset xs -> Coset (removeAll _A x xs);;

let rec member _A x xa1 = match x, xa1 with x, Set xs -> membera _A xs x
                    | x, Coset xs -> not (membera _A xs x);;

let rec remove _A
  x xa1 = match x, xa1 with x, Set xs -> Set (removeAll _A x xs)
    | x, Coset xs -> Coset (inserta _A x xs);;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if HOL.eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fset (Abs_fset x) = x;;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fun_upd _A f a b = (fun x -> (if HOL.eq _A x a then b else f x));;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec c (State_ext (c, infl, stabl, sigma, more)) = c;;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec lookup_resolved_st_q _A (Abs_resolved_st x) = lookup_resolved_st _A x;;

let rec location_of
  gs x = (if gs x then Global_Location x else Local_Location x);;

let rec fun_of_resolved_st_q_for _A
  gs s x = lookup_resolved_st_q _A s (location_of gs x);;

let rec inv_conservative r a1 a2 = (a1, a2);;

let rec normalize_ivl
  v = (let Ivl (l, u) = v in
        (if less_eq_eint l u &&
              (not (equal_eint l PlusInf) && not (equal_eint u MinInf))
          then v else bot_ivla));;

let rec mk_ivl l u = normalize_ivl (Ivl (l, u));;

let rec meet_ivl_norm
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    mk_ivl (if less_eq_eint l2 l1 then l1 else l2)
      (if less_eq_eint u1 u2 then u1 else u2);;

let rec remove_resolved_key
  loc x1 = match loc, x1 with loc, [] -> []
    | loca, (loc, a) :: ps ->
        (if equal_locationa loca loc then remove_resolved_key loca ps
          else (loc, a) :: remove_resolved_key loca ps);;

let rec update_resolved_st _A
  (dl, (dg, ps)) loc a = (dl, (dg, (loc, a) :: remove_resolved_key loc ps));;

let rec update_resolved_st_q _A
  (Abs_resolved_st xb) xa x = Abs_resolved_st (update_resolved_st _A xb xa x);;

let rec times_int
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec ivl_times_core
  uu uv = match uu, uv with
    Ivl (Fin l1, Fin u1), Ivl (Fin l2, Fin u2) ->
      Ivl (Fin (min ord_int (times_int l1 l2)
                 (min ord_int (times_int l1 u2)
                   (min ord_int (times_int u1 l2) (times_int u1 u2)))),
            Fin (max ord_int (times_int l1 l2)
                  (max ord_int (times_int l1 u2)
                    (max ord_int (times_int u1 l2) (times_int u1 u2)))))
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

let rec minus_int
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec minus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (minus_int n m)
    | Fin uu, MinInf -> PlusInf
    | Fin uv, PlusInf -> MinInf
    | MinInf, MinInf -> MinInf
    | MinInf, Fin uw -> MinInf
    | MinInf, PlusInf -> MinInf
    | PlusInf, MinInf -> PlusInf
    | PlusInf, Fin ux -> PlusInf
    | PlusInf, PlusInf -> PlusInf;;

let rec minus_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    (let (Ivl (a, b), Ivl (c, d)) =
       (normalize_ivl (Ivl (l1, u1)), normalize_ivl (Ivl (l2, u2))) in
      normalize_ivl (Ivl (minus_eint a d, minus_eint b c)));;

let rec plus_int
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

let rec plus_eint x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (plus_int n m)
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

let rec aval_ivl
  x0 sigma = match x0, sigma with N n, sigma -> Ivl (Fin n, Fin n)
    | V x, sigma -> sigma x
    | Plus (a, b), sigma -> plus_ivl (aval_ivl a sigma) (aval_ivl b sigma)
    | Minus (a, b), sigma -> minus_ivl (aval_ivl a sigma) (aval_ivl b sigma)
    | Times (a, b), sigma -> times_ivl (aval_ivl a sigma) (aval_ivl b sigma);;

let rec afilter_ivl_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q bot_ivl s (location_of gs x)
        (meet_ivl_norm a (fun_of_resolved_st_q_for bot_ivl gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, N v, a, s -> s;;

let rec meet_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l2 l1 then l1 else l2),
          (if less_eq_eint u1 u2 then u1 else u2));;

let rec inf_ivl x = meet_ivl x;;

let one_int : int = Int_of_integer (Z.of_int 1);;

let rec inv_less_ivl
  x0 x1 x2 = match x0, x1, x2 with
    true, Ivl (l1, u1), Ivl (l2, u2) ->
      (inf_ivl (Ivl (l1, u1)) (Ivl (MinInf, minus_eint u2 (Fin one_int))),
        inf_ivl (Ivl (l2, u2)) (Ivl (plus_eint l1 (Fin one_int), PlusInf)))
    | false, Ivl (l1, u1), Ivl (l2, u2) ->
        (inf_ivl (Ivl (l1, u1)) (Ivl (l2, PlusInf)),
          inf_ivl (Ivl (l2, u2)) (Ivl (MinInf, u1)));;

let rec inv_eq_ivl
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (meet_ivl a1 a2, meet_ivl a1 a2)
    | false, a1, a2 -> (a1, a2);;

let rec bfilter_ivl_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
           (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
         in
        afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_ivl_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_ivl_st gs b1 true (bfilter_ivl_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_ivl
          (bfilter_ivl_st gs b1 false s) (bfilter_ivl_st gs b2 false s)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_ivl
          (bfilter_ivl_st gs b1 true s) (bfilter_ivl_st gs b2 true s)
    | gs, Or (b1, b2), false, s ->
        bfilter_ivl_st gs b1 false (bfilter_ivl_st gs b2 false s)
    | gs, Eqa (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Bc v, uv, s -> s;;

let ivl_ops : (ivl, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_ivl, bfilter_ivl_st, ivl_top, ());;

let rec calls (Cfg_ext (intra, calls, cfg_entry, checks, more)) = calls;;

let rec intra (Cfg_ext (intra, calls, cfg_entry, checks, more)) = intra;;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filtera (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (HOL.eq _A aa a));;

let rec the (Some x2) = x2;;

let ret_var : string = "#ret";;

let rec cfg_entry
  (Cfg_ext (intra, calls, cfg_entry, checks, more)) = cfg_entry;;

let rec cfg_exit
  g = (match cfg_entry g with Statement a -> Statement a
        | FunctionEntry a -> FunctionResult a
        | FunctionResult a -> FunctionResult a);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec apsnd f (x, y) = (x, f y);;

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

let zero_int : int = Int_of_integer Z.zero;;

let rec sign_of_int
  n = (if less_int n zero_int then SNeg
        else (if equal_inta n zero_int then SZero else SPos));;

let rec aval_sign
  x0 sigma = match x0, sigma with N n, sigma -> sign_of_int n
    | V x, sigma -> sigma x
    | Plus (a, b), sigma -> plus_sign (aval_sign a sigma) (aval_sign b sigma)
    | Minus (a, b), sigma -> minus_sign (aval_sign a sigma) (aval_sign b sigma)
    | Times (a, b), sigma ->
        times_sign (aval_sign a sigma) (aval_sign b sigma);;

let rec meet_sign x0 uu = match x0, uu with SBot, uu -> SBot
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

let rec afilter_sign_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q bot_sign s (location_of gs x)
        (meet_sign a (fun_of_resolved_st_q_for bot_sign gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, N v, a, s -> s;;

let rec inv_less_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 ->
      (let a1a = (if sign_le a2 SNonPos then meet_sign a1 SNeg else a1) in
       let a = (if sign_le a1 SNonNeg then meet_sign a2 SPos else a2) in
        (a1a, a))
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a2 SPos then meet_sign a1 SPos
             else (if sign_le a2 SNonNeg then meet_sign a1 SNonNeg else a1))
           in
         let a =
           (if sign_le a1 SNeg then meet_sign a2 SNeg
             else (if sign_le a1 SNonPos then meet_sign a2 SNonPos else a2))
           in
          (a1a, a));;

let rec inv_eq_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (meet_sign a1 a2, meet_sign a1 a2)
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a2 SZero && sign_le a1 SNonNeg
                    then meet_sign a1 SPos
                    else (if sign_le a2 SZero && sign_le a1 SNonPos
                           then meet_sign a1 SNeg else a1)))
           in
         let a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a1 SZero && sign_le a2 SNonNeg
                    then meet_sign a2 SPos
                    else (if sign_le a1 SZero && sign_le a2 SNonPos
                           then meet_sign a2 SNeg else a2)))
           in
          (a1a, a));;

let rec bfilter_sign_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_sign res
           (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
           (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
         in
        afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_sign_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_sign_st gs b1 true (bfilter_sign_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_sign
          (bfilter_sign_st gs b1 false s) (bfilter_sign_st gs b2 false s)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_sign
          (bfilter_sign_st gs b1 true s) (bfilter_sign_st gs b2 true s)
    | gs, Or (b1, b2), false, s ->
        bfilter_sign_st gs b1 false (bfilter_sign_st gs b2 false s)
    | gs, Eqa (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_sign res
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Bc v, uv, s -> s;;

let sign_ops : (sign, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_sign, bfilter_sign_st, STop, ());;

let rec infl (State_ext (c, infl, stabl, sigma, more)) = infl;;

let rec length_tailrec x0 n = match x0, n with [], n -> n
                         | x :: xs, n -> length_tailrec xs (suc n);;

let rec stabl (State_ext (c, infl, stabl, sigma, more)) = stabl;;

let rec no_return = function Seq (c1, c2) -> no_return c1 && no_return c2
                    | If (uu, c1, c2) -> no_return c1 && no_return c2
                    | While (uv, c) -> no_return c
                    | Return uw -> false
                    | SKIP -> true
                    | Assign (v, va) -> true
                    | Check v -> true
                    | Call (v, va, vb) -> true
                    | Restore -> true
                    | Unwind -> true;;

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

let rec fmlookup_default _A
  m d x = (match fmlookup _A m x with None -> d | Some v -> v);;

let rec fminsert _A
  infl x y = fmupd _A x (y :: fmlookup_default _A infl [] x) infl;;

let abort_empty_set _ = failwith "List.abort_empty_set";;

let rec sup_set _A
  x0 a = match x0, a with Set xs, a -> fold (insert _A) xs a
    | Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs);;

let bot_set : 'a set = Set [];;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec aexp_vnames
  = function N uu -> bot_set
    | V x -> insert equal_literal x bot_set
    | Plus (a, b) -> sup_set equal_literal (aexp_vnames a) (aexp_vnames b)
    | Minus (a, b) -> sup_set equal_literal (aexp_vnames a) (aexp_vnames b)
    | Times (a, b) -> sup_set equal_literal (aexp_vnames a) (aexp_vnames b);;

let rec bexp_vnames
  = function Bc uu -> bot_set
    | Not b -> bexp_vnames b
    | And (b1, b2) -> sup_set equal_literal (bexp_vnames b1) (bexp_vnames b2)
    | Or (b1, b2) -> sup_set equal_literal (bexp_vnames b1) (bexp_vnames b2)
    | Less (a, b) -> sup_set equal_literal (aexp_vnames a) (aexp_vnames b)
    | Eqa (a, b) -> sup_set equal_literal (aexp_vnames a) (aexp_vnames b);;

let rec com_vnames
  = function SKIP -> bot_set
    | Assign (x, a) -> insert equal_literal x (aexp_vnames a)
    | Check c -> bexp_vnames c
    | Seq (c1, c2) -> sup_set equal_literal (com_vnames c1) (com_vnames c2)
    | If (b, c1, c2) ->
        sup_set equal_literal
          (sup_set equal_literal (bexp_vnames b) (com_vnames c1))
          (com_vnames c2)
    | While (b, c) -> sup_set equal_literal (bexp_vnames b) (com_vnames c)
    | Call (dst, uu, actuals) ->
        sup_set equal_literal
          (match dst with None -> bot_set
            | Some x -> insert equal_literal x bot_set)
          (sup_seta equal_literal (Set (map aexp_vnames actuals)))
    | Return None -> bot_set
    | Return (Some a) -> aexp_vnames a
    | Restore -> bot_set
    | Unwind -> bot_set;;

let rec source_com = function SKIP -> true
                     | Assign (x, a) -> true
                     | Check c -> true
                     | Seq (c1, c2) -> source_com c1 && source_com c2
                     | If (b, c1, c2) -> source_com c1 && source_com c2
                     | While (b, c) -> source_com c
                     | Call (dst, p, actuals) -> true
                     | Return e -> true
                     | Restore -> false
                     | Unwind -> false;;

let cinit_ivl_st : ivl resolved_st_q
  = Abs_resolved_st
      (Ivl (MinInf, PlusInf), (Ivl (Fin zero_int, Fin zero_int), []));;

let rec snd (x1, x2) = x2;;

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

let rec sup_fin _A = function Set [] -> abort_empty_set (sup_fin _A)
                     | Set (x :: xs) -> fold (sup _A.sup_semilattice_sup) xs x;;

let rec sup_fset _A s = sup_fin _A (fset s);;

let rec aexp_mentions_where
  p x1 = match p, x1 with p, N uu -> false
    | p, V x -> p x
    | p, Plus (a, b) -> aexp_mentions_where p a || aexp_mentions_where p b
    | p, Minus (a, b) -> aexp_mentions_where p a || aexp_mentions_where p b
    | p, Times (a, b) -> aexp_mentions_where p a || aexp_mentions_where p b;;

let rec aexp_mentions x = aexp_mentions_where (fun a -> ((x : string) = a));;

let rec source_aexp a = not (aexp_mentions ret_var a);;

let rec bexp_mentions_where
  p x1 = match p, x1 with p, Bc uu -> false
    | p, Not b -> bexp_mentions_where p b
    | p, And (b1, b2) -> bexp_mentions_where p b1 || bexp_mentions_where p b2
    | p, Or (b1, b2) -> bexp_mentions_where p b1 || bexp_mentions_where p b2
    | p, Less (a, b) -> aexp_mentions_where p a || aexp_mentions_where p b
    | p, Eqa (a, b) -> aexp_mentions_where p a || aexp_mentions_where p b;;

let rec bexp_mentions x = bexp_mentions_where (fun a -> ((x : string) = a));;

let rec source_bexp b = not (bexp_mentions ret_var b);;

let rec ivl_min
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (min ord_eint l1 l2, min ord_eint u1 u2));;

let rec ivl_max
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (max ord_eint l1 l2, max ord_eint u1 u2));;

let rec n_bfilter _A
  (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_bfilter;;

let rec generic_branch_st_for _A
  ops source_global b pol s = n_bfilter _A ops source_global b pol s;;

let rec branch_ivl_st_for x = generic_branch_st_for bot_ivl ivl_ops x;;

let rec ivl_tf_st_for
  source_global x1 s = match source_global, x1, s with
    source_global, EA_Nop, s -> s
    | source_global, EA_Assign (x, a), s ->
        update_resolved_st_q bot_ivl s (location_of source_global x)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
    | source_global, EA_Special (sc, x), s ->
        update_resolved_st_q bot_ivl s (location_of source_global x)
          (match sc with Nondet_Int -> ivl_top
            | Min (a, b) ->
              ivl_min
                (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl source_global s))
            | Max (a, b) ->
              ivl_max
                (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl source_global s)))
    | source_global, EA_Assume b, s -> branch_ivl_st_for source_global b true s
    | source_global, EA_AssumeNot b, s ->
        branch_ivl_st_for source_global b false s
    | source_global, EA_Ret (None, p), s -> s
    | source_global, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_ivl s (location_of source_global ret_var)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
    | source_global, EA_Check cnd, s -> s;;

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

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec char_of_integer
  k = Chr (if Z.leq Z.zero k && Z.lt k (Z.of_int 256) then k
            else modulo_integer k (Z.of_int 256));;

let rec explode s = map char_of_integer (Str_Literal.asciis_of_literal s);;

let rec map_ltree
  h x1 = match h, x1 with h, Answer d -> Answer d
    | h, QueryL (y, f) -> QueryL (h y, (fun d -> map_ltree h (f d)))
    | h, QueryG (y, f) -> QueryG (y, (fun d -> map_ltree h (f d)))
    | h, Side (y, d, t) -> Side (y, d, map_ltree h t);;

let rec sigma (State_ext (c, infl, stabl, sigma, more)) = sigma;;

let rec c_update
  ca (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (ca c, infl, stabl, sigma, more);;

let rec proc_decl_of xs bdy = Proc_decl_ext (xs, bdy, ());;

let rec valid_formal gs x = not (gs x) && not ((x : string) = ret_var);;

let rec formals (Proc_decl_ext (formals, body, more)) = formals;;

let rec body (Proc_decl_ext (formals, body, more)) = body;;

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

let zero_nat : nat = Nat Z.zero;;

let rec size_list xs = length_tailrec xs zero_nat;;

let special_pname_nondet_int : string = "__voblint_nondet_int";;

let special_pname_min : string = "min";;

let special_pname_max : string = "max";;

let rec special_table
  p = (if ((p : string) = special_pname_nondet_int) then Some SD_Nondet_Int
        else (if ((p : string) = special_pname_min) then Some SD_Min
               else (if ((p : string) = special_pname_max) then Some SD_Max
                      else None)));;

let rec may_fallthrough
  = function SKIP -> true
    | Assign (uu, uv) -> true
    | Check uw -> true
    | Seq (c1, c2) -> may_fallthrough c1 && may_fallthrough c2
    | If (ux, c1, c2) -> may_fallthrough c1 || may_fallthrough c2
    | While (uy, uz) -> true
    | Call (va, vb, vc) -> true
    | Return vd -> false
    | Restore -> false
    | Unwind -> false;;

let rec may_return_value
  = function
    Seq (c1, c2) ->
      may_return_value c1 || may_fallthrough c1 && may_return_value c2
    | If (uu, c1, c2) -> may_return_value c1 || may_return_value c2
    | While (uv, c) -> may_return_value c
    | Return e -> not (is_none e)
    | SKIP -> false
    | Assign (v, va) -> false
    | Check v -> false
    | Call (v, va, vb) -> false
    | Restore -> false
    | Unwind -> false;;

let rec may_return_none
  = function
    Seq (c1, c2) ->
      may_return_none c1 || may_fallthrough c1 && may_return_none c2
    | If (uu, c1, c2) -> may_return_none c1 || may_return_none c2
    | While (uv, c) -> may_return_none c
    | Return e -> is_none e
    | SKIP -> false
    | Assign (v, va) -> false
    | Check v -> false
    | Call (v, va, vb) -> false
    | Restore -> false
    | Unwind -> false;;

let rec value_providing
  c = source_com c &&
        (not (may_fallthrough c) &&
          (not (may_return_none c) && may_return_value c));;

let rec wf_source_com
  pi x1 = match pi, x1 with pi, SKIP -> true
    | pi, Assign (x, a) -> not ((x : string) = ret_var) && source_aexp a
    | pi, Check c -> source_bexp c
    | pi, Seq (c1, c2) -> wf_source_com pi c1 && wf_source_com pi c2
    | pi, If (b, c1, c2) ->
        source_bexp b && (wf_source_com pi c1 && wf_source_com pi c2)
    | pi, While (b, c) -> source_bexp b && wf_source_com pi c
    | pi, Call (dst, p, actuals) ->
        (match special_table p
          with None ->
            (match pi p with None -> false
              | Some decl ->
                equal_nata (size_list actuals) (size_list (formals decl)) &&
                  (list_all source_aexp actuals &&
                    (match dst with None -> true
                      | Some x ->
                        not ((x : string) = ret_var) &&
                          value_providing (body decl))))
          | Some desc ->
            not (is_none (classify_special desc actuals)) &&
              (list_all source_aexp actuals &&
                (match dst with None -> false
                  | Some x -> not ((x : string) = ret_var))))
    | pi, Return e -> (match e with None -> true | Some a -> source_aexp a)
    | pi, Restore -> false
    | pi, Unwind -> false;;

let rec wf_proc_decl
  gs pi decl =
    distinct equal_literal (formals decl) &&
      (list_all (valid_formal gs) (formals decl) &&
        wf_source_com pi (body decl));;

let rec csize
  = function SKIP -> one_nat
    | Assign (x, a) -> one_nat
    | Check c -> one_nat
    | Seq (c1, c2) -> plus_nat (csize c1) (csize c2)
    | If (b, c1, c2) -> plus_nat (plus_nat one_nat (csize c1)) (csize c2)
    | While (b, c) -> plus_nat one_nat (csize c)
    | Call (dst, q, actuals) -> one_nat
    | Return e -> one_nat
    | Restore -> one_nat
    | Unwind -> one_nat;;

let cinit_sign_st : sign resolved_st_q = Abs_resolved_st (STop, (SZero, []));;

let prog_main_name : string = "main";;

let rec proc_rep
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = proc_rep;;

let rec prog_table p = map_of equal_literal (proc_rep p);;

let rec prog_main p = body (the (prog_table p prog_main_name));;

let rec bind_lift x0 f = match x0, f with Bot, f -> Bot
                    | Lifted a, f -> f a;;

let rec map_lift f x = bind_lift x (fun a -> Lifted (f a));;

let rec uminus_int k = Int_of_integer (Z.neg (integer_of_int k));;

let char_0x2D : char = Chr (Z.of_int 45);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec char_of_nat x = comp char_of_integer integer_of_nat x;;

let rec show_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else show_nat (divide_nat n (nat_of_integer (Z.of_int 10))) @
               [char_of_nat
                  (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                    (nat_of_integer (Z.of_int 48)))]);;

let rec show_int
  i = (if less_int i zero_int then [char_0x2D] @ show_nat (nat (uminus_int i))
        else show_nat (nat i));;

let rec dgs_combine_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_combine_assign;;

let rec dgs_combine_env
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_combine_env;;

let rec dgs_combine
  s dst dc de g = dgs_combine_assign s dst de g (dgs_combine_env s dc de g);;

let rec etf_st_special
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_special;;

let rec etf_st_branch
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_branch;;

let rec etf_st_assign
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_assign;;

let rec etf_st_nop
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_nop;;

let rec apply_etf_st
  etf x1 u = match etf, x1, u with etf, EA_Nop, u -> etf_st_nop etf u
    | etf, EA_Assign (x, a), u -> etf_st_assign etf x a u
    | etf, EA_Special (sc, x), u -> etf_st_special etf sc x u
    | etf, EA_Assume b, u -> etf_st_branch etf b true u
    | etf, EA_AssumeNot b, u -> etf_st_branch etf b false u
    | etf, EA_Ret (e, p), u ->
        (match e with None -> etf_st_nop etf u
          | Some a -> etf_st_assign etf ret_var a u)
    | etf, EA_Check cnd, u -> etf_st_nop etf u;;

let rec seqcomp_tree
  x0 k = match x0, k with Answer v, k -> k v
    | QueryL (u, f), k -> QueryL (u, (fun d -> seqcomp_tree (f d) k))
    | QueryG (g, f), k -> QueryG (g, (fun d -> seqcomp_tree (f d) k))
    | Side (g, v, t), k -> Side (g, v, seqcomp_tree t k);;

let rec dg_combine_tree _A _B
  comb dst cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun dc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun de ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Side ((), DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                               fst (comb dst (locals dc) (locals de)
                                     (globs g))),
                       Answer
                         (DG (snd (comb dst (locals dc) (locals de) (globs g)),
                               bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))));;

let rec dg_spec_combine_tree _A _B
  s dst cc ex = dg_combine_tree _A _B (dgs_combine s) dst cc ex;;

let rec map_gtree
  r x1 = match r, x1 with r, Answer d -> Answer d
    | r, QueryL (y, f) -> QueryL (y, (fun d -> map_gtree r (f d)))
    | r, QueryG (y, f) -> QueryG (r y, (fun d -> map_gtree r (f d)))
    | r, Side (y, d, t) -> Side (r y, d, map_gtree r t);;

let rec dg_cmb_of _A _B
  s route ctx ca cc ex =
    (let CallEdge (dst, _, _) = ca in
      map_gtree (fun _ -> ())
        (map_ltree (fun w -> (w, ctx))
          (dg_spec_combine_tree _A _B s dst cc ex)));;

let rec insort_key _B
  f x xa2 = match f, x, xa2 with f, x, [] -> [x]
    | f, x, y :: ys ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then x :: y :: ys else y :: insort_key _B f x ys);;

let rec sort_key _B f xs = foldr (insort_key _B f) xs [];;

let rec sorted_list_of_set (_A1, _A2)
  (Set xs) = sort_key _A2 (fun x -> x) (remdups _A1 xs);;

let rec cfg_calls_list
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod equal_call_action
             (equal_prod equal_cfg_node equal_cfg_node))),
          (linorder_prod linorder_cfg_node
            (linorder_prod linorder_call_action
              (linorder_prod linorder_cfg_node linorder_cfg_node))))
        (calls g);;

let rec return_call_action_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, k))) = x in
                  equal_cfg_nodea k v &&
                    (match ce with Statement _ -> false
                      | FunctionEntry _ -> true | FunctionResult _ -> false))
              then Some (let (c, (ca, (ce, _))) = x in
                          (c, (ca, (match ce with Statement _ -> ce
                                     | FunctionEntry a -> FunctionResult a
                                     | FunctionResult _ -> ce))))
              else None))
          (cfg_calls_list g);;

let rec side_rhs_fold_dg _A _D
  acc x1 = match acc, x1 with
    acc, [] ->
      Answer
        (DG (acc, bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
    | acc, t :: ts ->
        seqcomp_tree t
          (fun res ->
            side_rhs_fold_dg _A _D
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc (locals res))
              ts);;

let rec dgs_special
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_special;;

let rec dgs_return
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_return;;

let rec dgs_branch
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_branch;;

let rec dgs_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_assign;;

let rec dgs_event
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_event;;

let rec dgs_skip
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_skip;;

let rec dg_spec_step s x1 = match s, x1 with s, EA_Nop -> dgs_skip s
                       | s, EA_Assign (x, e) -> dgs_assign s x e
                       | s, EA_Special (sc, x) -> dgs_special s sc x
                       | s, EA_Assume b -> dgs_branch s b true
                       | s, EA_AssumeNot b -> dgs_branch s b false
                       | s, EA_Ret (e, p) -> dgs_return s e p
                       | s, EA_Check cnd -> dgs_event s (Check_Event cnd);;

let rec dg_edge_tree _A _B
  step u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun d ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Side ((), DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                           fst (step (locals d) (globs g))),
                   Answer
                     (DG (snd (step (locals d) (globs g)),
                           bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))));;

let rec apply_dg_spec _A _B s a u = dg_edge_tree _A _B (dg_spec_step s a) u;;

let rec side_cfg_T_eff_keyed_seed_dg _C _D
  pred_sel gkey route cmb extra g s bot0 s0d s0g =
    (fun (v, c) ->
      (let acc0 =
         (if equal_cfg_nodea v (cfg_entry g)
           then sup _C.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                  bot0 s0d
           else bot0)
         in
       let intra =
         map (fun (u, a) ->
               map_gtree (fun _ -> gkey c)
                 (map_ltree (fun w -> (w, c)) (apply_dg_spec _C _D s a u)))
           (pred_sel g v)
         in
       let comb =
         map (fun (cc, (ca, a)) -> cmb route c ca cc a)
           (return_call_action_list g v)
         in
       let t = side_rhs_fold_dg _C _D acc0 (intra @ comb @ extra route c v) in
        (if equal_cfg_nodea v (cfg_entry g)
          then Side (gkey c,
                      DG (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                           s0g),
                      t)
          else t)));;

let rec cfg_intra_list
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod equal_edge_action equal_cfg_node)),
          (linorder_prod linorder_cfg_node
            (linorder_prod linorder_edge_action linorder_cfg_node)))
        (intra g);;

let rec intra_predecessor_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, w)) = x in equal_cfg_nodea w v)
              then Some (let (u, (a, _)) = x in (u, a)) else None))
          (cfg_intra_list g);;

let rec entry_call_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, _))) = x in equal_cfg_nodea ce v)
              then Some (let (c, (ca, (_, _))) = x in (c, ca)) else None))
          (cfg_calls_list g);;

let rec dgs_enter
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_enter;;

let rec dg_extra_of _A _B
  s g route ctx v =
    map (fun (cl, CallEdge (_, fs, asa)) ->
          map_gtree (fun _ -> ())
            (map_ltree (fun w -> (w, ctx))
              (dg_edge_tree _A _B (dgs_enter s fs asa) cl)))
      (entry_call_list g v);;

let rec dg_gen_of _A _B
  s g bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_dg _A _B intra_predecessor_list (fun _ -> ())
      (fun _ _ _ _ -> ()) (dg_cmb_of _A _B s) (dg_extra_of _A _B s g) g s bot0
      s0d s0g;;

let rec branch_sign_st_for x = generic_branch_st_for bot_sign sign_ops x;;

let rec sign_tf_st_for
  source_global x1 s = match source_global, x1, s with
    source_global, EA_Nop, s -> s
    | source_global, EA_Assign (x, a), s ->
        update_resolved_st_q bot_sign s (location_of source_global x)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign source_global s))
    | source_global, EA_Special (sc, x), s ->
        update_resolved_st_q bot_sign s (location_of source_global x)
          (match sc with Nondet_Int -> STop
            | Min (a, b) ->
              sign_min
                (aval_sign a
                  (fun_of_resolved_st_q_for bot_sign source_global s))
                (aval_sign b
                  (fun_of_resolved_st_q_for bot_sign source_global s))
            | Max (a, b) ->
              sign_max
                (aval_sign a
                  (fun_of_resolved_st_q_for bot_sign source_global s))
                (aval_sign b
                  (fun_of_resolved_st_q_for bot_sign source_global s)))
    | source_global, EA_Assume b, s -> branch_sign_st_for source_global b true s
    | source_global, EA_AssumeNot b, s ->
        branch_sign_st_for source_global b false s
    | source_global, EA_Ret (None, p), s -> s
    | source_global, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_sign s (location_of source_global ret_var)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign source_global s))
    | source_global, EA_Check cnd, s -> s;;

let rec make
  proc_rep declared_global_vars =
    Imp_prog_ext (proc_rep, declared_global_vars, ());;

let rec mk_program
  ps m gv = make ((prog_main_name, proc_decl_of [] m) :: ps) gv;;

let rec prog_procs
  p = filtera (fun n -> not ((n : string) = prog_main_name))
        (map fst (proc_rep p));;

let rec declared_global_vars
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = declared_global_vars;;

let rec declared_global p x = membera equal_literal (declared_global_vars p) x;;

let rec storage_of
  p owner x = (if declared_global p x then GlobalVar else LocalVar owner);;

let rec call_formals pi q = (match pi q with None -> [] | Some a -> formals a);;

let rec compile
  pi p x2 k n = match pi, p, x2, k, n with
    pi, p, SKIP, k, n ->
      (suc n,
        (Statement n,
          (insert
             (equal_prod equal_cfg_node
               (equal_prod equal_edge_action equal_cfg_node))
             (Statement n, (EA_Nop, k)) bot_set,
            bot_set)))
    | pi, p, Assign (x, a), k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Assign (x, a), k)) bot_set,
              bot_set)))
    | pi, p, Check c, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Check c, k)) bot_set,
              bot_set)))
    | pi, p, Seq (c1, c2), k, n ->
        (let (_, (en1, (e1, k1))) =
           compile pi p c1 (Statement (plus_nat n (csize c1))) n in
         let (n2, (_, (e2, k2))) = compile pi p c2 k (plus_nat n (csize c1)) in
          (n2, (en1, (sup_set
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        e1 e2,
                       sup_set
                         (equal_prod equal_cfg_node
                           (equal_prod equal_call_action
                             (equal_prod equal_cfg_node equal_cfg_node)))
                         k1 k2))))
    | pi, p, If (b, c1, c2), k, n ->
        (let (n1, (en1, (e1, k1))) = compile pi p c1 k (suc n) in
         let (n2, (en2, (e2, k2))) = compile pi p c2 k n1 in
          (n2, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      (insert
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        (Statement n, (EA_Assume b, en1))
                        (insert
                          (equal_prod equal_cfg_node
                            (equal_prod equal_edge_action equal_cfg_node))
                          (Statement n, (EA_AssumeNot b, en2)) bot_set))
                      e1)
                    e2,
                   sup_set
                     (equal_prod equal_cfg_node
                       (equal_prod equal_call_action
                         (equal_prod equal_cfg_node equal_cfg_node)))
                     k1 k2))))
    | pi, p, While (b, c), k, n ->
        (let (n1, (en1, (e1, k1))) = compile pi p c (Statement n) (suc n) in
          (n1, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (insert
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      (Statement n, (EA_Assume b, en1))
                      (insert
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        (Statement n, (EA_AssumeNot b, k)) bot_set))
                    e1,
                   k1))))
    | pi, p, Call (dst, q, actuals), k, n ->
        (match special_table q
          with None ->
            (suc n,
              (Statement n,
                (bot_set,
                  insert
                    (equal_prod equal_cfg_node
                      (equal_prod equal_call_action
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
                    (insert
                       (equal_prod equal_cfg_node
                         (equal_prod equal_edge_action equal_cfg_node))
                       (Statement n, (EA_Nop, k)) bot_set,
                      bot_set)))
              | Some sc ->
                (match dst
                  with None ->
                    (suc n,
                      (Statement n,
                        (insert
                           (equal_prod equal_cfg_node
                             (equal_prod equal_edge_action equal_cfg_node))
                           (Statement n, (EA_Nop, k)) bot_set,
                          bot_set)))
                  | Some x ->
                    (suc n,
                      (Statement n,
                        (insert
                           (equal_prod equal_cfg_node
                             (equal_prod equal_edge_action equal_cfg_node))
                           (Statement n, (EA_Special (sc, x), k)) bot_set,
                          bot_set))))))
    | pi, p, Return e, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Ret (e, p), FunctionResult p)) bot_set,
              bot_set)))
    | pi, p, Restore, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)))
    | pi, p, Unwind, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)));;

let rec location_is_local = function Local_Location x -> true
                            | Global_Location x -> false;;

let rec location_is_global = function Local_Location x -> false
                             | Global_Location x -> true;;

let rec enter_frame_D_resolved _A
  top_val s =
    (let (_, (dg, ps)) = s in
      (top_val, (dg, filtera (fun p -> location_is_global (fst p)) ps)));;

let rec enter_frame_D_resolved_q _A
  xa (Abs_resolved_st x) = Abs_resolved_st (enter_frame_D_resolved _A xa x);;

let rec bind_formals_resolved _A
  gs xs avs s =
    fold (fun (x, a) t -> update_resolved_st _A t (location_of gs x) a)
      (zip xs avs) s;;

let rec bind_formals_resolved_q _A
  xc xb xa (Abs_resolved_st x) =
    Abs_resolved_st (bind_formals_resolved _A xc xb xa x);;

let rec n_aval _A (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_aval;;

let rec n_top _A (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_top;;

let rec generic_enter_st_for _A
  ops source_global xs es s =
    bind_formals_resolved_q _A source_global xs
      (map (fun e ->
             n_aval _A ops e (fun_of_resolved_st_q_for _A source_global s))
        es)
      (enter_frame_D_resolved_q _A (n_top _A ops) s);;

let rec ivl_enter_st_for x = generic_enter_st_for bot_ivl ivl_ops x;;

let rec infl_update
  infla (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infla infl, stabl, sigma, more);;

let rec location_vname = function Local_Location x1 -> x1
                         | Global_Location x2 -> x2;;

let rec resolved_st_is_bot _A
  gs s =
    (let (dl, (_, ps)) = s in
      is_bot _A dl ||
        list_ex
          (fun loc ->
            is_bot _A
              (lookup_resolved_st
                _A.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                s loc) &&
              equal_locationa (location_of gs (location_vname loc)) loc)
          (map fst ps));;

let rec stabl_update
  stabla (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infl, stabla stabl, sigma, more);;

let rec scope_vnames
  p owner =
    sup_set equal_literal
      (sup_set equal_literal (Set (declared_global_vars p))
        (insert equal_literal ret_var bot_set))
      (match prog_table p owner with None -> bot_set
        | Some decl ->
          sup_set equal_literal (Set (formals decl)) (com_vnames (body decl)));;

let rec reserved_ret_var gs = not (gs ret_var);;

let rec ea_check_cond (EA_Check x7) = x7;;

let rec is_EA_Check = function EA_Nop -> false
                      | EA_Assign (x21, x22) -> false
                      | EA_Special (x31, x32) -> false
                      | EA_Assume x4 -> false
                      | EA_AssumeNot x5 -> false
                      | EA_Ret (x61, x62) -> false
                      | EA_Check x7 -> true;;

let rec falls_through
  = function SKIP -> true
    | Assign (x, a) -> true
    | Check c -> true
    | Seq (c1, c2) -> falls_through c1 && falls_through c2
    | If (b, c1, c2) -> falls_through c1 || falls_through c2
    | While (b, c) -> true
    | Call (dst, q, actuals) -> true
    | Return e -> false
    | Restore -> true
    | Unwind -> true;;

let rec compile_proc
  pi p decl n =
    (let r = plus_nat n (csize (body decl)) in
     let (_, (ben, (e, k))) = compile pi p (body decl) (Statement r) n in
      (suc r,
        (insert
           (equal_prod equal_cfg_node
             (equal_prod equal_edge_action equal_cfg_node))
           (FunctionEntry p, (EA_Nop, ben))
           (if falls_through (body decl)
             then insert
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (Statement r, (EA_Ret (None, p), FunctionResult p)) e
             else e),
          k)));;

let rec compile_procs
  pi x1 n = match pi, x1, n with pi, [], n -> (n, (bot_set, bot_set))
    | pi, p :: ps, n ->
        (match pi p with None -> compile_procs pi ps n
          | Some decl ->
            (let (n1, (e, k)) = compile_proc pi p decl n in
             let (n2, (ea, ka)) = compile_procs pi ps n1 in
              (n2, (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      e ea,
                     sup_set
                       (equal_prod equal_cfg_node
                         (equal_prod equal_call_action
                           (equal_prod equal_cfg_node equal_cfg_node)))
                       k ka))));;

let rec compile_prog
  pi ps mnm main =
    (let (n1, (eprocs, kprocs)) = compile_procs pi ps zero_nat in
     let (_, (emain, kmain)) = compile_proc pi mnm (proc_decl_of [] main) n1 in
      Cfg_ext
        (sup_set
           (equal_prod equal_cfg_node
             (equal_prod equal_edge_action equal_cfg_node))
           eprocs emain,
          sup_set
            (equal_prod equal_cfg_node
              (equal_prod equal_call_action
                (equal_prod equal_cfg_node equal_cfg_node)))
            kprocs kmain,
          FunctionEntry mnm,
          image (fun (u, (a, _)) -> (u, ea_check_cond a))
            (filter (fun (_, (a, _)) -> is_EA_Check a)
              (sup_set
                (equal_prod equal_cfg_node
                  (equal_prod equal_edge_action equal_cfg_node))
                eprocs emain)),
          ()));;

let rec prog_cfg
  mnm p = compile_prog (prog_table p) (prog_procs p) mnm (prog_main p);;

let rec restrict_global_resolved _A
  s = (let (_, (dg, ps)) = s in
        (bot _A, (dg, filtera (fun p -> location_is_global (fst p)) ps)));;

let rec restrict_global_resolved_q _A
  (Abs_resolved_st x) = Abs_resolved_st (restrict_global_resolved _A x);;

let rec restrict_local_resolved _A
  s = (let (dl, (_, ps)) = s in
        (dl, (bot _A, filtera (fun p -> location_is_local (fst p)) ps)));;

let rec restrict_local_resolved_q _A
  (Abs_resolved_st x) = Abs_resolved_st (restrict_local_resolved _A x);;

let rec combine_resolved_st _A
  sc se =
    (let (dlc, (_, psc)) = sc in
     let (_, (dge, pse)) = se in
      (dlc, (dge, filtera (fun p -> location_is_local (fst p)) psc @
                    filtera (fun p -> location_is_global (fst p)) pse)));;

let rec combine_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (combine_resolved_st _A xa x);;

let rec unit_step_st _A
  f d g =
    (let res =
       f (combine_resolved_st_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot d g)
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res));;

let rec routed_extra _C
  seed_key gk0 route ctx v =
    (match v with Statement _ -> []
      | FunctionEntry _ ->
        [seqcomp_tree (QueryG (seed_key v ctx, (fun a -> Answer a)))
           (fun seed_state ->
             Answer
               (DG (globs seed_state,
                     bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))]
      | FunctionResult _ -> []);;

let rec sign_less_true_of_inv
  a b = equal_signa (fst (inv_less_sign false a b)) bot_signa ||
          equal_signa (snd (inv_less_sign false a b)) bot_signa;;

let rec sign_less_true x = sign_less_true_of_inv x;;

let rec sign_less_false_of_inv
  a b = equal_signa (fst (inv_less_sign true a b)) bot_signa ||
          equal_signa (snd (inv_less_sign true a b)) bot_signa;;

let rec sign_eq_true_of_less
  a b = sign_less_false_of_inv a b && sign_less_false_of_inv b a;;

let rec sign_eq_true x = sign_eq_true_of_less x;;

let rec sign_less_false x = sign_less_false_of_inv x;;

let rec sign_eq_false_of_meet a b = equal_signa (meet_sign a b) bot_signa;;

let rec sign_eq_false x = sign_eq_false_of_meet x;;

let rec sign_check_true
  x0 d = match x0, d with Bc v, d -> v
    | Not b, d -> sign_check_false b d
    | And (b1, b2), d -> sign_check_true b1 d && sign_check_true b2 d
    | Or (b1, b2), d -> sign_check_true b1 d || sign_check_true b2 d
    | Less (a, b), d -> sign_less_true (aval_sign a d) (aval_sign b d)
    | Eqa (a, b), d -> sign_eq_true (aval_sign a d) (aval_sign b d)
and sign_check_false
  x0 d = match x0, d with Bc v, d -> not v
    | Not b, d -> sign_check_true b d
    | And (b1, b2), d -> sign_check_false b1 d || sign_check_false b2 d
    | Or (b1, b2), d -> sign_check_false b1 d && sign_check_false b2 d
    | Less (a, b), d -> sign_less_false (aval_sign a d) (aval_sign b d)
    | Eqa (a, b), d -> sign_eq_false (aval_sign a d) (aval_sign b d);;

let rec sign_enter_st_for x = generic_enter_st_for bot_sign sign_ops x;;

let rec is_bottom_sign s = equal_signa s SBot;;

let rec fold_rhs_trees _A
  acc x1 = match acc, x1 with acc, [] -> Answer acc
    | acc, t :: ts ->
        seqcomp_tree t
          (fun res ->
            fold_rhs_trees _A
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc res)
              ts);;

let char_0x0A : char = Chr (Z.of_int 10);;

let source_nl : char list = [char_0x0A];;

let rec result_proc (FunctionResult x3) = x3;;

let char_0x20 : char = Chr (Z.of_int 32);;

let char_0x21 : char = Chr (Z.of_int 33);;

let char_0x22 : char = Chr (Z.of_int 34);;

let char_0x23 : char = Chr (Z.of_int 35);;

let char_0x26 : char = Chr (Z.of_int 38);;

let char_0x28 : char = Chr (Z.of_int 40);;

let char_0x29 : char = Chr (Z.of_int 41);;

let char_0x2A : char = Chr (Z.of_int 42);;

let char_0x2B : char = Chr (Z.of_int 43);;

let char_0x2C : char = Chr (Z.of_int 44);;

let char_0x2E : char = Chr (Z.of_int 46);;

let char_0x2F : char = Chr (Z.of_int 47);;

let char_0x30 : char = Chr (Z.of_int 48);;

let char_0x31 : char = Chr (Z.of_int 49);;

let char_0x32 : char = Chr (Z.of_int 50);;

let char_0x34 : char = Chr (Z.of_int 52);;

let char_0x35 : char = Chr (Z.of_int 53);;

let char_0x36 : char = Chr (Z.of_int 54);;

let char_0x37 : char = Chr (Z.of_int 55);;

let char_0x38 : char = Chr (Z.of_int 56);;

let char_0x3A : char = Chr (Z.of_int 58);;

let char_0x3B : char = Chr (Z.of_int 59);;

let char_0x3C : char = Chr (Z.of_int 60);;

let char_0x3D : char = Chr (Z.of_int 61);;

let char_0x3E : char = Chr (Z.of_int 62);;

let char_0x41 : char = Chr (Z.of_int 65);;

let char_0x42 : char = Chr (Z.of_int 66);;

let char_0x43 : char = Chr (Z.of_int 67);;

let char_0x44 : char = Chr (Z.of_int 68);;

let char_0x45 : char = Chr (Z.of_int 69);;

let char_0x46 : char = Chr (Z.of_int 70);;

let char_0x47 : char = Chr (Z.of_int 71);;

let char_0x48 : char = Chr (Z.of_int 72);;

let char_0x49 : char = Chr (Z.of_int 73);;

let char_0x4C : char = Chr (Z.of_int 76);;

let char_0x4D : char = Chr (Z.of_int 77);;

let char_0x4E : char = Chr (Z.of_int 78);;

let char_0x4F : char = Chr (Z.of_int 79);;

let char_0x50 : char = Chr (Z.of_int 80);;

let char_0x52 : char = Chr (Z.of_int 82);;

let char_0x53 : char = Chr (Z.of_int 83);;

let char_0x54 : char = Chr (Z.of_int 84);;

let char_0x55 : char = Chr (Z.of_int 85);;

let char_0x57 : char = Chr (Z.of_int 87);;

let char_0x58 : char = Chr (Z.of_int 88);;

let char_0x5A : char = Chr (Z.of_int 90);;

let char_0x5B : char = Chr (Z.of_int 91);;

let char_0x5C : char = Chr (Z.of_int 92);;

let char_0x5D : char = Chr (Z.of_int 93);;

let char_0x5F : char = Chr (Z.of_int 95);;

let char_0x61 : char = Chr (Z.of_int 97);;

let char_0x62 : char = Chr (Z.of_int 98);;

let char_0x63 : char = Chr (Z.of_int 99);;

let char_0x64 : char = Chr (Z.of_int 100);;

let char_0x65 : char = Chr (Z.of_int 101);;

let char_0x66 : char = Chr (Z.of_int 102);;

let char_0x67 : char = Chr (Z.of_int 103);;

let char_0x68 : char = Chr (Z.of_int 104);;

let char_0x69 : char = Chr (Z.of_int 105);;

let char_0x6B : char = Chr (Z.of_int 107);;

let char_0x6C : char = Chr (Z.of_int 108);;

let char_0x6D : char = Chr (Z.of_int 109);;

let char_0x6E : char = Chr (Z.of_int 110);;

let char_0x6F : char = Chr (Z.of_int 111);;

let char_0x70 : char = Chr (Z.of_int 112);;

let char_0x72 : char = Chr (Z.of_int 114);;

let char_0x73 : char = Chr (Z.of_int 115);;

let char_0x74 : char = Chr (Z.of_int 116);;

let char_0x75 : char = Chr (Z.of_int 117);;

let char_0x76 : char = Chr (Z.of_int 118);;

let char_0x77 : char = Chr (Z.of_int 119);;

let char_0x78 : char = Chr (Z.of_int 120);;

let char_0x79 : char = Chr (Z.of_int 121);;

let char_0x7A : char = Chr (Z.of_int 122);;

let char_0x7B : char = Chr (Z.of_int 123);;

let char_0x7C : char = Chr (Z.of_int 124);;

let char_0x7D : char = Chr (Z.of_int 125);;

let rec side_env_lift_st _A
  gs x1 glo = match gs, x1, glo with gs, Bot, glo -> Bot
    | gs, Lifted l, Bot ->
        Lifted
          (fun_of_resolved_st_q_for
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs l)
    | gs, Lifted l, Lifted g ->
        Lifted
          (fun x ->
            sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
              (fun_of_resolved_st_q_for
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs l x)
              (fun_of_resolved_st_q_for
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs g
                x));;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec less_eq_set _A
  a b = match a, b with Set xs, b -> list_all (fun x -> member _A x b) xs
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Coset [], Set [] -> false;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec entry_seed_list
  g v = map (fun (c, CallEdge (_, fs, asa)) -> (c, (fs, asa)))
          (entry_call_list g v);;

let rec point
  (State_ext (c, infl, stabl, sigma, State_exta (point, more))) = point;;

let rec rho (Ug_state_ext (rho, more)) = rho;;

let rec storage_global
  p owner x =
    (match storage_of p owner x with LocalVar _ -> false | GlobalVar -> true);;

let rec normalize_lift
  is_bot_pred a = (if is_bot_pred a then Bot else Lifted a);;

let rec transfer_lift
  is_bot_pred f x = bind_lift x (fun a -> normalize_lift is_bot_pred (f a));;

let rec combine_env_abs gs sc se = (fun x -> (if gs x then se x else sc x));;

let rec bot_fun _B x = bot _B;;

let rec assemble_env_abs _A
  gs x1 g = match gs, x1, g with gs, Bot, g -> Bot
    | gs, Lifted d, g ->
        Lifted
          (combine_env_abs gs d
            (match g
              with Bot ->
                bot_fun _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              | Lifted g0 -> g0));;

let rec sigma_update
  sigmaa (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infl, stabl, sigmaa sigma, more);;

let rec sup_over_origins _A _C
  state g =
    sup_fset _C.semilattice_sup_bounded_semilattice_sup_bot
      (fimage
        (fmlookup_default _A (rho state g)
          (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
        (fmdom (rho state g)));;

let rec append_last
  suffix x1 = match suffix, x1 with suffix, [] -> []
    | suffix, [s] -> [s @ suffix]
    | suffix, s :: v :: va -> s :: append_last suffix (v :: va);;

let rec join_source
  sep x1 = match sep, x1 with sep, [] -> []
    | sep, [s] -> s
    | sep, s :: v :: va -> s @ sep @ join_source sep (v :: va);;

let rec transfer_lift2
  is_bot_pred f x y =
    bind_lift x
      (fun a -> bind_lift y (fun b -> normalize_lift is_bot_pred (f a b)));;

let rec resolved_st_is_bot_for _A
  globals gs s =
    list_ex
      (fun x ->
        is_bot _A
          (lookup_resolved_st
            _A.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
            s (location_of gs x)))
      globals ||
      resolved_st_is_bot _A gs s;;

let rec formals_context pars d = map d pars;;

let rec classify_checks
  g env classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      (u, (ea_check_cond a,
                            classify (ea_check_cond a) (env u))))
          else None))
      (cfg_intra_list g);;

let rec destab_opt _A _B
  x i s c =
    destab_iter_opt _A _B (fmlookup_default (equal_sum _A _B) i [] x)
      (fmdrop (equal_sum _A _B) x i) s c
and destab_iter_opt _A _B
  x0 i s c = match x0, i, s, c with [], i, s, c -> (i, s)
    | y :: ys, i, s, c ->
        (let (ia, sa) =
           (if member _A y c then (i, remove _A y s)
             else destab_opt _A _B (Inl y) i (remove _A y s) c)
           in
          destab_iter_opt _A _B ys ia sa c);;

let rec fun_of_dg_st_gen floc fglob d = DG (floc (locals d), fglob (globs d));;

let rec combine_assign_resolved _A
  gs dst v s =
    (match dst with None -> s
      | Some x -> update_resolved_st _A s (location_of gs x) v);;

let rec fun_of_exec_dg_st_for _A gs = fun_of_resolved_st_q_for _A gs;;

let rec rho_update
  rhoa (Ug_state_ext (rho, more)) = Ug_state_ext (rhoa rho, more);;

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
      (if HOL.eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec warrow _A
  a b = (if less_eq
              _A.widening_warrowing.order_widening.preorder_order.ord_preorder b
              a
          then narrow _A.narrowing_warrowing a b
          else widen _A.widening_warrowing a b);;

let rec point_update
  pointa (State_ext (c, infl, stabl, sigma, State_exta (point, more))) =
    State_ext (c, infl, stabl, sigma, State_exta (pointa point, more));;

let rec tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_always_join_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_always_join_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if HOL.eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_always_join_Interp_solve_rec_c _A _B
                                    (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_always_join_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_always_join (_C1, _C2) _A _B (sigma state (Inr y))
                  x y da ug_state
                with (None, ug_statea) ->
                  tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
                      t (E (x, (ta, (sides_a_c_ca,
                                      (sigma_update
 (fun _ -> fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
 (stabl_update (fun _ -> stabla) (infl_update (fun _ -> infla) state)),
ug_statea)))))))));;

let rec init_state (_C1, _C2)
  = State_ext
      (bot_set, fmempty, bot_set,
        (fun _ -> bot _C1.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
        State_exta (bot_set, ()));;

let rec init_basic_ug_state _C = Ug_state_ext ((fun _ -> fmempty), ());;

let rec tD_side_always_join_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
               (I (x, (c_update
                         (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                         (init_state (_C2, _C3)),
                        init_basic_ug_state
                          _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_always_join_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_always_join_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_always_join_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec combine_assign_resolved_q _A
  xc xb xa (Abs_resolved_st x) =
    Abs_resolved_st (combine_assign_resolved _A xc xb xa x);;

let rec unit_combine_step_st_assign_for _A
  gs dst de g merged =
    (let res =
       combine_assign_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs dst
         (lookup_resolved_st_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de
           (location_of gs ret_var))
         (sup_resolved_st_qa _A (fst merged) (snd merged))
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res));;

let rec unit_combine_step_st_env _A
  dc de g =
    (let m =
       combine_resolved_st_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot dc g
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot m,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot m));;

let rec unit_dg_spec_st_for _A
  gs tf_st enter_st =
    Dg_spec_ext
      (unit_step_st _A (tf_st EA_Nop),
        (fun x e -> unit_step_st _A (tf_st (EA_Assign (x, e)))),
        (fun sc x -> unit_step_st _A (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_step_st _A
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun _ -> unit_step_st _A (tf_st EA_Nop)),
        (fun e p -> unit_step_st _A (tf_st (EA_Ret (e, p)))),
        (fun xs es -> unit_step_st _A (enter_st xs es)),
        (fun (Check_Event bc) -> unit_step_st _A (tf_st (EA_Check bc))),
        unit_combine_step_st_env _A, unit_combine_step_st_assign_for _A gs,
        ());;

let rec analyse_sign_eqs_for
  gs p =
    dg_gen_of
      (bounded_semilattice_sup_bot_resolved_st_q
        bounded_semilattice_sup_bot_sign)
      (bounded_semilattice_sup_bot_resolved_st_q
        bounded_semilattice_sup_bot_sign)
      (unit_dg_spec_st_for bounded_semilattice_sup_bot_sign gs
        (sign_tf_st_for gs) (sign_enter_st_for gs))
      (prog_cfg prog_main_name p) (bot_resolved_st_qa bot_sign) cinit_sign_st
      cinit_sign_st;;

let rec analyse_sign_for
  gs p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_unit
      ((equal_dg_state
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)))
      (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ());;

let rec sign_classify_check
  c d = (if sign_check_true c d then Check_Proved
          else (if sign_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec analyse_sign_report_for
  gs p =
    (let sol = snd (analyse_sign_for gs p) in
      classify_checks (prog_cfg prog_main_name p)
        (fun v ->
          combine_env_abs gs
            (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
            (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ())))))
        sign_classify_check);;

let rec analyse_sign_report p = analyse_sign_report_for (declared_global p) p;;

let rec scope_vnames_list
  p owner =
    sorted_list_of_set (equal_literal, linorder_literal)
      (scope_vnames p owner);;

let rec source_indent
  n = (if equal_nata n zero_nat then []
        else [char_0x20; char_0x20] @ source_indent (minus_nat n one_nat));;

let rec string_of_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else string_of_nat (divide_nat n (nat_of_integer (Z.of_int 10))) @
               [char_of_nat
                  (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                    (nat_of_integer (Z.of_int 48)))]);;

let rec string_of_int
  i = (if less_int i zero_int
        then [char_0x2D] @ string_of_nat (nat (uminus_int i))
        else string_of_nat (nat i));;

let rec string_of_aexp
  = function N n -> string_of_int n
    | V x -> explode x
    | Plus (a, b) -> string_of_aexp a @ [char_0x2B] @ string_of_aexp b
    | Minus (a, b) -> string_of_aexp a @ [char_0x2D] @ string_of_aexp b
    | Times (a, b) -> string_of_aexp a @ [char_0x2A] @ string_of_aexp b;;

let rec string_of_bexp
  = function Bc true -> [char_0x74; char_0x72; char_0x75; char_0x65]
    | Bc false -> [char_0x66; char_0x61; char_0x6C; char_0x73; char_0x65]
    | Not b -> [char_0x21; char_0x28] @ string_of_bexp b @ [char_0x29]
    | And (b1, b2) ->
        [char_0x28] @
          string_of_bexp b1 @
            [char_0x26; char_0x26] @ string_of_bexp b2 @ [char_0x29]
    | Or (b1, b2) ->
        [char_0x28] @
          string_of_bexp b1 @
            [char_0x7C; char_0x7C] @ string_of_bexp b2 @ [char_0x29]
    | Less (a1, a2) -> string_of_aexp a1 @ [char_0x3C] @ string_of_aexp a2
    | Eqa (a1, a2) ->
        string_of_aexp a1 @ [char_0x3D; char_0x3D] @ string_of_aexp a2;;

let rec string_of_com
  = function SKIP -> [char_0x73; char_0x6B; char_0x69; char_0x70]
    | Assign (x, e) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20] @ string_of_aexp e
    | Check c ->
        [char_0x5F; char_0x5F; char_0x76; char_0x6F; char_0x62; char_0x6C;
          char_0x69; char_0x6E; char_0x74; char_0x5F; char_0x63; char_0x68;
          char_0x65; char_0x63; char_0x6B; char_0x28] @
          string_of_bexp c @ [char_0x29]
    | Seq (c1, c2) ->
        string_of_com c1 @ [char_0x3B] @ source_nl @ string_of_com c2
    | If (b, c1, c2) ->
        [char_0x69; char_0x66; char_0x20; char_0x28] @
          string_of_bexp b @
            [char_0x29; char_0x20; char_0x7B; char_0x20] @
              string_of_com c1 @
                [char_0x20; char_0x7D; char_0x20; char_0x65; char_0x6C;
                  char_0x73; char_0x65; char_0x20; char_0x7B; char_0x20] @
                  string_of_com c2 @ [char_0x20; char_0x7D]
    | While (b, c) ->
        [char_0x77; char_0x68; char_0x69; char_0x6C; char_0x65; char_0x20;
          char_0x28] @
          string_of_bexp b @
            [char_0x29; char_0x20; char_0x7B; char_0x20] @
              string_of_com c @ [char_0x20; char_0x7D]
    | Call (dst, p, es) ->
        (match dst
          with None ->
            explode p @
              [char_0x28] @
                join_source [char_0x2C; char_0x20] (map string_of_aexp es) @
                  [char_0x29]
          | Some x ->
            explode x @
              [char_0x20; char_0x3A; char_0x3D; char_0x20] @
                explode p @
                  [char_0x28] @
                    join_source [char_0x2C; char_0x20] (map string_of_aexp es) @
                      [char_0x29])
    | Return (Some e) ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E;
          char_0x20] @
          string_of_aexp e
    | Return None ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E]
    | Restore ->
        [char_0x72; char_0x65; char_0x73; char_0x74; char_0x6F; char_0x72;
          char_0x65]
    | Unwind ->
        [char_0x3C; char_0x75; char_0x6E; char_0x77; char_0x69; char_0x6E;
          char_0x64; char_0x3E];;

let rec return_call_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, k))) = x in
                  equal_cfg_nodea k v &&
                    (match ce with Statement _ -> false
                      | FunctionEntry _ -> true | FunctionResult _ -> false))
              then Some (let (c, (ca, (ce, _))) = x in
                          (c, ((let CallEdge (dst, _, _) = ca in dst),
                                (match ce with Statement _ -> ce
                                  | FunctionEntry a -> FunctionResult a
                                  | FunctionResult _ -> ce))))
              else None))
          (cfg_calls_list g);;

let rec resolved_st_q_is_bot_for _A
  xb (Abs_resolved_st xa) =
    resolved_st_is_bot_for _A xb (membera equal_literal xb) xa;;

let rec etf_st_enter
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_enter;;

let rec etf_st_combine_collect
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_combine_collect;;

let rec etf_combine_collect_st
  etf dst cc ex = etf_st_combine_collect etf dst cc ex;;

let rec side_contribution_trees_st _B
  etf es ens cs =
    map (fun (u, a) -> apply_etf_st etf a u) es @
      map (fun (cl, (fs, asa)) -> etf_st_enter etf fs asa cl) ens @
        map (fun (cc, (dst, a)) -> etf_combine_collect_st etf dst cc a) cs;;

let rec make_side_rhs_tree_eff_st_buffered _B
  g etf bot0_st s0_st gseed v =
    (let acc0 =
       (if equal_cfg_nodea v (cfg_entry g)
         then Lifted (sup_resolved_st_qa _B bot0_st s0_st) else Bot)
       in
     let t =
       fold_rhs_trees
         (bounded_semilattice_sup_bot_lifted (semilattice_sup_resolved_st_q _B))
         acc0
         (side_contribution_trees_st _B etf (intra_predecessor_list g v)
           (entry_seed_list g v) (return_call_list g v))
       in
      seqcomp_tree t
        (fun res ->
          seqcomp_tree
            (Side (gseed,
                    map_lift
                      (restrict_global_resolved_q
                        _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                      res,
                    Answer bot_lifteda))
            (fun _ ->
              Answer
                (map_lift
                  (restrict_local_resolved_q
                    _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                  res))));;

let rec side_cfg_T_eff_st_buffered _B
  g etf bot0_st s0_st gseed =
    make_side_rhs_tree_eff_st_buffered _B g etf bot0_st s0_st gseed;;

let rec assemble_local_global _A
  x0 g = match x0, g with Bot, g -> Bot
    | Lifted su, Bot -> Lifted su
    | Lifted su, Lifted sg -> Lifted (sup _A.sup_semilattice_sup su sg);;

let rec unit_combine_env_contribution_st _A
  is_bot_pred cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun sc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun se ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Answer
                  (transfer_lift2 is_bot_pred
                    (combine_resolved_st_q
                      _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) sc
                      g)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) se
                      g)))));;

let rec combine_collect_resolved_for _A
  gs dst sc se =
    combine_assign_resolved _A gs dst
      (lookup_resolved_st _A se (location_of gs ret_var))
      (combine_resolved_st _A sc se);;

let rec combine_collect_resolved_for_q _A
  xc xb (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (combine_collect_resolved_for _A xc xb xa x);;

let rec unit_combine_contribution_st _A
  is_bot_pred gs dst cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun sc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun se ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Answer
                  (transfer_lift2 is_bot_pred
                    (combine_collect_resolved_for_q
                      _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs
                      dst)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) sc
                      g)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) se
                      g)))));;

let rec unit_edge_contribution_st _A
  is_bot_pred f u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun su ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Answer
              (transfer_lift is_bot_pred f
                (assemble_local_global (semilattice_sup_resolved_st_q _A) su
                  g))));;

let rec unit_etf_st_contribution_of_transfer _A
  is_bot_pred gs tf_st enter_st =
    Effectful_st_transfer_ext
      (unit_edge_contribution_st _A is_bot_pred (tf_st EA_Nop),
        (fun x e ->
          unit_edge_contribution_st _A is_bot_pred (tf_st (EA_Assign (x, e)))),
        (fun sc x ->
          unit_edge_contribution_st _A is_bot_pred
            (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_edge_contribution_st _A is_bot_pred
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun xs es ->
          unit_edge_contribution_st _A is_bot_pred (enter_st xs es)),
        unit_combine_env_contribution_st _A is_bot_pred,
        unit_combine_contribution_st _A is_bot_pred gs, ());;

let rec ivl_etf_st_contribution_for
  is_bot_pred gs =
    unit_etf_st_contribution_of_transfer bounded_semilattice_sup_bot_ivl
      is_bot_pred gs (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec ivl_exec_eqs
  is_bot_pred gs pi ps mnm main =
    side_cfg_T_eff_st_buffered bounded_semilattice_sup_bot_ivl
      (compile_prog pi ps mnm main) (ivl_etf_st_contribution_for is_bot_pred gs)
      (bot_resolved_st_qa bot_ivl) cinit_ivl_st ();;

let rec ivl_exec_raw
  is_bot_pred gs pi ps mnm main =
    snd (tD_side_always_join_Interp_solve equal_cfg_node equal_unit
          ((equal_lifted
             (equal_resolved_st_q
               (equal_ivl,
                 bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
            (bounded_semilattice_sup_bot_lifted
              (bounded_warrowing_resolved_st_q
                bounded_warrowing_ivl).bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              (bounded_warrowing_resolved_st_q bounded_warrowing_ivl)))
          (ivl_exec_eqs is_bot_pred gs pi ps mnm main)
          (cfg_exit (compile_prog pi ps mnm main)));;

let rec unit_combine_step_st_assign_for_lifted _A
  gs dst is_bot_pred de merged =
    (let joined =
       sup_lifteda (semilattice_sup_resolved_st_q _A) (fst merged) (snd merged)
       in
     let res =
       transfer_lift2 is_bot_pred
         (fun de0 ->
           combine_assign_resolved_q
             _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs dst
             (lookup_resolved_st_q
               _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de0
               (location_of gs ret_var)))
         de joined
       in
      (map_lift
         (restrict_global_resolved_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
         res,
        map_lift
          (restrict_local_resolved_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          res));;

let rec assemble_resolved_env _A
  x0 g = match x0, g with Bot, g -> Bot
    | Lifted d, g ->
        Lifted
          (combine_resolved_st_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot d
            (match g
              with Bot ->
                bot_resolved_st_qa
                  _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              | Lifted g0 -> g0));;

let rec unit_combine_step_st_env_lifted _A
  d g = (let m = assemble_resolved_env _A d g in
          (map_lift
             (restrict_global_resolved_q
               _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
             m,
            map_lift
              (restrict_local_resolved_q
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
              m));;

let rec unit_step_st_lifted _A
  is_bot_pred f d g =
    (let res = transfer_lift is_bot_pred f (assemble_resolved_env _A d g) in
      (map_lift
         (restrict_global_resolved_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
         res,
        map_lift
          (restrict_local_resolved_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          res));;

let rec unit_dg_spec_st_for_lifted _A
  gs is_bot_pred tf_st enter_st =
    Dg_spec_ext
      (unit_step_st_lifted _A is_bot_pred (tf_st EA_Nop),
        (fun x e ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Assign (x, e)))),
        (fun sc x ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_step_st_lifted _A is_bot_pred
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun _ -> unit_step_st_lifted _A is_bot_pred (tf_st EA_Nop)),
        (fun e p -> unit_step_st_lifted _A is_bot_pred (tf_st (EA_Ret (e, p)))),
        (fun xs es -> unit_step_st_lifted _A is_bot_pred (enter_st xs es)),
        (fun (Check_Event bc) ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Check bc))),
        (fun dc _ -> unit_combine_step_st_env_lifted _A dc),
        (fun dst de _ ->
          unit_combine_step_st_assign_for_lifted _A gs dst is_bot_pred de),
        ());;

let rec ectx_spec
  gs is_bot_pred =
    unit_dg_spec_st_for_lifted bounded_semilattice_sup_bot_ivl gs is_bot_pred
      (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec interval_less_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u1 l2);;

let rec interval_eq_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) ||
        equal_eint l1 u1 && (equal_eint l2 u2 && equal_eint l1 l2));;

let rec interval_less_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || less_eq_eint u2 l1);;

let rec interval_eq_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || (less_eint u1 l2 || less_eint u2 l1));;

let rec interval_check_true
  x0 d = match x0, d with Bc v, d -> v
    | Not b, d -> interval_check_false b d
    | And (b1, b2), d -> interval_check_true b1 d && interval_check_true b2 d
    | Or (b1, b2), d -> interval_check_true b1 d || interval_check_true b2 d
    | Less (a, b), d -> interval_less_true (aval_ivl a d) (aval_ivl b d)
    | Eqa (a, b), d -> interval_eq_true (aval_ivl a d) (aval_ivl b d)
and interval_check_false
  x0 d = match x0, d with Bc v, d -> not v
    | Not b, d -> interval_check_true b d
    | And (b1, b2), d -> interval_check_false b1 d || interval_check_false b2 d
    | Or (b1, b2), d -> interval_check_false b1 d && interval_check_false b2 d
    | Less (a, b), d -> interval_less_false (aval_ivl a d) (aval_ivl b d)
    | Eqa (a, b), d -> interval_eq_false (aval_ivl a d) (aval_ivl b d);;

let rec analyse_sign_env_for
  gs p =
    (let sol = snd (analyse_sign_for gs p) in
      (fun v ->
        combine_env_abs gs
          (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
          (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ()))))));;

let rec interval_classify_check
  c d = (if interval_check_true c d then Check_Proved
          else (if interval_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec interval_check_report
  gs mnm p =
    (let raw =
       ivl_exec_raw
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec update_global_per_origin (_A1, _A2) _B _C
  da orig g d state =
    (let statea =
       rho_update
         (fun _ -> fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
         state
       in
     let db = sup_over_origins _B _A2 statea g in
      (if HOL.eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec dg_edge_contribution_tree _A _B
  step u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun d ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Answer
              (DG (snd (step (locals d) (globs g)),
                    fst (step (locals d) (globs g))))));;

let rec routed_cmb_contribution _A
  s gk0 seed_key route ctx ca cc ex =
    (let CallEdge (dst, fs, asa) = ca in
      seqcomp_tree (QueryL ((cc, ctx), (fun a -> Answer a)))
        (fun caller_state ->
          seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
            (fun globals_state1 ->
              (let caller = locals caller_state in
               let globals1 = globs globals_state1 in
               let ctxa = route cc ctx caller ca in
               let eg = fst (dgs_enter s fs asa caller globals1) in
                seqcomp_tree
                  (Side (seed_key (FunctionEntry (result_proc ex)) ctxa,
                          DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                               snd (dgs_enter s fs asa caller globals1)),
                          Answer
                            (DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                                  bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))
                  (fun _ ->
                    seqcomp_tree (QueryL ((ex, ctxa), (fun a -> Answer a)))
                      (fun callee_state ->
                        seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
                          (fun globals_state2 ->
                            (let callee = locals callee_state in
                             let globals2 = globs globals_state2 in
                             let cg =
                               fst (dgs_combine s dst caller callee globals2) in
                              Answer
                                (DG (snd (dgs_combine s dst caller callee
   globals2),
                                      sup
_A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup eg
cg))))))))));;

let rec apply_dg_spec_contribution _A _B
  s a u = dg_edge_contribution_tree _A _B (dg_spec_step s a) u;;

let rec analyse_interval_report
  p = interval_check_report (declared_global p) prog_main_name p;;

let rec tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if HOL.eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_per_origin_Interp_solve_rec_c _A _B
                                    (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_per_origin_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_per_origin (_C1, _C2) _A _B (sigma state (Inr y))
                  x y da ug_state
                with (None, ug_statea) ->
                  tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
                      t (E (x, (ta, (sides_a_c_ca,
                                      (sigma_update
 (fun _ -> fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
 (stabl_update (fun _ -> stabla) (infl_update (fun _ -> infla) state)),
ug_statea)))))))));;

let rec tD_side_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
               (I (x, (c_update
                         (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                         (init_state (_C2, _C3)),
                        init_basic_ug_state
                          _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_per_origin_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_per_origin_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec ivl_exec_raw_per_origin
  is_bot_pred gs pi ps mnm main =
    snd (tD_side_per_origin_Interp_solve equal_cfg_node equal_unit
          ((equal_lifted
             (equal_resolved_st_q
               (equal_ivl,
                 bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
            (bounded_semilattice_sup_bot_lifted
              (bounded_warrowing_resolved_st_q
                bounded_warrowing_ivl).bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              (bounded_warrowing_resolved_st_q bounded_warrowing_ivl)))
          (ivl_exec_eqs is_bot_pred gs pi ps mnm main)
          (cfg_exit (compile_prog pi ps mnm main)));;

let rec side_cfg_T_eff_keyed_seed_dg_buffered _C _D
  pred_sel gkey route cmb_c extra g s bot0 s0d s0g =
    (fun (v, c) ->
      (let acc0 =
         (if equal_cfg_nodea v (cfg_entry g)
           then DG (sup _C.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                      bot0 s0d,
                     s0g)
           else DG (bot0,
                     bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
         in
       let intra =
         map (fun (u, a) ->
               map_gtree (fun _ -> gkey c)
                 (map_ltree (fun w -> (w, c))
                   (apply_dg_spec_contribution _C _D s a u)))
           (pred_sel g v)
         in
       let comb =
         map (fun (cc, (ca, a)) -> cmb_c route c ca cc a)
           (return_call_action_list g v)
         in
       let t =
         fold_rhs_trees (bounded_semilattice_sup_bot_dg_state _C _D) acc0
           (intra @ comb @ extra route c v)
         in
        seqcomp_tree t
          (fun res ->
            Side (gkey c,
                   DG (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                        globs res),
                   Answer
                     (DG (locals res,
                           bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))));;

let rec entry_state_entered
  gs is_bot_pred d ca =
    (let CallEdge (_, fs, asa) = ca in
      snd (dgs_enter (ectx_spec gs is_bot_pred) fs asa d Bot));;

let rec entry_state_route
  gs is_bot_pred d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (fun x ->
          lookup_resolved_st_q bot_ivl
            (match entry_state_entered gs is_bot_pred d ca
              with Bot -> bot_resolved_st_qa bot_ivl | Lifted d0 -> d0)
            (location_of gs x)));;

let rec entry_state_route_gen
  gs is_bot_pred u ctx d ca = entry_state_route gs is_bot_pred d ca;;

let rec entry_state_eqs
  gs is_bot_pred pi ps mnm main =
    side_cfg_T_eff_keyed_seed_dg_buffered
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      intra_predecessor_list (fun _ -> Global)
      (entry_state_route_gen gs is_bot_pred)
      (routed_cmb_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (ectx_spec gs is_bot_pred) Global (fun a b -> Seed (a, b)))
      (routed_extra
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (fun a b -> Seed (a, b)) Global)
      (compile_prog pi ps mnm main) (ectx_spec gs is_bot_pred) Bot
      (Lifted cinit_ivl_st)
      (Lifted (restrict_global_resolved_q bot_ivl cinit_ivl_st));;

let rec update_global_warrowing_apinis (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if HOL.eq _A1
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

let rec tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if HOL.eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_warrowing_apinis_Interp_solve_rec_c _A
                                    _B (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                  (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_warrowing_apinis (_C1, _C2, _C3) _A _B
                  (sigma state (Inr y)) x y da ug_state
                with (None, ug_statea) ->
                  tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                    (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                      (_C1, _C2, _C3) t
                      (E (x, (ta, (sides_a_c_ca,
                                    (sigma_update
                                       (fun _ ->
 fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
                                       (stabl_update (fun _ -> stabla)
 (infl_update (fun _ -> infla) state)),
                                      ug_statea)))))))));;

let rec tD_side_warrowing_apinis_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
               t (I (x, (c_update
                           (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                           (init_state (_C2, _C3)),
                          init_basic_ug_state
                            _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_warrowing_apinis_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_warrowing_apinis_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_warrowing_apinis_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec entry_state_sol
  gs is_bot_pred pi ps mnm main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (entry_state_eqs gs is_bot_pred pi ps mnm main)
      (cfg_exit (compile_prog pi ps mnm main), []);;

let rec analyse_sign_for_per_origin
  gs p =
    tD_side_per_origin_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_unit
      ((equal_dg_state
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)))
      (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ());;

let rec analyse_interval_td_raw
  is_bot_pred gs pi ps mnm main =
    snd (tD_side_warrowing_apinis_Interp_solve equal_cfg_node equal_unit
          ((equal_lifted
             (equal_resolved_st_q
               (equal_ivl,
                 bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
            (bounded_semilattice_sup_bot_lifted
              (bounded_warrowing_resolved_st_q
                bounded_warrowing_ivl).bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              (bounded_warrowing_resolved_st_q bounded_warrowing_ivl)))
          (ivl_exec_eqs is_bot_pred gs pi ps mnm main)
          (cfg_exit (compile_prog pi ps mnm main)));;

let rec interval_td_check_report
  gs mnm p =
    (let raw =
       analyse_interval_td_raw
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec pretty_source_lines_com
  n x1 = match n, x1 with
    n, SKIP -> [source_indent n @ [char_0x73; char_0x6B; char_0x69; char_0x70]]
    | n, Assign (x, e) ->
        [source_indent n @
           explode x @
             [char_0x20; char_0x3A; char_0x3D; char_0x20] @ string_of_aexp e]
    | n, Check c ->
        [source_indent n @
           [char_0x5F; char_0x5F; char_0x76; char_0x6F; char_0x62; char_0x6C;
             char_0x69; char_0x6E; char_0x74; char_0x5F; char_0x63; char_0x68;
             char_0x65; char_0x63; char_0x6B; char_0x28] @
             string_of_bexp c @ [char_0x29]]
    | n, Seq (c1, c2) ->
        append_last [char_0x3B] (pretty_source_lines_com n c1) @
          pretty_source_lines_com n c2
    | n, If (b, c1, c2) ->
        [source_indent n @
           [char_0x69; char_0x66; char_0x20; char_0x28] @
             string_of_bexp b @ [char_0x29; char_0x20; char_0x7B]] @
          pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
            c1 @
            [source_indent n @
               [char_0x7D; char_0x20; char_0x65; char_0x6C; char_0x73;
                 char_0x65; char_0x20; char_0x7B]] @
              pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
                c2 @
                [source_indent n @ [char_0x7D]]
    | n, While (b, c) ->
        [source_indent n @
           [char_0x77; char_0x68; char_0x69; char_0x6C; char_0x65; char_0x20;
             char_0x28] @
             string_of_bexp b @ [char_0x29; char_0x20; char_0x7B]] @
          pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2))) c @
            [source_indent n @ [char_0x7D]]
    | n, Call (dst, p, es) ->
        [source_indent n @ string_of_com (Call (dst, p, es))]
    | n, Return e -> [source_indent n @ string_of_com (Return e)]
    | n, Restore ->
        [source_indent n @
           [char_0x72; char_0x65; char_0x73; char_0x74; char_0x6F; char_0x72;
             char_0x65]]
    | n, Unwind ->
        [source_indent n @
           [char_0x3C; char_0x75; char_0x6E; char_0x77; char_0x69; char_0x6E;
             char_0x64; char_0x3E]];;

let rec classify_checks_with_state
  g env classify =
    map (fun (u, (c, r)) -> (u, (c, (r, env u))))
      (classify_checks g env classify);;

let rec analyse_interval_td_report
  p = interval_td_check_report (declared_global p) prog_main_name p;;

let rec analyse_interval_td_at
  is_bot_pred gs pi ps mnm main =
    (let raw = analyse_interval_td_raw is_bot_pred gs pi ps mnm main in
      (fun v ->
        side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
          (raw (Inr ()))));;

let rec analyse_sign_report_per_origin
  p = (let gs = declared_global p in
       let sol = snd (analyse_sign_for_per_origin gs p) in
        classify_checks (prog_cfg prog_main_name p)
          (fun v ->
            combine_env_abs gs
              (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
              (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ())))))
          sign_classify_check);;

let rec analyse_sign_report_for_with_state
  gs p =
    (let sol = snd (analyse_sign_for gs p) in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          combine_env_abs gs
            (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
            (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ())))))
        sign_classify_check);;

let rec analyse_sign_report_with_state
  p = analyse_sign_report_for_with_state (declared_global p) p;;

let rec pretty_source_lines_proc
  n p decl =
    (source_indent n @
      [char_0x76; char_0x6F; char_0x69; char_0x64; char_0x20] @
        explode p @
          [char_0x28] @
            join_source [char_0x2C; char_0x20] (map explode (formals decl)) @
              [char_0x29; char_0x20; char_0x7B]) ::
      pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
        (body decl) @
        [source_indent n @ [char_0x7D]];;

let rec pretty_string_of_program
  pi ps main globals =
    join_source source_nl
      ((if null globals then []
         else [[char_0x67; char_0x6C; char_0x6F; char_0x62; char_0x61;
                 char_0x6C; char_0x20] @
                 join_source [char_0x2C; char_0x20] (map explode globals) @
                   [char_0x3B]]) @
        maps (fun p ->
               (match pi p
                 with None ->
                   [[char_0x70; char_0x72; char_0x6F; char_0x63; char_0x65;
                      char_0x64; char_0x75; char_0x72; char_0x65; char_0x20] @
                      explode p @
                        [char_0x20; char_0x3C; char_0x6D; char_0x69; char_0x73;
                          char_0x73; char_0x69; char_0x6E; char_0x67;
                          char_0x3E]]
                 | Some a -> pretty_source_lines_proc zero_nat p a))
          ps @
          [[char_0x76; char_0x6F; char_0x69; char_0x64; char_0x20; char_0x6D;
             char_0x61; char_0x69; char_0x6E; char_0x28; char_0x29; char_0x20;
             char_0x7B]] @
            pretty_source_lines_com (nat_of_integer (Z.of_int 2)) main @
              [[char_0x7D]]);;

let rec entry_state_classify_at
  v cnd reachable_keys sg =
    (let ctxs =
       image snd (filter (fun (va, _) -> equal_cfg_nodea va v) reachable_keys)
       in
     let unlift =
       comp (fun a ->
              (match a with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
         sg
       in
      (if equal_set (equal_list equal_ivl) ctxs bot_set
        then interval_classify_check cnd (unlift (Inl (v, [])))
        else sup_fin semilattice_sup_check_result
               (image
                 (fun ctx ->
                   interval_classify_check cnd (unlift (Inl (v, ctx))))
                 ctxs)));;

let rec wf_program_compile_input_exec
  p = (let procs = proc_rep p in
       let gs = storage_global p prog_main_name in
       let pi = map_of equal_literal procs in
        reserved_ret_var gs &&
          (distinct equal_literal (prog_procs p) &&
            (equal_set equal_literal (Set (prog_procs p))
               (remove equal_literal prog_main_name (Set (map fst procs))) &&
              (not (membera equal_literal (prog_procs p) prog_main_name) &&
                (equal_option (equal_proc_decl_ext equal_unit)
                   (pi prog_main_name) (Some (proc_decl_of [] (prog_main p))) &&
                  (wf_source_com pi (prog_main p) &&
                    (no_return (prog_main p) &&
                      (list_all (fun (_, a) -> wf_proc_decl gs pi a) procs &&
                        list_all (fun (q, _) -> is_none (special_table q))
                          procs))))))));;

let rec interval_check_report_per_origin
  gs mnm p =
    (let raw =
       ivl_exec_raw_per_origin
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec entry_state_sigma_abs_exec_from_sol
  gs sol_sigma =
    comp (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for bot_ivl gs))
           (map_lift (fun_of_resolved_st_q_for bot_ivl gs)))
      sol_sigma;;

let rec entry_state_sg_exec_from_sol
  gs sol k =
    (match k
      with Inl (v, ctx) ->
        (if member (equal_prod equal_cfg_node (equal_list equal_ivl)) (v, ctx)
              (fst sol)
          then assemble_env_abs bounded_semilattice_sup_bot_ivl gs
                 (locals
                   (entry_state_sigma_abs_exec_from_sol gs (snd sol)
                     (Inl (v, ctx))))
                 (globs
                   (entry_state_sigma_abs_exec_from_sol gs (snd sol)
                     (Inr Global)))
          else Bot)
      | Inr _ -> Bot);;

let rec entry_state_check_report
  gs is_bot_pred pi ps mnm main =
    (let sol = entry_state_sol gs is_bot_pred pi ps mnm main in
     let sg = entry_state_sg_exec_from_sol gs sol in
      map_filter
        (fun x ->
          (if (let (_, (a, _)) = x in is_EA_Check a)
            then Some (let (u, (a, _)) = x in
                        (u, (ea_check_cond a,
                              entry_state_classify_at u (ea_check_cond a)
                                (fst sol) sg)))
            else None))
        (cfg_intra_list (compile_prog pi ps mnm main)));;

let rec analyse_interval_report_per_origin
  p = interval_check_report_per_origin (declared_global p) prog_main_name p;;

let rec interval_td_check_report_with_state
  gs mnm p =
    (let raw =
       analyse_interval_td_raw
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks_with_state (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec entry_state_check_report_prog
  mnm p =
    entry_state_check_report (declared_global p)
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) mnm (prog_main p);;

let rec analyse_interval_entry_state
  p = entry_state_check_report_prog prog_main_name p;;

let rec is_bot_sign a = is_bottom_sign a;;

let rec analyse_interval_td_report_with_state
  p = interval_td_check_report_with_state (declared_global p) prog_main_name p;;

end;; (*struct Core*)

module Analyse : sig
  type context_mode = Ctx_None | Ctx_EntryState
  type analysis_kind = Sign_Analysis | Interval_Analysis
  type solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow
  type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl
  val analyse :
    analysis_kind ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node * (Core.bexp * Core.check_result)) list
  val analyse_ctx :
    analysis_kind ->
      context_mode ->
        unit Core.imp_prog_ext ->
          ((Core.cfg_node * (Core.bexp * Core.check_result)) list) option
  val analyse_with_state :
    analysis_kind ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node *
          (Core.bexp * (Core.check_result * (string -> abstract_value)))) list
  val analyse_with_solver :
    analysis_kind ->
      solver_choice ->
        unit Core.imp_prog_ext ->
          ((Core.cfg_node * (Core.bexp * Core.check_result)) list) option
end = struct

type context_mode = Ctx_None | Ctx_EntryState;;

type analysis_kind = Sign_Analysis | Interval_Analysis;;

type solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow;;

type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl;;

let rec analyse
  x0 p = match x0, p with Sign_Analysis, p -> Core.analyse_sign_report p
    | Interval_Analysis, p -> Core.analyse_interval_td_report p;;

let rec analyse_ctx
  x0 x1 p = match x0, x1, p with
    Sign_Analysis, Ctx_None, p -> Some (Core.analyse_sign_report p)
    | Interval_Analysis, Ctx_None, p -> Some (Core.analyse_interval_td_report p)
    | Interval_Analysis, Ctx_EntryState, p ->
        Some (Core.analyse_interval_entry_state p)
    | Sign_Analysis, Ctx_EntryState, p -> None;;

let rec analyse_with_state
  x0 p = match x0, p with
    Sign_Analysis, p ->
      Core.map
        (fun (u, (c, (r, s))) ->
          (u, (c, (r, Core.comp (fun a -> SignValue a) s))))
        (Core.analyse_sign_report_with_state p)
    | Interval_Analysis, p ->
        Core.map
          (fun (u, (c, (r, s))) ->
            (u, (c, (r, Core.comp (fun a -> IntervalValue a) s))))
          (Core.analyse_interval_td_report_with_state p);;

let rec analyse_with_solver
  x0 x1 p = match x0, x1, p with
    Sign_Analysis, Solver_Join, p -> Some (Core.analyse_sign_report p)
    | Sign_Analysis, Solver_PerOrigin, p ->
        Some (Core.analyse_sign_report_per_origin p)
    | Sign_Analysis, Solver_Warrow, p -> None
    | Interval_Analysis, Solver_Join, p -> Some (Core.analyse_interval_report p)
    | Interval_Analysis, Solver_PerOrigin, p ->
        Some (Core.analyse_interval_report_per_origin p)
    | Interval_Analysis, Solver_Warrow, p ->
        Some (Core.analyse_interval_td_report p);;

end;; (*struct Analyse*)

module Sign_Print : sig
  val string_of_sign : Core.sign -> Core.char list
end = struct

let rec string_of_sign
  = function
    Core.SBot ->
      [Core.char_0x42; Core.char_0x6F; Core.char_0x74; Core.char_0x74;
        Core.char_0x6F; Core.char_0x6D]
    | Core.SNeg ->
        [Core.char_0x4E; Core.char_0x65; Core.char_0x67; Core.char_0x61;
          Core.char_0x74; Core.char_0x69; Core.char_0x76; Core.char_0x65]
    | Core.SNonPos ->
        [Core.char_0x4E; Core.char_0x6F; Core.char_0x6E; Core.char_0x50;
          Core.char_0x6F; Core.char_0x73; Core.char_0x69; Core.char_0x74;
          Core.char_0x69; Core.char_0x76; Core.char_0x65]
    | Core.SZero ->
        [Core.char_0x5A; Core.char_0x65; Core.char_0x72; Core.char_0x6F]
    | Core.SNonNeg ->
        [Core.char_0x4E; Core.char_0x6F; Core.char_0x6E; Core.char_0x4E;
          Core.char_0x65; Core.char_0x67; Core.char_0x61; Core.char_0x74;
          Core.char_0x69; Core.char_0x76; Core.char_0x65]
    | Core.SPos ->
        [Core.char_0x50; Core.char_0x6F; Core.char_0x73; Core.char_0x69;
          Core.char_0x74; Core.char_0x69; Core.char_0x76; Core.char_0x65]
    | Core.STop -> [Core.char_0x54; Core.char_0x6F; Core.char_0x70];;

end;; (*struct Sign_Print*)

module Interval_Print : sig
  val string_of_ivl : Core.ivl -> Core.char list
end = struct

let rec string_of_eint
  = function
    Core.MinInf ->
      [Core.char_0x2D; Core.char_0x69; Core.char_0x6E; Core.char_0x66]
    | Core.PlusInf ->
        [Core.char_0x2B; Core.char_0x69; Core.char_0x6E; Core.char_0x66]
    | Core.Fin n -> Core.show_int n;;

let rec string_of_ivl
  (Core.Ivl (l, u)) =
    [Core.char_0x5B] @
      string_of_eint l @
        [Core.char_0x2C] @ string_of_eint u @ [Core.char_0x5D];;

end;; (*struct Interval_Print*)

module Analysis_GraphViz : sig
  type graphviz_node_annotation =
    Node_Annotation of Core.char list * Core.char list
  val join_gv_nl : (Core.char list) list -> Core.char list
  val raw_cfg_dot_lit :
    (string -> unit Core.proc_decl_ext option) ->
      string list ->
        string ->
          Core.com ->
            (Core.cfg_node -> graphviz_node_annotation option) -> string
  val check_result_annotation :
    Core.check_result -> Core.bexp -> graphviz_node_annotation
  val raw_cfg_canonical_text_lit :
    (string -> unit Core.proc_decl_ext option) ->
      string list ->
        string ->
          Core.com ->
            (Core.cfg_node -> graphviz_node_annotation option) -> string
end = struct

type ('a, 'b) analysis_node = LocalNode of Core.cfg_node * 'a | GlobalNode of 'b
  | SourceNode of Core.char list;;

let rec equal_analysis_nodea _A _B
  x0 x1 = match x0, x1 with GlobalNode x2, SourceNode x3 -> false
    | SourceNode x3, GlobalNode x2 -> false
    | LocalNode (x11, x12), SourceNode x3 -> false
    | SourceNode x3, LocalNode (x11, x12) -> false
    | LocalNode (x11, x12), GlobalNode x2 -> false
    | GlobalNode x2, LocalNode (x11, x12) -> false
    | SourceNode x3, SourceNode y3 -> Core.equal_lista Core.equal_char x3 y3
    | GlobalNode x2, GlobalNode y2 -> HOL.eq _B x2 y2
    | LocalNode (x11, x12), LocalNode (y11, y12) ->
        Core.equal_cfg_nodea x11 y11 && HOL.eq _A x12 y12;;

let rec equal_analysis_node _A _B =
  ({HOL.equal = equal_analysis_nodea _A _B} :
    ('a, 'b) analysis_node HOL.equal);;

type ('a, 'b) analysis_cluster = ContextCluster of Core.char list * 'a |
  GlobalCluster | SourceCluster;;

let rec equal_analysis_clustera _A
  x0 x1 = match x0, x1 with GlobalCluster, SourceCluster -> false
    | SourceCluster, GlobalCluster -> false
    | ContextCluster (x11, x12), SourceCluster -> false
    | SourceCluster, ContextCluster (x11, x12) -> false
    | ContextCluster (x11, x12), GlobalCluster -> false
    | GlobalCluster, ContextCluster (x11, x12) -> false
    | ContextCluster (x11, x12), ContextCluster (y11, y12) ->
        Core.equal_lista Core.equal_char x11 y11 && HOL.eq _A x12 y12
    | SourceCluster, SourceCluster -> true
    | GlobalCluster, GlobalCluster -> true;;

let rec equal_analysis_cluster _A =
  ({HOL.equal = equal_analysis_clustera _A} :
    ('a, 'b) analysis_cluster HOL.equal);;

type analysis_edge_kind = IntraEdge of Core.edge_action |
  EnterEdge of Core.char list * Core.call_action |
  CombineEdge of Core.cfg_node * string option * string option |
  CallToReturnEdge of string | GlobalReadEdge | GlobalWriteEdge;;

let rec equal_analysis_edge_kinda
  x0 x1 = match x0, x1 with GlobalReadEdge, GlobalWriteEdge -> false
    | GlobalWriteEdge, GlobalReadEdge -> false
    | CallToReturnEdge x4, GlobalWriteEdge -> false
    | GlobalWriteEdge, CallToReturnEdge x4 -> false
    | CallToReturnEdge x4, GlobalReadEdge -> false
    | GlobalReadEdge, CallToReturnEdge x4 -> false
    | CombineEdge (x31, x32, x33), GlobalWriteEdge -> false
    | GlobalWriteEdge, CombineEdge (x31, x32, x33) -> false
    | CombineEdge (x31, x32, x33), GlobalReadEdge -> false
    | GlobalReadEdge, CombineEdge (x31, x32, x33) -> false
    | CombineEdge (x31, x32, x33), CallToReturnEdge x4 -> false
    | CallToReturnEdge x4, CombineEdge (x31, x32, x33) -> false
    | EnterEdge (x21, x22), GlobalWriteEdge -> false
    | GlobalWriteEdge, EnterEdge (x21, x22) -> false
    | EnterEdge (x21, x22), GlobalReadEdge -> false
    | GlobalReadEdge, EnterEdge (x21, x22) -> false
    | EnterEdge (x21, x22), CallToReturnEdge x4 -> false
    | CallToReturnEdge x4, EnterEdge (x21, x22) -> false
    | EnterEdge (x21, x22), CombineEdge (x31, x32, x33) -> false
    | CombineEdge (x31, x32, x33), EnterEdge (x21, x22) -> false
    | IntraEdge x1, GlobalWriteEdge -> false
    | GlobalWriteEdge, IntraEdge x1 -> false
    | IntraEdge x1, GlobalReadEdge -> false
    | GlobalReadEdge, IntraEdge x1 -> false
    | IntraEdge x1, CallToReturnEdge x4 -> false
    | CallToReturnEdge x4, IntraEdge x1 -> false
    | IntraEdge x1, CombineEdge (x31, x32, x33) -> false
    | CombineEdge (x31, x32, x33), IntraEdge x1 -> false
    | IntraEdge x1, EnterEdge (x21, x22) -> false
    | EnterEdge (x21, x22), IntraEdge x1 -> false
    | CallToReturnEdge x4, CallToReturnEdge y4 -> ((x4 : string) = y4)
    | CombineEdge (x31, x32, x33), CombineEdge (y31, y32, y33) ->
        Core.equal_cfg_nodea x31 y31 &&
          (Core.equal_option Core.equal_literal x32 y32 &&
            Core.equal_option Core.equal_literal x33 y33)
    | EnterEdge (x21, x22), EnterEdge (y21, y22) ->
        Core.equal_lista Core.equal_char x21 y21 &&
          Core.equal_call_actiona x22 y22
    | IntraEdge x1, IntraEdge y1 -> Core.equal_edge_actiona x1 y1
    | GlobalWriteEdge, GlobalWriteEdge -> true
    | GlobalReadEdge, GlobalReadEdge -> true;;

let equal_analysis_edge_kind =
  ({HOL.equal = equal_analysis_edge_kinda} : analysis_edge_kind HOL.equal);;

type graphviz_node_annotation =
  Node_Annotation of Core.char list * Core.char list;;

type ('a, 'b, 'c, 'd, 'e) analysis_graph_config_ext =
  Analysis_graph_config_ext of
    ('c -> 'd) * (Core.cfg_node -> 'a -> Core.call_action -> 'd -> 'a) *
      ('a -> Core.char list) * (Core.cfg_node -> string list) *
      (Core.cfg_node -> string option) * string list *
      (Core.cfg_node -> 'a -> string list -> 'd -> (Core.char list) list) *
      (Core.cfg_node -> 'a -> string -> 'd -> (Core.char list) list) *
      ('b -> string list -> 'c -> (Core.char list) list) *
      ('b -> Core.char list) * ('b -> bool) * bool *
      (Core.cfg_node -> Core.char list) *
      (Core.char list -> 'a -> Core.char list) * (Core.char list) option *
      (Core.cfg_node -> graphviz_node_annotation option) * 'e;;

let dq : Core.char list = [Core.char_0x22];;

let nl : Core.char list = [Core.char_0x0A];;

let gv_nl : Core.char list = [Core.char_0x5C; Core.char_0x6E];;

let rec join_gv_nl = function [] -> []
                     | [s] -> s
                     | s :: v :: va -> s @ gv_nl @ join_gv_nl (v :: va);;

let rec cfg_point_list
  g = Core.remdups Core.equal_cfg_node
        (Core.cfg_entry g ::
          Core.maps (fun (u, (_, v)) -> [u; v]) (Core.cfg_intra_list g) @
            Core.maps
              (fun (call, (_, (entry, cont))) ->
                call ::
                  entry ::
                    cont ::
                      (match entry with Core.Statement _ -> []
                        | Core.FunctionEntry p -> [Core.FunctionResult p]
                        | Core.FunctionResult _ -> []))
              (Core.cfg_calls_list g));;

let rec contextual_graph_domain
  g contexts_for_pp =
    Core.maps
      (fun p -> Core.map (fun ctx -> Core.Inl (p, ctx)) (contexts_for_pp p))
      (cfg_point_list g);;

let rec owner_of
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = owner_of;;

let rec analysis_node_position _A _B
  x0 n = match x0, n with [], n -> Core.zero_nat
    | m :: ms, n ->
        (if equal_analysis_nodea _A _B n m then Core.zero_nat
          else Core.suc (analysis_node_position _A _B ms n));;

let rec analysis_nodes_in_cluster _A _B
  cfg cluster ns =
    Core.sort_key Core.linorder_nat (analysis_node_position _A _B ns)
      (Core.filtera
        (fun n ->
          (match (cluster, n)
            with (ContextCluster (owner, ctx), LocalNode (p, ctxa)) ->
              Core.equal_lista Core.equal_char owner (owner_of cfg p) &&
                HOL.eq _A ctx ctxa
            | (ContextCluster (_, _), GlobalNode _) -> false
            | (ContextCluster (_, _), SourceNode _) -> false
            | (GlobalCluster, LocalNode (_, _)) -> false
            | (GlobalCluster, GlobalNode _) -> true
            | (GlobalCluster, SourceNode _) -> false
            | (SourceCluster, LocalNode (_, _)) -> false
            | (SourceCluster, GlobalNode _) -> false
            | (SourceCluster, SourceNode _) -> true))
        ns);;

let rec cluster_label
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = cluster_label;;

let rec analysis_cluster_label
  cfg cluster =
    (match cluster with ContextCluster (a, b) -> cluster_label cfg a b
      | GlobalCluster ->
        [Core.char_0x53; Core.char_0x68; Core.char_0x61; Core.char_0x72;
          Core.char_0x65; Core.char_0x64; Core.char_0x20; Core.char_0x67;
          Core.char_0x6C; Core.char_0x6F; Core.char_0x62; Core.char_0x61;
          Core.char_0x6C; Core.char_0x73]
      | SourceCluster ->
        [Core.char_0x53; Core.char_0x6F; Core.char_0x75; Core.char_0x72;
          Core.char_0x63; Core.char_0x65]);;

let rec annotation_label (Node_Annotation (x1, x2)) = x1;;

let rec return_slot_for_pp
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = return_slot_for_pp;;

let rec show_global_key
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = show_global_key;;

let rec node_annotation
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = node_annotation;;

let rec globals_to_show
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = globals_to_show;;

let rec locals_for_pp
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = locals_for_pp;;

let rec format_return
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = format_return;;

let rec show_global
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = show_global;;

let rec show_local
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = show_local;;

let rec local_of
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = local_of;;

let rec string_of_cfg_node
  = function
    Core.Statement n -> [Core.char_0x70; Core.char_0x70] @ Core.string_of_nat n
    | Core.FunctionEntry p ->
        [Core.char_0x65; Core.char_0x6E; Core.char_0x74; Core.char_0x72;
          Core.char_0x79; Core.char_0x5F] @
          Core.explode p
    | Core.FunctionResult p ->
        [Core.char_0x72; Core.char_0x65; Core.char_0x73; Core.char_0x75;
          Core.char_0x6C; Core.char_0x74; Core.char_0x5F] @
          Core.explode p;;

let rec graphviz_point_label
  g p = (match p with Core.Statement _ -> string_of_cfg_node p
          | Core.FunctionEntry owner ->
            [Core.char_0x65; Core.char_0x6E; Core.char_0x74; Core.char_0x72;
              Core.char_0x79; Core.char_0x5F] @
              Core.explode owner
          | Core.FunctionResult owner ->
            [Core.char_0x65; Core.char_0x78; Core.char_0x69; Core.char_0x74;
              Core.char_0x5F] @
              Core.explode owner);;

let rec split_gv_nl_acc
  acc x1 = match acc, x1 with acc, [] -> [Core.rev acc]
    | acc, [ch] -> [Core.rev (ch :: acc)]
    | acc, ch1 :: ch2 :: rest ->
        (if Core.equal_chara ch1 Core.char_0x5C &&
              Core.equal_chara ch2 Core.char_0x6E
          then Core.rev acc :: split_gv_nl_acc [] rest
          else split_gv_nl_acc (ch1 :: acc) (ch2 :: rest));;

let rec split_gv_nl s = split_gv_nl_acc [] s;;

let rec contextual_node_label_lines
  cfg g sol n =
    (match n
      with LocalNode (p, ctx) ->
        graphviz_point_label g p ::
          show_local cfg p ctx (locals_for_pp cfg p)
            (local_of cfg (sol (Core.Inl (p, ctx)))) @
            (match return_slot_for_pp cfg p with None -> []
              | Some ret ->
                format_return cfg p ctx ret
                  (local_of cfg (sol (Core.Inl (p, ctx))))) @
              (match node_annotation cfg p with None -> []
                | Some ann ->
                  (if Core.null (annotation_label ann) then []
                    else split_gv_nl (annotation_label ann)))
      | GlobalNode k ->
        show_global_key cfg k ::
          show_global cfg k (globals_to_show cfg) (sol (Core.Inr k))
      | SourceNode src -> [src]);;

let rec contextual_node_label
  cfg g sol n = join_gv_nl (contextual_node_label_lines cfg g sol n);;

let rec graphviz_label_text
  = function [] -> []
    | ch :: rest ->
        (if Core.equal_chara ch Core.char_0x0A then gv_nl else [ch]) @
          graphviz_label_text rest;;

let rec annotation_style (Node_Annotation (x1, x2)) = x2;;

let rec proc_entry_pps_list
  g = Core.map (fun (_, (_, (entry, _))) -> entry) (Core.cfg_calls_list g);;

let rec proc_exit_pps_list
  g = Core.map
        (fun (_, (_, (entry, _))) ->
          (match entry with Core.Statement _ -> entry
            | Core.FunctionEntry a -> Core.FunctionResult a
            | Core.FunctionResult _ -> entry))
        (Core.cfg_calls_list g);;

let rec graphviz_exit
  g = (match Core.cfg_entry g with Core.Statement a -> Core.Statement a
        | Core.FunctionEntry a -> Core.FunctionResult a
        | Core.FunctionResult a -> Core.FunctionResult a);;

let rec analysis_node_attrs
  cfg g n =
    (match n
      with LocalNode (p, _) ->
        (match node_annotation cfg p
          with None ->
            (if Core.equal_cfg_nodea p (Core.cfg_entry g)
              then [Core.char_0x73; Core.char_0x68; Core.char_0x61;
                     Core.char_0x70; Core.char_0x65; Core.char_0x3D;
                     Core.char_0x64; Core.char_0x6F; Core.char_0x75;
                     Core.char_0x62; Core.char_0x6C; Core.char_0x65;
                     Core.char_0x63; Core.char_0x69; Core.char_0x72;
                     Core.char_0x63; Core.char_0x6C; Core.char_0x65;
                     Core.char_0x2C; Core.char_0x63; Core.char_0x6F;
                     Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
                     Core.char_0x3D; Core.char_0x67; Core.char_0x72;
                     Core.char_0x65; Core.char_0x65; Core.char_0x6E;
                     Core.char_0x2C; Core.char_0x73; Core.char_0x74;
                     Core.char_0x79; Core.char_0x6C; Core.char_0x65;
                     Core.char_0x3D; Core.char_0x66; Core.char_0x69;
                     Core.char_0x6C; Core.char_0x6C; Core.char_0x65;
                     Core.char_0x64; Core.char_0x2C; Core.char_0x66;
                     Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
                     Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
                     Core.char_0x6F; Core.char_0x72; Core.char_0x3D;
                     Core.char_0x6C; Core.char_0x69; Core.char_0x67;
                     Core.char_0x68; Core.char_0x74; Core.char_0x79;
                     Core.char_0x65; Core.char_0x6C; Core.char_0x6C;
                     Core.char_0x6F; Core.char_0x77]
              else (if Core.equal_cfg_nodea p (graphviz_exit g)
                     then [Core.char_0x73; Core.char_0x68; Core.char_0x61;
                            Core.char_0x70; Core.char_0x65; Core.char_0x3D;
                            Core.char_0x64; Core.char_0x6F; Core.char_0x75;
                            Core.char_0x62; Core.char_0x6C; Core.char_0x65;
                            Core.char_0x63; Core.char_0x69; Core.char_0x72;
                            Core.char_0x63; Core.char_0x6C; Core.char_0x65;
                            Core.char_0x2C; Core.char_0x63; Core.char_0x6F;
                            Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
                            Core.char_0x3D; Core.char_0x67; Core.char_0x72;
                            Core.char_0x61; Core.char_0x79; Core.char_0x34;
                            Core.char_0x30; Core.char_0x2C; Core.char_0x73;
                            Core.char_0x74; Core.char_0x79; Core.char_0x6C;
                            Core.char_0x65; Core.char_0x3D; Core.char_0x66;
                            Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
                            Core.char_0x65; Core.char_0x64; Core.char_0x2C;
                            Core.char_0x66; Core.char_0x69; Core.char_0x6C;
                            Core.char_0x6C; Core.char_0x63; Core.char_0x6F;
                            Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
                            Core.char_0x3D; Core.char_0x6C; Core.char_0x69;
                            Core.char_0x67; Core.char_0x68; Core.char_0x74;
                            Core.char_0x67; Core.char_0x72; Core.char_0x61;
                            Core.char_0x79]
                     else (if Core.membera Core.equal_cfg_node
                                (proc_entry_pps_list g) p
                            then [Core.char_0x73; Core.char_0x68;
                                   Core.char_0x61; Core.char_0x70;
                                   Core.char_0x65; Core.char_0x3D;
                                   Core.char_0x64; Core.char_0x6F;
                                   Core.char_0x75; Core.char_0x62;
                                   Core.char_0x6C; Core.char_0x65;
                                   Core.char_0x63; Core.char_0x69;
                                   Core.char_0x72; Core.char_0x63;
                                   Core.char_0x6C; Core.char_0x65;
                                   Core.char_0x2C; Core.char_0x63;
                                   Core.char_0x6F; Core.char_0x6C;
                                   Core.char_0x6F; Core.char_0x72;
                                   Core.char_0x3D; Core.char_0x67;
                                   Core.char_0x72; Core.char_0x65;
                                   Core.char_0x65; Core.char_0x6E;
                                   Core.char_0x2C; Core.char_0x73;
                                   Core.char_0x74; Core.char_0x79;
                                   Core.char_0x6C; Core.char_0x65;
                                   Core.char_0x3D; Core.char_0x66;
                                   Core.char_0x69; Core.char_0x6C;
                                   Core.char_0x6C; Core.char_0x65;
                                   Core.char_0x64; Core.char_0x2C;
                                   Core.char_0x66; Core.char_0x69;
                                   Core.char_0x6C; Core.char_0x6C;
                                   Core.char_0x63; Core.char_0x6F;
                                   Core.char_0x6C; Core.char_0x6F;
                                   Core.char_0x72; Core.char_0x3D;
                                   Core.char_0x6C; Core.char_0x69;
                                   Core.char_0x67; Core.char_0x68;
                                   Core.char_0x74; Core.char_0x79;
                                   Core.char_0x65; Core.char_0x6C;
                                   Core.char_0x6C; Core.char_0x6F;
                                   Core.char_0x77]
                            else (if Core.membera Core.equal_cfg_node
                                       (proc_exit_pps_list g) p
                                   then [Core.char_0x73; Core.char_0x68;
  Core.char_0x61; Core.char_0x70; Core.char_0x65; Core.char_0x3D;
  Core.char_0x64; Core.char_0x6F; Core.char_0x75; Core.char_0x62;
  Core.char_0x6C; Core.char_0x65; Core.char_0x63; Core.char_0x69;
  Core.char_0x72; Core.char_0x63; Core.char_0x6C; Core.char_0x65;
  Core.char_0x2C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
  Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x67;
  Core.char_0x72; Core.char_0x61; Core.char_0x79; Core.char_0x34;
  Core.char_0x30; Core.char_0x2C; Core.char_0x73; Core.char_0x74;
  Core.char_0x79; Core.char_0x6C; Core.char_0x65; Core.char_0x3D;
  Core.char_0x66; Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
  Core.char_0x65; Core.char_0x64; Core.char_0x2C; Core.char_0x66;
  Core.char_0x69; Core.char_0x6C; Core.char_0x6C; Core.char_0x63;
  Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
  Core.char_0x3D; Core.char_0x6C; Core.char_0x69; Core.char_0x67;
  Core.char_0x68; Core.char_0x74; Core.char_0x67; Core.char_0x72;
  Core.char_0x61; Core.char_0x79]
                                   else [Core.char_0x73; Core.char_0x68;
  Core.char_0x61; Core.char_0x70; Core.char_0x65; Core.char_0x3D;
  Core.char_0x62; Core.char_0x6F; Core.char_0x78; Core.char_0x2C;
  Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
  Core.char_0x65; Core.char_0x3D; Core.char_0x66; Core.char_0x69;
  Core.char_0x6C; Core.char_0x6C; Core.char_0x65; Core.char_0x64;
  Core.char_0x2C; Core.char_0x66; Core.char_0x69; Core.char_0x6C;
  Core.char_0x6C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
  Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x6C;
  Core.char_0x69; Core.char_0x67; Core.char_0x68; Core.char_0x74;
  Core.char_0x67; Core.char_0x72; Core.char_0x65; Core.char_0x65;
  Core.char_0x6E]))))
          | Some a -> annotation_style a)
      | GlobalNode _ ->
        [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
          Core.char_0x65; Core.char_0x3D; Core.char_0x6E; Core.char_0x6F;
          Core.char_0x74; Core.char_0x65; Core.char_0x2C; Core.char_0x77;
          Core.char_0x69; Core.char_0x64; Core.char_0x74; Core.char_0x68;
          Core.char_0x3D; Core.char_0x32; Core.char_0x2E; Core.char_0x32;
          Core.char_0x2C; Core.char_0x66; Core.char_0x69; Core.char_0x78;
          Core.char_0x65; Core.char_0x64; Core.char_0x73; Core.char_0x69;
          Core.char_0x7A; Core.char_0x65; Core.char_0x3D; Core.char_0x66;
          Core.char_0x61; Core.char_0x6C; Core.char_0x73; Core.char_0x65]
      | SourceNode _ ->
        [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
          Core.char_0x65; Core.char_0x3D; Core.char_0x70; Core.char_0x6C;
          Core.char_0x61; Core.char_0x69; Core.char_0x6E]);;

let rec analysis_cluster_position _A
  x0 cluster = match x0, cluster with [], cluster -> Core.zero_nat
    | cluster0 :: clusters, cluster ->
        (if equal_analysis_clustera _A cluster0 cluster then Core.zero_nat
          else Core.suc (analysis_cluster_position _A clusters cluster));;

let rec analysis_cluster_id _A
  clusters cluster =
    (match cluster
      with ContextCluster (_, _) ->
        [Core.char_0x63; Core.char_0x6C; Core.char_0x75; Core.char_0x73;
          Core.char_0x74; Core.char_0x65; Core.char_0x72; Core.char_0x5F;
          Core.char_0x63; Core.char_0x74; Core.char_0x78; Core.char_0x5F] @
          Core.string_of_nat (analysis_cluster_position _A clusters cluster)
      | GlobalCluster ->
        [Core.char_0x63; Core.char_0x6C; Core.char_0x75; Core.char_0x73;
          Core.char_0x74; Core.char_0x65; Core.char_0x72; Core.char_0x5F;
          Core.char_0x67; Core.char_0x6C; Core.char_0x6F; Core.char_0x62;
          Core.char_0x61; Core.char_0x6C; Core.char_0x73]
      | SourceCluster ->
        [Core.char_0x63; Core.char_0x6C; Core.char_0x75; Core.char_0x73;
          Core.char_0x74; Core.char_0x65; Core.char_0x72; Core.char_0x5F;
          Core.char_0x73; Core.char_0x6F; Core.char_0x75; Core.char_0x72;
          Core.char_0x63; Core.char_0x65]);;

let rec graphviz_html_text
  = function [] -> []
    | ch :: rest ->
        (if Core.equal_chara ch Core.char_0x0A
          then [Core.char_0x3C; Core.char_0x42; Core.char_0x52; Core.char_0x20;
                 Core.char_0x41; Core.char_0x4C; Core.char_0x49; Core.char_0x47;
                 Core.char_0x4E; Core.char_0x3D] @
                 dq @ [Core.char_0x4C; Core.char_0x45; Core.char_0x46;
                        Core.char_0x54] @
                        dq @ [Core.char_0x2F; Core.char_0x3E]
          else (if Core.equal_chara ch Core.char_0x20
                 then [Core.char_0x26; Core.char_0x23; Core.char_0x31;
                        Core.char_0x36; Core.char_0x30; Core.char_0x3B]
                 else (if Core.equal_chara ch Core.char_0x26
                        then [Core.char_0x26; Core.char_0x61; Core.char_0x6D;
                               Core.char_0x70; Core.char_0x3B]
                        else (if Core.equal_chara ch Core.char_0x3C
                               then [Core.char_0x26; Core.char_0x6C;
                                      Core.char_0x74; Core.char_0x3B]
                               else (if Core.equal_chara ch Core.char_0x3E
                                      then [Core.char_0x26; Core.char_0x67;
     Core.char_0x74; Core.char_0x3B]
                                      else [ch]))))) @
          graphviz_html_text rest;;

let rec ensure_trailing_nl
  src = (match Core.rev src with [] -> nl
          | ch :: _ ->
            (if Core.equal_chara ch Core.char_0x0A then src else src @ nl));;

let rec source_html_label
  src = [Core.char_0x3C; Core.char_0x3C; Core.char_0x54; Core.char_0x41;
          Core.char_0x42; Core.char_0x4C; Core.char_0x45; Core.char_0x20;
          Core.char_0x42; Core.char_0x4F; Core.char_0x52; Core.char_0x44;
          Core.char_0x45; Core.char_0x52; Core.char_0x3D] @
          dq @ [Core.char_0x31] @
                 dq @ [Core.char_0x20; Core.char_0x43; Core.char_0x45;
                        Core.char_0x4C; Core.char_0x4C; Core.char_0x42;
                        Core.char_0x4F; Core.char_0x52; Core.char_0x44;
                        Core.char_0x45; Core.char_0x52; Core.char_0x3D] @
                        dq @ [Core.char_0x30] @
                               dq @ [Core.char_0x20; Core.char_0x43;
                                      Core.char_0x45; Core.char_0x4C;
                                      Core.char_0x4C; Core.char_0x50;
                                      Core.char_0x41; Core.char_0x44;
                                      Core.char_0x44; Core.char_0x49;
                                      Core.char_0x4E; Core.char_0x47;
                                      Core.char_0x3D] @
                                      dq @
[Core.char_0x38] @
  dq @ [Core.char_0x3E; Core.char_0x3C; Core.char_0x54; Core.char_0x52;
         Core.char_0x3E; Core.char_0x3C; Core.char_0x54; Core.char_0x44;
         Core.char_0x20; Core.char_0x41; Core.char_0x4C; Core.char_0x49;
         Core.char_0x47; Core.char_0x4E; Core.char_0x3D] @
         dq @ [Core.char_0x4C; Core.char_0x45; Core.char_0x46; Core.char_0x54] @
                dq @ [Core.char_0x20; Core.char_0x57; Core.char_0x49;
                       Core.char_0x44; Core.char_0x54; Core.char_0x48;
                       Core.char_0x3D] @
                       dq @ [Core.char_0x32; Core.char_0x36; Core.char_0x30] @
                              dq @ [Core.char_0x20; Core.char_0x46;
                                     Core.char_0x49; Core.char_0x58;
                                     Core.char_0x45; Core.char_0x44;
                                     Core.char_0x53; Core.char_0x49;
                                     Core.char_0x5A; Core.char_0x45;
                                     Core.char_0x3D] @
                                     dq @ [Core.char_0x46; Core.char_0x41;
    Core.char_0x4C; Core.char_0x53; Core.char_0x45] @
    dq @ [Core.char_0x3E; Core.char_0x3C; Core.char_0x46; Core.char_0x4F;
           Core.char_0x4E; Core.char_0x54; Core.char_0x20; Core.char_0x46;
           Core.char_0x41; Core.char_0x43; Core.char_0x45; Core.char_0x3D] @
           dq @ [Core.char_0x4D; Core.char_0x65; Core.char_0x6E; Core.char_0x6C;
                  Core.char_0x6F] @
                  dq @ [Core.char_0x20; Core.char_0x50; Core.char_0x4F;
                         Core.char_0x49; Core.char_0x4E; Core.char_0x54;
                         Core.char_0x2D; Core.char_0x53; Core.char_0x49;
                         Core.char_0x5A; Core.char_0x45; Core.char_0x3D] @
                         dq @ [Core.char_0x31; Core.char_0x30] @
                                dq @ [Core.char_0x3E] @
                                       graphviz_html_text
 (ensure_trailing_nl src) @
 [Core.char_0x3C; Core.char_0x2F; Core.char_0x46; Core.char_0x4F;
   Core.char_0x4E; Core.char_0x54; Core.char_0x3E; Core.char_0x3C;
   Core.char_0x2F; Core.char_0x54; Core.char_0x44; Core.char_0x3E;
   Core.char_0x3C; Core.char_0x2F; Core.char_0x54; Core.char_0x52;
   Core.char_0x3E; Core.char_0x3C; Core.char_0x2F; Core.char_0x54;
   Core.char_0x41; Core.char_0x42; Core.char_0x4C; Core.char_0x45;
   Core.char_0x3E; Core.char_0x3E];;

let rec context_position _A
  x0 key = match x0, key with [], key -> Core.zero_nat
    | keya :: keys, key ->
        (if HOL.eq _A key keya then Core.zero_nat
          else Core.suc (context_position _A keys key));;

let rec owner_contexts
  cfg x1 = match cfg, x1 with cfg, [] -> []
    | cfg, LocalNode (p, ctx) :: ns ->
        (owner_of cfg p, ctx) :: owner_contexts cfg ns
    | cfg, GlobalNode k :: ns -> owner_contexts cfg ns
    | cfg, SourceNode src :: ns -> owner_contexts cfg ns;;

let rec analysis_node_id _A _B
  cfg ns n =
    (match n
      with LocalNode (p, ctx) ->
        owner_of cfg p @
          [Core.char_0x5F] @
            string_of_cfg_node p @
              [Core.char_0x5F; Core.char_0x63; Core.char_0x74; Core.char_0x78] @
                Core.string_of_nat
                  (context_position
                    (Core.equal_prod (Core.equal_list Core.equal_char) _A)
                    (Core.remdups
                      (Core.equal_prod (Core.equal_list Core.equal_char) _A)
                      (owner_contexts cfg ns))
                    (owner_of cfg p, ctx))
      | GlobalNode _ ->
        [Core.char_0x67; Core.char_0x6C; Core.char_0x6F; Core.char_0x62;
          Core.char_0x61; Core.char_0x6C; Core.char_0x5F] @
          Core.string_of_nat (analysis_node_position _A _B ns n)
      | SourceNode _ ->
        [Core.char_0x73; Core.char_0x6F; Core.char_0x75; Core.char_0x72;
          Core.char_0x63; Core.char_0x65]);;

let rec analysis_cluster_dot _A _B
  cfg g clusters ns es sol cluster =
    (let members = analysis_nodes_in_cluster _A _B cfg cluster ns in
      [Core.char_0x20; Core.char_0x20; Core.char_0x73; Core.char_0x75;
        Core.char_0x62; Core.char_0x67; Core.char_0x72; Core.char_0x61;
        Core.char_0x70; Core.char_0x68; Core.char_0x20] @
        analysis_cluster_id _A clusters cluster @
          [Core.char_0x20; Core.char_0x7B] @
            nl @ [Core.char_0x20; Core.char_0x20; Core.char_0x20;
                   Core.char_0x20; Core.char_0x6C; Core.char_0x61;
                   Core.char_0x62; Core.char_0x65; Core.char_0x6C;
                   Core.char_0x3D] @
                   dq @ analysis_cluster_label cfg cluster @
                          dq @ [Core.char_0x3B] @
                                 nl @ [Core.char_0x20; Core.char_0x20;
Core.char_0x20; Core.char_0x20; Core.char_0x73; Core.char_0x74; Core.char_0x79;
Core.char_0x6C; Core.char_0x65; Core.char_0x3D; Core.char_0x72; Core.char_0x6F;
Core.char_0x75; Core.char_0x6E; Core.char_0x64; Core.char_0x65; Core.char_0x64;
Core.char_0x3B; Core.char_0x20; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x67; Core.char_0x72;
Core.char_0x61; Core.char_0x79; Core.char_0x37; Core.char_0x30; Core.char_0x3B;
Core.char_0x20; Core.char_0x70; Core.char_0x65; Core.char_0x6E; Core.char_0x77;
Core.char_0x69; Core.char_0x64; Core.char_0x74; Core.char_0x68; Core.char_0x3D;
Core.char_0x31; Core.char_0x3B] @
nl @ Core.maps
       (fun n ->
         [Core.char_0x20; Core.char_0x20; Core.char_0x20; Core.char_0x20] @
           analysis_node_id _A _B cfg ns n @
             [Core.char_0x20; Core.char_0x5B] @
               analysis_node_attrs cfg g n @
                 (match n
                   with LocalNode (_, _) ->
                     [Core.char_0x2C; Core.char_0x6C; Core.char_0x61;
                       Core.char_0x62; Core.char_0x65; Core.char_0x6C;
                       Core.char_0x3D] @
                       dq @ graphviz_label_text
                              (contextual_node_label cfg g sol n) @
                              dq
                   | GlobalNode _ ->
                     [Core.char_0x2C; Core.char_0x6C; Core.char_0x61;
                       Core.char_0x62; Core.char_0x65; Core.char_0x6C;
                       Core.char_0x3D] @
                       dq @ graphviz_label_text
                              (contextual_node_label cfg g sol n) @
                              dq
                   | SourceNode _ ->
                     [Core.char_0x2C; Core.char_0x6C; Core.char_0x61;
                       Core.char_0x62; Core.char_0x65; Core.char_0x6C;
                       Core.char_0x3D] @
                       source_html_label (contextual_node_label cfg g sol n)) @
                   [Core.char_0x5D; Core.char_0x3B] @ nl)
       members @
       [Core.char_0x20; Core.char_0x20; Core.char_0x7D] @ nl);;

let rec analysis_graph_wf _A _B
  graph =
    (let (clusters, (ns, es)) = graph in
      Core.distinct (equal_analysis_cluster _A) clusters &&
        (Core.distinct (equal_analysis_node _A _B) ns &&
          (Core.distinct
             (Core.equal_prod (equal_analysis_node _A _B)
               (Core.equal_prod equal_analysis_edge_kind
                 (equal_analysis_node _A _B)))
             es &&
            Core.list_all
              (fun (src, (_, dst)) ->
                Core.membera (equal_analysis_node _A _B) ns src &&
                  Core.membera (equal_analysis_node _A _B) ns dst)
              es)));;

let rec string_of_action
  = function Core.EA_Nop -> [Core.char_0x6E; Core.char_0x6F; Core.char_0x70]
    | Core.EA_Assign (x, a) ->
        Core.explode x @
          [Core.char_0x20; Core.char_0x3A; Core.char_0x3D; Core.char_0x20] @
            Core.string_of_aexp a
    | Core.EA_Special (Core.Nondet_Int, x) ->
        Core.explode x @
          [Core.char_0x20; Core.char_0x3A; Core.char_0x3D; Core.char_0x20;
            Core.char_0x5F; Core.char_0x5F; Core.char_0x76; Core.char_0x6F;
            Core.char_0x62; Core.char_0x6C; Core.char_0x69; Core.char_0x6E;
            Core.char_0x74; Core.char_0x5F; Core.char_0x6E; Core.char_0x6F;
            Core.char_0x6E; Core.char_0x64; Core.char_0x65; Core.char_0x74;
            Core.char_0x5F; Core.char_0x69; Core.char_0x6E; Core.char_0x74;
            Core.char_0x28; Core.char_0x29]
    | Core.EA_Special (Core.Min (a, b), x) ->
        Core.explode x @
          [Core.char_0x20; Core.char_0x3A; Core.char_0x3D; Core.char_0x20;
            Core.char_0x6D; Core.char_0x69; Core.char_0x6E; Core.char_0x28] @
            Core.string_of_aexp a @
              [Core.char_0x2C; Core.char_0x20] @
                Core.string_of_aexp b @ [Core.char_0x29]
    | Core.EA_Special (Core.Max (a, b), x) ->
        Core.explode x @
          [Core.char_0x20; Core.char_0x3A; Core.char_0x3D; Core.char_0x20;
            Core.char_0x6D; Core.char_0x61; Core.char_0x78; Core.char_0x28] @
            Core.string_of_aexp a @
              [Core.char_0x2C; Core.char_0x20] @
                Core.string_of_aexp b @ [Core.char_0x29]
    | Core.EA_Assume b ->
        [Core.char_0x5B] @ Core.string_of_bexp b @ [Core.char_0x5D]
    | Core.EA_AssumeNot b ->
        [Core.char_0x21; Core.char_0x5B] @
          Core.string_of_bexp b @ [Core.char_0x5D]
    | Core.EA_Ret (None, p) ->
        [Core.char_0x72; Core.char_0x65; Core.char_0x74; Core.char_0x75;
          Core.char_0x72; Core.char_0x6E]
    | Core.EA_Ret (Some e, p) ->
        [Core.char_0x72; Core.char_0x65; Core.char_0x74; Core.char_0x75;
          Core.char_0x72; Core.char_0x6E; Core.char_0x20] @
          Core.string_of_aexp e
    | Core.EA_Check cnd ->
        [Core.char_0x63; Core.char_0x68; Core.char_0x65; Core.char_0x63;
          Core.char_0x6B; Core.char_0x28] @
          Core.string_of_bexp cnd @ [Core.char_0x29];;

let rec source_action_label
  g a = (match a with Core.EA_Nop -> string_of_action a
          | Core.EA_Assign (x, e) ->
            (if ((x : string) = Core.ret_var)
              then [Core.char_0x72; Core.char_0x65; Core.char_0x74;
                     Core.char_0x20; Core.char_0x3A; Core.char_0x3D;
                     Core.char_0x20] @
                     Core.string_of_aexp e
              else string_of_action a)
          | Core.EA_Special (_, _) -> string_of_action a
          | Core.EA_Assume aa -> Core.string_of_bexp aa
          | Core.EA_AssumeNot b ->
            [Core.char_0x6E; Core.char_0x6F; Core.char_0x74; Core.char_0x20;
              Core.char_0x28] @
              Core.string_of_bexp b @ [Core.char_0x29]
          | Core.EA_Ret (_, p) ->
            (if Core.equal_cfg_nodea (Core.cfg_entry g) (Core.FunctionEntry p)
              then [Core.char_0x74; Core.char_0x65; Core.char_0x72;
                     Core.char_0x6D; Core.char_0x69; Core.char_0x6E;
                     Core.char_0x61; Core.char_0x74; Core.char_0x65]
              else string_of_action a)
          | Core.EA_Check _ -> string_of_action a);;

let rec analysis_edge_attrs
  g kind =
    (match kind
      with IntraEdge a ->
        [Core.char_0x6C; Core.char_0x61; Core.char_0x62; Core.char_0x65;
          Core.char_0x6C; Core.char_0x3D] @
          dq @ source_action_label g a @ dq
      | EnterEdge (callee, a) ->
        [Core.char_0x63; Core.char_0x6F; Core.char_0x6C; Core.char_0x6F;
          Core.char_0x72; Core.char_0x3D; Core.char_0x70; Core.char_0x75;
          Core.char_0x72; Core.char_0x70; Core.char_0x6C; Core.char_0x65;
          Core.char_0x2C; Core.char_0x70; Core.char_0x65; Core.char_0x6E;
          Core.char_0x77; Core.char_0x69; Core.char_0x64; Core.char_0x74;
          Core.char_0x68; Core.char_0x3D; Core.char_0x32; Core.char_0x2C;
          Core.char_0x77; Core.char_0x65; Core.char_0x69; Core.char_0x67;
          Core.char_0x68; Core.char_0x74; Core.char_0x3D; Core.char_0x31;
          Core.char_0x30; Core.char_0x2C; Core.char_0x6C; Core.char_0x61;
          Core.char_0x62; Core.char_0x65; Core.char_0x6C; Core.char_0x3D] @
          dq @ [Core.char_0x63; Core.char_0x61; Core.char_0x6C; Core.char_0x6C;
                 Core.char_0x20] @
                 callee @
                   [Core.char_0x28] @
                     (let Core.CallEdge (_, _, es) = a in
                       Core.join_source [Core.char_0x2C; Core.char_0x20]
                         (Core.map Core.string_of_aexp es)) @
                       [Core.char_0x29] @ dq
      | CombineEdge (_, dst, ret) ->
        [Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
          Core.char_0x65; Core.char_0x3D; Core.char_0x64; Core.char_0x61;
          Core.char_0x73; Core.char_0x68; Core.char_0x65; Core.char_0x64;
          Core.char_0x2C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
          Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x62;
          Core.char_0x6C; Core.char_0x75; Core.char_0x65; Core.char_0x2C;
          Core.char_0x63; Core.char_0x6F; Core.char_0x6E; Core.char_0x73;
          Core.char_0x74; Core.char_0x72; Core.char_0x61; Core.char_0x69;
          Core.char_0x6E; Core.char_0x74; Core.char_0x3D; Core.char_0x66;
          Core.char_0x61; Core.char_0x6C; Core.char_0x73; Core.char_0x65;
          Core.char_0x2C; Core.char_0x78; Core.char_0x6C; Core.char_0x61;
          Core.char_0x62; Core.char_0x65; Core.char_0x6C; Core.char_0x3D] @
          dq @ (match (dst, ret)
                 with (None, _) ->
                   [Core.char_0x72; Core.char_0x65; Core.char_0x73;
                     Core.char_0x75; Core.char_0x6D; Core.char_0x65]
                 | (Some xa, None) ->
                   [Core.char_0x72; Core.char_0x65; Core.char_0x73;
                     Core.char_0x75; Core.char_0x6D; Core.char_0x65;
                     Core.char_0x20; Core.char_0x2F; Core.char_0x20] @
                     Core.explode xa
                 | (Some xa, Some r) ->
                   [Core.char_0x72; Core.char_0x65; Core.char_0x73;
                     Core.char_0x75; Core.char_0x6D; Core.char_0x65;
                     Core.char_0x20; Core.char_0x2F; Core.char_0x20] @
                     Core.explode xa @
                       [Core.char_0x20; Core.char_0x3A; Core.char_0x3D;
                         Core.char_0x20] @
                         Core.explode r) @
                 dq
      | CallToReturnEdge _ ->
        [Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
          Core.char_0x65; Core.char_0x3D; Core.char_0x64; Core.char_0x6F;
          Core.char_0x74; Core.char_0x74; Core.char_0x65; Core.char_0x64;
          Core.char_0x2C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
          Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x67;
          Core.char_0x72; Core.char_0x61; Core.char_0x79; Core.char_0x34;
          Core.char_0x30; Core.char_0x2C; Core.char_0x63; Core.char_0x6F;
          Core.char_0x6E; Core.char_0x73; Core.char_0x74; Core.char_0x72;
          Core.char_0x61; Core.char_0x69; Core.char_0x6E; Core.char_0x74;
          Core.char_0x3D; Core.char_0x66; Core.char_0x61; Core.char_0x6C;
          Core.char_0x73; Core.char_0x65; Core.char_0x2C; Core.char_0x6C;
          Core.char_0x61; Core.char_0x62; Core.char_0x65; Core.char_0x6C;
          Core.char_0x3D] @
          dq @ [Core.char_0x72; Core.char_0x65; Core.char_0x73; Core.char_0x75;
                 Core.char_0x6D; Core.char_0x65; Core.char_0x2D; Core.char_0x73;
                 Core.char_0x69; Core.char_0x74; Core.char_0x65] @
                 dq
      | GlobalReadEdge ->
        [Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
          Core.char_0x65; Core.char_0x3D; Core.char_0x64; Core.char_0x6F;
          Core.char_0x74; Core.char_0x74; Core.char_0x65; Core.char_0x64;
          Core.char_0x2C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
          Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x67;
          Core.char_0x72; Core.char_0x61; Core.char_0x79; Core.char_0x2C;
          Core.char_0x6C; Core.char_0x61; Core.char_0x62; Core.char_0x65;
          Core.char_0x6C; Core.char_0x3D] @
          dq @ [Core.char_0x72; Core.char_0x65; Core.char_0x61; Core.char_0x64;
                 Core.char_0x20; Core.char_0x67; Core.char_0x6C; Core.char_0x6F;
                 Core.char_0x62; Core.char_0x61; Core.char_0x6C] @
                 dq
      | GlobalWriteEdge ->
        [Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
          Core.char_0x65; Core.char_0x3D; Core.char_0x64; Core.char_0x6F;
          Core.char_0x74; Core.char_0x74; Core.char_0x65; Core.char_0x64;
          Core.char_0x2C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
          Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x67;
          Core.char_0x72; Core.char_0x61; Core.char_0x79; Core.char_0x2C;
          Core.char_0x6C; Core.char_0x61; Core.char_0x62; Core.char_0x65;
          Core.char_0x6C; Core.char_0x3D] @
          dq @ [Core.char_0x77; Core.char_0x72; Core.char_0x69; Core.char_0x74;
                 Core.char_0x65; Core.char_0x20; Core.char_0x67; Core.char_0x6C;
                 Core.char_0x6F; Core.char_0x62; Core.char_0x61;
                 Core.char_0x6C] @
                 dq);;

let rec analysis_edge_dot _A _B
  cfg g ns e =
    (let (src, (kind, dst)) = e in
      [Core.char_0x20; Core.char_0x20] @
        analysis_node_id _A _B cfg ns src @
          [Core.char_0x20; Core.char_0x2D; Core.char_0x3E; Core.char_0x20] @
            analysis_node_id _A _B cfg ns dst @
              [Core.char_0x20; Core.char_0x5B] @
                analysis_edge_attrs g kind @
                  [Core.char_0x5D; Core.char_0x3B] @ nl);;

let rec analysis_graph_to_dot _A _B
  cfg g sol graph =
    (let (clusters, (ns, es)) = graph in
      (if analysis_graph_wf _A _B graph
        then [Core.char_0x64; Core.char_0x69; Core.char_0x67; Core.char_0x72;
               Core.char_0x61; Core.char_0x70; Core.char_0x68; Core.char_0x20;
               Core.char_0x41; Core.char_0x6E; Core.char_0x61; Core.char_0x6C;
               Core.char_0x79; Core.char_0x73; Core.char_0x69; Core.char_0x73;
               Core.char_0x43; Core.char_0x46; Core.char_0x47; Core.char_0x20;
               Core.char_0x7B] @
               nl @ [Core.char_0x20; Core.char_0x20; Core.char_0x67;
                      Core.char_0x72; Core.char_0x61; Core.char_0x70;
                      Core.char_0x68; Core.char_0x20; Core.char_0x5B;
                      Core.char_0x72; Core.char_0x61; Core.char_0x6E;
                      Core.char_0x6B; Core.char_0x64; Core.char_0x69;
                      Core.char_0x72; Core.char_0x3D; Core.char_0x54;
                      Core.char_0x42; Core.char_0x2C; Core.char_0x6E;
                      Core.char_0x65; Core.char_0x77; Core.char_0x72;
                      Core.char_0x61; Core.char_0x6E; Core.char_0x6B;
                      Core.char_0x3D; Core.char_0x74; Core.char_0x72;
                      Core.char_0x75; Core.char_0x65; Core.char_0x2C;
                      Core.char_0x73; Core.char_0x70; Core.char_0x6C;
                      Core.char_0x69; Core.char_0x6E; Core.char_0x65;
                      Core.char_0x73; Core.char_0x3D; Core.char_0x70;
                      Core.char_0x6F; Core.char_0x6C; Core.char_0x79;
                      Core.char_0x6C; Core.char_0x69; Core.char_0x6E;
                      Core.char_0x65; Core.char_0x2C; Core.char_0x6E;
                      Core.char_0x6F; Core.char_0x64; Core.char_0x65;
                      Core.char_0x73; Core.char_0x65; Core.char_0x70;
                      Core.char_0x3D; Core.char_0x30; Core.char_0x2E;
                      Core.char_0x35; Core.char_0x2C; Core.char_0x72;
                      Core.char_0x61; Core.char_0x6E; Core.char_0x6B;
                      Core.char_0x73; Core.char_0x65; Core.char_0x70;
                      Core.char_0x3D; Core.char_0x30; Core.char_0x2E;
                      Core.char_0x37; Core.char_0x2C; Core.char_0x66;
                      Core.char_0x6F; Core.char_0x6E; Core.char_0x74;
                      Core.char_0x6E; Core.char_0x61; Core.char_0x6D;
                      Core.char_0x65; Core.char_0x3D] @
                      dq @ [Core.char_0x4D; Core.char_0x65; Core.char_0x6E;
                             Core.char_0x6C; Core.char_0x6F] @
                             dq @ [Core.char_0x5D; Core.char_0x3B] @
                                    nl @ [Core.char_0x20; Core.char_0x20;
   Core.char_0x6E; Core.char_0x6F; Core.char_0x64; Core.char_0x65;
   Core.char_0x20; Core.char_0x5B; Core.char_0x73; Core.char_0x68;
   Core.char_0x61; Core.char_0x70; Core.char_0x65; Core.char_0x3D;
   Core.char_0x62; Core.char_0x6F; Core.char_0x78; Core.char_0x2C;
   Core.char_0x73; Core.char_0x74; Core.char_0x79; Core.char_0x6C;
   Core.char_0x65; Core.char_0x3D; Core.char_0x66; Core.char_0x69;
   Core.char_0x6C; Core.char_0x6C; Core.char_0x65; Core.char_0x64;
   Core.char_0x2C; Core.char_0x66; Core.char_0x69; Core.char_0x6C;
   Core.char_0x6C; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
   Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x6C;
   Core.char_0x69; Core.char_0x67; Core.char_0x68; Core.char_0x74;
   Core.char_0x67; Core.char_0x72; Core.char_0x65; Core.char_0x65;
   Core.char_0x6E; Core.char_0x2C; Core.char_0x66; Core.char_0x6F;
   Core.char_0x6E; Core.char_0x74; Core.char_0x6E; Core.char_0x61;
   Core.char_0x6D; Core.char_0x65; Core.char_0x3D] @
   dq @ [Core.char_0x4D; Core.char_0x65; Core.char_0x6E; Core.char_0x6C;
          Core.char_0x6F] @
          dq @ [Core.char_0x5D; Core.char_0x3B] @
                 nl @ [Core.char_0x20; Core.char_0x20; Core.char_0x65;
                        Core.char_0x64; Core.char_0x67; Core.char_0x65;
                        Core.char_0x20; Core.char_0x5B; Core.char_0x66;
                        Core.char_0x6F; Core.char_0x6E; Core.char_0x74;
                        Core.char_0x6E; Core.char_0x61; Core.char_0x6D;
                        Core.char_0x65; Core.char_0x3D] @
                        dq @ [Core.char_0x4D; Core.char_0x65; Core.char_0x6E;
                               Core.char_0x6C; Core.char_0x6F] @
                               dq @ [Core.char_0x2C; Core.char_0x66;
                                      Core.char_0x6F; Core.char_0x6E;
                                      Core.char_0x74; Core.char_0x73;
                                      Core.char_0x69; Core.char_0x7A;
                                      Core.char_0x65; Core.char_0x3D;
                                      Core.char_0x31; Core.char_0x30;
                                      Core.char_0x2C; Core.char_0x61;
                                      Core.char_0x72; Core.char_0x72;
                                      Core.char_0x6F; Core.char_0x77;
                                      Core.char_0x73; Core.char_0x69;
                                      Core.char_0x7A; Core.char_0x65;
                                      Core.char_0x3D; Core.char_0x30;
                                      Core.char_0x2E; Core.char_0x38;
                                      Core.char_0x5D; Core.char_0x3B] @
                                      nl @
Core.maps (analysis_cluster_dot _A _B cfg g clusters ns es sol) clusters @
  Core.maps (analysis_edge_dot _A _B cfg g ns) es @ [Core.char_0x7D] @ nl
        else [Core.char_0x64; Core.char_0x69; Core.char_0x67; Core.char_0x72;
               Core.char_0x61; Core.char_0x70; Core.char_0x68; Core.char_0x20;
               Core.char_0x41; Core.char_0x6E; Core.char_0x61; Core.char_0x6C;
               Core.char_0x79; Core.char_0x73; Core.char_0x69; Core.char_0x73;
               Core.char_0x43; Core.char_0x46; Core.char_0x47; Core.char_0x20;
               Core.char_0x7B; Core.char_0x20; Core.char_0x69; Core.char_0x6E;
               Core.char_0x76; Core.char_0x61; Core.char_0x6C; Core.char_0x69;
               Core.char_0x64; Core.char_0x5F; Core.char_0x67; Core.char_0x72;
               Core.char_0x61; Core.char_0x70; Core.char_0x68; Core.char_0x20;
               Core.char_0x7D] @
               nl));;

let rec analysis_call_to_return_edges _A
  cfg g covered =
    Core.maps
      (fun src_ctx ->
        Core.maps
          (fun a ->
            (match a with (_, (_, (Core.Statement _, _))) -> []
              | (call, (_, (Core.FunctionEntry p, cont))) ->
                (if Core.equal_cfg_nodea (Core.fst src_ctx) call &&
                      Core.membera (Core.equal_prod Core.equal_cfg_node _A)
                        covered (cont, Core.snd src_ctx)
                  then [(LocalNode (call, Core.snd src_ctx),
                          (CallToReturnEdge p,
                            LocalNode (cont, Core.snd src_ctx)))]
                  else [])
              | (_, (_, (Core.FunctionResult _, _))) -> []))
          (Core.cfg_calls_list g))
      covered;;

let rec analysis_context_clusters _A
  cfg covered =
    Core.remdups (equal_analysis_cluster _A)
      (Core.map
        (fun pc -> ContextCluster (owner_of cfg (Core.fst pc), Core.snd pc))
        covered);;

let rec analysis_source_cluster
  ns = (if Core.list_ex
             (fun a ->
               (match a with LocalNode (_, _) -> false | GlobalNode _ -> false
                 | SourceNode _ -> true))
             ns
         then [SourceCluster] else []);;

let rec analysis_global_cluster
  ns = (if Core.list_ex
             (fun a ->
               (match a with LocalNode (_, _) -> false | GlobalNode _ -> true
                 | SourceNode _ -> false))
             ns
         then [GlobalCluster] else []);;

let rec route
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = route;;

let rec analysis_combine_edges _A
  cfg g covered sol =
    Core.maps
      (fun src_ctx ->
        Core.maps
          (fun a ->
            (match a with (_, (_, (Core.Statement _, _))) -> []
              | (call, (ca, (Core.FunctionEntry p, cont))) ->
                (if Core.equal_cfg_nodea (Core.fst src_ctx) call
                  then (let callee_ctx =
                          route cfg call (Core.snd src_ctx) ca
                            (local_of cfg (sol (Core.Inl src_ctx)))
                          in
                        let result = Core.FunctionResult p in
                         (if Core.membera
                               (Core.equal_prod Core.equal_cfg_node _A) covered
                               (result, callee_ctx) &&
                               Core.membera
                                 (Core.equal_prod Core.equal_cfg_node _A)
                                 covered (cont, Core.snd src_ctx)
                           then [(LocalNode (result, callee_ctx),
                                   (CombineEdge
                                      (call,
(let Core.CallEdge (dst, _, _) = ca in dst), return_slot_for_pp cfg result),
                                     LocalNode (cont, Core.snd src_ctx)))]
                           else []))
                  else [])
              | (_, (_, (Core.FunctionResult _, _))) -> []))
          (Core.cfg_calls_list g))
      covered;;

let rec source_text
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = source_text;;

let rec analysis_source_nodes
  cfg = (match source_text cfg with None -> [] | Some src -> [SourceNode src]);;

let rec show_internal_globals
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = show_internal_globals;;

let rec is_shared_global
  (Analysis_graph_config_ext
    (local_of, route, show_context, locals_for_pp, return_slot_for_pp,
      globals_to_show, show_local, format_return, show_global, show_global_key,
      is_shared_global, show_internal_globals, owner_of, cluster_label,
      source_text, node_annotation, more))
    = is_shared_global;;

let rec visible_global
  cfg k = is_shared_global cfg k || show_internal_globals cfg;;

let rec rendered_global
  cfg sol k =
    visible_global cfg k &&
      not (Core.null
            (show_global cfg k (globals_to_show cfg) (sol (Core.Inr k))));;

let rec analysis_global_nodes _B
  cfg sol keys =
    Core.map_filter
      (fun x ->
        (if rendered_global cfg sol x then Some (GlobalNode x) else None))
      (Core.remdups _B keys);;

let rec analysis_intra_edges _A
  g covered =
    Core.maps
      (fun src_ctx ->
        Core.maps
          (fun (u, (a, v)) ->
            (if Core.equal_cfg_nodea (Core.fst src_ctx) u &&
                  Core.membera (Core.equal_prod Core.equal_cfg_node _A) covered
                    (v, Core.snd src_ctx)
              then [(LocalNode (u, Core.snd src_ctx),
                      (IntraEdge a, LocalNode (v, Core.snd src_ctx)))]
              else []))
          (Core.cfg_intra_list g))
      covered;;

let rec analysis_enter_edges _A
  cfg g covered sol =
    Core.maps
      (fun src_ctx ->
        Core.maps
          (fun (u, (ca, (entry, _))) ->
            (if Core.equal_cfg_nodea (Core.fst src_ctx) u
              then (let callee_ctx =
                      route cfg u (Core.snd src_ctx) ca
                        (local_of cfg (sol (Core.Inl src_ctx)))
                      in
                     (if Core.membera (Core.equal_prod Core.equal_cfg_node _A)
                           covered (entry, callee_ctx)
                       then [(LocalNode (u, Core.snd src_ctx),
                               (EnterEdge (owner_of cfg entry, ca),
                                 LocalNode (entry, callee_ctx)))]
                       else []))
              else []))
          (Core.cfg_calls_list g))
      covered;;

let rec covered_local_nodes
  covered = Core.map (fun pc -> LocalNode (Core.fst pc, Core.snd pc)) covered;;

let rec build_analysis_graph_parts _A _B
  cfg g covered global_keys sol =
    (let locals = covered_local_nodes covered in
     let globals = analysis_global_nodes _B cfg sol global_keys in
     let sources = analysis_source_nodes cfg in
     let ns = locals @ globals @ sources in
      (analysis_context_clusters _A cfg covered @
         analysis_global_cluster ns @ analysis_source_cluster ns,
        (ns, analysis_intra_edges _A g covered @
               analysis_enter_edges _A cfg g covered sol @
                 analysis_combine_edges _A cfg g covered sol @
                   analysis_call_to_return_edges _A cfg g covered)));;

let rec analysis_global_domain
  = function [] -> []
    | Core.Inl pc :: domain -> analysis_global_domain domain
    | Core.Inr k :: domain -> k :: analysis_global_domain domain;;

let rec analysis_local_domain
  = function [] -> []
    | Core.Inl pc :: domain -> pc :: analysis_local_domain domain
    | Core.Inr k :: domain -> analysis_local_domain domain;;

let rec build_analysis_graph _A _B
  cfg g domain sol =
    build_analysis_graph_parts _A _B cfg g
      (analysis_local_domain
        (Core.remdups
          (Core.equal_sum (Core.equal_prod Core.equal_cfg_node _A) _B) domain))
      (analysis_global_domain
        (Core.remdups
          (Core.equal_sum (Core.equal_prod Core.equal_cfg_node _A) _B) domain))
      sol;;

let rec contextual_analysis_dot _A _B
  cfg g domain sol =
    analysis_graph_to_dot _A _B cfg g sol
      (build_analysis_graph _A _B cfg g domain sol);;

let rec compiled_proc_owner
  pi x1 n k = match pi, x1, n, k with pi, [], n, k -> None
    | pi, p :: ps, n, k ->
        (match pi p with None -> compiled_proc_owner pi ps n k
          | Some decl ->
            (let (na, (_, _)) = Core.compile_proc pi p decl n in
              (if Core.less_eq_nat n k && Core.less_nat k na then Some p
                else compiled_proc_owner pi ps na k)));;

let rec compiled_owner_of
  pi ps mnm main p =
    (match p
      with Core.Statement k ->
        (match compiled_proc_owner pi ps Core.zero_nat k with None -> mnm
          | Some owner -> owner)
      | Core.FunctionEntry owner -> owner
      | Core.FunctionResult owner -> owner);;

let rec raw_cfg_graph_config
  pi ps mnm main annotate =
    Analysis_graph_config_ext
      (Core.id, (fun _ _ _ _ -> ()), (fun _ -> []), (fun _ -> []),
        (fun _ -> None), [], (fun _ _ _ _ -> []), (fun _ _ _ _ -> []),
        (fun _ _ _ -> []), (fun _ -> []), (fun _ -> false), false,
        Core.comp Core.explode (compiled_owner_of pi ps mnm main),
        (fun owner _ -> owner),
        Some (Core.pretty_string_of_program pi ps main []), annotate, ());;

let rec raw_cfg_dot
  pi ps mnm main annotate =
    (let g = Core.compile_prog pi ps mnm main in
     let cfg = raw_cfg_graph_config pi ps mnm main annotate in
     let domain = contextual_graph_domain g (fun _ -> [()]) in
      contextual_analysis_dot Core.equal_unit Core.equal_unit cfg g domain
        (fun _ -> ()));;

let rec raw_cfg_dot_lit
  pi ps mnm main annotate = Core.implode (raw_cfg_dot pi ps mnm main annotate);;

let rec canonical_node_block _A _B
  cfg g sol ns n =
    (match contextual_node_label_lines cfg g sol n
      with [] ->
        [Core.char_0x20; Core.char_0x20] @
          analysis_node_id _A _B cfg ns n @ [Core.char_0x3A] @ nl
      | first :: rest ->
        [Core.char_0x20; Core.char_0x20] @
          analysis_node_id _A _B cfg ns n @
            [Core.char_0x3A; Core.char_0x20] @
              first @
                nl @ Core.maps
                       (fun line ->
                         [Core.char_0x20; Core.char_0x20; Core.char_0x20;
                           Core.char_0x20; Core.char_0x20; Core.char_0x20] @
                           line @ nl)
                       rest);;

let rec canonical_edge_kind_text
  g kind =
    (match kind with IntraEdge a -> source_action_label g a
      | EnterEdge (callee, a) ->
        [Core.char_0x65; Core.char_0x6E; Core.char_0x74; Core.char_0x65;
          Core.char_0x72; Core.char_0x20] @
          callee @
            [Core.char_0x28] @
              (let Core.CallEdge (_, _, es) = a in
                Core.join_source [Core.char_0x2C; Core.char_0x20]
                  (Core.map Core.string_of_aexp es)) @
                [Core.char_0x29]
      | CombineEdge (_, dst, ret) ->
        [Core.char_0x63; Core.char_0x6F; Core.char_0x6D; Core.char_0x62;
          Core.char_0x69; Core.char_0x6E; Core.char_0x65] @
          (match (dst, ret) with (None, _) -> []
            | (Some xa, None) -> [Core.char_0x20] @ Core.explode xa
            | (Some xa, Some r) ->
              [Core.char_0x20] @
                Core.explode xa @
                  [Core.char_0x20; Core.char_0x3A; Core.char_0x3D;
                    Core.char_0x20] @
                    Core.explode r)
      | CallToReturnEdge callee ->
        [Core.char_0x63; Core.char_0x61; Core.char_0x6C; Core.char_0x6C;
          Core.char_0x2D; Core.char_0x74; Core.char_0x6F; Core.char_0x2D;
          Core.char_0x72; Core.char_0x65; Core.char_0x74; Core.char_0x75;
          Core.char_0x72; Core.char_0x6E; Core.char_0x20] @
          Core.explode callee
      | GlobalReadEdge ->
        [Core.char_0x72; Core.char_0x65; Core.char_0x61; Core.char_0x64;
          Core.char_0x20; Core.char_0x67; Core.char_0x6C; Core.char_0x6F;
          Core.char_0x62; Core.char_0x61; Core.char_0x6C]
      | GlobalWriteEdge ->
        [Core.char_0x77; Core.char_0x72; Core.char_0x69; Core.char_0x74;
          Core.char_0x65; Core.char_0x20; Core.char_0x67; Core.char_0x6C;
          Core.char_0x6F; Core.char_0x62; Core.char_0x61; Core.char_0x6C]);;

let rec analysis_graph_to_canonical_text _A _B
  cfg g sol graph =
    (let (clusters, (ns, es)) = graph in
     let clustersa =
       Core.filtera (fun c -> not (equal_analysis_clustera _A c SourceCluster))
         clusters
       in
     let nsa =
       Core.filtera
         (fun a ->
           (match a with LocalNode (_, _) -> true | GlobalNode _ -> true
             | SourceNode _ -> false))
         ns
       in
      [Core.char_0x63; Core.char_0x6C; Core.char_0x75; Core.char_0x73;
        Core.char_0x74; Core.char_0x65; Core.char_0x72; Core.char_0x73;
        Core.char_0x3A] @
        nl @ Core.maps
               (fun c ->
                 [Core.char_0x20; Core.char_0x20] @
                   analysis_cluster_id _A clusters c @
                     [Core.char_0x3A] @
                       nl @ Core.maps
                              (fun n ->
                                [Core.char_0x20; Core.char_0x20; Core.char_0x20;
                                  Core.char_0x20] @
                                  analysis_node_id _A _B cfg ns n @ nl)
                              (analysis_nodes_in_cluster _A _B cfg c ns))
               clustersa @
               nl @ [Core.char_0x6E; Core.char_0x6F; Core.char_0x64;
                      Core.char_0x65; Core.char_0x73; Core.char_0x3A] @
                      nl @ Core.maps (canonical_node_block _A _B cfg g sol ns)
                             nsa @
                             nl @ [Core.char_0x65; Core.char_0x64;
                                    Core.char_0x67; Core.char_0x65;
                                    Core.char_0x73; Core.char_0x3A] @
                                    nl @ Core.maps
   (fun (src, (kind, dst)) ->
     [Core.char_0x20; Core.char_0x20] @
       analysis_node_id _A _B cfg ns src @
         [Core.char_0x20; Core.char_0x2D; Core.char_0x3E; Core.char_0x20] @
           analysis_node_id _A _B cfg ns dst @
             [Core.char_0x3A; Core.char_0x20] @
               canonical_edge_kind_text g kind @ nl)
   es);;

let rec contextual_analysis_canonical_text _A _B
  cfg g domain sol =
    analysis_graph_to_canonical_text _A _B cfg g sol
      (build_analysis_graph _A _B cfg g domain sol);;

let rec raw_cfg_canonical_text
  pi ps mnm main annotate =
    (let g = Core.compile_prog pi ps mnm main in
     let cfg = raw_cfg_graph_config pi ps mnm main annotate in
     let domain = contextual_graph_domain g (fun _ -> [()]) in
      contextual_analysis_canonical_text Core.equal_unit Core.equal_unit cfg g
        domain (fun _ -> ()));;

let rec check_result_annotation
  res cnd =
    (match res
      with Core.Check_Proved ->
        Node_Annotation
          ([Core.char_0x63; Core.char_0x68; Core.char_0x65; Core.char_0x63;
             Core.char_0x6B; Core.char_0x20] @
             Core.string_of_bexp cnd,
            [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
              Core.char_0x65; Core.char_0x3D; Core.char_0x62; Core.char_0x6F;
              Core.char_0x78; Core.char_0x2C; Core.char_0x73; Core.char_0x74;
              Core.char_0x79; Core.char_0x6C; Core.char_0x65; Core.char_0x3D;
              Core.char_0x66; Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
              Core.char_0x65; Core.char_0x64; Core.char_0x2C; Core.char_0x66;
              Core.char_0x69; Core.char_0x6C; Core.char_0x6C; Core.char_0x63;
              Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
              Core.char_0x3D; Core.char_0x64; Core.char_0x61; Core.char_0x72;
              Core.char_0x6B; Core.char_0x67; Core.char_0x72; Core.char_0x65;
              Core.char_0x65; Core.char_0x6E; Core.char_0x2C; Core.char_0x66;
              Core.char_0x6F; Core.char_0x6E; Core.char_0x74; Core.char_0x63;
              Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
              Core.char_0x3D; Core.char_0x77; Core.char_0x68; Core.char_0x69;
              Core.char_0x74; Core.char_0x65])
      | Core.Check_Refuted ->
        Node_Annotation
          ([Core.char_0x63; Core.char_0x68; Core.char_0x65; Core.char_0x63;
             Core.char_0x6B; Core.char_0x20] @
             Core.string_of_bexp cnd @
               [Core.char_0x20; Core.char_0x5B; Core.char_0x52; Core.char_0x45;
                 Core.char_0x46; Core.char_0x55; Core.char_0x54; Core.char_0x45;
                 Core.char_0x44; Core.char_0x5D],
            [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
              Core.char_0x65; Core.char_0x3D; Core.char_0x62; Core.char_0x6F;
              Core.char_0x78; Core.char_0x2C; Core.char_0x73; Core.char_0x74;
              Core.char_0x79; Core.char_0x6C; Core.char_0x65; Core.char_0x3D;
              Core.char_0x66; Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
              Core.char_0x65; Core.char_0x64; Core.char_0x2C; Core.char_0x66;
              Core.char_0x69; Core.char_0x6C; Core.char_0x6C; Core.char_0x63;
              Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
              Core.char_0x3D; Core.char_0x72; Core.char_0x65; Core.char_0x64;
              Core.char_0x2C; Core.char_0x66; Core.char_0x6F; Core.char_0x6E;
              Core.char_0x74; Core.char_0x63; Core.char_0x6F; Core.char_0x6C;
              Core.char_0x6F; Core.char_0x72; Core.char_0x3D; Core.char_0x77;
              Core.char_0x68; Core.char_0x69; Core.char_0x74; Core.char_0x65])
      | Core.Check_Unknown ->
        Node_Annotation
          ([Core.char_0x63; Core.char_0x68; Core.char_0x65; Core.char_0x63;
             Core.char_0x6B; Core.char_0x20] @
             Core.string_of_bexp cnd @
               [Core.char_0x20; Core.char_0x5B; Core.char_0x75; Core.char_0x6E;
                 Core.char_0x6B; Core.char_0x6E; Core.char_0x6F; Core.char_0x77;
                 Core.char_0x6E; Core.char_0x5D],
            [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
              Core.char_0x65; Core.char_0x3D; Core.char_0x62; Core.char_0x6F;
              Core.char_0x78; Core.char_0x2C; Core.char_0x73; Core.char_0x74;
              Core.char_0x79; Core.char_0x6C; Core.char_0x65; Core.char_0x3D;
              Core.char_0x66; Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
              Core.char_0x65; Core.char_0x64; Core.char_0x2C; Core.char_0x66;
              Core.char_0x69; Core.char_0x6C; Core.char_0x6C; Core.char_0x63;
              Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
              Core.char_0x3D; Core.char_0x67; Core.char_0x72; Core.char_0x61;
              Core.char_0x79; Core.char_0x37; Core.char_0x30]));;

let rec raw_cfg_canonical_text_lit
  pi ps mnm main annotate =
    Core.implode (raw_cfg_canonical_text pi ps mnm main annotate);;

end;; (*struct Analysis_GraphViz*)

module Example_State_Report_GraphViz : sig
  val string_of_abstract_value : Analyse.abstract_value -> Core.char list
  val program_vars : unit Core.imp_prog_ext -> string list
  val bexp_vnames_list : Core.bexp -> string list
  val full_state_dot_auto :
    Analyse.analysis_kind -> unit Core.imp_prog_ext -> string
  val state_report_dot_auto :
    Analyse.analysis_kind -> unit Core.imp_prog_ext -> string
  val is_bottom_abstract_value : Analyse.abstract_value -> bool
  val entry_state_report_dot_auto : unit Core.imp_prog_ext -> string
  val full_state_graph_snapshot_auto :
    Analyse.analysis_kind -> unit Core.imp_prog_ext -> string
  val entry_state_full_state_dot_auto : unit Core.imp_prog_ext -> string
  val state_report_graph_snapshot_auto :
    Analyse.analysis_kind -> unit Core.imp_prog_ext -> string
  val entry_state_report_graph_snapshot_auto : unit Core.imp_prog_ext -> string
  val entry_state_full_state_graph_snapshot_auto :
    unit Core.imp_prog_ext -> string
end = struct

let rec string_of_abstract_value
  = function Analyse.SignValue s -> Sign_Print.string_of_sign s
    | Analyse.IntervalValue i -> Interval_Print.string_of_ivl i;;

let rec state_line
  f x = Core.explode x @ [Core.char_0x3D] @ string_of_abstract_value (f x);;

let rec report_vars
  report =
    Core.sorted_list_of_set (Core.equal_literal, Core.linorder_literal)
      (Core.sup_seta Core.equal_literal
        (Core.image (fun (_, (c, (_, _))) -> Core.bexp_vnames c)
          (Core.Set report)));;

let rec program_vars
  p = Core.remdups Core.equal_literal
        (Core.maps (Core.scope_vnames_list p)
          (Core.prog_main_name :: Core.prog_procs p));;

let rec analyse_env_for
  kind p =
    (match kind
      with Analyse.Sign_Analysis ->
        (let env = Core.analyse_sign_env_for (Core.declared_global p) p in
          (fun v -> Core.comp (fun a -> Analyse.SignValue a) (env v)))
      | Analyse.Interval_Analysis ->
        (let env =
           Core.analyse_interval_td_at
             (Core.resolved_st_q_is_bot_for Core.computable_domain_ivl
               (Core.declared_global_vars p))
             (Core.declared_global p) (Core.prog_table p) (Core.prog_procs p)
             Core.prog_main_name (Core.prog_main p)
           in
          (fun v ->
            Core.comp (fun a -> Analyse.IntervalValue a)
              (match env v with Core.Bot -> Core.bot_fun Core.bot_ivl
                | Core.Lifted a -> Core.id a))));;

let rec bexp_vnames_list
  b = Core.sorted_list_of_set (Core.equal_literal, Core.linorder_literal)
        (Core.bexp_vnames b);;

let rec entry_state_env_at
  gs is_bot_pred pi ps mnm main =
    (let sol = Core.entry_state_sol gs is_bot_pred pi ps mnm main in
     let sg = Core.entry_state_sg_exec_from_sol gs sol in
      (fun v x ->
        (let ctxs =
           Core.image Core.snd
             (Core.filter (fun (va, _) -> Core.equal_cfg_nodea va v)
               (Core.fst sol))
           in
          Analyse.IntervalValue
            (if Core.equal_set (Core.equal_list Core.equal_ivl) ctxs
                  Core.bot_set
              then (match sg (Core.Inl (v, []))
                     with Core.Bot -> Core.bot_fun Core.bot_ivl
                     | Core.Lifted a -> Core.id a)
                     x
              else Core.sup_fin Core.semilattice_sup_ivl
                     (Core.image
                       (fun ctx ->
                         (match sg (Core.Inl (v, ctx))
                           with Core.Bot -> Core.bot_fun Core.bot_ivl
                           | Core.Lifted a -> Core.id a)
                           x)
                       ctxs)))));;

let rec full_state_node_annotation
  vars env v =
    Some (Analysis_GraphViz.Node_Annotation
           (Analysis_GraphViz.join_gv_nl (Core.map (state_line (env v)) vars),
             [Core.char_0x73; Core.char_0x68; Core.char_0x61; Core.char_0x70;
               Core.char_0x65; Core.char_0x3D; Core.char_0x62; Core.char_0x6F;
               Core.char_0x78; Core.char_0x2C; Core.char_0x73; Core.char_0x74;
               Core.char_0x79; Core.char_0x6C; Core.char_0x65; Core.char_0x3D;
               Core.char_0x66; Core.char_0x69; Core.char_0x6C; Core.char_0x6C;
               Core.char_0x65; Core.char_0x64; Core.char_0x2C; Core.char_0x66;
               Core.char_0x69; Core.char_0x6C; Core.char_0x6C; Core.char_0x63;
               Core.char_0x6F; Core.char_0x6C; Core.char_0x6F; Core.char_0x72;
               Core.char_0x3D; Core.char_0x6C; Core.char_0x69; Core.char_0x67;
               Core.char_0x68; Core.char_0x74; Core.char_0x67; Core.char_0x72;
               Core.char_0x65; Core.char_0x65; Core.char_0x6E]));;

let rec full_state_dot_auto
  kind p =
    Analysis_GraphViz.raw_cfg_dot_lit (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (full_state_node_annotation (program_vars p) (analyse_env_for kind p));;

let rec state_report_node_annotation
  vars report v =
    (match
      Core.find (fun entry -> Core.equal_cfg_nodea (Core.fst entry) v) report
      with None -> None
      | Some (_, (cnd, (res, f))) ->
        (let Analysis_GraphViz.Node_Annotation (lbl, style) =
           Analysis_GraphViz.check_result_annotation res cnd in
          Some (Analysis_GraphViz.Node_Annotation
                 (Analysis_GraphViz.join_gv_nl
                    (lbl :: Core.map (state_line f) vars),
                   style))));;

let rec state_report_dot_auto
  kind p =
    (let report = Analyse.analyse_with_state kind p in
      Analysis_GraphViz.raw_cfg_dot_lit (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (state_report_node_annotation (report_vars report) report));;

let rec is_bottom_abstract_value
  = function Analyse.SignValue s -> Core.is_bot_sign s
    | Analyse.IntervalValue i -> Core.is_bot_ivl i;;

let rec entry_state_report_for_annotation
  p = Core.map
        (fun (v, (cnd, res)) ->
          (v, (cnd, (res, entry_state_env_at (Core.declared_global p)
                            (Core.resolved_st_q_is_bot_for
                              Core.computable_domain_ivl
                              (Core.declared_global_vars p))
                            (Core.prog_table p) (Core.prog_procs p)
                            Core.prog_main_name (Core.prog_main p) v))))
        (Core.entry_state_check_report_prog Core.prog_main_name p);;

let rec entry_state_report_dot_auto
  p = (let report = entry_state_report_for_annotation p in
        Analysis_GraphViz.raw_cfg_dot_lit (Core.prog_table p)
          (Core.prog_procs p) Core.prog_main_name (Core.prog_main p)
          (state_report_node_annotation (report_vars report) report));;

let rec full_state_graph_snapshot_auto
  kind p =
    Analysis_GraphViz.raw_cfg_canonical_text_lit (Core.prog_table p)
      (Core.prog_procs p) Core.prog_main_name (Core.prog_main p)
      (full_state_node_annotation (program_vars p) (analyse_env_for kind p));;

let rec entry_state_full_state_dot_auto
  p = Analysis_GraphViz.raw_cfg_dot_lit (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (full_state_node_annotation (program_vars p)
          (entry_state_env_at (Core.declared_global p)
            (Core.resolved_st_q_is_bot_for Core.computable_domain_ivl
              (Core.declared_global_vars p))
            (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
            (Core.prog_main p)));;

let rec state_report_graph_snapshot_auto
  kind p =
    (let report = Analyse.analyse_with_state kind p in
      Analysis_GraphViz.raw_cfg_canonical_text_lit (Core.prog_table p)
        (Core.prog_procs p) Core.prog_main_name (Core.prog_main p)
        (state_report_node_annotation (report_vars report) report));;

let rec entry_state_report_graph_snapshot_auto
  p = (let report = entry_state_report_for_annotation p in
        Analysis_GraphViz.raw_cfg_canonical_text_lit (Core.prog_table p)
          (Core.prog_procs p) Core.prog_main_name (Core.prog_main p)
          (state_report_node_annotation (report_vars report) report));;

let rec entry_state_full_state_graph_snapshot_auto
  p = Analysis_GraphViz.raw_cfg_canonical_text_lit (Core.prog_table p)
        (Core.prog_procs p) Core.prog_main_name (Core.prog_main p)
        (full_state_node_annotation (program_vars p)
          (entry_state_env_at (Core.declared_global p)
            (Core.resolved_st_q_is_bot_for Core.computable_domain_ivl
              (Core.declared_global_vars p))
            (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
            (Core.prog_main p)));;

end;; (*struct Example_State_Report_GraphViz*)
