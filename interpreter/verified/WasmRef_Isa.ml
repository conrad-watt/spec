module WasmRef_Isa : sig
  type nat = Nat of Z.t
  type num = One | Bit0 of num | Bit1 of num
  val one_nata : nat
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_nat : nat one
  val integer_of_nat : nat -> Z.t
  val times_nata : nat -> nat -> nat
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power = {one_power : 'a one; times_power : 'a times}
  val times_nat : nat times
  val power_nat : nat power
  val less_eq_nat : nat -> nat -> bool
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat ord
  type t = T_i32 | T_i64 | T_f32 | T_f64
  val equal_ta : t -> t -> bool
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val equal_t : t equal
  val eq : 'a equal -> 'a -> 'a -> bool
  val equal_list : 'a equal -> 'a list -> 'a list -> bool
  type tf = Tf of t list * t list
  val equal_tfa : tf -> tf -> bool
  val equal_tf : tf equal
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val zero_f32 : F32Wrapper.t zero
  type 'a wasm_base = {zero_wasm_base : 'a zero}
  val wasm_base_f32 : F32Wrapper.t wasm_base
  type 'a wasm_float =
    {wasm_base_wasm_float : 'a wasm_base; float_neg : 'a -> 'a;
      float_abs : 'a -> 'a; float_ceil : 'a -> 'a; float_floor : 'a -> 'a;
      float_trunc : 'a -> 'a; float_nearest : 'a -> 'a; float_sqrt : 'a -> 'a;
      float_add : 'a -> 'a -> 'a; float_sub : 'a -> 'a -> 'a;
      float_mul : 'a -> 'a -> 'a; float_div : 'a -> 'a -> 'a;
      float_min : 'a -> 'a -> 'a; float_max : 'a -> 'a -> 'a;
      float_copysign : 'a -> 'a -> 'a; float_eq : 'a -> 'a -> bool;
      float_lt : 'a -> 'a -> bool; float_gt : 'a -> 'a -> bool;
      float_le : 'a -> 'a -> bool; float_ge : 'a -> 'a -> bool}
  val float_neg : 'a wasm_float -> 'a -> 'a
  val float_abs : 'a wasm_float -> 'a -> 'a
  val float_ceil : 'a wasm_float -> 'a -> 'a
  val float_floor : 'a wasm_float -> 'a -> 'a
  val float_trunc : 'a wasm_float -> 'a -> 'a
  val float_nearest : 'a wasm_float -> 'a -> 'a
  val float_sqrt : 'a wasm_float -> 'a -> 'a
  val float_add : 'a wasm_float -> 'a -> 'a -> 'a
  val float_sub : 'a wasm_float -> 'a -> 'a -> 'a
  val float_mul : 'a wasm_float -> 'a -> 'a -> 'a
  val float_div : 'a wasm_float -> 'a -> 'a -> 'a
  val float_min : 'a wasm_float -> 'a -> 'a -> 'a
  val float_max : 'a wasm_float -> 'a -> 'a -> 'a
  val float_copysign : 'a wasm_float -> 'a -> 'a -> 'a
  val float_eq : 'a wasm_float -> 'a -> 'a -> bool
  val float_lt : 'a wasm_float -> 'a -> 'a -> bool
  val float_gt : 'a wasm_float -> 'a -> 'a -> bool
  val float_le : 'a wasm_float -> 'a -> 'a -> bool
  val float_ge : 'a wasm_float -> 'a -> 'a -> bool
  val wasm_float_f32 : F32Wrapper.t wasm_float
  val zero_f64 : F64Wrapper.t zero
  val wasm_base_f64 : F64Wrapper.t wasm_base
  val wasm_float_f64 : F64Wrapper.t wasm_float
  val zero_i32 : I32Wrapper.t zero
  type 'a wasm_int =
    {wasm_base_wasm_int : 'a wasm_base; int_clz : 'a -> 'a; int_ctz : 'a -> 'a;
      int_popcnt : 'a -> 'a; int_add : 'a -> 'a -> 'a; int_sub : 'a -> 'a -> 'a;
      int_mul : 'a -> 'a -> 'a; int_div_u : 'a -> 'a -> 'a option;
      int_div_s : 'a -> 'a -> 'a option; int_rem_u : 'a -> 'a -> 'a option;
      int_rem_s : 'a -> 'a -> 'a option; int_and : 'a -> 'a -> 'a;
      int_or : 'a -> 'a -> 'a; int_xor : 'a -> 'a -> 'a;
      int_shl : 'a -> 'a -> 'a; int_shr_u : 'a -> 'a -> 'a;
      int_shr_s : 'a -> 'a -> 'a; int_rotl : 'a -> 'a -> 'a;
      int_rotr : 'a -> 'a -> 'a; int_eqz : 'a -> bool;
      int_eq : 'a -> 'a -> bool; int_lt_u : 'a -> 'a -> bool;
      int_lt_s : 'a -> 'a -> bool; int_gt_u : 'a -> 'a -> bool;
      int_gt_s : 'a -> 'a -> bool; int_le_u : 'a -> 'a -> bool;
      int_le_s : 'a -> 'a -> bool; int_ge_u : 'a -> 'a -> bool;
      int_ge_s : 'a -> 'a -> bool; int_of_nat : nat -> 'a;
      nat_of_int : 'a -> nat}
  val int_clz : 'a wasm_int -> 'a -> 'a
  val int_ctz : 'a wasm_int -> 'a -> 'a
  val int_popcnt : 'a wasm_int -> 'a -> 'a
  val int_add : 'a wasm_int -> 'a -> 'a -> 'a
  val int_sub : 'a wasm_int -> 'a -> 'a -> 'a
  val int_mul : 'a wasm_int -> 'a -> 'a -> 'a
  val int_div_u : 'a wasm_int -> 'a -> 'a -> 'a option
  val int_div_s : 'a wasm_int -> 'a -> 'a -> 'a option
  val int_rem_u : 'a wasm_int -> 'a -> 'a -> 'a option
  val int_rem_s : 'a wasm_int -> 'a -> 'a -> 'a option
  val int_and : 'a wasm_int -> 'a -> 'a -> 'a
  val int_or : 'a wasm_int -> 'a -> 'a -> 'a
  val int_xor : 'a wasm_int -> 'a -> 'a -> 'a
  val int_shl : 'a wasm_int -> 'a -> 'a -> 'a
  val int_shr_u : 'a wasm_int -> 'a -> 'a -> 'a
  val int_shr_s : 'a wasm_int -> 'a -> 'a -> 'a
  val int_rotl : 'a wasm_int -> 'a -> 'a -> 'a
  val int_rotr : 'a wasm_int -> 'a -> 'a -> 'a
  val int_eqz : 'a wasm_int -> 'a -> bool
  val int_eq : 'a wasm_int -> 'a -> 'a -> bool
  val int_lt_u : 'a wasm_int -> 'a -> 'a -> bool
  val int_lt_s : 'a wasm_int -> 'a -> 'a -> bool
  val int_gt_u : 'a wasm_int -> 'a -> 'a -> bool
  val int_gt_s : 'a wasm_int -> 'a -> 'a -> bool
  val int_le_u : 'a wasm_int -> 'a -> 'a -> bool
  val int_le_s : 'a wasm_int -> 'a -> 'a -> bool
  val int_ge_u : 'a wasm_int -> 'a -> 'a -> bool
  val int_ge_s : 'a wasm_int -> 'a -> 'a -> bool
  val int_of_nat : 'a wasm_int -> nat -> 'a
  val nat_of_int : 'a wasm_int -> 'a -> nat
  val wasm_base_i32 : I32Wrapper.t wasm_base
  val wasm_int_i32 : I32Wrapper.t wasm_int
  val zero_i64 : I64Wrapper.t zero
  val wasm_base_i64 : I64Wrapper.t wasm_base
  val wasm_int_i64 : I64Wrapper.t wasm_int
  type mut = T_immut | T_mut
  val equal_muta : mut -> mut -> bool
  val equal_mut : mut equal
  val equal_literal : string equal
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit equal
  val ord_integer : Z.t ord
  type 'a inst_ext =
    Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a
  type v = ConstInt32 of I32Wrapper.t | ConstInt64 of I64Wrapper.t |
    ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t
  type 'a f_ext = F_ext of v list * unit inst_ext * 'a
  type testop = Eqz
  type sx = S | U
  type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx
  type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  type relop = Relop_i of relop_i | Relop_f of relop_f
  type cvtop = Convert | Reinterpret
  type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl
    | Shr of sx | Rotl | Rotr
  type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  type binop = Binop_i of binop_i | Binop_f of binop_f
  type unop_i = Clz | Ctz | Popcnt
  type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
  type unop = Unop_i of unop_i | Unop_f of unop_f
  type tp = Tp_i8 | Tp_i16 | Tp_i32
  type b_e = Unreachable | Nop | Drop | Select | Block of tf * b_e list |
    Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of nat |
    Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
    Call_indirect of nat | Get_local of nat | Set_local of nat |
    Tee_local of nat | Get_global of nat | Set_global of nat |
    Load of t * (tp * sx) option * nat * nat |
    Store of t * tp option * nat * nat | Current_memory | Grow_memory |
    EConst of v | Unop of t * unop | Binop of t * binop | Testop of t * testop |
    Relop of t * relop | Cvtop of t * cvtop * t * sx option
  type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list
    | Frame of nat * unit f_ext * e list
  type 'a global_ext = Global_ext of mut * v * 'a
  type mem_rep = Abs_mem_rep of ImplWrapper.byte list
  type cl = Func_native of unit inst_ext * tf * t list * b_e list |
    Func_host of tf * host
  and 'a s_ext =
    S_ext of
      cl list * ((nat option) list * nat option) list *
        (mem_rep * nat option) list * unit global_ext list * 'a
  and host = Abs_host of (unit s_ext * v list -> (unit s_ext * v list) option)
  type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  and 'a pred = Seq of (unit -> 'a seq)
  type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
    Ext_glob of nat
  type 'a tg_ext = Tg_ext of mut * t * 'a
  type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a
  type imp_desc = Imp_func of nat | Imp_tab of unit limit_t_ext |
    Imp_mem of unit limit_t_ext | Imp_glob of unit tg_ext
  type 'a module_import_ext =
    Module_import_ext of string * string * imp_desc * 'a
  type 'a module_export_ext = Module_export_ext of string * v_ext * 'a
  type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a
  type 'a module_elem_ext = Module_elem_ext of nat * b_e list * nat list * 'a
  type 'a module_data_ext =
    Module_data_ext of nat * b_e list * ImplWrapper.byte list * 'a
  type 'a m_ext =
    M_ext of
      tf list * (nat * (t list * b_e list)) list * unit limit_t_ext list *
        unit limit_t_ext list * unit module_glob_ext list *
        unit module_elem_ext list * unit module_data_ext list * nat option *
        unit module_import_ext list * unit module_export_ext list * 'a
  type res_crash = CError | CExhaustion
  type res = RCrash of res_crash | RTrap | RValue of v list
  type extern_t = Te_func of tf | Te_tab of unit limit_t_ext |
    Te_mem of unit limit_t_ext | Te_glob of unit tg_ext
  type ct = TAny | TSome of t
  type res_step = RSCrash of res_crash | RSBreak of nat * v list |
    RSReturn of v list | RSNormal of v list * e list
  type checker_type = TopType of ct list | Type of t list | Bot
  type 'a t_context_ext =
    T_context_ext of
      tf list * tf list * unit tg_ext list * unit limit_t_ext list *
        unit limit_t_ext list * t list * (t list) list * (t list) option * 'a
  val plus_nat : nat -> nat -> nat
  val suc : nat -> nat
  val max : 'a ord -> 'a -> 'a -> 'a
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val nth : 'a list -> nat -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val upt : nat -> nat -> nat list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val drop : nat -> 'a list -> 'a list
  val null : 'a list -> bool
  val last : 'a list -> 'a
  val take_tr : nat -> 'a list -> 'a list -> 'a list
  val take : nat -> 'a list -> 'a list
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val those : ('a option) list -> ('a list) option
  val member : 'a equal -> 'a list -> 'a -> bool
  val distinct : 'a equal -> 'a list -> bool
  val map : ('a -> 'b) -> 'a list -> 'b list
  val nat_of_integer : Z.t -> nat
  val ki64 : nat
  val replicate_tr : nat -> 'a -> 'a list -> 'a list
  val replicate : nat -> 'a -> 'a list
  val is_none : 'a option -> bool
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val apply : ('a -> 'b pred) -> 'a seq -> 'b seq
  val gen_length : nat -> 'a list -> nat
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val eval : 'a equal -> 'a pred -> 'a -> bool
  val membera : 'a equal -> 'a seq -> 'a -> bool
  val holds : unit pred -> bool
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_integer : Z.t -> Z.t -> Z.t * Z.t
  val fst : 'a * 'b -> 'a
  val divide_integer : Z.t -> Z.t -> Z.t
  val divide_nat : nat -> nat -> nat
  val size_list : 'a list -> nat
  val mem_rep_length : mem_rep -> nat
  val mem_length : mem_rep * nat option -> nat
  val mem_size : mem_rep * nat option -> nat
  val pred_option : ('a -> bool) -> 'a option -> bool
  val l_min : 'a limit_t_ext -> nat
  val l_max : 'a limit_t_ext -> nat option
  val limits_compat : 'a limit_t_ext -> 'b limit_t_ext -> bool
  val snd : 'a * 'b -> 'b
  val mem_max : mem_rep * nat option -> nat option
  val mem_typing : mem_rep * nat option -> 'a limit_t_ext -> bool
  val tab_typing : (nat option) list * nat option -> 'a limit_t_ext -> bool
  val bytes_replicate : nat -> ImplWrapper.byte -> ImplWrapper.byte list
  val mem_rep_mk : nat -> mem_rep
  val mem_mk : unit limit_t_ext -> mem_rep * nat option
  val msbyte : ImplWrapper.byte list -> ImplWrapper.byte
  val mems : 'a s_ext -> (mem_rep * nat option) list
  val tabs : 'a s_ext -> ((nat option) list * nat option) list
  val list_update : 'a list -> nat -> 'a -> 'a list
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val typeof : v -> t
  val g_val : 'a global_ext -> v
  val g_mut : 'a global_ext -> mut
  val tg_mut : 'a tg_ext -> mut
  val tg_t : 'a tg_ext -> t
  val glob_typing : 'a global_ext -> 'b tg_ext -> bool
  val funcs : 'a s_ext -> cl list
  val globs : 'a s_ext -> unit global_ext list
  val adjunct : 'a pred -> 'a seq -> 'a seq
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
  val f_inst : 'a f_ext -> unit inst_ext
  val f_locs : 'a f_ext -> v list
  val list_all : ('a -> bool) -> 'a list -> bool
  val memsa : 'a inst_ext -> nat list
  val tabsa : 'a inst_ext -> nat list
  val cvt_i64 : sx option -> v -> I64Wrapper.t option
  val cvt_i32 : sx option -> v -> I32Wrapper.t option
  val cvt_f64 : sx option -> v -> F64Wrapper.t option
  val cvt_f32 : sx option -> v -> F32Wrapper.t option
  val cvt : t -> sx option -> v -> v option
  val select_return_top : ct list -> ct -> ct -> checker_type
  val to_ct_list : t list -> ct list
  val produce : checker_type -> checker_type -> checker_type
  val ct_compat : ct -> ct -> bool
  val ct_prefix : ct list -> ct list -> bool
  val ct_suffix : ct list -> ct list -> bool
  val consume : checker_type -> ct list -> checker_type
  val type_update : checker_type -> ct list -> checker_type -> checker_type
  val type_update_select : checker_type -> checker_type
  val tp_length : tp -> nat
  val t_length : t -> nat
  val is_int_t : t -> bool
  val power : 'a power -> 'a -> nat -> 'a
  val load_store_t_bounds : nat -> tp option -> t -> bool
  val label_update :
    ((t list) list -> (t list) list) -> 'a t_context_ext -> 'a t_context_ext
  val c_types_agree : checker_type -> t list -> bool
  val is_float_t : t -> bool
  val relop_t_agree : relop -> t -> bool
  val binop_t_agree : binop -> t -> bool
  val unop_t_agree : unop -> t -> bool
  val option_projl : ('a * 'b) option -> 'a option
  val types_t : 'a t_context_ext -> tf list
  val equal_bool : bool -> bool -> bool
  val convert_cond : t -> t -> sx option -> bool
  val return : 'a t_context_ext -> (t list) option
  val memory : 'a t_context_ext -> unit limit_t_ext list
  val global : 'a t_context_ext -> unit tg_ext list
  val func_t : 'a t_context_ext -> tf list
  val table : 'a t_context_ext -> unit limit_t_ext list
  val local : 'a t_context_ext -> t list
  val label : 'a t_context_ext -> (t list) list
  val same_lab_h : nat list -> (t list) list -> t list -> (t list) option
  val same_lab : nat list -> (t list) list -> (t list) option
  val is_mut : unit tg_ext -> bool
  val check : unit t_context_ext -> b_e list -> checker_type -> checker_type
  val b_e_type_checker : unit t_context_ext -> b_e list -> tf -> bool
  val check_single : unit t_context_ext -> b_e -> checker_type -> checker_type
  val eq_i_i : 'a equal -> 'a -> 'a -> unit pred
  val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val funcsa : 'a inst_ext -> nat list
  val globsa : 'a inst_ext -> nat list
  val types : 'a inst_ext -> tf list
  val app_rev_tr : 'a list -> 'a list -> 'a list
  val mem_rep_append : mem_rep -> nat -> ImplWrapper.byte -> mem_rep
  val mem_append :
    mem_rep * nat option -> nat -> ImplWrapper.byte -> mem_rep * nat option
  val mem_rep_read_bytes : mem_rep -> nat -> nat -> ImplWrapper.byte list
  val read_bytes : mem_rep * nat option -> nat -> nat -> ImplWrapper.byte list
  val bits : v -> ImplWrapper.byte list
  val load :
    mem_rep * nat option -> nat -> nat -> nat -> (ImplWrapper.byte list) option
  val stab_cl_ind : unit s_ext -> nat -> nat -> nat option
  val stab : unit s_ext -> unit inst_ext -> nat -> nat option
  val mem_rep_write_bytes : mem_rep -> nat -> ImplWrapper.byte list -> mem_rep
  val write_bytes :
    mem_rep * nat option -> nat -> ImplWrapper.byte list -> mem_rep * nat option
  val sglob_ind : unit s_ext -> unit inst_ext -> nat -> nat
  val sglob : unit s_ext -> unit inst_ext -> nat -> unit global_ext
  val takefill : 'a -> nat -> 'a list -> 'a list
  val bytes_takefill :
    ImplWrapper.byte -> nat -> ImplWrapper.byte list -> ImplWrapper.byte list
  val store :
    mem_rep * nat option ->
      nat ->
        nat -> ImplWrapper.byte list -> nat -> (mem_rep * nat option) option
  val m_data : 'a m_ext -> unit module_data_ext list
  val m_elem : 'a m_ext -> unit module_elem_ext list
  val m_mems : 'a m_ext -> unit limit_t_ext list
  val m_tabs : 'a m_ext -> unit limit_t_ext list
  val stypes : unit s_ext -> unit inst_ext -> nat -> tf
  val m_funcs : 'a m_ext -> (nat * (t list * b_e list)) list
  val m_globs : 'a m_ext -> unit module_glob_ext list
  val m_start : 'a m_ext -> nat option
  val m_types : 'a m_ext -> tf list
  val mems_update :
    ((mem_rep * nat option) list -> (mem_rep * nat option) list) ->
      'a s_ext -> 'a s_ext
  val tabs_update :
    (((nat option) list * nat option) list ->
      ((nat option) list * nat option) list) ->
      'a s_ext -> 'a s_ext
  val bitzero : t -> v
  val cl_type : cl -> tf
  val n_zeros : t list -> v list
  val split_vals_e : e list -> v list * e list
  val e_is_trap : e -> bool
  val es_is_trap : e list -> bool
  val rep_host : host -> unit s_ext * v list -> (unit s_ext * v list) option
  val host_apply_impl :
    unit s_ext -> tf -> host -> v list -> (unit s_ext * v list) option
  val wasm_deserialise : ImplWrapper.byte list -> t -> v
  val g_val_update : (v -> v) -> 'a global_ext -> 'a global_ext
  val globs_update :
    (unit global_ext list -> unit global_ext list) -> 'a s_ext -> 'a s_ext
  val supdate_glob_s : unit s_ext -> nat -> v -> unit s_ext
  val supdate_glob : unit s_ext -> unit inst_ext -> nat -> v -> unit s_ext
  val store_packed :
    mem_rep * nat option ->
      nat ->
        nat -> ImplWrapper.byte list -> nat -> (mem_rep * nat option) option
  val types_agree : t -> v -> bool
  val sign_extend : sx -> nat -> ImplWrapper.byte list -> ImplWrapper.byte list
  val load_packed :
    sx -> mem_rep * nat option ->
            nat -> nat -> nat -> nat -> (ImplWrapper.byte list) option
  val app_testop_i : 'a wasm_int -> testop -> 'a -> bool
  val app_testop : testop -> v -> v
  val split_n : v list -> nat -> v list * v list
  val sglob_val : unit s_ext -> unit inst_ext -> nat -> v
  val sfunc_ind : unit inst_ext -> nat -> nat
  val app_relop_i : 'a wasm_int -> relop_i -> 'a -> 'a -> bool
  val app_relop_i_v : relop_i -> v -> v -> v
  val app_relop_f : 'a wasm_float -> relop_f -> 'a -> 'a -> bool
  val app_relop_f_v : relop_f -> v -> v -> v
  val app_relop : relop -> v -> v -> v
  val app_binop_i : 'a wasm_int -> binop_i -> 'a -> 'a -> 'a option
  val app_binop_i_v : binop_i -> v -> v -> v option
  val app_binop_f : 'a wasm_float -> binop_f -> 'a -> 'a -> 'a option
  val app_binop_f_v : binop_f -> v -> v -> v option
  val app_binop : binop -> v -> v -> v option
  val smem_ind : unit s_ext -> unit inst_ext -> nat option
  val mem_grow : mem_rep * nat option -> nat -> (mem_rep * nat option) option
  val app_unop_i : 'a wasm_int -> unop_i -> 'a -> 'a
  val app_unop_i_v : unop_i -> v -> v
  val app_unop_f : 'a wasm_float -> unop_f -> 'a -> 'a
  val app_unop_f_v : unop_f -> v -> v
  val app_unop : unop -> v -> v
  val run_step :
    nat ->
      unit s_ext * (unit f_ext * (v list * e list)) ->
        unit s_ext * (unit f_ext * res_step)
  val run_vs_es :
    nat ->
      nat -> unit s_ext * (unit f_ext * (v list * e list)) -> unit s_ext * res
  val run_v :
    nat -> nat -> unit s_ext * (unit f_ext * e list) -> unit s_ext * res
  val const_expr_p : unit t_context_ext -> b_e -> unit pred
  val const_expr : unit t_context_ext -> b_e -> bool
  val min : 'a ord -> 'a -> 'a -> 'a
  val funcs_update : (cl list -> cl list) -> 'a s_ext -> 'a s_ext
  val m_exports : 'a m_ext -> unit module_export_ext list
  val m_imports : 'a m_ext -> unit module_import_ext list
  val limit_type_checker_p : unit limit_t_ext -> nat -> unit pred
  val limit_typing : unit limit_t_ext -> nat -> bool
  val alloc_Xs :
    (unit s_ext -> 'a -> unit s_ext * nat) ->
      unit s_ext -> 'a list -> unit s_ext * nat list
  val d_init : 'a module_data_ext -> ImplWrapper.byte list
  val d_data : 'a module_data_ext -> nat
  val init_mem :
    unit s_ext -> unit inst_ext -> nat -> unit module_data_ext -> unit s_ext
  val e_init : 'a module_elem_ext -> nat list
  val e_tab : 'a module_elem_ext -> nat
  val init_tab :
    unit s_ext -> unit inst_ext -> nat -> unit module_elem_ext -> unit s_ext
  val external_checker : unit s_ext -> v_ext -> extern_t -> unit pred
  val external_typing : unit s_ext -> v_ext -> extern_t -> bool
  val typing : unit t_context_ext -> b_e list -> tf -> bool
  val alloc_mem : unit s_ext -> unit limit_t_ext -> unit s_ext * nat
  val alloc_tab : unit s_ext -> unit limit_t_ext -> unit s_ext * nat
  val init_mems :
    unit s_ext ->
      unit inst_ext -> nat list -> unit module_data_ext list -> unit s_ext
  val init_tabs :
    unit s_ext ->
      unit inst_ext -> nat list -> unit module_elem_ext list -> unit s_ext
  val export_get_v_ext : unit inst_ext -> v_ext -> v_ext
  val alloc_func :
    unit s_ext -> nat * (t list * b_e list) -> unit inst_ext -> unit s_ext * nat
  val g_type : 'a module_glob_ext -> unit tg_ext
  val alloc_glob : unit s_ext -> unit module_glob_ext * v -> unit s_ext * nat
  val run : unit s_ext * (unit f_ext * e list) -> unit s_ext * res
  val d_off : 'a module_data_ext -> b_e list
  val e_off : 'a module_elem_ext -> b_e list
  val g_init : 'a module_glob_ext -> b_e list
  val local_update : (t list -> t list) -> 'a t_context_ext -> 'a t_context_ext
  val interp_get_v : unit s_ext -> unit inst_ext -> b_e list -> v
  val module_start_type_checker_p : unit t_context_ext -> nat -> unit pred
  val module_start_typing : unit t_context_ext -> nat -> bool
  val return_update :
    ((t list) option -> (t list) option) -> 'a t_context_ext -> 'a t_context_ext
  val e_desc : 'a module_export_ext -> v_ext
  val e_name : 'a module_export_ext -> string
  val i_desc : 'a module_import_ext -> imp_desc
  val interp_get_i32 : unit s_ext -> unit inst_ext -> b_e list -> I32Wrapper.t
  val gather_m_f_type : tf list -> nat * (t list * b_e list) -> tf option
  val module_glob_type_checker :
    unit t_context_ext -> unit module_glob_ext -> bool
  val module_func_type_checker :
    unit t_context_ext -> nat * (t list * b_e list) -> bool
  val module_elem_type_checker :
    unit t_context_ext -> unit module_elem_ext -> bool
  val module_data_type_checker :
    unit t_context_ext -> unit module_data_ext -> bool
  val module_import_typer : tf list -> imp_desc -> extern_t option
  val module_export_typer : unit t_context_ext -> v_ext -> extern_t option
  val module_type_checker : unit m_ext -> (extern_t list * extern_t list) option
  val interp_alloc_module :
    unit s_ext ->
      unit m_ext ->
        v_ext list ->
          v list -> unit s_ext * (unit inst_ext * unit module_export_ext list)
  val interp_instantiate :
    unit s_ext ->
      unit m_ext ->
        v_ext list ->
          ((unit s_ext * (unit inst_ext * unit module_export_ext list)) *
            nat option) option
end = struct

type nat = Nat of Z.t;;

type num = One | Bit0 of num | Bit1 of num;;

let one_nata : nat = Nat (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec integer_of_nat (Nat x) = x;;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type t = T_i32 | T_i64 | T_f32 | T_f64;;

let rec equal_ta x0 x1 = match x0, x1 with T_f32, T_f64 -> false
                   | T_f64, T_f32 -> false
                   | T_i64, T_f64 -> false
                   | T_f64, T_i64 -> false
                   | T_i64, T_f32 -> false
                   | T_f32, T_i64 -> false
                   | T_i32, T_f64 -> false
                   | T_f64, T_i32 -> false
                   | T_i32, T_f32 -> false
                   | T_f32, T_i32 -> false
                   | T_i32, T_i64 -> false
                   | T_i64, T_i32 -> false
                   | T_f64, T_f64 -> true
                   | T_f32, T_f32 -> true
                   | T_i64, T_i64 -> true
                   | T_i32, T_i32 -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_t = ({equal = equal_ta} : t equal);;

let rec eq _A a b = equal _A a b;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

type tf = Tf of t list * t list;;

let rec equal_tfa
  (Tf (x1, x2)) (Tf (y1, y2)) =
    equal_list equal_t x1 y1 && equal_list equal_t x2 y2;;

let equal_tf = ({equal = equal_tfa} : tf equal);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_f32 = ({zero = F32Wrapper.zero} : F32Wrapper.t zero);;

type 'a wasm_base = {zero_wasm_base : 'a zero};;

let wasm_base_f32 = ({zero_wasm_base = zero_f32} : F32Wrapper.t wasm_base);;

type 'a wasm_float =
  {wasm_base_wasm_float : 'a wasm_base; float_neg : 'a -> 'a;
    float_abs : 'a -> 'a; float_ceil : 'a -> 'a; float_floor : 'a -> 'a;
    float_trunc : 'a -> 'a; float_nearest : 'a -> 'a; float_sqrt : 'a -> 'a;
    float_add : 'a -> 'a -> 'a; float_sub : 'a -> 'a -> 'a;
    float_mul : 'a -> 'a -> 'a; float_div : 'a -> 'a -> 'a;
    float_min : 'a -> 'a -> 'a; float_max : 'a -> 'a -> 'a;
    float_copysign : 'a -> 'a -> 'a; float_eq : 'a -> 'a -> bool;
    float_lt : 'a -> 'a -> bool; float_gt : 'a -> 'a -> bool;
    float_le : 'a -> 'a -> bool; float_ge : 'a -> 'a -> bool};;
let float_neg _A = _A.float_neg;;
let float_abs _A = _A.float_abs;;
let float_ceil _A = _A.float_ceil;;
let float_floor _A = _A.float_floor;;
let float_trunc _A = _A.float_trunc;;
let float_nearest _A = _A.float_nearest;;
let float_sqrt _A = _A.float_sqrt;;
let float_add _A = _A.float_add;;
let float_sub _A = _A.float_sub;;
let float_mul _A = _A.float_mul;;
let float_div _A = _A.float_div;;
let float_min _A = _A.float_min;;
let float_max _A = _A.float_max;;
let float_copysign _A = _A.float_copysign;;
let float_eq _A = _A.float_eq;;
let float_lt _A = _A.float_lt;;
let float_gt _A = _A.float_gt;;
let float_le _A = _A.float_le;;
let float_ge _A = _A.float_ge;;

let wasm_float_f32 =
  ({wasm_base_wasm_float = wasm_base_f32; float_neg = F32Wrapper.neg;
     float_abs = F32Wrapper.abs; float_ceil = F32Wrapper.ceil;
     float_floor = F32Wrapper.floor; float_trunc = F32Wrapper.trunc;
     float_nearest = F32Wrapper.nearest; float_sqrt = F32Wrapper.sqrt;
     float_add = F32Wrapper.add; float_sub = F32Wrapper.sub;
     float_mul = F32Wrapper.mul; float_div = F32Wrapper.div;
     float_min = F32Wrapper.min; float_max = F32Wrapper.max;
     float_copysign = F32Wrapper.copysign; float_eq = F32Wrapper.eq;
     float_lt = F32Wrapper.lt; float_gt = F32Wrapper.gt;
     float_le = F32Wrapper.le; float_ge = F32Wrapper.ge}
    : F32Wrapper.t wasm_float);;

let zero_f64 = ({zero = F64Wrapper.zero} : F64Wrapper.t zero);;

let wasm_base_f64 = ({zero_wasm_base = zero_f64} : F64Wrapper.t wasm_base);;

let wasm_float_f64 =
  ({wasm_base_wasm_float = wasm_base_f64; float_neg = F64Wrapper.neg;
     float_abs = F64Wrapper.abs; float_ceil = F64Wrapper.ceil;
     float_floor = F64Wrapper.floor; float_trunc = F64Wrapper.trunc;
     float_nearest = F64Wrapper.nearest; float_sqrt = F64Wrapper.sqrt;
     float_add = F64Wrapper.add; float_sub = F64Wrapper.sub;
     float_mul = F64Wrapper.mul; float_div = F64Wrapper.div;
     float_min = F64Wrapper.min; float_max = F64Wrapper.max;
     float_copysign = F64Wrapper.copysign; float_eq = F64Wrapper.eq;
     float_lt = F64Wrapper.lt; float_gt = F64Wrapper.gt;
     float_le = F64Wrapper.le; float_ge = F64Wrapper.ge}
    : F64Wrapper.t wasm_float);;

let zero_i32 = ({zero = I32Wrapper.zero} : I32Wrapper.t zero);;

type 'a wasm_int =
  {wasm_base_wasm_int : 'a wasm_base; int_clz : 'a -> 'a; int_ctz : 'a -> 'a;
    int_popcnt : 'a -> 'a; int_add : 'a -> 'a -> 'a; int_sub : 'a -> 'a -> 'a;
    int_mul : 'a -> 'a -> 'a; int_div_u : 'a -> 'a -> 'a option;
    int_div_s : 'a -> 'a -> 'a option; int_rem_u : 'a -> 'a -> 'a option;
    int_rem_s : 'a -> 'a -> 'a option; int_and : 'a -> 'a -> 'a;
    int_or : 'a -> 'a -> 'a; int_xor : 'a -> 'a -> 'a; int_shl : 'a -> 'a -> 'a;
    int_shr_u : 'a -> 'a -> 'a; int_shr_s : 'a -> 'a -> 'a;
    int_rotl : 'a -> 'a -> 'a; int_rotr : 'a -> 'a -> 'a; int_eqz : 'a -> bool;
    int_eq : 'a -> 'a -> bool; int_lt_u : 'a -> 'a -> bool;
    int_lt_s : 'a -> 'a -> bool; int_gt_u : 'a -> 'a -> bool;
    int_gt_s : 'a -> 'a -> bool; int_le_u : 'a -> 'a -> bool;
    int_le_s : 'a -> 'a -> bool; int_ge_u : 'a -> 'a -> bool;
    int_ge_s : 'a -> 'a -> bool; int_of_nat : nat -> 'a;
    nat_of_int : 'a -> nat};;
let int_clz _A = _A.int_clz;;
let int_ctz _A = _A.int_ctz;;
let int_popcnt _A = _A.int_popcnt;;
let int_add _A = _A.int_add;;
let int_sub _A = _A.int_sub;;
let int_mul _A = _A.int_mul;;
let int_div_u _A = _A.int_div_u;;
let int_div_s _A = _A.int_div_s;;
let int_rem_u _A = _A.int_rem_u;;
let int_rem_s _A = _A.int_rem_s;;
let int_and _A = _A.int_and;;
let int_or _A = _A.int_or;;
let int_xor _A = _A.int_xor;;
let int_shl _A = _A.int_shl;;
let int_shr_u _A = _A.int_shr_u;;
let int_shr_s _A = _A.int_shr_s;;
let int_rotl _A = _A.int_rotl;;
let int_rotr _A = _A.int_rotr;;
let int_eqz _A = _A.int_eqz;;
let int_eq _A = _A.int_eq;;
let int_lt_u _A = _A.int_lt_u;;
let int_lt_s _A = _A.int_lt_s;;
let int_gt_u _A = _A.int_gt_u;;
let int_gt_s _A = _A.int_gt_s;;
let int_le_u _A = _A.int_le_u;;
let int_le_s _A = _A.int_le_s;;
let int_ge_u _A = _A.int_ge_u;;
let int_ge_s _A = _A.int_ge_s;;
let int_of_nat _A = _A.int_of_nat;;
let nat_of_int _A = _A.nat_of_int;;

let wasm_base_i32 = ({zero_wasm_base = zero_i32} : I32Wrapper.t wasm_base);;

let wasm_int_i32 =
  ({wasm_base_wasm_int = wasm_base_i32; int_clz = I32Wrapper.clz;
     int_ctz = I32Wrapper.ctz; int_popcnt = I32Wrapper.popcnt;
     int_add = I32Wrapper.add; int_sub = I32Wrapper.sub;
     int_mul = I32Wrapper.mul; int_div_u = I32Wrapper.div_u;
     int_div_s = I32Wrapper.div_s; int_rem_u = I32Wrapper.rem_u;
     int_rem_s = I32Wrapper.rem_s; int_and = I32Wrapper.and_;
     int_or = I32Wrapper.or_; int_xor = I32Wrapper.xor;
     int_shl = I32Wrapper.shl; int_shr_u = I32Wrapper.shr_u;
     int_shr_s = I32Wrapper.shr_s; int_rotl = I32Wrapper.rotl;
     int_rotr = I32Wrapper.rotr; int_eqz = I32Wrapper.eqz;
     int_eq = I32Wrapper.eq; int_lt_u = I32Wrapper.lt_u;
     int_lt_s = I32Wrapper.lt_s; int_gt_u = I32Wrapper.gt_u;
     int_gt_s = I32Wrapper.gt_s; int_le_u = I32Wrapper.le_u;
     int_le_s = I32Wrapper.le_s; int_ge_u = I32Wrapper.ge_u;
     int_ge_s = I32Wrapper.ge_s;
     int_of_nat = (fun a -> I32Wrapper.int_of_z (integer_of_nat a));
     nat_of_int = (fun a -> Nat (I32Wrapper.z_of_int a))}
    : I32Wrapper.t wasm_int);;

let zero_i64 = ({zero = I64Wrapper.zero} : I64Wrapper.t zero);;

let wasm_base_i64 = ({zero_wasm_base = zero_i64} : I64Wrapper.t wasm_base);;

let wasm_int_i64 =
  ({wasm_base_wasm_int = wasm_base_i64; int_clz = I64Wrapper.clz;
     int_ctz = I64Wrapper.ctz; int_popcnt = I64Wrapper.popcnt;
     int_add = I64Wrapper.add; int_sub = I64Wrapper.sub;
     int_mul = I64Wrapper.mul; int_div_u = I64Wrapper.div_u;
     int_div_s = I64Wrapper.div_s; int_rem_u = I64Wrapper.rem_u;
     int_rem_s = I64Wrapper.rem_s; int_and = I64Wrapper.and_;
     int_or = I64Wrapper.or_; int_xor = I64Wrapper.xor;
     int_shl = I64Wrapper.shl; int_shr_u = I64Wrapper.shr_u;
     int_shr_s = I64Wrapper.shr_s; int_rotl = I64Wrapper.rotl;
     int_rotr = I64Wrapper.rotr; int_eqz = I64Wrapper.eqz;
     int_eq = I64Wrapper.eq; int_lt_u = I64Wrapper.lt_u;
     int_lt_s = I64Wrapper.lt_s; int_gt_u = I64Wrapper.gt_u;
     int_gt_s = I64Wrapper.gt_s; int_le_u = I64Wrapper.le_u;
     int_le_s = I64Wrapper.le_s; int_ge_u = I64Wrapper.ge_u;
     int_ge_s = I64Wrapper.ge_s;
     int_of_nat = (fun a -> I64Wrapper.int_of_z (integer_of_nat a));
     nat_of_int = (fun a -> Nat (I64Wrapper.z_of_int a))}
    : I64Wrapper.t wasm_int);;

type mut = T_immut | T_mut;;

let rec equal_muta x0 x1 = match x0, x1 with T_immut, T_mut -> false
                     | T_mut, T_immut -> false
                     | T_mut, T_mut -> true
                     | T_immut, T_immut -> true;;

let equal_mut = ({equal = equal_muta} : mut equal);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type 'a inst_ext =
  Inst_ext of tf list * nat list * nat list * nat list * nat list * 'a;;

type v = ConstInt32 of I32Wrapper.t | ConstInt64 of I64Wrapper.t |
  ConstFloat32 of F32Wrapper.t | ConstFloat64 of F64Wrapper.t;;

type 'a f_ext = F_ext of v list * unit inst_ext * 'a;;

type testop = Eqz;;

type sx = S | U;;

type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx;;

type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef;;

type relop = Relop_i of relop_i | Relop_f of relop_f;;

type cvtop = Convert | Reinterpret;;

type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl |
  Shr of sx | Rotl | Rotr;;

type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign;;

type binop = Binop_i of binop_i | Binop_f of binop_f;;

type unop_i = Clz | Ctz | Popcnt;;

type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt;;

type unop = Unop_i of unop_i | Unop_f of unop_f;;

type tp = Tp_i8 | Tp_i16 | Tp_i32;;

type b_e = Unreachable | Nop | Drop | Select | Block of tf * b_e list |
  Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of nat |
  Br_if of nat | Br_table of nat list * nat | Return | Call of nat |
  Call_indirect of nat | Get_local of nat | Set_local of nat | Tee_local of nat
  | Get_global of nat | Set_global of nat |
  Load of t * (tp * sx) option * nat * nat | Store of t * tp option * nat * nat
  | Current_memory | Grow_memory | EConst of v | Unop of t * unop |
  Binop of t * binop | Testop of t * testop | Relop of t * relop |
  Cvtop of t * cvtop * t * sx option;;

type e = Basic of b_e | Trap | Invoke of nat | Label of nat * e list * e list |
  Frame of nat * unit f_ext * e list;;

type 'a global_ext = Global_ext of mut * v * 'a;;

type mem_rep = Abs_mem_rep of ImplWrapper.byte list;;

type cl = Func_native of unit inst_ext * tf * t list * b_e list |
  Func_host of tf * host
and 'a s_ext =
  S_ext of
    cl list * ((nat option) list * nat option) list *
      (mem_rep * nat option) list * unit global_ext list * 'a
and host = Abs_host of (unit s_ext * v list -> (unit s_ext * v list) option);;

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

type v_ext = Ext_func of nat | Ext_tab of nat | Ext_mem of nat |
  Ext_glob of nat;;

type 'a tg_ext = Tg_ext of mut * t * 'a;;

type 'a limit_t_ext = Limit_t_ext of nat * nat option * 'a;;

type imp_desc = Imp_func of nat | Imp_tab of unit limit_t_ext |
  Imp_mem of unit limit_t_ext | Imp_glob of unit tg_ext;;

type 'a module_import_ext =
  Module_import_ext of string * string * imp_desc * 'a;;

type 'a module_export_ext = Module_export_ext of string * v_ext * 'a;;

type 'a module_glob_ext = Module_glob_ext of unit tg_ext * b_e list * 'a;;

type 'a module_elem_ext = Module_elem_ext of nat * b_e list * nat list * 'a;;

type 'a module_data_ext =
  Module_data_ext of nat * b_e list * ImplWrapper.byte list * 'a;;

type 'a m_ext =
  M_ext of
    tf list * (nat * (t list * b_e list)) list * unit limit_t_ext list *
      unit limit_t_ext list * unit module_glob_ext list *
      unit module_elem_ext list * unit module_data_ext list * nat option *
      unit module_import_ext list * unit module_export_ext list * 'a;;

type res_crash = CError | CExhaustion;;

type res = RCrash of res_crash | RTrap | RValue of v list;;

type extern_t = Te_func of tf | Te_tab of unit limit_t_ext |
  Te_mem of unit limit_t_ext | Te_glob of unit tg_ext;;

type ct = TAny | TSome of t;;

type res_step = RSCrash of res_crash | RSBreak of nat * v list |
  RSReturn of v list | RSNormal of v list * e list;;

type checker_type = TopType of ct list | Type of t list | Bot;;

type 'a t_context_ext =
  T_context_ext of
    tf list * tf list * unit tg_ext list * unit limit_t_ext list *
      unit limit_t_ext list * t list * (t list) list * (t list) option * 'a;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nata;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let zero_nat : nat = Nat Z.zero;;

let rec nth
  x0 n = match x0, n with [], n -> failwith "nth"
    | x :: xs, n ->
        (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nata));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nat n zero_nat then x :: xs
          else drop (minus_nat n one_nata) xs);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec take_tr
  n x1 acc_r = match n, x1, acc_r with n, [], acc_r -> rev acc_r
    | n, x :: xs, acc_r ->
        (if equal_nat n zero_nat then rev acc_r
          else take_tr (minus_nat n one_nata) xs (x :: acc_r));;

let rec take n xs = take_tr n xs [];;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> map_option (fun a -> y :: a) (those xs));;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> eq _A x y || member _A xs y;;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (member _A xs x) && distinct _A xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let ki64 : nat = nat_of_integer (Z.of_int 65536);;

let rec replicate_tr
  n x acc =
    (if equal_nat n zero_nat then acc
      else replicate_tr (minus_nat n one_nata) x (x :: acc));;

let rec replicate n x = replicate_tr n x [];;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec eval _A (Seq f) = membera _A (f ())
and membera _A xa0 x = match xa0, x with Empty, x -> false
                 | Insert (y, p), x -> eq _A x y || eval _A p x
                 | Join (p, xq), x -> eval _A p x || membera _A xq x;;

let rec holds p = eval equal_unit p ();;

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

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec size_list x = gen_length zero_nat x;;

let rec mem_rep_length (Abs_mem_rep x) = size_list x;;

let rec mem_length m = mem_rep_length (fst m);;

let rec mem_size m = divide_nat (mem_length m) ki64;;

let rec pred_option p x1 = match p, x1 with p, Some a -> p a
                      | p, None -> true;;

let rec l_min (Limit_t_ext (l_min, l_max, more)) = l_min;;

let rec l_max (Limit_t_ext (l_min, l_max, more)) = l_max;;

let rec limits_compat
  lt1 lt2 =
    less_eq_nat (l_min lt2) (l_min lt1) &&
      pred_option
        (fun lt2_the ->
          (match l_max lt1 with None -> false
            | Some lt1_the -> less_eq_nat lt1_the lt2_the))
        (l_max lt2);;

let rec snd (x1, x2) = x2;;

let rec mem_max m = snd m;;

let rec mem_typing
  m mt = limits_compat (Limit_t_ext (mem_size m, mem_max m, ())) mt;;

let rec tab_typing
  t tt = limits_compat (Limit_t_ext (size_list (fst t), snd t, ())) tt;;

let rec bytes_replicate x = replicate x;;

let rec mem_rep_mk
  x = Abs_mem_rep (bytes_replicate (times_nata x ki64) ImplWrapper.zero_byte);;

let rec mem_mk lim = (mem_rep_mk (l_min lim), l_max lim);;

let rec msbyte bs = last bs;;

let rec mems (S_ext (funcs, tabs, mems, globs, more)) = mems;;

let rec tabs (S_ext (funcs, tabs, mems, globs, more)) = tabs;;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nat i zero_nat then y :: xs
          else x :: list_update xs (minus_nat i one_nata) y);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec typeof
  v = (match v with ConstInt32 _ -> T_i32 | ConstInt64 _ -> T_i64
        | ConstFloat32 _ -> T_f32 | ConstFloat64 _ -> T_f64);;

let rec g_val (Global_ext (g_mut, g_val, more)) = g_val;;

let rec g_mut (Global_ext (g_mut, g_val, more)) = g_mut;;

let rec tg_mut (Tg_ext (tg_mut, tg_t, more)) = tg_mut;;

let rec tg_t (Tg_ext (tg_mut, tg_t, more)) = tg_t;;

let rec glob_typing
  g tg =
    equal_muta (tg_mut tg) (g_mut g) && equal_ta (tg_t tg) (typeof (g_val g));;

let rec funcs (S_ext (funcs, tabs, mems, globs, more)) = funcs;;

let rec globs (S_ext (funcs, tabs, mems, globs, more)) = globs;;

let rec adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
                  | p, Insert (x, q) -> Insert (x, sup_pred q p)
                  | p, Join (q, xq) -> Join (q, adjunct p xq)
and sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))));;

let rec if_pred b = (if b then single () else bot_pred);;

let rec f_inst (F_ext (f_locs, f_inst, more)) = f_inst;;

let rec f_locs (F_ext (f_locs, f_inst, more)) = f_locs;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec memsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = mems;;

let rec tabsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = tabs;;

let rec cvt_i64
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None
          | Some S -> Some ((I64Wrapper_convert.extend_s_i32) c)
          | Some U -> Some ((I64Wrapper_convert.extend_u_i32) c))
      | ConstInt64 _ -> None
      | ConstFloat32 c ->
        (match sx with None -> None | Some S -> I64Wrapper_convert.trunc_s_f32 c
          | Some U -> I64Wrapper_convert.trunc_u_f32 c)
      | ConstFloat64 c ->
        (match sx with None -> None | Some S -> I64Wrapper_convert.trunc_s_f64 c
          | Some U -> I64Wrapper_convert.trunc_u_f64 c));;

let rec cvt_i32
  sx v =
    (match v with ConstInt32 _ -> None
      | ConstInt64 c -> Some ((I32Wrapper_convert.wrap_i64) c)
      | ConstFloat32 c ->
        (match sx with None -> None | Some S -> I32Wrapper_convert.trunc_s_f32 c
          | Some U -> I32Wrapper_convert.trunc_u_f32 c)
      | ConstFloat64 c ->
        (match sx with None -> None | Some S -> I32Wrapper_convert.trunc_s_f64 c
          | Some U -> I32Wrapper_convert.trunc_u_f64 c));;

let rec cvt_f64
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None
          | Some S -> Some (F64Wrapper_convert.convert_s_i32 c)
          | Some U -> Some (F64Wrapper_convert.convert_u_i32 c))
      | ConstInt64 c ->
        (match sx with None -> None
          | Some S -> Some (F64Wrapper_convert.convert_s_i64 c)
          | Some U -> Some (F64Wrapper_convert.convert_u_i64 c))
      | ConstFloat32 c -> Some ((F64Wrapper_convert.promote_f32) c)
      | ConstFloat64 _ -> None);;

let rec cvt_f32
  sx v =
    (match v
      with ConstInt32 c ->
        (match sx with None -> None
          | Some S -> Some (F32Wrapper_convert.convert_s_i32 c)
          | Some U -> Some (F32Wrapper_convert.convert_u_i32 c))
      | ConstInt64 c ->
        (match sx with None -> None
          | Some S -> Some (F32Wrapper_convert.convert_s_i64 c)
          | Some U -> Some (F32Wrapper_convert.convert_u_i64 c))
      | ConstFloat32 _ -> None
      | ConstFloat64 c -> Some ((F32Wrapper_convert.demote_f64) c));;

let rec cvt
  t sx v =
    (match t
      with T_i32 ->
        (match cvt_i32 sx v with None -> None | Some c -> Some (ConstInt32 c))
      | T_i64 ->
        (match cvt_i64 sx v with None -> None | Some c -> Some (ConstInt64 c))
      | T_f32 ->
        (match cvt_f32 sx v with None -> None | Some c -> Some (ConstFloat32 c))
      | T_f64 ->
        (match cvt_f64 sx v with None -> None
          | Some c -> Some (ConstFloat64 c)));;

let rec select_return_top
  ts ct1 x2 = match ts, ct1, x2 with
    ts, ct1, TAny ->
      TopType
        (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))) ts @
          [ct1])
    | ts, TAny, TSome v ->
        TopType
          (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))) ts @
            [TSome v])
    | ts, TSome t1, TSome t2 ->
        (if equal_ta t1 t2
          then TopType
                 (take (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3)))
                    ts @
                   [TSome t1])
          else Bot);;

let rec to_ct_list ts = map (fun a -> TSome a) ts;;

let rec produce
  uu uv = match uu, uv with
    TopType tsa, Type ts -> TopType (tsa @ to_ct_list ts)
    | Type tsa, Type ts -> Type (tsa @ ts)
    | Type tsa, TopType ts -> TopType ts
    | TopType tsa, TopType ts -> TopType ts
    | Type v, Bot -> Bot
    | Bot, uv -> Bot
    | uu, Bot -> Bot;;

let rec ct_compat x0 uu = match x0, uu with TSome ta, TSome t -> equal_ta ta t
                    | TAny, uu -> true
                    | TSome v, TAny -> true;;

let rec ct_prefix
  x0 xs = match x0, xs with x :: xs, y :: ys -> ct_compat x y && ct_prefix xs ys
    | x :: xs, [] -> false
    | [], xs -> true;;

let rec ct_suffix xs ys = ct_prefix (rev xs) (rev ys);;

let rec consume
  x0 cons = match x0, cons with
    Type ts, cons ->
      (if ct_suffix cons (to_ct_list ts)
        then Type (take (minus_nat (size_list ts) (size_list cons)) ts)
        else Bot)
    | TopType cts, cons ->
        (if ct_suffix cons cts
          then TopType (take (minus_nat (size_list cts) (size_list cons)) cts)
          else (if ct_suffix cts cons then TopType [] else Bot))
    | Bot, uv -> Bot;;

let rec type_update
  curr_type cons prods = produce (consume curr_type cons) prods;;

let rec type_update_select
  = function
    Type ts ->
      (if less_eq_nat (nat_of_integer (Z.of_int 3)) (size_list ts) &&
            equal_ta
              (nth ts (minus_nat (size_list ts) (nat_of_integer (Z.of_int 2))))
              (nth ts (minus_nat (size_list ts) (nat_of_integer (Z.of_int 3))))
        then consume (Type ts) [TAny; TSome T_i32] else Bot)
    | TopType ts ->
        (if equal_nat (size_list ts) zero_nat then TopType [TAny]
          else (if equal_nat (minus_nat (size_list ts) one_nata) zero_nat
                 then type_update (TopType ts) [TSome T_i32] (TopType [TAny])
                 else (if equal_nat
                            (minus_nat (minus_nat (size_list ts) one_nata)
                              one_nata)
                            zero_nat
                        then consume (TopType ts) [TSome T_i32]
                        else type_update (TopType ts) [TAny; TAny; TSome T_i32]
                               (select_return_top ts
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 2))))
                                 (nth ts
                                   (minus_nat (size_list ts)
                                     (nat_of_integer (Z.of_int 3))))))))
    | Bot -> Bot;;

let rec tp_length
  tp = (match tp with Tp_i8 -> one_nata | Tp_i16 -> nat_of_integer (Z.of_int 2)
         | Tp_i32 -> nat_of_integer (Z.of_int 4));;

let rec t_length
  t = (match t with T_i32 -> nat_of_integer (Z.of_int 4)
        | T_i64 -> nat_of_integer (Z.of_int 8)
        | T_f32 -> nat_of_integer (Z.of_int 4)
        | T_f64 -> nat_of_integer (Z.of_int 8));;

let rec is_int_t
  t = (match t with T_i32 -> true | T_i64 -> true | T_f32 -> false
        | T_f64 -> false);;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nata)));;

let rec load_store_t_bounds
  a tp t =
    (match tp
      with None ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (t_length t)
      | Some tpa ->
        less_eq_nat (power power_nat (nat_of_integer (Z.of_int 2)) a)
          (tp_length tpa) &&
          (less_nat (tp_length tpa) (t_length t) && is_int_t t));;

let rec label_update
  labela
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, labela label, return,
          more);;

let rec c_types_agree
  x0 ts = match x0, ts with Type tsa, ts -> equal_list equal_t tsa ts
    | TopType tsa, ts -> ct_suffix tsa (to_ct_list ts)
    | Bot, uu -> false;;

let rec is_float_t
  t = (match t with T_i32 -> false | T_i64 -> false | T_f32 -> true
        | T_f64 -> true);;

let rec relop_t_agree
  relop t =
    (match relop with Relop_i _ -> is_int_t t | Relop_f _ -> is_float_t t);;

let rec binop_t_agree
  binop t =
    (match binop with Binop_i _ -> is_int_t t | Binop_f _ -> is_float_t t);;

let rec unop_t_agree
  unop t = (match unop with Unop_i _ -> is_int_t t | Unop_f _ -> is_float_t t);;

let rec option_projl x = map_option fst x;;

let rec types_t
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = types_t;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec convert_cond
  t1 t2 sx =
    not (equal_ta t1 t2) &&
      equal_bool (is_none sx)
        (is_float_t t1 && is_float_t t2 ||
          is_int_t t1 &&
            (is_int_t t2 && less_nat (t_length t1) (t_length t2)));;

let rec return
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = return;;

let rec memory
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = memory;;

let rec global
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = global;;

let rec func_t
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = func_t;;

let rec table
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = table;;

let rec local
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = local;;

let rec label
  (T_context_ext
    (types_t, func_t, global, table, memory, local, label, return, more))
    = label;;

let rec same_lab_h
  x0 uu ts = match x0, uu, ts with [], uu, ts -> Some ts
    | i :: is, lab_c, ts ->
        (if less_eq_nat (size_list lab_c) i then None
          else (if equal_list equal_t (nth lab_c i) ts
                 then same_lab_h is lab_c (nth lab_c i) else None));;

let rec same_lab
  x0 lab_c = match x0, lab_c with [], lab_c -> None
    | i :: is, lab_c ->
        (if less_eq_nat (size_list lab_c) i then None
          else same_lab_h is lab_c (nth lab_c i));;

let rec is_mut tg = equal_muta (tg_mut tg) T_mut;;

let rec check
  c es ts =
    (match es with [] -> ts
      | e :: esa ->
        (match ts with TopType _ -> check c esa (check_single c e ts)
          | Type _ -> check c esa (check_single c e ts) | Bot -> Bot))
and b_e_type_checker
  c es (Tf (tn, tm)) = c_types_agree (check c es (Type tn)) tm
and check_single
  c x1 ts = match c, x1, ts with
    c, EConst v, ts -> type_update ts [] (Type [typeof v])
    | c, Unop (t, op), ts ->
        (if unop_t_agree op t then type_update ts [TSome t] (Type [t]) else Bot)
    | c, Binop (t, op), ts ->
        (if binop_t_agree op t then type_update ts [TSome t; TSome t] (Type [t])
          else Bot)
    | c, Testop (t, uu), ts ->
        (if is_int_t t then type_update ts [TSome t] (Type [T_i32]) else Bot)
    | c, Relop (t, op), ts ->
        (if relop_t_agree op t
          then type_update ts [TSome t; TSome t] (Type [T_i32]) else Bot)
    | c, Cvtop (t1, Convert, t2, sx), ts ->
        (if convert_cond t1 t2 sx then type_update ts [TSome t2] (Type [t1])
          else Bot)
    | c, Cvtop (t1, Reinterpret, t2, sx), ts ->
        (if not (equal_ta t1 t2) &&
              (equal_nat (t_length t1) (t_length t2) && is_none sx)
          then type_update ts [TSome t2] (Type [t1]) else Bot)
    | c, Unreachable, ts -> type_update ts [] (TopType [])
    | c, Nop, ts -> ts
    | c, Drop, ts -> type_update ts [TAny] (Type [])
    | c, Select, ts -> type_update_select ts
    | c, Block (Tf (tn, tm), es), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es
              (Tf (tn, tm))
          then type_update ts (to_ct_list tn) (Type tm) else Bot)
    | c, Loop (Tf (tn, tm), es), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tn] @ label c) c) es
              (Tf (tn, tm))
          then type_update ts (to_ct_list tn) (Type tm) else Bot)
    | c, If (Tf (tn, tm), es1, es2), ts ->
        (if b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es1
              (Tf (tn, tm)) &&
              b_e_type_checker (label_update (fun _ -> [tm] @ label c) c) es2
                (Tf (tn, tm))
          then type_update ts (to_ct_list (tn @ [T_i32])) (Type tm) else Bot)
    | c, Br i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i)) (TopType [])
          else Bot)
    | c, Br_if i, ts ->
        (if less_nat i (size_list (label c))
          then type_update ts (to_ct_list (nth (label c) i @ [T_i32]))
                 (Type (nth (label c) i))
          else Bot)
    | c, Br_table (is, i), ts ->
        (match same_lab (is @ [i]) (label c) with None -> Bot
          | Some tls ->
            type_update ts (to_ct_list (tls @ [T_i32])) (TopType []))
    | c, Return, ts ->
        (match return c with None -> Bot
          | Some tls -> type_update ts (to_ct_list tls) (TopType []))
    | c, Call i, ts ->
        (if less_nat i (size_list (func_t c))
          then (let Tf (tn, tm) = nth (func_t c) i in
                 type_update ts (to_ct_list tn) (Type tm))
          else Bot)
    | c, Call_indirect i, ts ->
        (if less_eq_nat one_nata (size_list (table c)) &&
              less_nat i (size_list (types_t c))
          then (let Tf (tn, tm) = nth (types_t c) i in
                 type_update ts (to_ct_list (tn @ [T_i32])) (Type tm))
          else Bot)
    | c, Get_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [] (Type [nth (local c) i]) else Bot)
    | c, Set_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [TSome (nth (local c) i)] (Type []) else Bot)
    | c, Tee_local i, ts ->
        (if less_nat i (size_list (local c))
          then type_update ts [TSome (nth (local c) i)] (Type [nth (local c) i])
          else Bot)
    | c, Get_global i, ts ->
        (if less_nat i (size_list (global c))
          then type_update ts [] (Type [tg_t (nth (global c) i)]) else Bot)
    | c, Set_global i, ts ->
        (if less_nat i (size_list (global c)) && is_mut (nth (global c) i)
          then type_update ts [TSome (tg_t (nth (global c) i))] (Type [])
          else Bot)
    | c, Load (t, tp_sx, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a (option_projl tp_sx) t
          then type_update ts [TSome T_i32] (Type [t]) else Bot)
    | c, Store (t, tp, a, off), ts ->
        (if less_eq_nat one_nata (size_list (memory c)) &&
              load_store_t_bounds a tp t
          then type_update ts [TSome T_i32; TSome t] (Type []) else Bot)
    | c, Current_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [] (Type [T_i32]) else Bot)
    | c, Grow_memory, ts ->
        (if less_eq_nat one_nata (size_list (memory c))
          then type_update ts [TSome T_i32] (Type [T_i32]) else Bot);;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec list_all2
  p xs ys = match p, xs, ys with
    p, x :: xs, y :: ys -> p x y && list_all2 p xs ys
    | p, xs, [] -> null xs
    | p, [], ys -> null ys;;

let rec funcsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = funcs;;

let rec globsa (Inst_ext (types, funcs, tabs, mems, globs, more)) = globs;;

let rec types (Inst_ext (types, funcs, tabs, mems, globs, more)) = types;;

let rec app_rev_tr x0 ys = match x0, ys with [], ys -> ys
                     | x :: xs, ys -> app_rev_tr xs (x :: ys);;

let rec mem_rep_append
  (Abs_mem_rep m) n b = Abs_mem_rep (app_rev_tr (rev m) (replicate n b));;

let rec mem_append m n b = (mem_rep_append (fst m) n b, snd m);;

let rec mem_rep_read_bytes (Abs_mem_rep x) = (fun n l -> take l (drop n x));;

let rec read_bytes m n l = mem_rep_read_bytes (fst m) n l;;

let rec bits
  v = (match v with ConstInt32 a -> ImplWrapper.serialise_i32 a
        | ConstInt64 a -> ImplWrapper.serialise_i64 a
        | ConstFloat32 a -> ImplWrapper.serialise_f32 a
        | ConstFloat64 a -> ImplWrapper.serialise_f64 a);;

let rec load
  m n off l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (read_bytes m (plus_nat n off) l) else None);;

let rec stab_cl_ind
  s i j =
    (let stabinst = fst (nth (tabs s) i) in
      (if less_nat j (size_list stabinst) then nth stabinst j else None));;

let rec stab
  s i j = (match tabsa i with [] -> None | k :: _ -> stab_cl_ind s k j);;

let rec mem_rep_write_bytes
  (Abs_mem_rep xb) xa x =
    Abs_mem_rep (take xa xb @ x @ drop (plus_nat xa (size_list x)) xb);;

let rec write_bytes m n bs = (mem_rep_write_bytes (fst m) n bs, snd m);;

let rec sglob_ind s i j = nth (globsa i) j;;

let rec sglob s i j = nth (globs s) (sglob_ind s i j);;

let rec takefill
  fill n xs =
    (if equal_nat n zero_nat then []
      else (match xs with [] -> fill :: takefill fill (minus_nat n one_nata) xs
             | y :: ys -> y :: takefill fill (minus_nat n one_nata) ys));;

let rec bytes_takefill x = takefill x;;

let rec store
  m n off bs l =
    (if less_eq_nat (plus_nat (plus_nat n off) l) (mem_length m)
      then Some (write_bytes m (plus_nat n off)
                  (bytes_takefill ImplWrapper.zero_byte l bs))
      else None);;

let rec m_data
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_data;;

let rec m_elem
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_elem;;

let rec m_mems
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_mems;;

let rec m_tabs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_tabs;;

let rec stypes s i j = nth (types i) j;;

let rec m_funcs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_funcs;;

let rec m_globs
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_globs;;

let rec m_start
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_start;;

let rec m_types
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_types;;

let rec mems_update
  memsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabs, memsa mems, globs, more);;

let rec tabs_update
  tabsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabsa tabs, mems, globs, more);;

let rec bitzero
  t = (match t with T_i32 -> ConstInt32 I32Wrapper.zero
        | T_i64 -> ConstInt64 I64Wrapper.zero
        | T_f32 -> ConstFloat32 F32Wrapper.zero
        | T_f64 -> ConstFloat64 F64Wrapper.zero);;

let rec cl_type
  cl = (match cl with Func_native (_, tf, _, _) -> tf
         | Func_host (tf, _) -> tf);;

let rec n_zeros ts = map bitzero ts;;

let rec split_vals_e
  = function
    Basic (EConst v) :: es -> (let a = split_vals_e es in
                               let (vs, aa) = a in
                                (v :: vs, aa))
    | [] -> ([], [])
    | Basic Unreachable :: va -> ([], Basic Unreachable :: va)
    | Basic Nop :: va -> ([], Basic Nop :: va)
    | Basic Drop :: va -> ([], Basic Drop :: va)
    | Basic Select :: va -> ([], Basic Select :: va)
    | Basic (Block (vc, vd)) :: va -> ([], Basic (Block (vc, vd)) :: va)
    | Basic (Loop (vc, vd)) :: va -> ([], Basic (Loop (vc, vd)) :: va)
    | Basic (If (vc, vd, ve)) :: va -> ([], Basic (If (vc, vd, ve)) :: va)
    | Basic (Br vc) :: va -> ([], Basic (Br vc) :: va)
    | Basic (Br_if vc) :: va -> ([], Basic (Br_if vc) :: va)
    | Basic (Br_table (vc, vd)) :: va -> ([], Basic (Br_table (vc, vd)) :: va)
    | Basic Return :: va -> ([], Basic Return :: va)
    | Basic (Call vc) :: va -> ([], Basic (Call vc) :: va)
    | Basic (Call_indirect vc) :: va -> ([], Basic (Call_indirect vc) :: va)
    | Basic (Get_local vc) :: va -> ([], Basic (Get_local vc) :: va)
    | Basic (Set_local vc) :: va -> ([], Basic (Set_local vc) :: va)
    | Basic (Tee_local vc) :: va -> ([], Basic (Tee_local vc) :: va)
    | Basic (Get_global vc) :: va -> ([], Basic (Get_global vc) :: va)
    | Basic (Set_global vc) :: va -> ([], Basic (Set_global vc) :: va)
    | Basic (Load (vc, vd, ve, vf)) :: va ->
        ([], Basic (Load (vc, vd, ve, vf)) :: va)
    | Basic (Store (vc, vd, ve, vf)) :: va ->
        ([], Basic (Store (vc, vd, ve, vf)) :: va)
    | Basic Current_memory :: va -> ([], Basic Current_memory :: va)
    | Basic Grow_memory :: va -> ([], Basic Grow_memory :: va)
    | Basic (Unop (vc, vd)) :: va -> ([], Basic (Unop (vc, vd)) :: va)
    | Basic (Binop (vc, vd)) :: va -> ([], Basic (Binop (vc, vd)) :: va)
    | Basic (Testop (vc, vd)) :: va -> ([], Basic (Testop (vc, vd)) :: va)
    | Basic (Relop (vc, vd)) :: va -> ([], Basic (Relop (vc, vd)) :: va)
    | Basic (Cvtop (vc, vd, ve, vf)) :: va ->
        ([], Basic (Cvtop (vc, vd, ve, vf)) :: va)
    | Trap :: va -> ([], Trap :: va)
    | Invoke vb :: va -> ([], Invoke vb :: va)
    | Label (vb, vc, vd) :: va -> ([], Label (vb, vc, vd) :: va)
    | Frame (vb, vc, vd) :: va -> ([], Frame (vb, vc, vd) :: va);;

let rec e_is_trap
  e = (match e with Basic _ -> false | Trap -> true | Invoke _ -> false
        | Label (_, _, _) -> false | Frame (_, _, _) -> false);;

let rec es_is_trap
  es = (match es with [] -> false | [e] -> e_is_trap e | _ :: _ :: _ -> false);;

let rec rep_host (Abs_host x) = x;;

let rec host_apply_impl s tf h vs = rep_host h (s, vs);;

let rec wasm_deserialise
  bs t =
    (match t with T_i32 -> ConstInt32 (ImplWrapper.deserialise_i32 bs)
      | T_i64 -> ConstInt64 (ImplWrapper.deserialise_i64 bs)
      | T_f32 -> ConstFloat32 (ImplWrapper.deserialise_f32 bs)
      | T_f64 -> ConstFloat64 (ImplWrapper.deserialise_f64 bs));;

let rec g_val_update
  g_vala (Global_ext (g_mut, g_val, more)) =
    Global_ext (g_mut, g_vala g_val, more);;

let rec globs_update
  globsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcs, tabs, mems, globsa globs, more);;

let rec supdate_glob_s
  s k v =
    globs_update
      (fun _ ->
        list_update (globs s) k (g_val_update (fun _ -> v) (nth (globs s) k)))
      s;;

let rec supdate_glob
  s i j v = (let k = sglob_ind s i j in supdate_glob_s s k v);;

let rec store_packed x = store x;;

let rec types_agree t v = equal_ta (typeof v) t;;

let rec sign_extend
  sx l bytes =
    (let msb = ImplWrapper.msb_byte (msbyte bytes) in
     let byte =
       (match sx
         with S ->
           (if msb then ImplWrapper.negone_byte else ImplWrapper.zero_byte)
         | U -> ImplWrapper.zero_byte)
       in
      bytes_takefill byte l bytes);;

let rec load_packed
  sx m n off lp l = map_option (sign_extend sx l) (load m n off lp);;

let rec app_testop_i _A testop c = (let Eqz = testop in int_eqz _A c);;

let rec app_testop
  op v =
    (match v
      with ConstInt32 c ->
        ConstInt32 (ImplWrapper.bool (app_testop_i wasm_int_i32 op c))
      | ConstInt64 c ->
        ConstInt32 (ImplWrapper.bool (app_testop_i wasm_int_i64 op c))
      | ConstFloat32 _ -> ConstInt32 I32Wrapper.zero
      | ConstFloat64 _ -> ConstInt32 I32Wrapper.zero);;

let rec split_n
  x0 n = match x0, n with [], n -> ([], [])
    | v :: va, n ->
        (if equal_nat n zero_nat then ([], v :: va)
          else (let a = split_n va (minus_nat n one_nata) in
                let (es, aa) = a in
                 (v :: es, aa)));;

let rec sglob_val s i j = g_val (sglob s i j);;

let rec sfunc_ind i j = nth (funcsa i) j;;

let rec app_relop_i _A
  rop c1 c2 =
    (match rop with Eq -> int_eq _A c1 c2 | Ne -> not (int_eq _A c1 c2)
      | Lt S -> int_lt_s _A c1 c2 | Lt U -> int_lt_u _A c1 c2
      | Gt S -> int_gt_s _A c1 c2 | Gt U -> int_gt_u _A c1 c2
      | Le S -> int_le_s _A c1 c2 | Le U -> int_le_u _A c1 c2
      | Ge S -> int_ge_s _A c1 c2 | Ge U -> int_ge_u _A c1 c2);;

let rec app_relop_i_v
  iop v1 v2 =
    (match (v1, v2)
      with (ConstInt32 c1, ConstInt32 c2) ->
        ConstInt32 (ImplWrapper.bool (app_relop_i wasm_int_i32 iop c1 c2))
      | (ConstInt32 _, ConstInt64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt32 _, ConstFloat32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt32 _, ConstFloat64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt64 _, ConstInt32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt64 c1, ConstInt64 c2) ->
        ConstInt32 (ImplWrapper.bool (app_relop_i wasm_int_i64 iop c1 c2))
      | (ConstInt64 _, ConstFloat32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt64 _, ConstFloat64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat32 _, _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat64 _, _) -> ConstInt32 I32Wrapper.zero);;

let rec app_relop_f _A
  rop c1 c2 =
    (match rop with Eqf -> float_eq _A c1 c2 | Nef -> not (float_eq _A c1 c2)
      | Ltf -> float_lt _A c1 c2 | Gtf -> float_gt _A c1 c2
      | Lef -> float_le _A c1 c2 | Gef -> float_ge _A c1 c2);;

let rec app_relop_f_v
  fop v1 v2 =
    (match (v1, v2) with (ConstInt32 _, _) -> ConstInt32 I32Wrapper.zero
      | (ConstInt64 _, _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat32 _, ConstInt32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat32 _, ConstInt64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat32 c1, ConstFloat32 c2) ->
        ConstInt32 (ImplWrapper.bool (app_relop_f wasm_float_f32 fop c1 c2))
      | (ConstFloat32 _, ConstFloat64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat64 _, ConstInt32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat64 _, ConstInt64 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat64 _, ConstFloat32 _) -> ConstInt32 I32Wrapper.zero
      | (ConstFloat64 c1, ConstFloat64 c2) ->
        ConstInt32 (ImplWrapper.bool (app_relop_f wasm_float_f64 fop c1 c2)));;

let rec app_relop
  rop v1 v2 =
    (match rop with Relop_i iop -> app_relop_i_v iop v1 v2
      | Relop_f fop -> app_relop_f_v fop v1 v2);;

let rec app_binop_i _A
  iop c1 c2 =
    (match iop with Add -> Some (int_add _A c1 c2)
      | Sub -> Some (int_sub _A c1 c2) | Mul -> Some (int_mul _A c1 c2)
      | Div S -> int_div_s _A c1 c2 | Div U -> int_div_u _A c1 c2
      | Rem S -> int_rem_s _A c1 c2 | Rem U -> int_rem_u _A c1 c2
      | And -> Some (int_and _A c1 c2) | Or -> Some (int_or _A c1 c2)
      | Xor -> Some (int_xor _A c1 c2) | Shl -> Some (int_shl _A c1 c2)
      | Shr S -> Some (int_shr_s _A c1 c2) | Shr U -> Some (int_shr_u _A c1 c2)
      | Rotl -> Some (int_rotl _A c1 c2) | Rotr -> Some (int_rotr _A c1 c2));;

let rec app_binop_i_v
  iop v1 v2 =
    (match (v1, v2)
      with (ConstInt32 c1, ConstInt32 c2) ->
        map_option (fun a -> ConstInt32 a) (app_binop_i wasm_int_i32 iop c1 c2)
      | (ConstInt32 _, ConstInt64 _) -> None
      | (ConstInt32 _, ConstFloat32 _) -> None
      | (ConstInt32 _, ConstFloat64 _) -> None
      | (ConstInt64 _, ConstInt32 _) -> None
      | (ConstInt64 c1, ConstInt64 c2) ->
        map_option (fun a -> ConstInt64 a) (app_binop_i wasm_int_i64 iop c1 c2)
      | (ConstInt64 _, ConstFloat32 _) -> None
      | (ConstInt64 _, ConstFloat64 _) -> None | (ConstFloat32 _, _) -> None
      | (ConstFloat64 _, _) -> None);;

let rec app_binop_f _A
  fop c1 c2 =
    (match fop with Addf -> Some (float_add _A c1 c2)
      | Subf -> Some (float_sub _A c1 c2) | Mulf -> Some (float_mul _A c1 c2)
      | Divf -> Some (float_div _A c1 c2) | Min -> Some (float_min _A c1 c2)
      | Max -> Some (float_max _A c1 c2)
      | Copysign -> Some (float_copysign _A c1 c2));;

let rec app_binop_f_v
  fop v1 v2 =
    (match (v1, v2) with (ConstInt32 _, _) -> None | (ConstInt64 _, _) -> None
      | (ConstFloat32 _, ConstInt32 _) -> None
      | (ConstFloat32 _, ConstInt64 _) -> None
      | (ConstFloat32 c1, ConstFloat32 c2) ->
        map_option (fun a -> ConstFloat32 a)
          (app_binop_f wasm_float_f32 fop c1 c2)
      | (ConstFloat32 _, ConstFloat64 _) -> None
      | (ConstFloat64 _, ConstInt32 _) -> None
      | (ConstFloat64 _, ConstInt64 _) -> None
      | (ConstFloat64 _, ConstFloat32 _) -> None
      | (ConstFloat64 c1, ConstFloat64 c2) ->
        map_option (fun a -> ConstFloat64 a)
          (app_binop_f wasm_float_f64 fop c1 c2));;

let rec app_binop
  bop v1 v2 =
    (match bop with Binop_i iop -> app_binop_i_v iop v1 v2
      | Binop_f fop -> app_binop_f_v fop v1 v2);;

let rec smem_ind s i = (match memsa i with [] -> None | n :: _ -> Some n);;

let rec mem_grow
  m n = (let len = plus_nat (mem_size m) n in
          (if less_eq_nat len
                (power power_nat (nat_of_integer (Z.of_int 2))
                  (nat_of_integer (Z.of_int 16))) &&
                pred_option (less_eq_nat len) (mem_max m)
            then Some (mem_append m (times_nata n ki64) ImplWrapper.zero_byte)
            else None));;

let rec app_unop_i _A
  iop c =
    (match iop with Clz -> int_clz _A c | Ctz -> int_ctz _A c
      | Popcnt -> int_popcnt _A c);;

let rec app_unop_i_v
  iop v =
    (match v with ConstInt32 c -> ConstInt32 (app_unop_i wasm_int_i32 iop c)
      | ConstInt64 c -> ConstInt64 (app_unop_i wasm_int_i64 iop c)
      | ConstFloat32 a -> ConstFloat32 a | ConstFloat64 a -> ConstFloat64 a);;

let rec app_unop_f _A
  fop c =
    (match fop with Neg -> float_neg _A c | Abs -> float_abs _A c
      | Ceil -> float_ceil _A c | Floor -> float_floor _A c
      | Trunc -> float_trunc _A c | Nearest -> float_nearest _A c
      | Sqrt -> float_sqrt _A c);;

let rec app_unop_f_v
  fop v =
    (match v with ConstInt32 a -> ConstInt32 a | ConstInt64 a -> ConstInt64 a
      | ConstFloat32 c -> ConstFloat32 (app_unop_f wasm_float_f32 fop c)
      | ConstFloat64 c -> ConstFloat64 (app_unop_f wasm_float_f64 fop c));;

let rec app_unop
  uop v =
    (match uop with Unop_i iop -> app_unop_i_v iop v
      | Unop_f fop -> app_unop_f_v fop v);;

let rec run_step
  d (s, (f, (ves, es))) =
    (match es with [] -> (s, (f, RSCrash CError))
      | e :: esa ->
        (if e_is_trap e
          then (if not (null esa) || not (null ves)
                 then (s, (f, RSNormal ([], [Trap])))
                 else (s, (f, RSCrash CError)))
          else (match e
                 with Basic Unreachable -> (s, (f, RSNormal (ves, Trap :: esa)))
                 | Basic Nop -> (s, (f, RSNormal (ves, esa)))
                 | Basic Drop ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | _ :: vesa -> (s, (f, RSNormal (vesa, esa))))
                 | Basic Select ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | [ConstInt32 _] -> (s, (f, RSCrash CError))
                     | [ConstInt32 _; _] -> (s, (f, RSCrash CError))
                     | ConstInt32 c :: v2 :: v1 :: vesa ->
                       (if I32Wrapper.eq c I32Wrapper.zero
                         then (s, (f, RSNormal (v2 :: vesa, esa)))
                         else (s, (f, RSNormal (v1 :: vesa, esa))))
                     | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError)))
                 | Basic (Block (Tf (t1s, t2s), esaa)) ->
                   (if less_eq_nat (size_list t1s) (size_list ves)
                     then (let (vesb, vesa) = split_n ves (size_list t1s) in
                            (s, (f, RSNormal
                                      (vesa,
Label (size_list t2s, [],
        map (fun v -> Basic (EConst v)) (rev vesb) @
          map (fun a -> Basic a) esaa) ::
  esa))))
                     else (s, (f, RSCrash CError)))
                 | Basic (Loop (Tf (t1s, t2s), esaa)) ->
                   (if less_eq_nat (size_list t1s) (size_list ves)
                     then (let (vesb, vesa) = split_n ves (size_list t1s) in
                            (s, (f, RSNormal
                                      (vesa,
Label (size_list t1s, [Basic (Loop (Tf (t1s, t2s), esaa))],
        map (fun v -> Basic (EConst v)) (rev vesb) @
          map (fun a -> Basic a) esaa) ::
  esa))))
                     else (s, (f, RSCrash CError)))
                 | Basic (If (tf, es1, es2)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | ConstInt32 c :: vesa ->
                       (if I32Wrapper.eq c I32Wrapper.zero
                         then (s, (f, RSNormal
(vesa, Basic (Block (tf, es2)) :: esa)))
                         else (s, (f, RSNormal
(vesa, Basic (Block (tf, es1)) :: esa))))
                     | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError)))
                 | Basic (Br j) -> (s, (f, RSBreak (j, ves)))
                 | Basic (Br_if j) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | ConstInt32 c :: vesa ->
                       (if I32Wrapper.eq c I32Wrapper.zero
                         then (s, (f, RSNormal (vesa, esa)))
                         else (s, (f, RSNormal (vesa, Basic (Br j) :: esa))))
                     | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError)))
                 | Basic (Br_table (js, j)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | ConstInt32 c :: vesa ->
                       (let k = Nat (I32Wrapper.z_of_int c) in
                         (if less_nat k (size_list js)
                           then (s, (f, RSNormal
  (vesa, Basic (Br (nth js k)) :: esa)))
                           else (s, (f, RSNormal (vesa, Basic (Br j) :: esa)))))
                     | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError)))
                 | Basic Return -> (s, (f, RSReturn ves))
                 | Basic (Call j) ->
                   (s, (f, RSNormal
                             (ves, Invoke (sfunc_ind (f_inst f) j) :: esa)))
                 | Basic (Call_indirect j) ->
                   (let i = f_inst f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | ConstInt32 c :: vesa ->
                         (match stab s i (Nat (I32Wrapper.z_of_int c))
                           with None -> (s, (f, RSNormal (vesa, Trap :: esa)))
                           | Some i_cl ->
                             (if equal_tfa (stypes s i j)
                                   (cl_type (nth (funcs s) i_cl))
                               then (s, (f,
  RSNormal (vesa, Invoke i_cl :: esa)))
                               else (s, (f, RSNormal (vesa, Trap :: esa)))))
                       | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError))))
                 | Basic (Get_local j) ->
                   (let vs = f_locs f in
                     (if less_nat j (size_list vs)
                       then (s, (f, RSNormal (nth vs j :: ves, esa)))
                       else (s, (f, RSCrash CError))))
                 | Basic (Set_local j) ->
                   (let vs = f_locs f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | v :: vesa ->
                         (if less_nat j (size_list vs)
                           then (s, (F_ext (list_update vs j v, f_inst f, ()),
                                      RSNormal (vesa, esa)))
                           else (s, (f, RSCrash CError)))))
                 | Basic (Tee_local j) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: _ ->
                       (s, (f, RSNormal
                                 (v :: ves, Basic (Set_local j) :: esa))))
                 | Basic (Get_global j) ->
                   (s, (f, RSNormal (sglob_val s (f_inst f) j :: ves, esa)))
                 | Basic (Set_global j) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: vesa ->
                       (supdate_glob s (f_inst f) j v,
                         (f, RSNormal (vesa, esa))))
                 | Basic (Load (t, None, _, off)) ->
                   (let i = f_inst f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | ConstInt32 k :: vesa ->
                         (match smem_ind s i
                           with None -> (s, (f, RSCrash CError))
                           | Some a ->
                             (match
                               load (nth (mems s) a)
                                 (Nat (I32Wrapper.z_of_int k)) off (t_length t)
                               with None ->
                                 (s, (f, RSNormal (vesa, Trap :: esa)))
                               | Some aa ->
                                 (s, (f, RSNormal
   (wasm_deserialise aa t :: vesa, esa)))))
                       | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError))))
                 | Basic (Load (t, Some (tp, sx), _, off)) ->
                   (let i = f_inst f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | ConstInt32 k :: vesa ->
                         (match smem_ind s i
                           with None -> (s, (f, RSCrash CError))
                           | Some a ->
                             (match
                               load_packed sx (nth (mems s) a)
                                 (Nat (I32Wrapper.z_of_int k)) off
                                 (tp_length tp) (t_length t)
                               with None ->
                                 (s, (f, RSNormal (vesa, Trap :: esa)))
                               | Some aa ->
                                 (s, (f, RSNormal
   (wasm_deserialise aa t :: vesa, esa)))))
                       | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                       | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError))))
                 | Basic (Store (t, None, _, off)) ->
                   (let i = f_inst f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | [_] -> (s, (f, RSCrash CError))
                       | v :: ConstInt32 k :: vesa ->
                         (if types_agree t v
                           then (match smem_ind s i
                                  with None -> (s, (f, RSCrash CError))
                                  | Some a ->
                                    (match
                                      store (nth (mems s) a)
(Nat (I32Wrapper.z_of_int k)) off (bits v) (t_length t)
                                      with None ->
(s, (f, RSNormal (vesa, Trap :: esa)))
                                      | Some a_a ->
(mems_update (fun _ -> list_update (mems s) a a_a) s,
  (f, RSNormal (vesa, esa)))))
                           else (s, (f, RSCrash CError)))
                       | _ :: ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                       | _ :: ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                       | _ :: ConstFloat64 _ :: _ -> (s, (f, RSCrash CError))))
                 | Basic (Store (t, Some tp, _, off)) ->
                   (let i = f_inst f in
                     (match ves with [] -> (s, (f, RSCrash CError))
                       | [_] -> (s, (f, RSCrash CError))
                       | v :: ConstInt32 k :: vesa ->
                         (if types_agree t v
                           then (match smem_ind s i
                                  with None -> (s, (f, RSCrash CError))
                                  | Some a ->
                                    (match
                                      store_packed (nth (mems s) a)
(Nat (I32Wrapper.z_of_int k)) off (bits v) (tp_length tp)
                                      with None ->
(s, (f, RSNormal (vesa, Trap :: esa)))
                                      | Some a_a ->
(mems_update (fun _ -> list_update (mems s) a a_a) s,
  (f, RSNormal (vesa, esa)))))
                           else (s, (f, RSCrash CError)))
                       | _ :: ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                       | _ :: ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                       | _ :: ConstFloat64 _ :: _ -> (s, (f, RSCrash CError))))
                 | Basic Current_memory ->
                   (match smem_ind s (f_inst f)
                     with None -> (s, (f, RSCrash CError))
                     | Some a ->
                       (s, (f, RSNormal
                                 (ConstInt32
                                    (I32Wrapper.int_of_z (integer_of_nat (mem_size
                                   (nth (mems s) a)))) ::
                                    ves,
                                   esa))))
                 | Basic Grow_memory ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | ConstInt32 c :: vesa ->
                       (match smem_ind s (f_inst f)
                         with None -> (s, (f, RSCrash CError))
                         | Some a ->
                           (let l = mem_size (nth (mems s) a) in
                             (match
                               mem_grow (nth (mems s) a)
                                 (Nat (I32Wrapper.z_of_int c))
                               with None ->
                                 (s, (f, RSNormal
   (ConstInt32 I32Wrapper.minus_one :: vesa, esa)))
                               | Some a_a ->
                                 (mems_update
                                    (fun _ -> list_update (mems s) a a_a) s,
                                   (f, RSNormal
 (ConstInt32 (I32Wrapper.int_of_z (integer_of_nat l)) :: vesa, esa))))))
                     | ConstInt64 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat32 _ :: _ -> (s, (f, RSCrash CError))
                     | ConstFloat64 _ :: _ -> (s, (f, RSCrash CError)))
                 | Basic (EConst _) -> (s, (f, RSCrash CError))
                 | Basic (Unop (_, op)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: vesa ->
                       (s, (f, RSNormal (app_unop op v :: vesa, esa))))
                 | Basic (Binop (_, op)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | [_] -> (s, (f, RSCrash CError))
                     | v2 :: v1 :: vesa ->
                       (match app_binop op v1 v2
                         with None -> (s, (f, RSNormal (vesa, Trap :: esa)))
                         | Some a -> (s, (f, RSNormal (a :: vesa, esa)))))
                 | Basic (Testop (_, testop)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: vesa ->
                       (s, (f, RSNormal (app_testop testop v :: vesa, esa))))
                 | Basic (Relop (_, op)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | [_] -> (s, (f, RSCrash CError))
                     | v2 :: v1 :: vesa ->
                       (s, (f, RSNormal (app_relop op v1 v2 :: vesa, esa))))
                 | Basic (Cvtop (t2, Convert, t1, sx)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: vesa ->
                       (if types_agree t1 v
                         then (match cvt t2 sx v
                                with None ->
                                  (s, (f, RSNormal (vesa, Trap :: esa)))
                                | Some a -> (s, (f, RSNormal (a :: vesa, esa))))
                         else (s, (f, RSCrash CError))))
                 | Basic (Cvtop (t2, Reinterpret, t1, sx)) ->
                   (match ves with [] -> (s, (f, RSCrash CError))
                     | v :: vesa ->
                       (if types_agree t1 v && is_none sx
                         then (s, (f, RSNormal
(wasm_deserialise (bits v) t2 :: vesa, esa)))
                         else (s, (f, RSCrash CError))))
                 | Trap -> (s, (f, RSCrash CError))
                 | Invoke i_cl ->
                   (match nth (funcs s) i_cl
                     with Func_native (i, Tf (t1s, t2s), ts, esaa) ->
                       (let n = size_list t1s in
                        let m = size_list t2s in
                         (if less_eq_nat n (size_list ves)
                           then (let (vesb, vesa) = split_n ves n in
                                 let zs = n_zeros ts in
                                  (s, (f,
RSNormal
  (vesa,
    Frame (m, F_ext (rev vesb @ zs, i, ()),
            [Basic (Block (Tf ([], t2s), esaa))]) ::
      esa))))
                           else (s, (f, RSCrash CError))))
                     | Func_host (Tf (t1s, t2s), h) ->
                       (let n = size_list t1s in
                        let _ = size_list t2s in
                         (if less_eq_nat n (size_list ves)
                           then (let (vesb, vesa) = split_n ves n in
                                  (match
                                    host_apply_impl s (Tf (t1s, t2s)) h
                                      (rev vesb)
                                    with None ->
                                      (s, (f, RSNormal (vesa, Trap :: esa)))
                                    | Some (sa, rves) ->
                                      (if list_all2 types_agree t2s rves
then (sa, (f, RSNormal (rev rves @ vesa, esa)))
else (sa, (f, RSCrash CError)))))
                           else (s, (f, RSCrash CError)))))
                 | Label (ln, les, esaa) ->
                   (if es_is_trap esaa
                     then (s, (f, RSNormal (ves, Trap :: esa)))
                     else (match split_vals_e esaa
                            with (lsves, []) ->
                              (s, (f, RSNormal (rev lsves @ ves, esa)))
                            | (lsves, aa :: lista) ->
                              (let a =
                                 run_step d (s, (f, (rev lsves, aa :: lista)))
                                 in
                               let (sa, ab) = a in
                               let (fa, ac) = ab in
                                (match ac
                                  with RSCrash c -> (sa, (fa, RSCrash c))
                                  | RSBreak (ad, bvs) ->
                                    (if equal_nat ad zero_nat
                                      then (if less_eq_nat ln (size_list bvs)
     then (sa, (fa, RSNormal (take ln bvs @ ves, les @ esa)))
     else (sa, (fa, RSCrash CError)))
                                      else (sa,
     (fa, RSBreak (minus_nat ad one_nata, bvs))))
                                  | RSReturn rvs -> (sa, (fa, RSReturn rvs))
                                  | RSNormal (lsvesa, lses) ->
                                    (sa, (fa,
   RSNormal
     (ves, Label (ln, les,
                   map (fun v -> Basic (EConst v)) (rev lsvesa) @ lses) ::
             esa)))))))
                 | Frame (ln, fls, esaa) ->
                   (if es_is_trap esaa
                     then (s, (f, RSNormal (ves, Trap :: esa)))
                     else (match split_vals_e esaa
                            with (fsves, []) ->
                              (s, (f, RSNormal (rev fsves @ ves, esa)))
                            | (fsves, aa :: lista) ->
                              (if equal_nat d zero_nat
                                then (s, (f, RSCrash CExhaustion))
                                else (match
                                       run_step (minus_nat d one_nata)
 (s, (fls, (rev fsves, aa :: lista)))
                                       with (sa, (_, RSCrash c)) ->
 (sa, (f, RSCrash c))
                                       | (sa, (_, RSBreak (_, _))) ->
 (sa, (f, RSCrash CError))
                                       | (sa, (_, RSReturn rvs)) ->
 (if less_eq_nat ln (size_list rvs)
   then (sa, (f, RSNormal (take ln rvs @ ves, esa)))
   else (sa, (f, RSCrash CError)))
                                       | (sa, (flsa, RSNormal (fsvesa, fses)))
 -> (sa, (f, RSNormal
               (ves, Frame (ln, flsa,
                             map (fun v -> Basic (EConst v)) (rev fsvesa) @
                               fses) ::
                       esa))))))))));;

let rec run_vs_es
  n d (s, (f, (ves, es))) =
    (if equal_nat n zero_nat then (s, RCrash CExhaustion)
      else (if es_is_trap es then (s, RTrap)
             else (if null es then (s, RValue (rev ves))
                    else (match run_step d (s, (f, (ves, es)))
                           with (_, (_, RSCrash error)) -> (s, RCrash error)
                           | (_, (_, RSBreak (_, _))) -> (s, RCrash CError)
                           | (_, (_, RSReturn _)) -> (s, RCrash CError)
                           | (sa, (fa, RSNormal (vesa, esa))) ->
                             run_vs_es (minus_nat n one_nata) d
                               (sa, (fa, (vesa, esa)))))));;

let rec run_v
  n d (s, (f, es)) =
    (let (ves, esa) = split_vals_e es in
      run_vs_es n d (s, (f, (rev ves, esa))));;

let rec const_expr_p
  x xa =
    sup_pred
      (bind (single (x, xa))
        (fun a ->
          (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
            | (_, Drop) -> bot_pred | (_, Select) -> bot_pred
            | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
            | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
            | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
            | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
            | (_, Call_indirect _) -> bot_pred | (_, Get_local _) -> bot_pred
            | (_, Set_local _) -> bot_pred | (_, Tee_local _) -> bot_pred
            | (_, Get_global _) -> bot_pred | (_, Set_global _) -> bot_pred
            | (_, Load (_, _, _, _)) -> bot_pred
            | (_, Store (_, _, _, _)) -> bot_pred
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> single () | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred)))
      (bind (single (x, xa))
        (fun a ->
          (match a with (_, Unreachable) -> bot_pred | (_, Nop) -> bot_pred
            | (_, Drop) -> bot_pred | (_, Select) -> bot_pred
            | (_, Block (_, _)) -> bot_pred | (_, Loop (_, _)) -> bot_pred
            | (_, If (_, _, _)) -> bot_pred | (_, Br _) -> bot_pred
            | (_, Br_if _) -> bot_pred | (_, Br_table (_, _)) -> bot_pred
            | (_, Return) -> bot_pred | (_, Call _) -> bot_pred
            | (_, Call_indirect _) -> bot_pred | (_, Get_local _) -> bot_pred
            | (_, Set_local _) -> bot_pred | (_, Tee_local _) -> bot_pred
            | (c, Get_global k) ->
              bind (if_pred (less_nat k (size_list (global c))))
                (fun () ->
                  bind (eq_i_i equal_mut (tg_mut (nth (global c) k)) T_immut)
                    (fun () -> single ()))
            | (_, Set_global _) -> bot_pred | (_, Load (_, _, _, _)) -> bot_pred
            | (_, Store (_, _, _, _)) -> bot_pred
            | (_, Current_memory) -> bot_pred | (_, Grow_memory) -> bot_pred
            | (_, EConst _) -> bot_pred | (_, Unop (_, _)) -> bot_pred
            | (_, Binop (_, _)) -> bot_pred | (_, Testop (_, _)) -> bot_pred
            | (_, Relop (_, _)) -> bot_pred
            | (_, Cvtop (_, _, _, _)) -> bot_pred)));;

let rec const_expr x1 x2 = holds (const_expr_p x1 x2);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec funcs_update
  funcsa (S_ext (funcs, tabs, mems, globs, more)) =
    S_ext (funcsa funcs, tabs, mems, globs, more);;

let rec m_exports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_exports;;

let rec m_imports
  (M_ext
    (m_types, m_funcs, m_tabs, m_mems, m_globs, m_elem, m_data, m_start,
      m_imports, m_exports, more))
    = m_imports;;

let rec limit_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (Limit_t_ext (n, m_opt, ()), k) ->
        bind (if_pred
               (less_eq_nat k
                 (power power_nat (nat_of_integer (Z.of_int 2))
                   (nat_of_integer (Z.of_int 32)))))
          (fun () ->
            bind (if_pred (less_eq_nat n k))
              (fun () ->
                bind (if_pred (pred_option (fun m -> less_eq_nat m k) m_opt))
                  (fun () ->
                    bind (if_pred (pred_option (less_eq_nat n) m_opt))
                      (fun () -> single ())))));;

let rec limit_typing x1 x2 = holds (limit_type_checker_p x1 x2);;

let rec alloc_Xs
  f s x2 = match f, s, x2 with f, s, [] -> (s, [])
    | f, s, m_X :: m_Xs ->
        (let (sa, i_X) = f s m_X in
         let (sb, i_Xs) = alloc_Xs f sa m_Xs in
          (sb, i_X :: i_Xs));;

let rec d_init (Module_data_ext (d_data, d_off, d_init, more)) = d_init;;

let rec d_data (Module_data_ext (d_data, d_off, d_init, more)) = d_data;;

let rec init_mem
  s inst d_ind d =
    (let m_ind = nth (memsa inst) (d_data d) in
     let mem = nth (mems s) m_ind in
     let mema = write_bytes mem d_ind (d_init d) in
      mems_update (fun _ -> list_update (mems s) m_ind mema) s);;

let rec e_init (Module_elem_ext (e_tab, e_off, e_init, more)) = e_init;;

let rec e_tab (Module_elem_ext (e_tab, e_off, e_init, more)) = e_tab;;

let rec init_tab
  s inst e_ind e =
    (let t_ind = nth (tabsa inst) (e_tab e) in
     let (tab_e, max) = nth (tabs s) t_ind in
     let e_pay = map (fun i -> Some (nth (funcsa inst) i)) (e_init e) in
     let tab_ea =
       take e_ind tab_e @ e_pay @ drop (plus_nat e_ind (size_list e_pay)) tab_e
       in
      tabs_update (fun _ -> list_update (tabs s) t_ind (tab_ea, max)) s);;

let rec external_checker
  x xa xb =
    sup_pred
      (bind (single (x, (xa, xb)))
        (fun a ->
          (match a
            with (s, (Ext_func i, Te_func tf)) ->
              bind (if_pred (less_nat i (size_list (funcs s))))
                (fun () ->
                  bind (eq_i_i equal_tf (cl_type (nth (funcs s) i)) tf)
                    (fun () -> single ()))
            | (_, (Ext_func _, Te_tab _)) -> bot_pred
            | (_, (Ext_func _, Te_mem _)) -> bot_pred
            | (_, (Ext_func _, Te_glob _)) -> bot_pred
            | (_, (Ext_tab _, _)) -> bot_pred | (_, (Ext_mem _, _)) -> bot_pred
            | (_, (Ext_glob _, _)) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, xb)))
          (fun a ->
            (match a with (_, (Ext_func _, _)) -> bot_pred
              | (_, (Ext_tab _, Te_func _)) -> bot_pred
              | (s, (Ext_tab i, Te_tab tt)) ->
                bind (if_pred (less_nat i (size_list (tabs s))))
                  (fun () ->
                    bind (if_pred (tab_typing (nth (tabs s) i) tt))
                      (fun () -> single ()))
              | (_, (Ext_tab _, Te_mem _)) -> bot_pred
              | (_, (Ext_tab _, Te_glob _)) -> bot_pred
              | (_, (Ext_mem _, _)) -> bot_pred
              | (_, (Ext_glob _, _)) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, xb)))
            (fun a ->
              (match a with (_, (Ext_func _, _)) -> bot_pred
                | (_, (Ext_tab _, _)) -> bot_pred
                | (_, (Ext_mem _, Te_func _)) -> bot_pred
                | (_, (Ext_mem _, Te_tab _)) -> bot_pred
                | (s, (Ext_mem i, Te_mem mt)) ->
                  bind (if_pred (less_nat i (size_list (mems s))))
                    (fun () ->
                      bind (if_pred (mem_typing (nth (mems s) i) mt))
                        (fun () -> single ()))
                | (_, (Ext_mem _, Te_glob _)) -> bot_pred
                | (_, (Ext_glob _, _)) -> bot_pred)))
          (bind (single (x, (xa, xb)))
            (fun a ->
              (match a with (_, (Ext_func _, _)) -> bot_pred
                | (_, (Ext_tab _, _)) -> bot_pred
                | (_, (Ext_mem _, _)) -> bot_pred
                | (_, (Ext_glob _, Te_func _)) -> bot_pred
                | (_, (Ext_glob _, Te_tab _)) -> bot_pred
                | (_, (Ext_glob _, Te_mem _)) -> bot_pred
                | (s, (Ext_glob i, Te_glob gt)) ->
                  bind (if_pred (less_nat i (size_list (globs s))))
                    (fun () ->
                      bind (if_pred (glob_typing (nth (globs s) i) gt))
                        (fun () -> single ())))))));;

let rec external_typing x1 x2 x3 = holds (external_checker x1 x2 x3);;

let rec typing x = b_e_type_checker x;;

let rec alloc_mem
  s m_m = (mems_update (fun _ -> mems s @ [mem_mk m_m]) s, size_list (mems s));;

let rec alloc_tab
  s m_t =
    (tabs_update (fun _ -> tabs s @ [(replicate (l_min m_t) None, l_max m_t)])
       s,
      size_list (tabs s));;

let rec init_mems
  s inst d_inds ds =
    foldl (fun sa (a, b) -> init_mem sa inst a b) s (zip d_inds ds);;

let rec init_tabs
  s inst e_inds es =
    foldl (fun sa (a, b) -> init_tab sa inst a b) s (zip e_inds es);;

let rec export_get_v_ext
  inst exp =
    (match exp with Ext_func i -> Ext_func (nth (funcsa inst) i)
      | Ext_tab i -> Ext_tab (nth (tabsa inst) i)
      | Ext_mem i -> Ext_mem (nth (memsa inst) i)
      | Ext_glob i -> Ext_glob (nth (globsa inst) i));;

let rec alloc_func
  s m_f inst =
    (let (i_t, (loc_ts, b_es)) = m_f in
      (funcs_update
         (fun _ ->
           funcs s @ [Func_native (inst, nth (types inst) i_t, loc_ts, b_es)])
         s,
        size_list (funcs s)));;

let rec g_type (Module_glob_ext (g_type, g_init, more)) = g_type;;

let rec alloc_glob
  s m_g_v =
    (let (m_g, v) = m_g_v in
      (globs_update
         (fun _ -> globs s @ [Global_ext (tg_mut (g_type m_g), v, ())]) s,
        size_list (globs s)));;

let rec run
  x = run_v (power power_nat (nat_of_integer (Z.of_int 2))
              (nat_of_integer (Z.of_int 63)))
        (nat_of_integer (Z.of_int 300)) x;;

let rec d_off (Module_data_ext (d_data, d_off, d_init, more)) = d_off;;

let rec e_off (Module_elem_ext (e_tab, e_off, e_init, more)) = e_off;;

let rec g_init (Module_glob_ext (g_type, g_init, more)) = g_init;;

let rec local_update
  locala
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, locala local, label, return,
          more);;

let rec interp_get_v
  s inst b_es =
    (let (_, RValue [v]) =
       run_v (nat_of_integer (Z.of_int 2)) zero_nat
         (s, (F_ext ([], inst, ()), map (fun a -> Basic a) b_es))
       in
      v);;

let rec module_start_type_checker_p
  x xa =
    bind (single (x, xa))
      (fun (c, i) ->
        bind (if_pred (less_nat i (size_list (func_t c))))
          (fun () ->
            bind (eq_i_i equal_tf (nth (func_t c) i) (Tf ([], [])))
              (fun () -> single ())));;

let rec module_start_typing x1 x2 = holds (module_start_type_checker_p x1 x2);;

let rec return_update
  returna
    (T_context_ext
      (types_t, func_t, global, table, memory, local, label, return, more))
    = T_context_ext
        (types_t, func_t, global, table, memory, local, label, returna return,
          more);;

let rec e_desc (Module_export_ext (e_name, e_desc, more)) = e_desc;;

let rec e_name (Module_export_ext (e_name, e_desc, more)) = e_name;;

let rec i_desc (Module_import_ext (i_module, i_name, i_desc, more)) = i_desc;;

let rec interp_get_i32
  s inst b_es =
    (match interp_get_v s inst b_es with ConstInt32 c -> c
      | ConstInt64 _ -> I32Wrapper.zero | ConstFloat32 _ -> I32Wrapper.zero
      | ConstFloat64 _ -> I32Wrapper.zero);;

let rec gather_m_f_type
  tfs m_f =
    (if less_nat (fst m_f) (size_list tfs) then Some (nth tfs (fst m_f))
      else None);;

let rec module_glob_type_checker
  c (Module_glob_ext (tg, es, ())) =
    list_all (const_expr c) es && b_e_type_checker c es (Tf ([], [tg_t tg]));;

let rec module_func_type_checker
  c (i, (t_locs, b_es)) =
    less_nat i (size_list (types_t c)) &&
      (let Tf (tn, tm) = nth (types_t c) i in
        b_e_type_checker
          (return_update (fun _ -> Some tm)
            (label_update (fun _ -> [tm] @ label c)
              (local_update (fun _ -> tn @ t_locs) c)))
          b_es (Tf ([], tm)));;

let rec module_elem_type_checker
  c (Module_elem_ext (t, es, is, ())) =
    list_all (const_expr c) es &&
      (b_e_type_checker c es (Tf ([], [T_i32])) &&
        (less_nat t (size_list (table c)) &&
          list_all (fun i -> less_nat i (size_list (func_t c))) is));;

let rec module_data_type_checker
  c (Module_data_ext (d, es, bs, ())) =
    list_all (const_expr c) es &&
      (b_e_type_checker c es (Tf ([], [T_i32])) &&
        less_nat d (size_list (memory c)));;

let rec module_import_typer
  tfs x1 = match tfs, x1 with
    tfs, Imp_func i ->
      (if less_nat i (size_list tfs) then Some (Te_func (nth tfs i)) else None)
    | tfs, Imp_tab tt ->
        (if limit_typing tt
              (power power_nat (nat_of_integer (Z.of_int 2))
                (nat_of_integer (Z.of_int 32)))
          then Some (Te_tab tt) else None)
    | tfs, Imp_mem mt ->
        (if limit_typing mt
              (power power_nat (nat_of_integer (Z.of_int 2))
                (nat_of_integer (Z.of_int 16)))
          then Some (Te_mem mt) else None)
    | tfs, Imp_glob gt -> Some (Te_glob gt);;

let rec module_export_typer
  c x1 = match c, x1 with
    c, Ext_func i ->
      (if less_nat i (size_list (func_t c))
        then Some (Te_func (nth (func_t c) i)) else None)
    | c, Ext_tab i ->
        (if less_nat i (size_list (table c))
          then Some (Te_tab (nth (table c) i)) else None)
    | c, Ext_mem i ->
        (if less_nat i (size_list (memory c))
          then Some (Te_mem (nth (memory c) i)) else None)
    | c, Ext_glob i ->
        (if less_nat i (size_list (global c))
          then Some (Te_glob (nth (global c) i)) else None);;

let rec module_type_checker
  (M_ext (tfs, fs, ts, ms, gs, els, ds, i_opt, imps, exps, ())) =
    (match
      (those (map (gather_m_f_type tfs) fs),
        those (map (fun imp -> module_import_typer tfs (i_desc imp)) imps))
      with (None, _) -> None | (Some _, None) -> None
      | (Some fts, Some impts) ->
        (let ifts =
           map_filter
             (fun a ->
               (match a with Te_func aa -> Some aa | Te_tab _ -> None
                 | Te_mem _ -> None | Te_glob _ -> None))
             impts
           in
         let its =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab aa -> Some aa
                 | Te_mem _ -> None | Te_glob _ -> None))
             impts
           in
         let ims =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab _ -> None
                 | Te_mem aa -> Some aa | Te_glob _ -> None))
             impts
           in
         let igs =
           map_filter
             (fun a ->
               (match a with Te_func _ -> None | Te_tab _ -> None
                 | Te_mem _ -> None | Te_glob aa -> Some aa))
             impts
           in
         let gts = map g_type gs in
         let c =
           T_context_ext
             (tfs, ifts @ fts, igs @ gts, its @ ts, ims @ ms, [], [], None, ())
           in
         let ca = T_context_ext ([], [], igs, [], [], [], [], None, ()) in
          (if list_all (fun (Tf (_, tm)) -> less_eq_nat (size_list tm) one_nata)
                tfs &&
                (list_all (module_func_type_checker c) fs &&
                  (list_all
                     (fun t ->
                       limit_typing t
                         (power power_nat (nat_of_integer (Z.of_int 2))
                           (nat_of_integer (Z.of_int 32))))
                     ts &&
                    (list_all
                       (fun t ->
                         limit_typing t
                           (power power_nat (nat_of_integer (Z.of_int 2))
                             (nat_of_integer (Z.of_int 16))))
                       ms &&
                      (list_all (module_glob_type_checker ca) gs &&
                        (list_all (module_elem_type_checker c) els &&
                          (list_all (module_data_type_checker c) ds &&
                            (pred_option (module_start_typing c) i_opt &&
                              (distinct equal_literal (map e_name exps) &&
                                (less_eq_nat (size_list (its @ ts)) one_nata &&
                                  less_eq_nat (size_list (ims @ ms))
                                    one_nata)))))))))
            then (match
                   those (map (fun exp -> module_export_typer c (e_desc exp))
                           exps)
                   with None -> None | Some expts -> Some (impts, expts))
            else None)));;

let rec interp_alloc_module
  s m imps gvs =
    (let i_fs =
       upt (size_list (funcs s))
         (plus_nat (size_list (funcs s)) (size_list (m_funcs m)))
       in
     let i_ts =
       upt (size_list (tabs s))
         (plus_nat (size_list (tabs s)) (size_list (m_tabs m)))
       in
     let i_ms =
       upt (size_list (mems s))
         (plus_nat (size_list (mems s)) (size_list (m_mems m)))
       in
     let i_gs =
       upt (size_list (globs s))
         (plus_nat (size_list (globs s))
           (min ord_nat (size_list (m_globs m)) (size_list gvs)))
       in
     let inst =
       Inst_ext
         (m_types m,
           map_filter
             (fun a ->
               (match a with Ext_func aa -> Some aa | Ext_tab _ -> None
                 | Ext_mem _ -> None | Ext_glob _ -> None))
             imps @
             i_fs,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab aa -> Some aa
                 | Ext_mem _ -> None | Ext_glob _ -> None))
             imps @
             i_ts,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab _ -> None
                 | Ext_mem aa -> Some aa | Ext_glob _ -> None))
             imps @
             i_ms,
           map_filter
             (fun a ->
               (match a with Ext_func _ -> None | Ext_tab _ -> None
                 | Ext_mem _ -> None | Ext_glob aa -> Some aa))
             imps @
             i_gs,
           ())
       in
     let (s1, _) = alloc_Xs (fun sa m_f -> alloc_func sa m_f inst) s (m_funcs m)
       in
     let (s2, _) = alloc_Xs alloc_tab s1 (m_tabs m) in
     let (s3, _) = alloc_Xs alloc_mem s2 (m_mems m) in
     let (sa, _) = alloc_Xs alloc_glob s3 (zip (m_globs m) gvs) in
     let exps =
       map (fun m_exp ->
             Module_export_ext
               (e_name m_exp, export_get_v_ext inst (e_desc m_exp), ()))
         (m_exports m)
       in
      (sa, (inst, exps)));;

let rec interp_instantiate
  s m v_imps =
    (match module_type_checker m with None -> None
      | Some (t_imps, _) ->
        (if list_all2 (external_typing s) v_imps t_imps
          then (let g_inits =
                  map (fun g ->
                        interp_get_v s
                          (Inst_ext
                            ([], [], [], [],
                              map_filter
                                (fun a ->
                                  (match a with Ext_func _ -> None
                                    | Ext_tab _ -> None | Ext_mem _ -> None
                                    | Ext_glob aa -> Some aa))
                                v_imps,
                              ()))
                          (g_init g))
                    (m_globs m)
                  in
                let (sa, (inst, v_exps)) =
                  interp_alloc_module s m v_imps g_inits in
                let e_offs =
                  map (fun e -> interp_get_i32 sa inst (e_off e)) (m_elem m) in
                let d_offs =
                  map (fun d -> interp_get_i32 sa inst (d_off d)) (m_data m) in
                 (if list_all2
                       (fun e_offa e ->
                         less_eq_nat
                           (plus_nat (Nat (I32Wrapper.z_of_int e_offa))
                             (size_list (e_init e)))
                           (size_list
                             (fst (nth (tabs sa)
                                    (nth (tabsa inst) (e_tab e))))))
                       e_offs (m_elem m) &&
                       list_all2
                         (fun d_offa d ->
                           less_eq_nat
                             (plus_nat (Nat (I32Wrapper.z_of_int d_offa))
                               (size_list (d_init d)))
                             (mem_length
                               (nth (mems sa) (nth (memsa inst) (d_data d)))))
                         d_offs (m_data m)
                   then (let start = map_option (nth (funcsa inst)) (m_start m)
                           in
                         let sb =
                           init_tabs sa inst
                             (map (fun a -> Nat (I32Wrapper.z_of_int a)) e_offs)
                             (m_elem m)
                           in
                         let s_end =
                           init_mems sb inst
                             (map (fun a -> Nat (I32Wrapper.z_of_int a)) d_offs)
                             (m_data m)
                           in
                          Some ((s_end, (inst, v_exps)), start))
                   else None))
          else None));;

end;; (*struct WasmRef_Isa*)
