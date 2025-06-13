open WasmRef_Isa.WasmRef_Isa
open Source
open Types
open Values
open Script

exception PostMVP
exception InvalidModule

let convert_t_num = function
  | I32Type -> T_i32
  | F32Type -> T_f32
  | I64Type -> T_i64
  | F64Type -> T_f64
  | _ -> raise PostMVP

let convert_t_vec = function
  | V128Type -> T_v128
  | _ -> raise PostMVP

let convert_t_ref = function
  | FuncRefType -> T_func_ref
  | ExternRefType -> T_ext_ref

let convert_t = function
  | NumType t -> T_num (convert_t_num t)
  | VecType t -> T_vec (convert_t_vec t)
  | RefType t -> T_ref (convert_t_ref t)
  | _ -> raise PostMVP

let convert_vltype vl_type = List.map convert_t vl_type

let convert_vltype_opt t_maybe = (match t_maybe with | Some t -> [convert_t t] | None -> [])

let ocaml_int_to_nat n = nat_of_integer (Z.of_int n)
let ocaml_int32_to_nat n = nat_of_integer (LibAux.z_of_uint32 n)

let var_to_nat n = ocaml_int32_to_nat n.it

let convert_tp = function
	| Types.Pack8 -> Tp_i8
	| Types.Pack16 -> Tp_i16
	| Types.Pack32 -> Tp_i32
        | _ -> raise PostMVP

let convert_sx = function
	| Types.SX -> S
	| Types.ZX -> U

let convert_value_num = function
	| I32 c -> ConstInt32 (ocaml_int32_to_isabelle_int32 c)
	| I64 c -> ConstInt64 (ocaml_int64_to_isabelle_int64 c)
	| F32 c -> ConstFloat32 c
	| F64 c -> ConstFloat64 c

let convert_value_vec = function
	| V128 c -> ConstVec128 c

let convert_value_ref = function
  | NullRef t_r -> (ConstNull (convert_t_ref t_r))
  | ExternRef x -> (ConstRefExtern (Host_ref  x))
  (* | ConstRefFunc i -> () *)
  | _ -> raise PostMVP

let convert_value = function
        | Num n -> V_num (convert_value_num n)
        | Vec v-> V_vec (convert_value_vec v)
        | Ref r -> V_ref (convert_value_ref r)
        | _ -> raise PostMVP

let convert_value_num_rev = function
	| ConstInt32 c -> I32 (isabelle_int32_to_ocaml_int32 c)
	| ConstInt64 c -> I64 (isabelle_int64_to_ocaml_int64 c)
	| ConstFloat32 c -> F32 c
	| ConstFloat64 c -> F64 c

let convert_value_vec_rev = function
	| ConstVec128 c -> V128 c

let convert_t_ref_rev = function
  | T_func_ref -> FuncRefType
  | T_ext_ref -> ExternRefType

  let convert_value_ref_rev = function
	| (ConstRefExtern (Host_ref  x)) -> ExternRef x
  | (ConstNull t_r) -> NullRef (convert_t_ref_rev t_r)
  | _ -> raise PostMVP

let convert_value_rev = function
        | V_num v -> Num (convert_value_num_rev v)
        | V_vec v -> Vec (convert_value_vec_rev v)
        | V_ref v -> (Ref (convert_value_ref_rev v))
        | _ -> raise PostMVP

let convert_int_testop = function
	| Ast.IntOp.Eqz -> Eqz

let convert_testop = function
	| I32 op -> Testop (T_i32, convert_int_testop op)
	| I64 op -> Testop (T_i64, convert_int_testop op)
	| _  -> failwith "ill-formed"

let convert_int_compareop = function
  | Ast.IntOp.Eq -> Eq
	| Ast.IntOp.Ne -> Ne
	| Ast.IntOp.LtS -> Lt S
  | Ast.IntOp.LtU -> Lt U
	| Ast.IntOp.GtS -> Gt S
	| Ast.IntOp.GtU -> Gt U
	| Ast.IntOp.LeS -> Le S
	| Ast.IntOp.LeU -> Le U
	| Ast.IntOp.GeS -> Ge S
	| Ast.IntOp.GeU -> Ge U

let convert_float_compareop = function
	| Ast.FloatOp.Eq -> Eqf
	| Ast.FloatOp.Ne -> Nef
	| Ast.FloatOp.Lt -> Ltf
	| Ast.FloatOp.Gt -> Gtf
	| Ast.FloatOp.Le -> Lef
	| Ast.FloatOp.Ge -> Gef

let convert_compareop = function
	| I32 op -> Relop (T_i32, Relop_i (convert_int_compareop op))
	| I64 op -> Relop (T_i64, Relop_i (convert_int_compareop op))
	| F32 op -> Relop (T_f32, Relop_f (convert_float_compareop op))
	| F64 op -> Relop (T_f64, Relop_f (convert_float_compareop op))

let convert_int_unop = function
	| Ast.IntOp.Clz -> Unop_i Clz
	| Ast.IntOp.Ctz -> Unop_i Ctz
	| Ast.IntOp.Popcnt -> Unop_i Popcnt
        | Ast.IntOp.ExtendS tp -> Extend_s (convert_tp tp)

let convert_float_unop = function
	| Ast.FloatOp.Neg -> Neg
	| Ast.FloatOp.Abs -> Abs
	| Ast.FloatOp.Ceil -> Ceil
	| Ast.FloatOp.Floor -> Floor
	| Ast.FloatOp.Trunc -> Trunc
	| Ast.FloatOp.Nearest -> Nearest
	| Ast.FloatOp.Sqrt -> Sqrt

let convert_unop = function
	| I32 op -> Unop (T_i32, (convert_int_unop op))
	| I64 op -> Unop (T_i64, (convert_int_unop op))
	| F32 op -> Unop (T_f32, Unop_f (convert_float_unop op))
	| F64 op  -> Unop (T_f64, Unop_f (convert_float_unop op))

let convert_int_binop = function
	| Ast.IntOp.Add -> Add
	| Ast.IntOp.Sub -> Sub
	| Ast.IntOp.Mul -> Mul
	| Ast.IntOp.DivS -> Div S
	| Ast.IntOp.DivU -> Div U
	| Ast.IntOp.RemS -> Rem S
	| Ast.IntOp.RemU -> Rem U
	| Ast.IntOp.And -> And
	| Ast.IntOp.Or -> Or
	| Ast.IntOp.Xor -> Xor
	| Ast.IntOp.Shl -> Shl
	| Ast.IntOp.ShrS -> Shr S
	| Ast.IntOp.ShrU -> Shr U
	| Ast.IntOp.Rotl -> Rotl
	| Ast.IntOp.Rotr -> Rotr

let convert_float_binop = function
	| Ast.FloatOp.Add -> Addf
	| Ast.FloatOp.Sub -> Subf
	| Ast.FloatOp.Mul -> Mulf
	| Ast.FloatOp.Div -> Divf
	| Ast.FloatOp.Min -> Min
	| Ast.FloatOp.Max -> Max
	| Ast.FloatOp.CopySign -> Copysign

let convert_binop = function
	| I32 op -> Binop (T_i32, Binop_i (convert_int_binop op))
	| I64 op -> Binop (T_i64, Binop_i (convert_int_binop op))
	| F32 op -> Binop (T_f32, Binop_f (convert_float_binop op))
	| F64 op  -> Binop (T_f64, Binop_f (convert_float_binop op))

let t_reinterpret = function
	| T_i32 -> T_f32
	| T_i64 -> T_f64
	| T_f32 -> T_i32
	| T_f64 -> T_i64
        | _ -> raise PostMVP

let convert_int_convertop t1 = function
	| Ast.IntOp.ExtendSI32 -> Cvtop (t1, Convert, T_i32, Some (Nonsat, S))
	| Ast.IntOp.ExtendUI32 -> Cvtop (t1, Convert, T_i32, Some (Nonsat, U))
	| Ast.IntOp.WrapI64 -> Cvtop (t1, Convert, T_i64, None)
	| Ast.IntOp.TruncSF32 -> Cvtop (t1, Convert, T_f32, Some (Nonsat, S))
	| Ast.IntOp.TruncUF32 -> Cvtop (t1, Convert, T_f32, Some (Nonsat, U))
	| Ast.IntOp.TruncSF64 -> Cvtop (t1, Convert, T_f64, Some (Nonsat, S))
	| Ast.IntOp.TruncUF64 -> Cvtop (t1, Convert, T_f64, Some (Nonsat, U))
	| Ast.IntOp.TruncSatSF32 -> Cvtop (t1, Convert, T_f32, Some (Sat, S))
	| Ast.IntOp.TruncSatUF32 -> Cvtop (t1, Convert, T_f32, Some (Sat, U))
	| Ast.IntOp.TruncSatSF64 -> Cvtop (t1, Convert, T_f64, Some (Sat, S))
	| Ast.IntOp.TruncSatUF64 -> Cvtop (t1, Convert, T_f64, Some (Sat, U))
	| Ast.IntOp.ReinterpretFloat -> Cvtop (t1, Reinterpret, t_reinterpret t1, None)
        | _ -> raise PostMVP

let convert_float_convertop t1 = function
  | Ast.FloatOp.ConvertSI32 -> Cvtop (t1, Convert, T_i32, Some (Nonsat, S))
  | Ast.FloatOp.ConvertUI32 -> Cvtop (t1, Convert, T_i32, Some (Nonsat, U))
  | Ast.FloatOp.ConvertSI64 -> Cvtop (t1, Convert, T_i64, Some (Nonsat, S))
  | Ast.FloatOp.ConvertUI64 -> Cvtop (t1, Convert, T_i64, Some (Nonsat, U))
  | Ast.FloatOp.PromoteF32 -> Cvtop (t1, Convert, T_f32, None)
  | Ast.FloatOp.DemoteF64 -> Cvtop (t1, Convert, T_f64, None)
  | Ast.FloatOp.ReinterpretInt -> Cvtop (t1, Reinterpret, t_reinterpret t1, None)

let convert_convertop = function
	| I32 op -> convert_int_convertop T_i32 op
	| I64 op -> convert_int_convertop T_i64 op
	| F32 op -> convert_float_convertop T_f32 op
	| F64 op  -> convert_float_convertop T_f64 op

let convert_ftype' = function
	| FuncType (stype1, stype2) -> Tf (convert_vltype stype1, convert_vltype stype2)

let convert_ftype ft = convert_ftype' (ft.it)

let convert_tb = function
  | Ast.VarBlockType i -> Tbf (var_to_nat i)
  | Ast.ValBlockType (Some t) -> Tbv (Some (convert_t t))
  | Ast.ValBlockType None -> Tbv None

let convert_load_tp_sx = function
	| None -> None
	| Some (mtp, msx) -> Some (convert_tp mtp, convert_sx msx)

let convert_store_tp = function
	| None -> None
	| Some mtp -> Some (convert_tp mtp)

let convert_pack_size_to_shape_vec_i = function
        | Pack8 -> I8_16 | Pack16 -> I16_8 | Pack32 -> I32_4 | Pack64 -> I64_2

let convert_pack_shape_to_tp_vec = function
        | Pack8x8 -> Tp_v8_8 | Pack16x4 -> Tp_v16_4 | Pack32x2 -> Tp_v32_2

let convert_extension_to_sx = function
        | SX -> S | ZX -> U

let convert_loadop_vec = function
	| None -> Load_128
        (* TODO: check if there are constraints on x for the ExtLane case *)
        | Some (x,ExtLane (ps,ext)) -> Load_packed_vec ((convert_pack_shape_to_tp_vec ps), (convert_extension_to_sx ext))
	| Some (Pack32,ExtZero) -> Load_32_zero
	| Some (Pack64,ExtZero) -> Load_64_zero
	| Some (x,ExtSplat) -> Load_splat (convert_pack_size_to_shape_vec_i x)
        | _ -> failwith "loadop_vec invariant"

let convert_splatop_to_shape_vec = function
  | V128 (V128.I8x16 Ast.V128Op.Splat) -> Svi I8_16
  | V128 (V128.I16x8 Ast.V128Op.Splat) -> Svi I16_8
  | V128 (V128.I32x4 Ast.V128Op.Splat) -> Svi I32_4
  | V128 (V128.I64x2 Ast.V128Op.Splat) -> Svi I64_2
  | V128 (V128.F32x4 Ast.V128Op.Splat) -> Svf F32_4
  | V128 (V128.F64x2 Ast.V128Op.Splat) -> Svf F64_2

let convert_replaceop_to_shape_vec_and_i = function
  | V128 (V128.I8x16 (Ast.V128Op.Replace i)) -> (Svi I8_16, ocaml_int_to_nat i)
  | V128 (V128.I16x8 (Ast.V128Op.Replace i)) -> (Svi I16_8, ocaml_int_to_nat i)
  | V128 (V128.I32x4 (Ast.V128Op.Replace i)) -> (Svi I32_4, ocaml_int_to_nat i)
  | V128 (V128.I64x2 (Ast.V128Op.Replace i)) -> (Svi I64_2, ocaml_int_to_nat i)
  | V128 (V128.F32x4 (Ast.V128Op.Replace i)) -> (Svf F32_4, ocaml_int_to_nat i)
  | V128 (V128.F64x2 (Ast.V128Op.Replace i)) -> (Svf F64_2, ocaml_int_to_nat i)

let convert_extractop_to_shape_vec_and_sx_and_i = function
  | V128 (V128.I8x16 (Ast.V128Op.Extract (i,ext))) -> (Svi I8_16, convert_extension_to_sx ext, ocaml_int_to_nat i)
  | V128 (V128.I16x8 (Ast.V128Op.Extract (i,ext))) -> (Svi I16_8, convert_extension_to_sx ext, ocaml_int_to_nat i)
  | V128 (V128.I32x4 (Ast.V128Op.Extract (i,_))) -> (Svi I32_4, U, ocaml_int_to_nat i)
  | V128 (V128.I64x2 (Ast.V128Op.Extract (i,_))) -> (Svi I64_2, U, ocaml_int_to_nat i)
  | V128 (V128.F32x4 (Ast.V128Op.Extract (i,_))) -> (Svf F32_4, U, ocaml_int_to_nat i)
  | V128 (V128.F64x2 (Ast.V128Op.Extract (i,_))) -> (Svf F64_2, U, ocaml_int_to_nat i)

let rec convert_instr instr =
	match instr.it with
	| Ast.Unreachable -> Unreachable
	| Ast.Nop -> Nop
        (* TODO: multi-value *)
	| Ast.Block (tb, binstrs) ->
            Block (convert_tb tb, convert_instrs binstrs)
	| Ast.Loop (tb, binstrs) ->
            Loop (convert_tb tb, convert_instrs binstrs)
	| Ast.If (tb, binstrs1, binstrs2) ->
            If (convert_tb tb, convert_instrs binstrs1, convert_instrs binstrs2)
	| Ast.Br n -> Br (var_to_nat n)
 	| Ast.BrIf n -> Br_if (var_to_nat n)
	| Ast.BrTable (ns, n) -> Br_table (List.map var_to_nat ns, var_to_nat n)
	| Ast.Return -> Return
	| Ast.Call n -> Call (var_to_nat n)
	| Ast.CallIndirect(n, y) -> Call_indirect (var_to_nat n, var_to_nat y)
	| Ast.Drop -> Drop
	| Ast.Select None -> Select None
  | Ast.Select (Some []) -> Select None
  | Ast.Select (Some (t::_)) -> Select (Some (convert_t t))
	| Ast.LocalGet n -> Get_local (var_to_nat n)
	| Ast.LocalSet n -> Set_local (var_to_nat n)
	| Ast.LocalTee n -> Tee_local (var_to_nat n)
	| Ast.GlobalGet n -> Get_global (var_to_nat n)
	| Ast.GlobalSet n -> Set_global (var_to_nat n)
	| Ast.Load lop -> let {Ast.ty; Ast.align; Ast.offset; Ast.pack} = lop in
	                  Load ((convert_t_num ty), convert_load_tp_sx pack, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
	| Ast.Store sop -> let {Ast.ty; Ast.align; Ast.offset; Ast.pack} = sop in
	                   Store ((convert_t_num ty), convert_store_tp pack, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
	| Ast.MemorySize -> Current_memory
	| Ast.MemoryGrow -> Grow_memory
	| Ast.Const v -> EConstNum (convert_value_num v.it)
	| Ast.Test top -> convert_testop top
	| Ast.Compare cop -> convert_compareop cop
	| Ast.Unary uop -> convert_unop uop
	| Ast.Binary bop -> convert_binop bop
	| Ast.Convert cop -> convert_convertop cop

	| Ast.VecConst v -> EConstVec (convert_value_vec v.it)
        | Ast.VecTest op -> Test_vec (V128Wrapper.Testop_VecTest op)
        | Ast.VecTestBits op -> Test_vec (V128Wrapper.Testop_VecTestBits op)
        | Ast.VecBitmask op -> Test_vec (V128Wrapper.Testop_VecBitmask op)
        | Ast.VecUnary op -> Unop_vec (V128Wrapper.Unop_VecUnary op)
        | Ast.VecUnaryBits op -> Unop_vec (V128Wrapper.Unop_VecUnaryBits op)
        | Ast.VecConvert op -> Unop_vec (V128Wrapper.Unop_VecConvert op)
        | Ast.VecBinary op -> Binop_vec (V128Wrapper.Binop_VecBinary op)
        | Ast.VecBinaryBits op -> Binop_vec (V128Wrapper.Binop_VecBinaryBits op)
        | Ast.VecCompare op -> Binop_vec (V128Wrapper.Binop_VecCompare op)
        | Ast.VecTernaryBits op -> Ternop_vec (V128Wrapper.Ternop_VecTernaryBits op)
        | Ast.VecShift op -> Shift_vec (V128Wrapper.Shift_VecShift op)
        | Ast.VecSplat op -> Splat_vec (convert_splatop_to_shape_vec op)
        | Ast.VecExtract op -> let (sv,sx,i) = convert_extractop_to_shape_vec_and_sx_and_i op in Extract_vec (sv, sx, i)
        | Ast.VecReplace op -> let (sv,i) = convert_replaceop_to_shape_vec_and_i op in Replace_vec (sv, i)

        | Ast.VecLoad lop -> let {Ast.ty; Ast.align; Ast.offset; Ast.pack} = lop in
                             Load_vec (convert_loadop_vec pack, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
        | Ast.VecStore sop -> let {Ast.ty; Ast.align; Ast.offset; Ast.pack} = sop in
                              Store_vec (Store_128, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
        | Ast.VecLoadLane llop -> let ({Ast.ty; Ast.align; Ast.offset; Ast.pack},n) = llop in
                                  Load_lane_vec ((convert_pack_size_to_shape_vec_i pack), (ocaml_int_to_nat n), (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
        | Ast.VecStoreLane slop -> let ({Ast.ty; Ast.align; Ast.offset; Ast.pack},n) = slop in
                                  Store_vec (Store_lane ((convert_pack_size_to_shape_vec_i pack), (ocaml_int_to_nat n)), (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))

        | Ast.ElemDrop x -> Elem_drop (var_to_nat x)
        | Ast.DataDrop x -> Data_drop (var_to_nat x)
        | Ast.RefFunc x -> Ref_func (var_to_nat x)
        | Ast.RefIsNull -> Ref_is_null
        | Ast.RefNull t -> Ref_null (convert_t_ref t)
        | Ast.MemoryFill -> Memory_fill 
        | Ast.MemoryInit x -> Memory_init (var_to_nat x)
        | Ast.MemoryCopy -> Memory_copy
        | Ast.TableGet x -> Table_get (var_to_nat x)
        | Ast.TableSet x -> Table_set (var_to_nat x)
        | Ast.TableSize x -> Table_size (var_to_nat x)
        | Ast.TableGrow x -> Table_grow (var_to_nat x)
        | Ast.TableFill x -> Table_fill (var_to_nat x)
        | Ast.TableCopy (x, y) -> Table_copy (var_to_nat x, var_to_nat y)
        | Ast.TableInit (x, y) -> Table_init (var_to_nat x, var_to_nat y)
        | _ -> raise PostMVP

and convert_instrs instrs = List.map convert_instr instrs

let convert_tg = function
  | GlobalType (t, Immutable) -> Tg_ext (T_immut, (convert_t t), ())
  | GlobalType (t, Mutable) -> Tg_ext (T_mut, (convert_t t), ())

let convert_glob' glob =
  let {
    Ast.gtype;
    Ast.ginit;
  } = glob in
  Module_glob_ext (convert_tg gtype, convert_instrs ginit.it, ())

let convert_glob glob = convert_glob' (glob.it)

let convert_limit lim =
  let {
    Types.min;
    Types.max;
  } = lim in
  Limit_t_ext (ocaml_int32_to_nat min, Lib.Option.map ocaml_int32_to_nat max, ())

let convert_tt tt =
  match tt with
  | TableType (lim, tr) -> T_tab (convert_limit lim, convert_t_ref tr)

let convert_tab tab =
  convert_tt ((tab.it).Ast.ttype)

let convert_mt mt =
  match mt with
  | MemoryType (lim) -> convert_limit lim

let convert_mem mem =
  convert_mt ((mem.it).Ast.mtype)

let convert_func' func =
  let {
    Ast.ftype;
    Ast.locals;
    Ast.body;
  } = func in
  ((var_to_nat ftype), (convert_vltype locals, convert_instrs body))

let convert_func func = convert_func' (func.it)

let convert_emode' emode =
    match emode with
    | Ast.Passive -> Em_passive
    | Ast.Active {index; offset; } -> Em_active (var_to_nat index, convert_instrs offset.it)
    | Ast.Declarative -> Em_declarative

let convert_elem' elem =
  let {
    Ast.etype;
    Ast.einit;
    Ast.emode;
  } = elem in Module_elem_ext (convert_t_ref etype, List.map (fun x -> convert_instrs x.it) einit, convert_emode' emode.it, ())

let convert_elem elem = convert_elem' (elem.it)

let convert_dmode' dmode =
  match dmode with
  | Ast.Passive -> Dm_passive
  | Ast.Active {index; offset; } -> Dm_active (var_to_nat index, convert_instrs offset.it)
  | Ast.Declarative -> raise InvalidModule
(** There are no declarative data segments *)

let convert_data' data =
 let {
    Ast.dinit;
    Ast.dmode;
  } = data in Module_data_ext (List.map ocaml_char_to_isabelle_byte (LibAux.string_explode dinit), convert_dmode' dmode.it, ())

let convert_data data = convert_data' (data.it)

let convert_export_desc edesc =
  match edesc.it with
  | Ast.FuncExport v -> Ext_func (var_to_nat v)
  | Ast.TableExport v -> Ext_tab (var_to_nat v)
  | Ast.MemoryExport v -> Ext_mem (var_to_nat v)
  | Ast.GlobalExport v -> Ext_glob (var_to_nat v)

let unescaped_string_of_name name =
  let b = Buffer.create 16 in
  List.iter (fun c -> (Buffer.add_utf_8_uchar b (Uchar.of_int c))) name;
  Buffer.contents b

let convert_export exp =
  let {
    Ast.name;
    Ast.edesc;
  } = exp.it in
  Module_export_ext ((Ast.string_of_name name), (convert_export_desc edesc), ())

let convert_import_desc idesc =
  match idesc.it with
  | Ast.FuncImport v -> Imp_func (var_to_nat v)
  | Ast.TableImport tt -> Imp_tab (convert_tt tt)
  | Ast.MemoryImport mt -> Imp_mem (convert_mt mt)
  | Ast.GlobalImport gt -> Imp_glob (convert_tg gt)

let convert_import imp =
  let {
    Ast.module_name;
    Ast.item_name;
    Ast.idesc;
  } = imp.it in
  Module_import_ext ((unescaped_string_of_name module_name), (unescaped_string_of_name item_name), (convert_import_desc idesc), ())

let convert_module (modul : Ast.module_') : unit m_ext =
  let {
    Ast.types;
    Ast.globals;
    Ast.tables;
    Ast.memories;
    Ast.funcs;
    Ast.start;
    Ast.elems;
    Ast.datas;
    Ast.imports;
    Ast.exports} = modul in
  let m_types = List.map convert_ftype types in
  let m_funcs = List.map convert_func funcs in
  let m_tabs = List.map convert_tab tables in
  let m_mems = List.map convert_mem memories in
  let m_globs = List.map convert_glob globals in
  let m_elem = List.map convert_elem elems in
  let m_data = List.map convert_data datas in
  let m_start = Lib.Option.map var_to_nat start in
  let m_imports = List.map convert_import imports in
  let m_exports = List.map convert_export exports in
  M_ext (m_types, m_funcs, m_tabs,m_mems, m_globs, m_elem, m_data, m_start, m_imports, m_exports, ())


