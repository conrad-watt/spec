open WasmRef_Isa_m.WasmRef_Isa
open Source
open Types
open Values

exception PostMVP

let convert_t_num = function
  | I32Type -> T_i32
  | F32Type -> T_f32
  | I64Type -> T_i64
  | F64Type -> T_f64
  | _ -> raise PostMVP

let convert_t = function
  | NumType t -> convert_t_num t
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

let conv_elem_init econst =
  match econst.it with
  | [{it = Ast.RefFunc v; at;}] -> var_to_nat v
  | _ -> raise PostMVP

let convert_value_num = function
	| I32 c -> ConstInt32 (ocaml_int32_to_isabelle_int32 c)
	| I64 c -> ConstInt64 (ocaml_int64_to_isabelle_int64 c)
	| F32 c -> ConstFloat32 c
	| F64 c -> ConstFloat64 c

let convert_value = function
        | Num n -> convert_value_num n
        | _ -> raise PostMVP

let convert_value_num_rev = function
	| ConstInt32 c -> I32 (isabelle_int32_to_ocaml_int32 c)
	| ConstInt64 c -> I64 (isabelle_int64_to_ocaml_int64 c)
	| ConstFloat32 c -> F32 c
	| ConstFloat64 c -> F64 c

let convert_value_rev v = Num (convert_value_num_rev v)

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

let convert_load_tp_sx = function
	| None -> None
	| Some (mtp, msx) -> Some (convert_tp mtp, convert_sx msx)

let convert_store_tp = function
	| None -> None
	| Some mtp -> Some (convert_tp mtp)

let rec convert_instr instr =
	match instr.it with
	| Ast.Unreachable -> Unreachable
	| Ast.Nop -> Nop
        (* TODO: multi-value *)
	| Ast.Block (Ast.ValBlockType st, binstrs) ->
            Block (Tf ([],convert_vltype_opt st), convert_instrs binstrs)
	| Ast.Loop (Ast.ValBlockType st, binstrs) ->
            Loop (Tf ([],convert_vltype_opt st), convert_instrs binstrs)
	| Ast.If (Ast.ValBlockType st, binstrs1, binstrs2) ->
            If (Tf ([],convert_vltype_opt st), convert_instrs binstrs1, convert_instrs binstrs2)
	| Ast.Br n -> Br (var_to_nat n)
 	| Ast.BrIf n -> Br_if (var_to_nat n)
	| Ast.BrTable (ns, n) -> Br_table (List.map var_to_nat ns, var_to_nat n)
	| Ast.Return -> Return
	| Ast.Call n -> Call (var_to_nat n)
	| Ast.CallIndirect(n, y) -> (if (n.it)=0l then Call_indirect (var_to_nat y) else raise PostMVP)
	| Ast.Drop -> Drop
	| Ast.Select None -> Select
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
	| Ast.Const v -> EConst (convert_value_num v.it)
	| Ast.Test top -> convert_testop top
	| Ast.Compare cop -> convert_compareop cop
	| Ast.Unary uop -> convert_unop uop
	| Ast.Binary bop -> convert_binop bop
	| Ast.Convert cop -> convert_convertop cop

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
  | TableType (lim, _) -> convert_limit lim

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

let convert_elem' elem =
  let {
    Ast.etype;
    Ast.einit;
    Ast.emode;
  } = elem in
  match etype with
  | FuncRefType->
    (match emode.it with
     | Ast.Active {index; offset; } ->
         Module_elem_ext (var_to_nat index, convert_instrs offset.it, List.map conv_elem_init einit, ())
     | _ -> raise PostMVP)
  | _ -> raise PostMVP


let convert_elem elem = convert_elem' (elem.it)

let convert_data' data =
 let {
    Ast.dinit;
    Ast.dmode;
  } = data in
  (match dmode.it with
   | Ast.Active {index; offset; } ->
       Module_data_ext (var_to_nat index, convert_instrs offset.it, List.map ocaml_char_to_isabelle_byte (LibAux.string_explode dinit), ())
   | _ -> raise PostMVP)

let convert_data data = convert_data' (data.it)

let convert_export_desc edesc =
  match edesc.it with
  | Ast.FuncExport v -> Ext_func (var_to_nat v)
  | Ast.TableExport v -> Ext_tab (var_to_nat v)
  | Ast.MemoryExport v -> Ext_mem (var_to_nat v)
  | Ast.GlobalExport v -> Ext_glob (var_to_nat v)

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
  Module_import_ext ((Ast.string_of_name module_name), (Ast.string_of_name item_name), (convert_import_desc idesc), ())

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


