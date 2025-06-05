(*
 * Simple collection of functions useful for writing test cases.
 *)

open WasmRef_Isa.WasmRef_Isa

let print_value' v =
  Printf.printf "%s : %s\n"
    (Values.string_of_value v)
    (Types.string_of_value_type (Values.type_of_value v))


let print_value (v : v) =
  let v' = Ast_convert.convert_value_rev v in
  print_value' v'

(* let print' : host =
  Abs_host_m (fun (s, vs) -> fun () -> List.iter print_value vs; flush_all (); Some (s, [])) *)
  let print' : host =
    Abs_host (fun (s, vs) -> List.iter print_value vs; flush_all (); Some (s, []))

let spectest_func_imports =
 [("print", Func_host (Tf ([],[]), print'));
  ("print_i32", Func_host (Tf ([T_num T_i32],[]), print'));
  ("print_i64", Func_host (Tf ([T_num T_i64],[]), print'));
  ("print_f32", Func_host (Tf ([T_num T_f32],[]), print'));
  ("print_f64", Func_host (Tf ([T_num T_f64],[]), print'));
  ("print_i32_f32", Func_host (Tf ([T_num T_i32; T_num T_f32],[]), print'));
  ("print_f64_f64", Func_host (Tf ([T_num T_f64; T_num T_f64],[]), print'))
 ]

(* let spectest_tab_imports =
 [("table", (Array.make 10 None, Some (Nat (Z.of_int 20))))
 ] *)
let spectest_tab_imports =
 [("table", ((T_tab (Limit_t_ext (Nat (Z.of_int 10), Some (Nat (Z.of_int 20)), ()), T_func_ref)), Lib.List.make 10 ((ConstNull T_func_ref)) ))
 ]

(* let spectest_mem_imports =
 [("memory", (new_zeroed_byte_array (Nat (Z.of_int 65536)) (), Some (Nat (Z.of_int 2))))
 ] *)
 let spectest_mem_imports =
  [("memory", (Limit_t_ext (Nat (Z.of_int 1), Some (Nat (Z.of_int 2)), ()), Abs_mem_rep (Lib.List.make 65536 (zero_byte))))
  ]

let spectest_glob_imports =
 [("global_i32", Global_ext (T_immut, V_num (ConstInt32 (ocaml_int32_to_isabelle_int32 666l)), ()));
  ("global_i64", Global_ext (T_immut, V_num (ConstInt64 (ocaml_int64_to_isabelle_int64 666L)), ()));
  ("global_f32", Global_ext (T_immut, V_num (ConstFloat32 (F32.of_float 666.6)), ()));
  ("global_f64", Global_ext (T_immut, V_num (ConstFloat64 (F64.of_float 666.6)), ()))
 ]

 let install_spectest_funcs (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
  match s with
  | (S_ext (cls, tabs, mems, globs, elems, datas, _)) ->
    let cl_n = List.length cls in
    let (spectest_names, spectest_cls) = List.split spectest_func_imports in
    let exp_list = List.mapi (fun i name -> (name, Ext_func (Nat (Z.of_int i)))) spectest_names in
    (S_ext (cls@spectest_cls, tabs, mems, globs, elems, datas, ()), exp_list)

let install_spectest_tabs (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
  match s with
  | (S_ext (cls, tabs, mems, globs, elems, datas,_)) ->
    let tab_n = List.length tabs in
    let (spectest_names, spectest_tabs) = List.split spectest_tab_imports in
    let exp_list = List.mapi (fun i name -> (name, Ext_tab (Nat (Z.of_int i)))) spectest_names in
    (S_ext (cls, tabs@spectest_tabs, mems, globs, elems, datas,()), exp_list)

let install_spectest_mems (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
  match s with
  | (S_ext (cls, tabs, mems, globs, elems, datas,_)) ->
    let mem_n = List.length mems in
    let (spectest_names, spectest_mems) = List.split spectest_mem_imports in
    let exp_list = List.mapi (fun i name -> (name, Ext_mem (Nat (Z.of_int i)))) spectest_names in
    (S_ext (cls, tabs, mems@spectest_mems, globs, elems, datas,()), exp_list)

let install_spectest_globs (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
  match s with
  | (S_ext (cls, tabs, mems, globs, elems, datas, _)) ->
    let glob_n = List.length globs in
    let (spectest_names, spectest_globs) = List.split spectest_glob_imports in
    let exp_list = List.mapi (fun i name -> (name, Ext_glob (Nat (Z.of_int i)))) spectest_names in
    (S_ext (cls, tabs, mems, globs@spectest_globs, elems, datas, ()), exp_list)

let install_spectest_isa (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
  match s with
  | S_ext (cls, tabs, mems, globs, elems, datas, _) ->
    let (s', exp_funcs) = install_spectest_funcs s in
    let (s'', exp_tabs) = install_spectest_tabs s' in
    let (s''', exp_mems) = install_spectest_mems s'' in
    let (s'''', exp_globs) = install_spectest_globs s''' in
    (s'''', exp_funcs@exp_tabs@exp_mems@exp_globs)
