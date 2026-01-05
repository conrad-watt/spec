(*
 * Utilities for test cases and benchmarking
 *)

 open WasmRef_Isa.WasmRef_Isa
 
 let clock_ms vs =
   let seconds = Unix.gettimeofday () in
   let milliseconds = (Int64.of_float (seconds *. 1000.)) in
   [V_num (ConstInt64 (I64_impl_abs milliseconds))]
 
 let clock_ms' : host =
   Host_func (Abs_host_func (fun (s, vs) -> Some (s, clock_ms vs)))
 
  let env_func_imports =
   [
    ("clock_ms", Func_host (Tf ([],[T_num T_i64]), clock_ms'))
   ]
 
let install_env_funcs (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
   match s with
   | (S_ext (cls, tabs, mems, globs, elems, datas, _)) ->
     let cl_n = List.length cls in
     let (env_names, spectest_cls) = List.split env_func_imports in
     let exp_list = List.mapi (fun i name -> (name, Ext_func (Nat (Z.of_int (cl_n + i))))) env_names in
     (S_ext (cls@spectest_cls, tabs, mems, globs, elems, datas, ()), exp_list)
 
 let install_env_isa (s : unit s_ext) : (unit s_ext * ((string * v_ext) list)) =
   match s with
   | S_ext (cls, tabs, mems, globs, elems, datas, _) ->
     let (s', exp_funcs) = install_env_funcs s in
     (s', exp_funcs)
 