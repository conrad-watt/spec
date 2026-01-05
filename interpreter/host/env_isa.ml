(*
 * Utilities for test cases and benchmarking
 *)

open WasmRef_Isa_m.WasmRef_Isa

let clock_ms vs =
  let seconds = Unix.gettimeofday () in
  let milliseconds = (Int64.of_float (seconds *. 1000.)) in
  [V_num (ConstInt64 (I64_impl_abs milliseconds))]
  
let clock_ms' : host =
  Abs_host_m (fun (s, vs) -> fun () -> Some (s, clock_ms vs))
   

let env_func_imports =
  
   [
    ("clock_ms", Func_host (Tf ([],[T_num T_i64]), clock_ms'))
   ]
 
   let install_spectest_funcs (s : unit s_m_ext) : (unit s_m_ext * ((string * v_ext) list)) =
    match s with
    | (S_m_ext (cls, tabs, mems, globs, _)) ->
      let cl_n = Array.length cls in
      let (env_names, env_cls) = List.split env_func_imports in
      let exp_list = List.mapi (fun i name -> (name, Ext_func (Nat (Z.of_int (cl_n + i))))) env_names in
      (S_m_ext (Array.append cls (Array.of_list env_cls), tabs, mems, globs, ()), exp_list)
 
let install_env_isa (s : unit s_m_ext) : (unit s_m_ext * ((string * v_ext) list)) =
  match s with
  | S_m_ext (cls, tabs, mems, globs, _) ->
    let (s', exp_funcs) = install_spectest_funcs s in
    (s', exp_funcs)
 