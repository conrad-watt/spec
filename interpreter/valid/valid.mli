exception Invalid of Source.region * string

val check_module : Ast.module_ -> unit (* raises Invalid *)

val check_module_isa : (unit WasmRef_Isa_m.WasmRef_Isa.m_ext) -> unit (* raises Invalid *)
