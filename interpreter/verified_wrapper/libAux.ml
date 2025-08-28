let string_explode s = List.init (String.length s) (String.get s)
let string_implode bl = String.init (List.length bl) (List.nth bl)

let bytes_explode bs = List.init (Bytes.length bs) (Bytes.get bs)

let z_of_uint32 x = Z.of_string (Printf.sprintf "%#lx" x)
let z_of_uint64 x = Z.of_string (Printf.sprintf "%#Lx" x)

let uint32_of_z x = I32.of_string (Z.to_string x)
let uint64_of_z x = I64.of_string (Z.to_string x)

let z_of_float32rep x = z_of_uint32 (F32.to_bits x)
let z_of_float64rep x = z_of_uint64 (F64.to_bits x)

let z_of_char c = Z.of_int (Char.code c)
let char_of_z x = Char.chr (Z.to_int x)

module Map_isa = Map.Make(struct type t = (string) let compare = compare end)
