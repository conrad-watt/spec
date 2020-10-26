let string_explode s = List.init (String.length s) (String.get s)
let string_implode bl = String.init (List.length bl) (List.nth bl)

let bytes_explode bs = List.init (Bytes.length bs) (Bytes.get bs)

let z_of_uint32 x = Z.of_string (Printf.sprintf "%#lx" x)
let z_of_uint64 x = Z.of_string (Printf.sprintf "%#Lx" x)

let z_of_float32rep x = failwith "NYI"
let z_of_float64rep x = failwith "NYI"
