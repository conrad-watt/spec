open Bytes

let memRepAt memRep n = Bytes.get memRep n

let memRepAppend memRep n byte = Bytes.cat memRep (Bytes.make n byte)

let rec memRepReadBytesHelper memRep n m arr =
  if (0 < m) then
    memRepReadBytesHelper memRep n (m-1) ((Bytes.get memRep (n+m-1)::arr))
  else
    arr

let memRepReadBytes memRep n m = memRepReadBytesHelper memRep n m []

let rec memRepWriteBytes memRep n arr =
  match arr with
    [] -> memRep
  | (x :: xs) -> (Bytes.set memRep n x); memRepWriteBytes memRep (n+1) xs
