open Parray

let memRepAt memRep n = Parray.get memRep n

let memRepAppend memRep n byte = Parray.init (length memRep + n) (fun idx -> if idx < (length memRep) then (Parray.get memRep idx) else byte)

let rec memRepReadBytesHelper memRep n m arr = if (0 < m) then memRepReadBytesHelper memRep n (m-1) ((Parray.get memRep (n+m-1))::arr) else arr

let memRepReadBytes memRep n m = memRepReadBytesHelper memRep n m []

let rec memRepWriteBytes memRep n arr =
  match arr with
    [] -> memRep
  | (x :: xs) -> memRepWriteBytes (Parray.set memRep n x) (n+1) xs
