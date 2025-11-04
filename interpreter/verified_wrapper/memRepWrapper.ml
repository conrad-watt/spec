(* open Pbytes *)

let memRepAt memRep n = Pbytes.get_char memRep n

let memRepAppend = Pbytes.append
  (* Pbytes.append memRep n byte *)
  (* let newMemRep = (Pbytes.make (length memRep + n) byte) in
  Pbytes.blit memRep 0 newMemRep 0 (length memRep);
  newMemRep *)
  (* Pbytes.init (length memRep + n) (fun idx -> if idx < (length memRep) then (Pbytes.get_char memRep idx) else byte) *)

let rec memRepReadBytesHelper memRep n m arr = if (0 < m) then memRepReadBytesHelper memRep n (m-1) ((Pbytes.get_char memRep (n+m-1))::arr) else arr

let memRepReadBytes memRep n m = memRepReadBytesHelper memRep n m []

let rec memRepWriteBytes memRep n arr =
  match arr with
    [] -> memRep
  | (x :: xs) -> memRepWriteBytes (Pbytes.set_char memRep n x) (n+1) xs
