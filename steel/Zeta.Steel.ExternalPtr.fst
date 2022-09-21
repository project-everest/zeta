module Zeta.Steel.ExternalPtr
open Steel.ST.GenElim

let extern_input_ptr = A.array U8.t

[@@__reduce__]
let has_extern_input_ptr0 e n =
  exists_ (fun p -> exists_ (fun contents -> A.pts_to e p contents)) `star`
  pure (U32.v n == A.length e)

let has_extern_input_ptr e n =
  has_extern_input_ptr0 e n

assume
val enclave_api_validate (x:A.array U8.t) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length x))

let copy_extern_input_ptr
  e n a
=
  if enclave_api_validate e n
  then begin
    rewrite (has_extern_input_ptr e n) (has_extern_input_ptr0 e n);
    let _ = gen_elim () in
    A.memcpy e a n;
    rewrite (has_extern_input_ptr0 e n) (has_extern_input_ptr e n);
    return true
  end else begin
    return false
  end
