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

let valid_input = enclave_api_validate

let copy_extern_input_ptr
  e n
=
  let res = A.alloc 0uy n in
  rewrite (has_extern_input_ptr e n) (has_extern_input_ptr0 e n);
  let _ = gen_elim () in
  A.memcpy e res n;
  rewrite (has_extern_input_ptr0 e n) (has_extern_input_ptr e n);
  return res

let extern_output_ptr = A.array U8.t

let gtake p = p

let valid_output = enclave_api_validate

let take x n = x

assume
val enclave_api_check_input_output_disjoint
  (input: extern_input_ptr)
  (input_len: U32.t)
  (output: extern_output_ptr)
  (output_len: U32.t)
  (output_contents: Ghost.erased (Seq.seq U8.t))
: ST bool
    (has_extern_input_ptr input input_len `sl_and` A.pts_to (gtake output) full_perm output_contents)
    (fun b -> check_disjoint_post b (has_extern_input_ptr input input_len) (A.pts_to (gtake output) full_perm output_contents))
    (valid_input input input_len /\ valid_output output output_len)
    (fun _ -> True)

let check_input_output_disjoint = enclave_api_check_input_output_disjoint
