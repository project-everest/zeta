module Zeta.Steel.ExternalPtr

let extern_ptr = A.array U8.t

let gtake p = p

assume
val enclave_api_validate (x:A.array U8.t) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length x))

let valid = enclave_api_validate

let take x n = x
