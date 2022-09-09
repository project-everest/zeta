module Zeta.Steel.ExternalPtr

let extern_ptr a = A.array a

let gtake p = p

assume
val enclave_api_validate (#a: Type) (x:A.array a) (n: U32.t) : Pure bool
  (requires True)
  (ensures (fun b -> b == true ==> U32.v n == A.length x))

let valid = enclave_api_validate

let take x n = x
