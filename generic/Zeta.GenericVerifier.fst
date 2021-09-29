module Zeta.GenericVerifier

let contains_distinct_app_keys_comp
  (#vspec:_) (vtls: vspec.vtls_t{vspec.valid vtls}) (ss: S.seq vspec.slot_t)
  : b:bool {b <==> contains_distinct_app_keys vtls ss}
  = admit()

