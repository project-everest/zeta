module Zeta.Steel.Util
open Steel.ST.Util
module A = Steel.ST.Array
module U32 = FStar.UInt32
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
let larray t (n:U32.t) = A.larray t (U32.v n)

assume
val empty_map (#k:eqtype) (#v:Type) : FStar.Map.t k v
