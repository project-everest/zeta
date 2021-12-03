module Zeta.Steel.Util
open Steel.ST.Util
module A = Steel.ST.Array
module U32 = FStar.UInt32
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
let larray t (n:U32.t) = A.larray t (U32.v n)

let sum_halves : squash (sum_perm half half == full) = admit()

assume
val empty_map (#k:eqtype) (#v:Type) : FStar.Map.t k v


assume
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:post_t a)
            (_:unit)
  : STF a p q True (fun _ -> False)

assume
val cancellable_lock (v:vprop) : Type0

assume
val can_release (#v:vprop) (c:cancellable_lock v) : vprop

assume
val new_cancellable_lock (v:vprop)
  : STT (cancellable_lock v) v (fun _ -> emp)

let maybe_acquired (b:bool) (#v:vprop) (c:cancellable_lock v)
  = if b then (v `star` can_release c) else emp

assume
val acquire (#v:vprop) (c:cancellable_lock v)
  : STT bool emp (fun b -> maybe_acquired b c)

assume
val release (#v:vprop) (c:cancellable_lock v)
  : STT unit (v `star` can_release c) (fun _ -> emp)

assume
val cancel (#v:vprop) (c:cancellable_lock v)
  : STT unit (can_release c) (fun _ -> emp)
