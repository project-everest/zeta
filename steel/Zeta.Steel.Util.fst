module Zeta.Steel.Util
open Steel.ST.Util
module A = Steel.ST.Array
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
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


let check_overflow_add32 (x y:U32.t)
  : Pure (option U32.t)
    (requires True)
    (ensures fun res ->
        if FStar.UInt.fits (U32.v x + U32.v y) 32
        then Some? res /\
             Some?.v res == U32.add x y
        else None? res)
 = let open U64 in
   let res = U64.(Cast.uint32_to_uint64 x +^
                  Cast.uint32_to_uint64 y)
   in
   if res >^ 0xffffffffuL
   then None
   else (assert (U64.v res  == U32.v x + U32.v y);
         assert (U64.v res <= pow2 32);
         let res = Cast.uint64_to_uint32 res in
         assert (U32.v res  == U32.v x + U32.v y);
         Some res)


let check_overflow_add (x y:U64.t)
  : res:option U64.t {
        if FStar.UInt.fits (U64.v x + U64.v y) 64
        then Some? res /\
             Some?.v res == U64.add x y
        else None? res
    }
 = let open U64 in
   let res = U64.add_mod x y in
   if res <^ x then None
   else if res -^ x = y then Some res
   else None


let st_check_overflow_add32 (x y:U32.t)
  : ST (option U32.t)
       emp
       (fun _ -> emp)
       (requires True)
       (ensures fun res ->
         if FStar.UInt.fits (U32.v x + U32.v y) 32
         then Some? res /\
              Some?.v res == U32.add x y
         else None? res)
  = let r = check_overflow_add32 x y in return r
