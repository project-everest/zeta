module Zeta.Steel.Util
open Steel.ST.Util
open Steel.ST.CancellableSpinLock
module A = Steel.ST.Array
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
let larray t (n:U32.t) = A.larray t (U32.v n)
[@@__steel_reduce__;__reduce__]
let array_pts_to #t (a:A.array t) (v:Seq.seq t) = A.pts_to a full_perm v

let sum_halves : squash (sum_perm half half == full) = admit()

[@@warn_on_use "uses an axiom"]
assume
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:a -> vprop)
            (_:unit)
  : STF a p q True (fun _ -> False)

[@@warn_on_use "uses an axiom"]
assume
val admit___ (#opened:_)
             (#a:Type)
             (#p:pre_t)
             (#q:a -> vprop)
             (_:unit)
  : STAtomicF a opened p q True (fun _ -> False)

let cancellable_lock (v:vprop) = cancellable_lock v

let can_release (#v:vprop) (c:cancellable_lock v) = can_release c

let new_cancellable_lock (v:vprop)
  : STT (cancellable_lock v) v (fun _ -> emp)
  = new_cancellable_lock v

let maybe_acquired (b:bool) (#v:vprop) (c:cancellable_lock v)
  = maybe_acquired b c

let acquire (#v:vprop) (c:cancellable_lock v)
  : STT bool emp (fun b -> maybe_acquired b c)
  = acquire c

let release (#v:vprop) (c:cancellable_lock v)
  : STT unit (v `star` can_release c) (fun _ -> emp)
  = release c

let cancel (#v:vprop) (c:cancellable_lock v)
  : STT unit (can_release c) (fun _ -> emp)
  = cancel c

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

assume
val map_literal (#k:eqtype) (#v:Type) (f: k -> v)
  : Map.t k v

let map_literal_interp (#k:eqtype) (#v:Type) (f: k -> v)
  : Lemma ((forall k. Map.sel (map_literal f) k == f k) /\
           Map.domain (map_literal f) == Set.complement Set.empty)
          [SMTPat (map_literal f)]
  = admit()

let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_


module R = Steel.ST.Reference
module Loops = Steel.ST.Loops
let repeat_until (p: bool -> vprop)
                 ($body: (unit -> STT bool (p true) (fun b -> p b)))
  : STT unit (p true) (fun _ -> p false)
  = let r = R.alloc true in
    let inv : bool -> vprop = fun b -> R.pts_to r full b `star` p b in
    let cond (_:unit)
      : STT bool (exists_ inv)
                 inv
      = let _b = elim_exists () in
        rewrite (inv _b)
                (R.pts_to r full _b `star` p _b);
        let b = R.read r in
        rewrite (R.pts_to r full _b `star` p _b)
                (inv b);
        return b
    in
    let body (_:unit)
      : STT unit
        (inv true)
        (fun _ -> exists_ inv)
      = rewrite (inv true)
                (R.pts_to r full true `star` p true);
        let b = body () in
        R.write r b;
        rewrite (R.pts_to r full b `star` p b)
                (inv b);
        intro_exists b inv
    in
    rewrite (R.pts_to r full true `star` p true)
            (inv true);
    intro_exists true inv;
    Steel.ST.Loops.while_loop inv cond body;
    rewrite (inv false)
            (R.pts_to r full false `star` p false);
    R.free r
