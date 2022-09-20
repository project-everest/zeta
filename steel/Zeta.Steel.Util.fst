module Zeta.Steel.Util
open Steel.ST.Util
module A = Steel.ST.Array
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
let larray t (n:U32.t) = A.larray t (U32.v n)
[@@__steel_reduce__;__reduce__]
let array_pts_to #t (a:A.array t) (v:Seq.seq t) = A.pts_to a full_perm v

let sum_halves : squash (sum_perm half half == full) = ()

inline_for_extraction
let will_add_overflow32 (x y:U32.t)
  : res:bool{
       res <==> not (FStar.UInt.fits (U32.v x + U32.v y) 32)
    }
  = let open U32 in
    (0xfffffffful -^ x) <^ y

let check_overflow_add32 (x y:U32.t)
  : Pure (option U32.t)
    (requires True)
    (ensures fun res ->
        if FStar.UInt.fits (U32.v x + U32.v y) 32
        then Some? res /\
             Some?.v res == U32.add x y
        else None? res)
 = if will_add_overflow32 x y
   then None
   else Some U32.(x +^ y)

inline_for_extraction
let will_add_overflow64 (x y:U64.t)
  : res:bool{
       res <==> not (FStar.UInt.fits (U64.v x + U64.v y) 64)
    }
  = let open U64 in
    (0xffffffffffffffffuL -^ x) <^ y

let check_overflow_add64 (x y:U64.t)
  : res:option U64.t {
        if FStar.UInt.fits (U64.v x + U64.v y) 64
        then Some? res /\
             Some?.v res == U64.add x y
        else None? res
    }
 = if will_add_overflow64 x y
   then None
   else Some U64.(x +^ y)

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

let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_

// let next (t:U64.t)
//   : option U64.t
//   = let ctr = FStar.Int.Cast.uint64_to_uint32 t in
//     if FStar.UInt.fits (U32.v ctr + 1) 32
//     then Some (U64.add t 1uL)
//     else None

// let will_add_overflow32 (x y:U32.t)
//   : res:bool{
//        res <==> not (FStar.UInt.fits (U32.v x + U32.v y) 32)
//     }
//   = let open U32 in
//     (0xfffffffful -^ x) <^ y

// module C = FStar.Int.Cast

// let try_increment_counter (x:U64.t)
//   : Tot (v:option (U64.t) { v == next x })
//   = let ctr = FStar.Int.Cast.uint64_to_uint32 x in
//     if will_add_overflow32 ctr 1ul
//     then None
//     else let res = U64.(x +^ 1uL) in
//          Some res

       
