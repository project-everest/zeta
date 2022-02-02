module Zeta.Steel.EpochMap
open Steel.ST.Util
open Zeta.Steel.Util
module M = Zeta.Steel.ThreadStateModel
module G = FStar.Ghost
module Set = FStar.Set
module Map = FStar.Map
module U32 = FStar.UInt32

val tbl (#v:Type0)
        (#c:Type0) 
        (vp:M.epoch_id -> v -> c -> vprop)
    : Type0

let repr (a:Type)
  : Type0
  = m:Map.t M.epoch_id a {
      Map.domain m `Set.equal` Set.complement Set.empty
    }

let borrows (a:Type)
  : Type0
  = FStar.PartialMap.t M.epoch_id a

let empty_borrows #a
  : borrows a
  = PartialMap.empty M.epoch_id a

(*
  One representation for this is a pair containing an
    1. an EHT
    2. a high-water-mark, a concrete epoch_id ref

  with an invariant stating that for all 
  
    epoch_id greater than the high-water-mark
    the value of the map associated with that epoch id
    is the default_value

  Additionally, if an epoch `i` is in the borrows set, 
  then `i` is less than or equal to the high water mark
*)
val perm (#v:Type)
         (#c:Type)
         (#vp:M.epoch_id -> v -> c -> vprop)
         (t:tbl vp)
         (default_value: c)
         ([@@@smt_fallback] m:repr c)
         ([@@@smt_fallback] b:borrows v)
  : vprop

[@@__steel_reduce__; __reduce__]
let full_perm (#v:Type)
              (#c:Type)
              (#vp:M.epoch_id -> v -> c -> vprop)
              (t:tbl vp)
              (default_value: c)              
              ([@@@smt_fallback] m:repr c)
  = perm t default_value m empty_borrows

(* initializes the EHT and sets high-water-mark to 0 *)
val create (#v:Type)
           (#c:Type)
           (#vp:M.epoch_id -> v -> c -> vprop)
           (n:U32.t{U32.v n > 0})
           (init:G.erased c)
  : STT (tbl #v #c vp)
        emp
        (fun a -> perm a init (Map.const #M.epoch_id #c init) empty_borrows)

(* Call the finalizer on the array only.
   Freeing every element of the array is up to the client *)
val free (#v:Type)
         (#c:Type)
         (#vp:M.epoch_id -> v -> c -> vprop)
         (#init:G.erased c)
         (#m:G.erased (repr c))
         (#b:G.erased (borrows v))
         (t:tbl vp)
  : STT unit
        (perm t init m b)
        (fun _ -> emp)

noeq
type get_result (v:Type) =
  | Found    : v -> get_result v
  | Fresh    : get_result v
  | NotFound : get_result v

let get_post
         (#v:Type) 
         (#c:Type)
         (#vp:M.epoch_id -> v -> c -> vprop)
         (init:G.erased c)
         (m:G.erased (repr c))
         (b:G.erased (borrows v))
         (a:tbl vp)
         (i:M.epoch_id)
  : get_result v -> vprop
  = fun o ->
    match o with
    | Found x ->
      perm a init m (PartialMap.upd b i x)  //when `get` succeeds, the key is added to `borrows`
        `star`
      vp i x (Map.sel m i)      //in addition, we return the vp permission for the key

    | _ ->
      perm a init m b

(*
   tests if i > high-water-mark; if so it immediately returns Fresh.
   Otherwise, it looks for epoch i in the EHT
     - if EHT returns Missing or Absent, return NotFound
     - Otherwise return Found
*)     
val get (#v:Type) 
        (#c:Type)
        (#vp:M.epoch_id -> v -> c -> vprop)
        (#init:G.erased c)
        (#m:G.erased (repr c))
        (#b:G.erased (borrows v))
        (a:tbl vp)
        (i:M.epoch_id)
  : ST (get_result v)
       (perm a init m b)
       (get_post init m b a i)
       (requires ~ (PartialMap.contains b i))
       (ensures fun res -> Fresh? res ==> Map.sel m i == G.reveal init) //<-- This is the main new property

(* Calls EHT.put and moves the high-water-mark to i *)
val put (#v:Type) 
        (#c:Type)
        (#vp:M.epoch_id -> v -> c -> vprop)
        (#init:G.erased c)
        (#m:G.erased (repr c))
        (#b:G.erased (borrows v))
        (a:tbl vp)
        (i:M.epoch_id)
        (x:v)
        (content:Ghost.erased c)
  : STT unit
      (perm a init m b `star` vp i x content)
      (fun _ -> perm a init (Map.upd m i content) (PartialMap.remove b i))

(* Calls EHT.ghost_put
   High water mark does not need to be updated, since `i` is in the borrows map *)
val ghost_put (#o:_)
              (#v:Type) 
              (#c:Type)
              (#vp:M.epoch_id -> v -> c -> vprop)
              (#init:G.erased c)
              (#m:G.erased (repr c))
              (#b:G.erased (borrows v))
              (a:tbl vp)
              (i:M.epoch_id)
              (x:v)
              (content:Ghost.erased c)
  : STGhost unit o
      (perm a init m b `star` vp i x content)
      (fun _ -> perm a init (Map.upd m i content) (PartialMap.remove b i))
      (requires
        PartialMap.sel b i == Some x)
      (ensures fun _ ->
        True)

(* This marks a slot in the underlying EHT as being free to reuse, 
   indicating that the value (if borrowed) will never be returned *)
val reclaim (#v:Type) 
            (#c:Type)
            (#vp:M.epoch_id -> v -> c -> vprop)
            (#init:G.erased c)
            (#m:G.erased (repr c))
            (#b:G.erased (borrows v))
            (a:tbl vp)
            (i:M.epoch_id)
  : STT unit
      (perm a init m b)
      (fun _ -> perm a init m (PartialMap.remove b i))
