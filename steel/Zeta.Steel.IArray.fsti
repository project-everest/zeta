module Zeta.Steel.IArray
open Steel.ST.Util
open Zeta.Steel.Util

module G = FStar.Ghost
module Set = FStar.Set
module Map = FStar.Map
module U32 = FStar.UInt32
module EHT = Steel.ST.EphemeralHashtbl

val tbl (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (h:EHT.hash_fn k)
        (vp:EHT.vp_t k v contents)
  : Type0

let repr (k:eqtype)
         (contents:Type0)
  : Type0
  = m:Map.t k contents { Map.domain m `Set.equal` Set.complement Set.empty }

let borrows (k:eqtype)
            (v:Type0)
  : Type0
  = FStar.PartialMap.t k v

let empty_borrows #k #v 
  : borrows k v
  = PartialMap.empty k v

(* perm t m b: asserts ownership of the underlying array

       *and* ownership of `vp k v c` for every (k, v)
             in memory
             except for those keys in b, that have been borrowed

             The representation map `m` collapses the indirection
             via v. I.e., it directly associates keys `k`
             with the contents of `v`.
*)
val perm (#k:eqtype)
         (#v:Type0)
         (#contents:Type0)
         (#h:EHT.hash_fn k)
         (#vp:EHT.vp_t k v contents)
         (t:tbl h vp)
         ([@@@smt_fallback] m:repr k contents)
         ([@@@smt_fallback] b:borrows k v)
  : vprop

[@@__steel_reduce__; __reduce__]
let full_perm (#k:eqtype)
              (#v:Type0)
              (#contents:Type0)
              (#h:EHT.hash_fn k)
              (#vp:EHT.vp_t k v contents)
              (t:tbl h vp)
              ([@@@smt_fallback] m:repr k contents)
  = perm t m empty_borrows
         
val create (#k:eqtype)
           (#v:Type0)
           (#contents:Type0)
           (#vp:EHT.vp_t k v contents)
           (h:EHT.hash_fn k)
           (n:U32.t{U32.v n > 0})
           (init:Ghost.erased contents)
  : STT (tbl h vp) emp (fun a -> perm a (Map.const #k #contents init) empty_borrows)

(* Call the finalizer on the array only.
   Freeing every element of the array is up to the client *)
val free (#k:eqtype)
         (#v:Type0)
         (#h:EHT.hash_fn k)
         (#contents: Type0)
         (#vp:EHT.vp_t k v contents)
         (#m:G.erased (repr k contents))
         (#b:G.erased (borrows k v))
         (a:tbl h vp)
  : STT unit
      (perm a m b)
      (fun _ -> emp)


let get_post 
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (m:G.erased (repr k contents))
  (borrows:G.erased (borrows k v))
  (a:tbl h vp)
  (i:k)
  : EHT.get_result k v -> vprop
  = fun r ->
    match r with
    | EHT.Present x ->
      perm a m (PartialMap.upd i x borrows)  //when `get` succeeds, the key is added to `borrows`
        `star`
      vp i x (Map.sel m i)                   //in addition, we return the vp permission for the key

    | _ ->
      perm a m borrows

val get
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (borrows k v))
  (a:tbl h vp)
  (i:k)
  : ST (EHT.get_result k v)
       (perm a m borrows)
       (get_post m borrows a i)
       (requires ~ (PartialMap.contains i borrows))
       (ensures fun _ -> True)

(* If i happens to collide with an existing key i' in memory
   then then i' is vacated and the finalizer is called on its contents *)
val put (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (#h:EHT.hash_fn k)
        (#vp:EHT.vp_t k v contents)
        (#m:G.erased (repr k contents))
        (#b:G.erased (borrows k v))
        (a:tbl h vp)
        (i:k)
        (x:v)
        (c:Ghost.erased contents)
  : STT unit
      (perm a m b `star` vp i x c)
      (fun _ -> perm a (Map.upd m i c) (PartialMap.remove i b))


val ghost_put
        (#o:_)
        (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (#h:EHT.hash_fn k)
        (#vp:EHT.vp_t k v contents)
        (#m:G.erased (repr k contents))
        (#b:G.erased (borrows k v))
        (a:tbl h vp)
        (i:k)
        (x:v)
        (c:Ghost.erased contents)
  : STGhost unit o
      (perm a m b `star` vp i x c)
      (fun _ -> perm a (Map.upd m i c) (PartialMap.remove i b))
      (requires
        PartialMap.sel i b == Some x)
      (ensures fun _ -> 
        True)

let with_key_post_present_predicate
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (m:G.erased (repr k contents))
  (b:G.erased (borrows k v))
  (a:tbl h vp)
  (i:k)
  (#res:Type)
  (f_post:contents -> contents -> res -> vprop)
  (r:res)
  : contents -> vprop
  = fun c' ->
    perm a (Map.upd m i c') b
      `star`
    f_post (Map.sel m i) c' r
  
let with_key_post
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (m:G.erased (repr k contents))
  (b:G.erased (borrows k v))
  (a:tbl h vp)
  (i:k)
  (#res:Type)
  (f_pre:vprop)
  (f_post:contents -> contents -> res -> vprop)
  : EHT.get_result k res -> vprop
  = fun r ->
    match r with
    | EHT.Present res ->
      exists_ (with_key_post_present_predicate m b a i f_post res)
    | _ ->
      perm a m b
        `star`
      f_pre

val with_key
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (#m:G.erased (repr k contents))
  (#b:G.erased (borrows k v))  
  (a:tbl h vp)
  (i:k)
  (#res:Type)
  (#f_pre:vprop)
  (#f_post:contents -> contents -> res -> vprop)
  ($f:(x:v -> STT res
             (f_pre `star` vp i x (Map.sel m i))
             (fun res -> exists_ (fun c' -> f_post (Map.sel m i) c' res `star` vp i x c'))))
  : ST (EHT.get_result k res)
       (perm a m b `star` f_pre)
       (with_key_post m b a i f_pre f_post)
       (requires ~(PartialMap.contains i b))
       (ensures fun _ -> True)

let elim_with_key_post_present
        #o
        (#k:eqtype)
        (#v #contents:Type0)
        (#vp:EHT.vp_t k v contents)
        (#h:EHT.hash_fn k)
        (#m:G.erased (repr k contents))
        (#b:G.erased (borrows k v))        
        (#a:tbl h vp)
        (#i:k)
        (#res:Type)
        (#f_pre:vprop)
        (#f_post:contents -> contents -> res -> vprop)
        (r:res)
  : STGhostT (G.erased contents) o
    (with_key_post m b a i f_pre f_post (EHT.Present r))
    (fun c' ->
       perm a (Map.upd m i c') b
         `star`
       f_post (Map.sel m i) c' r)
  = rewrite
      (with_key_post m b a i f_pre f_post (EHT.Present r))
      (exists_ (with_key_post_present_predicate m b a i f_post r));
    let c' = elim_exists () in
    rewrite (with_key_post_present_predicate m b a i f_post r c') _;
    c'
