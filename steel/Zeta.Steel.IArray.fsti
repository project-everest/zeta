module Zeta.Steel.IArray
open Steel.ST.Util
open Zeta.Steel.Util

module G = FStar.Ghost
module Set = FStar.Set
module Map = FStar.Map
module U32 = FStar.UInt32

type hash_fn (k:eqtype) = k -> U32.t

val tbl (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (h:hash_fn k)
        (vp:k -> v -> contents -> vprop)
  : Type0

let repr (k:eqtype) (contents:Type0) = Map.t k contents

let set_add (s:Set.set 'a) (x:'a) = Set.union s (Set.singleton x)
let set_remove (s:Set.set 'a) (x:'a) = Set.intersect s (Set.complement (Set.singleton x))


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
         (#h:hash_fn k)
         (#vp: k -> v -> contents -> vprop)
         (t:tbl h vp)
         ([@@@smt_fallback] m:repr k contents)
         ([@@@smt_fallback] borrows:Set.set k)
  : vprop

let finalizer (#k:eqtype)
              (#v:Type)
              (#contents:Type)
              (vp:k -> v -> contents -> vprop) =
  x:k -> y:v -> STT unit (exists_ (vp x y)) (fun _ -> emp)

val create (#k:eqtype)
           (#v:Type0)
           (#contents:Type0)
           (#vp: k -> v -> contents -> vprop)
           (h:hash_fn k)
           (n:U32.t{U32.v n > 0})
           (finalize: finalizer vp)
  : STT (tbl h vp) emp (fun a -> perm a empty_map Set.empty)


let get_post (#k:eqtype)
             (#v:Type0)
             (#contents:Type0)
             (#h:hash_fn k)
             (#vp: k -> v -> contents -> vprop)
             (m:G.erased (repr k contents))
             (b:G.erased (Set.set k))
             (a:tbl h vp)
             (i:k)
             (res:option v)
  : vprop
  = let c = Map.sel m i in
    match res with
    | Some x ->
      vp i x c `star` perm a m (set_add b i)
    | _ -> perm a m b

(* Returns the value associated with i and permission to it.

   In this formulation, the rest of the map becomes unusable
   until permission to the returned value is restored to the map *)
val get (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (#h:hash_fn k)
        (#vp: k -> v -> contents -> vprop)
        (#m:G.erased (repr k contents))
        (#b:G.erased (Set.set k))
        (a:tbl h vp)
        (i:k)
  : ST (option v)
       (perm a m b)
       (get_post m b a i)
       (requires not (Set.mem i b))
       (ensures fun o -> Some? o ==> Map.contains m i)

(* If i happens to collide with an existing key i' in memory
   then then i' is vacated and the finalizer is called on its contents *)
val put (#k:eqtype)
        (#v:Type0)
        (#contents:Type0)
        (#h:hash_fn k)
        (#vp: k -> v -> contents -> vprop)
        (#m:G.erased (repr k contents))
        (#b:G.erased (Set.set k))
        (a:tbl h vp)
        (i:k)
        (x:v)
        (c:Ghost.erased contents)
  : STT unit
      (perm a m b `star` vp i x c)
      (fun _ -> perm a (Map.upd m i c) (set_remove b i))

(* Call the finalizer on every value stored in memory
   and then frees the array itself *)
val free (#k:eqtype)
         (#v:Type0)
         (#h:hash_fn k)
         (#contents: Type0)
         (#vp:k -> v -> contents -> vprop)
         (#m:G.erased (repr k contents))
         (a:tbl h vp)
  : STT unit
      (perm a m Set.empty)
      (fun _ -> emp)
