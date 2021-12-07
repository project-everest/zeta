module Zeta.Steel.GhostSharedMap
open Steel.ST.Util
open FStar.Map
open FStar.PCM
open FStar.Preorder
open Steel.Preorder
open Zeta.Steel.Util
open FStar.TSet
open Steel.FractionalPermission
#push-options "--z3cliopt 'smt.qi.eager_threshold=100' --fuel 0 --ifuel 2 --z3rlimit_factor 4"
let kmap (k:eqtype) (v:Type) (p:preorder v) =
  Map.t k (option perm & vhist p)

#push-options "--fuel 1"
let initial_map (#k:eqtype) (#v:Type) (#p:preorder v)
                (f:option perm) (value:v)
  : kmap k v p
  = map_literal (fun _ -> f, ([value] <: vhist p))
#pop-options

[@@erasable]
noeq
type knowledge (k:eqtype) (v:Type) (p:preorder v) =
  | Full     : kmap k v p -> knowledge k v p
  | Owns     : kmap k v p -> knowledge k v p
  | Nothing  : knowledge k v p

let b2p (b:bool)
  : prop
  = b == true

let perm_opt_composable (p0 p1:option perm)
  : prop
  = match p0, p1 with
    | None, None -> True
    | Some p, None
    | None, Some p -> b2p (p `lesser_equal_perm` full)
    | Some p0, Some p1 -> b2p (sum_perm p0 p1 `lesser_equal_perm` full)

let kmap_composable_k (#k:eqtype) (#v:Type) (#p:preorder v) (m0 m1: kmap k v p)
                      (key:k)
   : prop
   = match Map.sel m0 key, Map.sel m1 key with
     | (None, v0), (None, v1) ->
       p_composable _ v0 v1

     | (Some p, v), (None, v')
     | (None, v'), (Some p, v) ->
       v `extends` v' /\
       perm_opt_composable (Some p) None

     | (Some p0, v0), (Some p1, v1) ->
        perm_opt_composable (Some p0) (Some p1) /\
        v0 == v1

let kmap_composable (#k:eqtype) (#v:Type) (#p:preorder v) (m0 m1: kmap k v p)
   : prop
   = forall k. kmap_composable_k m0 m1 k

let full_kmap_composable_k (#k:eqtype) (#v:Type) (#p:preorder v) (full:kmap k v p) (m1: kmap k v p) (key:k)
  : prop
  = let p0, v0 = Map.sel full key in
    let p1, v1 = Map.sel m1 key in
    perm_opt_composable p0 p1   /\
    (match p1 with
     | None -> v0 `extends` v1
     | Some _ -> v0 == v1)

let full_kmap_composable (#k:eqtype) (#v:Type) (#p:preorder v) (full:kmap k v p) (m1: kmap k v p)
  : prop
  = forall k. full_kmap_composable_k full m1 k

let composable #k #v #p
  : symrel (knowledge k v p)
  = fun (k0 k1:knowledge k v p) ->
    match k0, k1 with
    | Nothing, _
    | _, Nothing -> True

    | Full _, Full _ ->
      False

    | Full m, Owns m'
    | Owns m', Full m ->
      full_kmap_composable m m'

    | Owns m, Owns m' ->
      kmap_composable m m'

let p_op (#a: Type u#a) (q:preorder a) (x:vhist q) (y:vhist q{p_composable q x y}) : vhist q =
  p_op _ x y

let compose_kmaps (#k:eqtype) (#v:Type) (#p:preorder v)
                 (m0: kmap k v p)
                 (m1: kmap k v p { kmap_composable m0 m1 })
  : kmap k v p
  =  map_literal
          (fun k ->
            match Map.sel m0 k, Map.sel m1 k with
            | (None, v0), (None, v1) ->
               None, p_op _ v0 v1

            | (Some p, v), (None, _)
            | (None, _), (Some p, v) ->
              Some p, v

            | (Some p0, v0), (Some p1, _) ->
              Some (sum_perm p0 p1), v0)


let compose_kmaps_comm (#k:eqtype) (#v:Type) (#p:preorder v)
                       (m0: kmap k v p)
                       (m1: kmap k v p { kmap_composable m0 m1 })
 : Lemma (compose_kmaps m0 m1 `Map.equal` compose_kmaps m1 m0)
         [SMTPat (compose_kmaps m0 m1);
          SMTPat (compose_kmaps m1 m0)]
 = ()

let compose_maps_assoc (#k:eqtype) (#v:Type) (#p:preorder v)
                       (m0: kmap k v p)
                       (m1: kmap k v p)
                       (m2: kmap k v p {
                         kmap_composable m1 m2 /\
                         kmap_composable m0 (compose_kmaps m1 m2)
                       })
 : Lemma (kmap_composable m0 m1 /\
          kmap_composable (compose_kmaps m0 m1) m2 /\
          compose_kmaps m0 (compose_kmaps m1 m2) `Map.equal`
          compose_kmaps (compose_kmaps m0 m1) m2)
         [SMTPat (compose_kmaps (compose_kmaps m0 m1) m2);
          SMTPat (compose_kmaps m0 (compose_kmaps m2 m2))]
 = ()


let compose_maps_assoc_r (#k:eqtype) (#v:Type) (#p:preorder v)
                       (m0: kmap k v p)
                       (m1: kmap k v p)
                       (m2: kmap k v p {
                         kmap_composable m0 m1 /\
                         kmap_composable (compose_kmaps m0 m1) m2
                       })
 : Lemma (kmap_composable m1 m2 /\
          kmap_composable m0 (compose_kmaps m1 m2) /\
          compose_kmaps m0 (compose_kmaps m1 m2) `Map.equal`
          compose_kmaps (compose_kmaps m0 m1) m2)
         [SMTPat (compose_kmaps (compose_kmaps m0 m1) m2);
          SMTPat (compose_kmaps m0 (compose_kmaps m2 m2))]
 = ()

let compose #k #v #p (k0:knowledge k v p)
                     (k1:knowledge k v p { composable k0 k1 })
  : knowledge k v p
  = match k0, k1 with
    | Nothing, k
    | k, Nothing -> k

    | Full m, Owns m'
    | Owns m', Full m ->
      Full (compose_kmaps m m')

    | Owns m, Owns m' ->
      Owns (compose_kmaps m m')

let kmap_composable_assoc_l #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           kmap_composable k1 k2 /\
           kmap_composable k0 (compose_kmaps k1 k2))
    (ensures
           kmap_composable k0 k1 /\
           kmap_composable (compose_kmaps k0 k1) k2)
  = ()

let kmap_composable_assoc_r #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           kmap_composable k0 k1 /\
           kmap_composable (compose_kmaps k0 k1) k2)
    (ensures
           kmap_composable k1 k2 /\
           kmap_composable k0 (compose_kmaps k1 k2))
  = ()


let full_kmap_composable_assoc_r_0 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           full_kmap_composable k0 k1 /\
           full_kmap_composable (compose_kmaps k0 k1) k2)
    (ensures
           kmap_composable k1 k2 /\
           full_kmap_composable k0 (compose_kmaps k1 k2))
  = ()


let full_kmap_composable_assoc_r_1 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           full_kmap_composable k1 k0 /\
           full_kmap_composable (compose_kmaps k0 k1) k2)
    (ensures
           full_kmap_composable k1 k2 /\
           full_kmap_composable (compose_kmaps k1 k2) k0)
  = ()

let full_kmap_composable_assoc_r_2 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           kmap_composable k1 k0 /\
           full_kmap_composable k2 (compose_kmaps k0 k1))
    (ensures
           full_kmap_composable k2 k1 /\
           full_kmap_composable (compose_kmaps k1 k2) k0)
  = ()



let full_kmap_composable_assoc_l_0 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           kmap_composable k1 k2 /\
           full_kmap_composable k0 (compose_kmaps k1 k2))
    (ensures
           full_kmap_composable k0 k1 /\
           full_kmap_composable (compose_kmaps k0 k1) k2)
  = ()


let full_kmap_composable_assoc_l_1 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           full_kmap_composable k1 k2 /\
           full_kmap_composable (compose_kmaps k1 k2) k0)
    (ensures
           full_kmap_composable k1 k0 /\
           full_kmap_composable (compose_kmaps k0 k1) k2)
  = ()

let full_kmap_composable_assoc_l_2 #k #v #p (k0 k1 k2: kmap k v p)
  : Lemma
    (requires
           full_kmap_composable k2 k1 /\
           full_kmap_composable (compose_kmaps k1 k2) k0)
    (ensures
           kmap_composable k1 k0 /\
           full_kmap_composable k2 (compose_kmaps k0 k1))
  = ()

let composable_assoc_r #k #v #p (k0 k1 k2: knowledge k v p)
  : Lemma
    (requires  composable k0 k1 /\
               composable (compose k0 k1) k2)
    (ensures
               composable k1 k2 /\
               composable k0 (compose k1 k2))
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | _ ->
      (match k0 with
       | Full m0 -> (
         match k1, k2 with
         | Owns m1, Owns m2 ->
           full_kmap_composable_assoc_r_0 m0 m1 m2
         | Owns m1, Full m2 -> ()
         | Full m1, Owns m2 -> ()
         | Full m1, Full m2 -> ()
       )

       | Owns m0 -> (
         match k1, k2 with
         | Owns m1, Owns m2 ->
           kmap_composable_assoc_r m0 m1 m2
         | Owns m1, Full m2 ->
           full_kmap_composable_assoc_r_2 m0 m1 m2
         | Full m1, Owns m2 ->
           full_kmap_composable_assoc_r_1 m0 m1 m2
         | Full m1, Full m2 -> ()
       )
      )


let composable_assoc_l #k #v #p (k0 k1 k2: knowledge k v p)
  : Lemma
    (requires
               composable k1 k2 /\
               composable k0 (compose k1 k2))
    (ensures   composable k0 k1 /\
               composable (compose k0 k1) k2)
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | _ ->
      (match k0 with
       | Full m0 -> (
         match k1, k2 with
         | Owns m1, Owns m2 ->
           full_kmap_composable_assoc_l_0 m0 m1 m2
         | Owns m1, Full m2 -> ()
         | Full m1, Owns m2 -> ()
         | Full m1, Full m2 -> ()
       )

       | Owns m0 -> (
         match k1, k2 with
         | Owns m1, Owns m2 ->
           kmap_composable_assoc_l m0 m1 m2
         | Owns m1, Full m2 ->
           full_kmap_composable_assoc_l_2 m0 m1 m2
         | Full m1, Owns m2 ->
           full_kmap_composable_assoc_l_1 m0 m1 m2
         | Full m1, Full m2 -> ()
       )
      )


let p0 #k #v #p : pcm' (knowledge k v p) = {
  composable;
  op=compose;
  one=Nothing
}

let kmap_of_knowledge #k #v #p (kn:knowledge k v p { ~(Nothing? kn) })
  : GTot (kmap k v p)
  = match kn with
    | Owns m
    | Full m -> m


let pcm #k #v #p : pcm (knowledge k v p) = {
  p = p0;
  comm = (fun _ _ -> ());
  assoc = (fun k0 k1 k2 ->
             composable_assoc_l k0 k1 k2;
             match k0, k1, k2 with
             | Nothing, _, _
             | _, Nothing, _
             | _, _, Nothing -> ()
             | _ ->
               compose_maps_assoc (kmap_of_knowledge k0)
                                  (kmap_of_knowledge k1)
                                  (kmap_of_knowledge k2));
  assoc_r = (fun k0 k1 k2 ->
               composable_assoc_r k0 k1 k2;
               match k0, k1, k2 with
               | Nothing, _, _
               | _, Nothing, _
               | _, _, Nothing -> ()
               | _ ->
                 compose_maps_assoc_r (kmap_of_knowledge k0)
                                      (kmap_of_knowledge k1)
                                      (kmap_of_knowledge k2));
  is_unit = (fun _ -> ());
  refine = (fun x -> Full? x == true);
}

let tmap (k:eqtype) (v:Type0) (c:preorder v) = Map.t k (hist c)


let kmap_perm_of (#k:eqtype)
                 (#v:Type)
                 (#p:preorder v)
                 (m:kmap k v p)
                 (key:k)
    = fst (Map.sel m key)

let kmap_owns_key (#k:eqtype)
                  (#v:Type)
                  (#p:preorder v)
                  (m:kmap k v p)
                  (key:k)
    = kmap_perm_of m key == Some full

let kmap_value_of (#k:eqtype)
                  (#v:Type)
                  (#p:preorder v)
                  (m:kmap k v p)
                  (key:k)
    = snd (Map.sel m key)

let kmap_update_key (#k:eqtype)
                    (#v:Type)
                    (#p:preorder v)
                    (m:kmap k v p)
                    (key:k)
                    (value:vhist p)
    = Map.upd m key (kmap_perm_of m key, value)

let update_key (#k:eqtype)
               (#v:Type)
               (#p:preorder v)
               (m:kmap k v p)
               (key:k)
               (v1:vhist p {
                 kmap_owns_key m key /\
                 v1 `extends` kmap_value_of m key
               })
  : frame_preserving_upd pcm (Owns m) (Owns (kmap_update_key m key v1))
  = fun full_v ->
      assert (Full? full_v);
      assert (compatible pcm (Owns m) full_v);
      let Full full_m = full_v in
      let res = Full (kmap_update_key full_m key v1) in
      let m' = (kmap_update_key m key v1) in
      eliminate exists frame. composable (Owns m) frame /\ compose frame (Owns m) == full_v
      returns (compatible pcm (Owns (kmap_update_key m key v1)) res)
      with _. (
           assume (composable (Owns (kmap_update_key m key v1)) frame);
           assume (compose frame (Owns (kmap_update_key m key v1)) == res)
      );
      assert (compatible pcm (Owns (kmap_update_key m key v1)) res);
      assume (forall (frame:_{composable (Owns m) frame}).
                composable (Owns m') frame /\
                (compose (Owns m) frame == full_v ==> compose (Owns m') frame == res));
      res


val t (k:eqtype) (v:Type0) (c:preorder v) : Type0

val k_of (#k:eqtype) (#v:Type0) (#c:preorder v)
         (t:t k v c)
         (knowledge: knowledge k v c)
  : vprop

val share  (#o:_)
           (#k:eqtype) (#v:Type0) (#c:preorder v)
           (#m0 :kmap k v c)
           (#m1: kmap k v c { kmap_composable m0 m1 })
           (t:t k v c)
  : STGhostT unit o
    (k_of t (Owns (compose_kmaps m0 m1)))
    (fun _ -> k_of t (Owns m0) `star` k_of t (Owns m1))

val gather (#o:_)
           (#k:eqtype) (#v:Type0) (#c:preorder v)
           (#m0 #m1: kmap k v c)
           (t:t k v c)
  : STGhostT (_:unit { kmap_composable m0 m1 }) o
    (k_of t (Owns m0) `star` k_of t (Owns m1))
    (fun _ -> k_of t (Owns (compose_kmaps m0 m1)))

let ksnapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
             (m: kmap k v c)
  : kmap k v c
  = map_literal (fun k -> None, snd (Map.sel m k))

let snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
             (m: kmap k v c)
  : Map.t k v
  = map_literal (fun k -> curval (snd (Map.sel m k)))

let global_snapshot (#k:eqtype) (#v:Type0) (#c:preorder v)
                    (t:t k v c)
                    (m: Map.t k v)
  : vprop
  = exists_ (fun (km:kmap k v c) ->
        pure (snapshot km == m) `star`
        k_of t (Owns (ksnapshot km)))

val take_snapshot (#o:_)
                  (#k:eqtype) (#v:Type0) (#c:preorder v)
                  (#m: kmap k v c)
                  (t:t k v c)
  : STGhostT unit o
    (k_of t (Owns m))
    (fun _ -> k_of t (Owns m) `star` global_snapshot t (snapshot m))

let owns_key (#k:eqtype) (#v:Type0) (#c:preorder v)
             (t:t k v c)
             (key:k)
             (perm:perm)
             (value:v)
  = exists_ (fun (m:kmap k v c) ->
       pure ((forall key'. (key<>key' ==> fst (Map.sel m key') == None)) /\
             (match Map.sel m key with
              | None, _ -> False
              | Some p, h ->
                perm == p /\
                curval h == value)) `star`
       k_of t (Owns m))

let snapshot_of_key (#k:eqtype) (#v:Type0) (#c:preorder v)
                    (t:t k v c)
                    (key:k)
                    (value:v)
  = exists_ (fun (m:kmap k v c) ->
       pure ((forall key'. fst (Map.sel m key') == None) /\
             (match Map.sel m key with
              | Some _, _ -> False
              | None, h -> curval h == value)) `star`
       k_of t (Owns m))

val local_snapshot (#o:_)
                   (#k:eqtype) (#v:Type0) (#c:preorder v)
                   (#key:k) (#frac:_) (#value:v)
                   (t:t k v c)
  : STGhostT unit o
    (owns_key t key frac value)
    (fun _ -> owns_key t key frac value `star` snapshot_of_key t key value)

val dup_snapshot (#o:_)
                 (#k:eqtype) (#v:Type0) (#c:preorder v)
                 (#key:k) (#value:v)
                 (t:t k v c)
  : STGhostT unit o
    (snapshot_of_key t key value)
    (fun _ -> snapshot_of_key t key value `star` snapshot_of_key t key value)

val update (#o:_)
           (#k:eqtype) (#v:Type0) (#c:preorder v)
           (#key:k) (#value:v)
           (t:t k v c)
           (value':v {c value value'})
  : STGhostT unit o
    (owns_key t key full_perm value)
    (fun _ -> owns_key t key full_perm value')

val update_global_snapshot (#o:_)
                           (#k:eqtype) (#v:Type0) (#c:preorder v)
                           (#key:k) (#frac:_) (#value:v)
                           (t:t k v c)
                           (m:Map.t k v)
  : STGhostT unit o
    (owns_key t key frac value `star` global_snapshot t m)
    (fun _ -> owns_key t key frac value `star` global_snapshot t (Map.upd m key value))
