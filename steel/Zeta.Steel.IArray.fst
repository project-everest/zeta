module Zeta.Steel.IArray

module G = FStar.Ghost
module ETbl = Steel.ST.EphemeralHashtbl

let tbl #k #v #contents h vp = finalizer:ETbl.finalizer_t vp & ETbl.tbl h finalizer

let repr_to_eht_repr (#k:eqtype) (#contents:Type0) (m:repr k contents)
  : ETbl.repr k contents
  = PartialMap.literal (fun x -> if m `Map.contains` x then Some (Map.sel m x) else None)

let perm t m =
  ETbl.tperm (dsnd t) (repr_to_eht_repr m) (PartialMap.empty _ _)

let unpack_perm (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (#m:G.erased (repr k contents))
  (a:tbl h vp)
  : STGhostT unit opened
      (perm a m)
      (fun _ -> ETbl.tperm (dsnd a) (repr_to_eht_repr m) (PartialMap.empty k v))
  = rewrite (perm a m) _

let pack_perm (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:EHT.vp_t k v contents)
  (#h:EHT.hash_fn k)
  (#finalizer:ETbl.finalizer_t vp)
  (#e_m:ETbl.repr k contents)
  (#e_borrows:PartialMap.t k v)
  (e_a:ETbl.tbl h finalizer)
  (a:tbl h vp)
  (m:repr k contents)
  : STGhost unit opened
      (ETbl.tperm e_a e_m e_borrows)
      (fun _ -> perm a m)
      (requires
        a == (| finalizer, e_a |) /\
        PartialMap.equal e_m (repr_to_eht_repr m) /\
        PartialMap.equal e_borrows (PartialMap.empty _ _))
      (ensures fun _ -> True)
  = rewrite _ (perm a m)

let create #k #v #contents #vp h n finalize init =
  let etbl = ETbl.create h finalize n in
  let r = (| finalize, etbl |) in
  pack_perm etbl r (Map.restrict Set.empty (Map.const #k #contents init));
  return r

let free a = ETbl.free (dsnd a)

let put #k #v #contents #h #vp #m a i x c =
  unpack_perm a;
  ETbl.put (dsnd a) i x c;
  pack_perm (dsnd a) a (Map.upd m i (G.reveal c))

let remove #k #v #contents #h #vp #m a i =
  unpack_perm a;
  let b = ETbl.remove (dsnd a) i in
  pack_perm (dsnd a) a m;
  return b

let etbl_with_key_post_to_with_key_post (#opened:_)
  (#k:eqtype) (#v #contents:Type0) (#vp:ETbl.vp_t k v contents) (#h:ETbl.hash_fn k)
  (#m:repr k contents)
  (a:tbl h vp)
  (i:k)
  (#res:Type)
  (f_pre:vprop)
  (f_post:contents -> contents -> res -> vprop)
  (r:ETbl.get_result k res)
  : STGhostT unit opened
      (ETbl.with_key_post (repr_to_eht_repr m) (PartialMap.empty _ _) (dsnd a) i f_pre f_post r)
      (fun _ -> with_key_post m a i f_pre f_post r)
  = let etbl_m = repr_to_eht_repr m in
    match r, PartialMap.sel i etbl_m with
    | ETbl.Present r0, Some c ->
      rewrite
        (ETbl.with_key_post _ _ _ _ _ _ _)
        (exists_ (ETbl.with_key_post_present_predicate (repr_to_eht_repr m)
                                                       (PartialMap.empty _ _)
                                                       (dsnd a) i f_post c r0));
      let c' = elim_exists () in
      assert (PartialMap.equal (PartialMap.upd i (G.reveal c') (repr_to_eht_repr m))
                               (repr_to_eht_repr (Map.upd m i (G.reveal c'))));
      rewrite
        (ETbl.with_key_post_present_predicate _ _ _ _ _ _ _ _)
        (with_key_post_present_predicate m a i f_post r0 (G.reveal c'));

      intro_exists (G.reveal c') (with_key_post_present_predicate m a i f_post r0);

      rewrite _ (with_key_post m a i f_pre f_post r)
    | ETbl.Present r0, None ->
      rewrite
        (ETbl.with_key_post _ _ _ _ _ _ _)
        (pure False);
      elim_pure False;
      rewrite emp _
    | ETbl.Absent, _ -> rewrite (ETbl.with_key_post _ _ _ _ _ _ _) _
    | ETbl.Missing j, _ ->
      rewrite
        (ETbl.with_key_post _ _ _ _ _ _ _)
        (ETbl.tperm (dsnd a) (repr_to_eht_repr m) (PartialMap.empty _ _)
           `star`
         f_pre
           `star`
         pure (ETbl.map_contains_prop j (repr_to_eht_repr m)));
      elim_pure _;
      rewrite
        (ETbl.tperm (dsnd a) (repr_to_eht_repr m) (PartialMap.empty _ _)
           `star`
         f_pre) _

let with_key #k #v #contents #vp #h #m a i #res #f_pre #f_post $f =
  unpack_perm a;
  let r = ETbl.with_key (dsnd a) i #_ #f_pre #f_post f in
  etbl_with_key_post_to_with_key_post a i f_pre f_post r;
  rewrite _ (with_key_post m a i f_pre f_post r);
  return r
